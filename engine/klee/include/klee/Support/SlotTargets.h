//===-- SlotTargets.h -------------------------------------------*- C++ -*-===//
//
// Indirect-call targets by the memory slot the called pointer is loaded
// from (DESIGN-D §6, slot targets). Shared by the KLEE sink distance and
// the harness synthesizer, so both read the same call graph.
//
// A slot is where a function pointer lives:
//   - a field (S, i) of a struct type S, S identified up to C11 6.2.7
//     compatibility across translation units (the tag, without the suffix
//     the IR linker appends to a duplicate of the same tag);
//   - the k-th virtual function entry of an Itanium C++ vtable.
// A function f is confined to the slots its uses store it into: a store
// whose address is a field GEP, a constant struct field (an initializer),
// or a vtable entry. Any other use of f's address (an argument, a phi, a
// store through an untyped address, a global table) makes f escaped.
// The targets of a call whose callee is loaded from slot s are the
// functions of the call's type confined to s, plus every escaped function
// of that type. A call whose callee is not a slot load keeps every
// address-taken function of its type.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SLOTTARGETS_H
#define KLEE_SLOTTARGETS_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"

#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>

namespace klee {
namespace slots {

// (struct identity, field) or ("", virtual index).
using Slot = std::pair<std::string, uint64_t>;

inline std::string structKey(llvm::StructType *ST) {
  if (ST->isLiteral() || !ST->hasName()) {
    // A literal struct is uniqued by its element types.
    std::string s;
    llvm::raw_string_ostream os(s);
    ST->print(os);
    return os.str();
  }
  llvm::StringRef n = ST->getName();
  // The IR linker renames a second definition of the same tag to tag.N.
  while (true) {
    size_t dot = n.rfind('.');
    if (dot == llvm::StringRef::npos || dot + 1 == n.size())
      break;
    llvm::StringRef tail = n.substr(dot + 1);
    if (!llvm::all_of(tail, [](char c) { return c >= '0' && c <= '9'; }))
      break;
    n = n.substr(0, dot);
  }
  return n.str();
}

// The field slot an address designates: the innermost struct field a GEP
// with constant struct indices selects, when that field holds a pointer
// (directly or as an array element).
inline std::optional<Slot> fieldSlot(const llvm::Value *P) {
  const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P);
  if (!G || G->getNumIndices() < 2)
    return std::nullopt;
  llvm::Type *T = G->getSourceElementType();
  std::optional<Slot> s;
  auto it = G->idx_begin();
  ++it; // steps over the pointer operand
  for (; it != G->idx_end(); ++it) {
    if (auto *ST = llvm::dyn_cast<llvm::StructType>(T)) {
      const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(it->get());
      if (!CI)
        return std::nullopt;
      uint64_t i = CI->getZExtValue();
      if (i >= ST->getNumElements())
        return std::nullopt;
      s = Slot{structKey(ST), i};
      T = ST->getElementType(i);
    } else if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(T)) {
      T = AT->getElementType();
    } else {
      return std::nullopt;
    }
  }
  if (!s || !T->isPointerTy())
    return std::nullopt;
  return s;
}

// The vtable slot of an Itanium virtual call: the callee is loaded from
// vptr + k, the vptr is loaded from the object, and the object is the
// call's this argument (the first, or the second after an sret pointer).
inline std::optional<Slot> vcallSlot(const llvm::CallBase &CB,
                                     const llvm::LoadInst *L) {
  const llvm::Value *P = L->getPointerOperand();
  uint64_t k = 0;
  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P)) {
    if (G->getNumIndices() != 1 ||
        !G->getSourceElementType()->isPointerTy())
      return std::nullopt;
    const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->idx_begin()->get());
    if (!CI || CI->isNegative())
      return std::nullopt;
    k = CI->getZExtValue();
    P = G->getPointerOperand();
  }
  const auto *V = llvm::dyn_cast<llvm::LoadInst>(P);
  if (!V)
    return std::nullopt;
  const llvm::Value *obj = V->getPointerOperand();
  for (unsigned a = 0; a < 2 && a < CB.arg_size(); ++a)
    if (CB.getArgOperand(a) == obj)
      return Slot{"", k};
  return std::nullopt;
}

// The slot a call's callee is loaded from.
inline std::optional<Slot> calleeSlot(const llvm::CallBase &CB) {
  const auto *L = llvm::dyn_cast<llvm::LoadInst>(
      CB.getCalledOperand()->stripPointerCasts());
  if (!L)
    return std::nullopt;
  if (auto s = vcallSlot(CB, L))
    return s;
  return fieldSlot(L->getPointerOperand());
}

struct Targets {
  std::map<Slot, std::set<const llvm::Function *>> confined;
  std::set<const llvm::Function *> escaped;

  bool admits(const llvm::CallBase &CB, const llvm::Function *F) const {
    auto s = calleeSlot(CB);
    if (!s)
      return true;
    if (escaped.count(F))
      return true;
    auto it = confined.find(*s);
    return it != confined.end() && it->second.count(F);
  }

  void build(const llvm::Module &M) {
    using namespace llvm;
    // Vtable groups: each array of a _ZTV initializer is one vtable; its
    // entries from the first function on are the virtual functions 0, 1, ...
    std::map<const Constant *, uint64_t> vtableBase;
    for (const GlobalVariable &G : M.globals()) {
      if (!G.hasInitializer() || !G.getName().starts_with("_ZTV"))
        continue;
      std::vector<const Constant *> arrays;
      const Constant *I = G.getInitializer();
      if (isa<ConstantArray>(I))
        arrays.push_back(I);
      else if (const auto *CS = dyn_cast<ConstantStruct>(I))
        for (unsigned i = 0; i < CS->getNumOperands(); ++i)
          if (isa<ConstantArray>(CS->getOperand(i)))
            arrays.push_back(CS->getOperand(i));
      for (const Constant *A : arrays) {
        for (unsigned j = 0; j < A->getNumOperands(); ++j)
          if (isa<Function>(A->getOperand(j)->stripPointerCasts())) {
            vtableBase[A] = j;
            break;
          }
      }
    }
    for (const Function &F : M) {
      if (!F.hasAddressTaken())
        continue;
      for (const Use &U : F.uses()) {
        const User *Us = U.getUser();
        if (const auto *CB = dyn_cast<CallBase>(Us);
            CB && CB->isCallee(&U))
          continue;
        if (isa<ICmpInst>(Us))
          continue;
        if (const auto *SI = dyn_cast<StoreInst>(Us);
            SI && U.getOperandNo() == 0) {
          if (auto s = fieldSlot(SI->getPointerOperand())) {
            confined[*s].insert(&F);
            continue;
          }
        } else if (const auto *CS = dyn_cast<ConstantStruct>(Us)) {
          confined[Slot{structKey(CS->getType()), U.getOperandNo()}].insert(&F);
          continue;
        } else if (const auto *CA = dyn_cast<ConstantArray>(Us)) {
          auto vb = vtableBase.find(CA);
          if (vb != vtableBase.end() && U.getOperandNo() >= vb->second) {
            confined[Slot{"", U.getOperandNo() - vb->second}].insert(&F);
            continue;
          }
          // An array of pointers that is a struct field: that field.
          bool inField = false;
          for (const User *AU : CA->users())
            if (const auto *PS = dyn_cast<ConstantStruct>(AU))
              for (unsigned i = 0; i < PS->getNumOperands(); ++i)
                if (PS->getOperand(i) == CA) {
                  confined[Slot{structKey(PS->getType()), i}].insert(&F);
                  inField = true;
                }
          if (inField && CA->getNumUses() > 0) {
            bool allFields = llvm::all_of(CA->users(), [](const User *AU) {
              return isa<ConstantStruct>(AU);
            });
            if (allFields)
              continue;
          }
        }
        escaped.insert(&F);
        break;
      }
    }
  }
};

} // namespace slots
} // namespace klee

#endif
