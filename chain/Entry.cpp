#include "Entry.hpp"
#include "Field.hpp"
#include "Points.hpp"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <cmath>
#include <deque>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {

namespace {

std::string show(const llvm::Function *F) {
  std::string n = F->getName().str();
  std::string d = llvm::demangle(n);
  if (d.empty() || d == n)
    return n;
  return d;
}

bool strongExport(const llvm::Function *F) {
  if (!F || F->isDeclaration() || F->isIntrinsic() || !F->hasName())
    return false;
  if (F->hasLocalLinkage())
    return false;
  if (F->getVisibility() == llvm::GlobalValue::HiddenVisibility)
    return false;
  return true;
}

const llvm::Function *asFunction(const llvm::Value *V) {
  if (!V)
    return nullptr;
  return llvm::dyn_cast<llvm::Function>(V->stripPointerCastsAndAliases());
}

bool sameType(const llvm::Function *F, const llvm::CallBase *C) {
  return F && C && F->getFunctionType() == C->getFunctionType();
}

struct CodePtr {
  const llvm::GlobalVariable *gv = nullptr;
  int64_t off = 0;
  bool operator==(const CodePtr &o) const { return gv == o.gv && off == o.off; }
};

struct CodeHash {
  size_t operator()(const CodePtr &c) const {
    return (size_t)(uintptr_t)c.gv ^ ((size_t)c.off * 1315423911u);
  }
};

struct Field {
  const llvm::StructType *ty = nullptr;
  int64_t off = 0;
  bool operator==(const Field &o) const { return ty == o.ty && off == o.off; }
};

struct FieldHash {
  size_t operator()(const Field &f) const {
    return (size_t)(uintptr_t)f.ty ^ ((size_t)f.off * 1315423911u);
  }
};

struct Slot {
  int id = 0;
  Field field;
  bool operator==(const Slot &o) const { return id == o.id && field == o.field; }
};

struct SlotHash {
  size_t operator()(const Slot &s) const { return FieldHash{}(s.field) ^ ((size_t)s.id * 2654435761u); }
};

// Function-pointer fields are one slot per (struct type, constant offset).
// Virtual-call tables are per object, and only along the copy path described
// in Entry.hpp. Tokens name those objects.
class Solve {
 public:
  explicit Solve(llvm::Module &M) : M(M), DL(M.getDataLayout()) { run(); }

  std::vector<const llvm::Function *> callees(const llvm::CallBase *C, bool) const {
    std::vector<const llvm::Function *> out;
    std::unordered_set<const llvm::Function *> seen;
    auto add = [&](const llvm::Function *F) {
      if (F && seen.insert(F).second)
        out.push_back(F);
    };
    if (const llvm::Function *D = asFunction(C->getCalledOperand())) {
      add(D);
      return out;
    }
    // The call and the function each state a dereferenceable size. The
    // function reaches this call only when those sizes are equal. A missing
    // size leaves the function in the set. LLVM merges every std::function
    // instantiation into one struct; the size is the instantiation.
    auto sameBytes = [&](const llvm::Function *F) {
      unsigned i = 0;
      const unsigned nCall = C->arg_size();
      const unsigned nFun = F->arg_size();
      for (; i < nCall && i < nFun; ++i) {
        if (!C->paramHasAttr(i, llvm::Attribute::Dereferenceable))
          continue;
        if (!F->hasParamAttribute(i, llvm::Attribute::Dereferenceable))
          continue;
        if (C->getParamDereferenceableBytes(i) != F->getParamDereferenceableBytes(i))
          return false;
      }
      return true;
    };
    auto addSized = [&](const llvm::Function *F) {
      if (F && sameBytes(F))
        add(F);
    };
    // The target did not reduce to one function. Functions copied onto this
    // address are the callees when that copy reduced. Otherwise a function
    // constant on the operand, or a function stored at a constant field of a
    // mixed struct, reaches the call. The LLVM function type is not a source
    // of callees. Nothing reached leaves the call open.
    auto flowed = flowAt.find(C);
    if (flowed != flowAt.end() && !flowed->second.empty()) {
      for (const llvm::Function *F : flowed->second)
        if (sameType(F, C))
          addSized(F);
    } else {
      std::unordered_set<const llvm::Value *> walked;
      for (const llvm::Function *F : fnsOf(C->getCalledOperand(), walked, C->getFunction()))
        if (sameType(F, C))
          addSized(F);
    }
    const llvm::Value *obj = nullptr;
    int64_t delta = 0;
    std::unordered_set<const llvm::Value *> seenV;
    if (vtableCall(C->getCalledOperand(), obj, delta, seenV)) {
      auto it = tok.find(obj);
      if (it != tok.end()) {
        for (int t : it->second) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + delta});
            if (fit != fnAt.end() && fit->second && fit->second->getFunctionType() == C->getFunctionType())
              add(fit->second);
          }
        }
      }
    }
    std::sort(out.begin(), out.end(), [](const llvm::Function *a, const llvm::Function *b) {
      return show(a) < show(b);
    });
    return out;
  }

  // Functions that may run this call. A direct callee is that function. A
  // virtual call is the table recovered for this object, or, when that
  // points-to set is empty, every function of this type stored in a table.
  // The second set is an over-approximation of the callees. It is used only
  // to find a copy, not to prove that one function is the target.
  std::vector<const llvm::Function *> slotMay(const llvm::CallBase *C) const {
    std::vector<const llvm::Function *> out;
    std::unordered_set<const llvm::Function *> seen;
    auto add = [&](const llvm::Function *F) {
      if (F && !F->isIntrinsic() && seen.insert(F).second)
        out.push_back(F);
    };
    if (!C)
      return out;
    if (const llvm::Function *D = asFunction(C->getCalledOperand())) {
      add(D);
      return out;
    }
    const llvm::Value *obj = nullptr;
    int64_t delta = 0;
    std::unordered_set<const llvm::Value *> seenV;
    if (!vtableCall(C->getCalledOperand(), obj, delta, seenV))
      return out;
    if (obj) {
      auto it = tok.find(obj);
      if (it != tok.end()) {
        for (int t : it->second) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + delta});
            if (fit != fnAt.end() && fit->second && fit->second->getFunctionType() == C->getFunctionType())
              add(fit->second);
          }
        }
      }
    }
    if (!out.empty())
      return out;
    for (const auto &kv : fnAt)
      if (kv.second && kv.second->getFunctionType() == C->getFunctionType())
        add(kv.second);
    return out;
  }

  // This call passes the argument to P. A direct call does. A function
  // pointer does when the copy into that pointer reduced to P. A vtable
  // slot does when this object's table names P. A type-wide set of
  // functions is not a call of P.
  bool proves(const llvm::CallBase *C, const llvm::Function *P) const {
    if (!C || !P)
      return false;
    if (asFunction(C->getCalledOperand()) == P)
      return true;
    auto sameBytes = [&](const llvm::Function *F) {
      unsigned i = 0;
      const unsigned nCall = C->arg_size();
      const unsigned nFun = F->arg_size();
      for (; i < nCall && i < nFun; ++i) {
        if (!C->paramHasAttr(i, llvm::Attribute::Dereferenceable))
          continue;
        if (!F->hasParamAttribute(i, llvm::Attribute::Dereferenceable))
          continue;
        if (C->getParamDereferenceableBytes(i) != F->getParamDereferenceableBytes(i))
          return false;
      }
      return true;
    };
    auto flowed = flowAt.find(C);
    if (flowed != flowAt.end() && !flowed->second.empty()) {
      for (const llvm::Function *F : flowed->second)
        if (F == P && sameType(F, C) && sameBytes(F))
          return true;
    }
    const llvm::Value *obj = nullptr;
    int64_t delta = 0;
    std::unordered_set<const llvm::Value *> seenV;
    if (!vtableCall(C->getCalledOperand(), obj, delta, seenV))
      return false;
    if (obj) {
      auto it = tok.find(obj);
      if (it != tok.end()) {
        for (int t : it->second) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + delta});
            if (fit != fnAt.end() && fit->second == P && P->getFunctionType() == C->getFunctionType())
              return true;
          }
        }
      }
    }
    // The receiver's points-to set missed this table. P is still a possible
    // target when it overrides the slot in a class derived from the class of
    // the function that contains the call. The derivation is the base list in
    // the Itanium typeinfo stored in the vtable.
    if (P->getFunctionType() != C->getFunctionType())
      return false;
    const llvm::Function *Caller = C->getFunction();
    if (!Caller)
      return false;
    if (!slotsReady) {
      slotsReady = true;
      for (const auto &kv : fnAt) {
        slotsOf[kv.second].push_back(kv.first);
        if (kv.first.first)
          fnTables[kv.second].push_back(kv.first.first);
      }
      for (const llvm::GlobalVariable *gv : tables) {
        if (!gv || !gv->hasInitializer())
          continue;
        for (const llvm::User *U : gv->users()) {
          const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U);
          if (!G)
            continue;
          llvm::APInt off(64, 0);
          if (G->accumulateConstantOffset(DL, off))
            vptrBase[gv].insert(off.getSExtValue());
        }
        const llvm::Constant *init = gv->getInitializer();
        if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(init))
          if (CS->getNumOperands() == 1)
            init = CS->getOperand(0);
        if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(init))
          if (CA->getNumOperands() >= 2)
            if (const auto *TI = llvm::dyn_cast<llvm::GlobalVariable>(CA->getOperand(1)->stripPointerCasts()))
              vtableTI[gv] = TI;
      }
      std::unordered_set<const llvm::Constant *> constSeen;
      std::function<void(const llvm::Constant *, std::vector<const llvm::GlobalVariable *> &)> collect;
      collect = [&](const llvm::Constant *C0, std::vector<const llvm::GlobalVariable *> &gs) {
        if (!C0 || !constSeen.insert(C0).second)
          return;
        if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(C0->stripPointerCasts())) {
          gs.push_back(G);
          return;
        }
        if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(C0)) {
          if (CE->getOpcode() == llvm::Instruction::GetElementPtr || CE->getOpcode() == llvm::Instruction::BitCast ||
              CE->getOpcode() == llvm::Instruction::AddrSpaceCast)
            collect(CE->getOperand(0), gs);
          return;
        }
        if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C0)) {
          for (unsigned i = 0; i < CS->getNumOperands(); ++i)
            collect(CS->getOperand(i), gs);
          return;
        }
        if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C0))
          for (unsigned i = 0; i < CA->getNumOperands(); ++i)
            collect(CA->getOperand(i), gs);
      };
      for (const auto &kv : vtableTI) {
        const llvm::GlobalVariable *TI = kv.second;
        if (!TI || !TI->hasInitializer())
          continue;
        std::vector<const llvm::GlobalVariable *> gs;
        constSeen.clear();
        collect(TI->getInitializer(), gs);
        for (size_t i = 2; i < gs.size(); ++i)
          if (gs[i] && gs[i] != TI)
            tiBases[TI].push_back(gs[i]);
      }
    }
    auto sit = slotsOf.find(P);
    if (sit == slotsOf.end())
      return false;
    std::vector<const llvm::GlobalVariable *> pTIs;
    for (const auto &pl : sit->second) {
      int64_t base = pl.second - delta;
      auto bit = vptrBase.find(pl.first);
      if (bit == vptrBase.end() || !bit->second.count(base))
        continue;
      auto ti = vtableTI.find(pl.first);
      if (ti != vtableTI.end() && ti->second)
        pTIs.push_back(ti->second);
    }
    if (pTIs.empty())
      return false;
    std::unordered_set<const llvm::GlobalVariable *> callerTI;
    auto ct = fnTables.find(Caller);
    if (ct == fnTables.end())
      return false;
    for (const llvm::GlobalVariable *gv : ct->second) {
      auto ti = vtableTI.find(gv);
      if (ti != vtableTI.end() && ti->second)
        callerTI.insert(ti->second);
    }
    if (callerTI.empty())
      return false;
    for (const llvm::GlobalVariable *pTI : pTIs) {
      std::vector<const llvm::GlobalVariable *> q{pTI};
      std::unordered_set<const llvm::GlobalVariable *> seen{pTI};
      for (size_t i = 0; i < q.size(); ++i) {
        if (callerTI.count(q[i]))
          return true;
        auto bt = tiBases.find(q[i]);
        if (bt == tiBases.end())
          continue;
        for (const llvm::GlobalVariable *B : bt->second)
          if (B && seen.insert(B).second)
            q.push_back(B);
      }
    }
    return false;
  }

  // A call through a field of an argument. The functions are those stored
  // into that argument's object, not every function stored into the struct
  // type: one LLVM type can be every std::function.
  bool argField(const llvm::CallBase *C, int &arg, int64_t &off) const {
    std::unordered_set<const llvm::Value *> seen;
    std::vector<const llvm::Value *> stack{C->getCalledOperand()};
    const llvm::LoadInst *load = nullptr;
    while (!stack.empty()) {
      const llvm::Value *V = stack.back();
      stack.pop_back();
      if (!V || !seen.insert(V).second)
        continue;
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        load = L;
        break;
      }
      if (const auto *X = llvm::dyn_cast<llvm::CastInst>(V))
        stack.push_back(X->getOperand(0));
      else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        stack.push_back(Fr->getOperand(0));
      else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values())
          stack.push_back(inc);
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        stack.push_back(Sel->getTrueValue());
        stack.push_back(Sel->getFalseValue());
      }
    }
    if (!load)
      return false;
    auto f = fieldOf(load->getPointerOperand());
    if (!f)
      return false;
    const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(load->getPointerOperand()));
    if (!G)
      return false;
    std::vector<int> args;
    std::unordered_set<const llvm::Value *> seenA;
    whichArgs(G->getPointerOperand(), C->getFunction(), seenA, args);
    if (args.size() != 1)
      return false;
    arg = args[0];
    off = f->off;
    return true;
  }

  // Edges from the callers that pass the object, when a function was stored
  // into that object. Returns false when nothing was stored. The struct type
  // is not then used as the callee set.
  template <class Note>
  bool noteObjectField(const llvm::CallBase *C, Note note) const {
    int arg = -1;
    int64_t off = 0;
    if (asFunction(C->getCalledOperand()) || !argField(C, arg, off))
      return false;
    auto sit = directSites.find(C->getFunction());
    if (sit == directSites.end())
      return false;
    bool any = false;
    for (const llvm::CallBase *S : sit->second) {
      if (static_cast<unsigned>(arg) >= S->arg_size())
        continue;
      std::vector<const llvm::Function *> fns;
      std::unordered_set<const llvm::Value *> seen;
      objectFieldFns(S->getArgOperand(static_cast<unsigned>(arg)), off, fns, seen);
      if (fns.empty())
        continue;
      any = true;
      for (const llvm::Function *D : fns)
        if (sameType(D, C))
          note(S->getFunction(), D);
    }
    return any;
  }

  void objectFieldFns(const llvm::Value *obj, int64_t off, std::vector<const llvm::Function *> &out,
                      std::unordered_set<const llvm::Value *> &seen) const {
    if (!obj || !seen.insert(obj).second)
      return;
    std::deque<const llvm::Value *> q;
    q.push_back(obj);
    std::unordered_set<const llvm::Value *> local{obj};
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
            llvm::isa<llvm::SelectInst>(U)) {
          if (local.insert(U).second)
            q.push_back(U);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          int64_t go = 0;
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            if (offsetOf(G, go) && go == 0 && local.insert(G).second)
              q.push_back(G);
            else if (auto f = fieldOf(G))
              if (f->off == off)
                for (const llvm::User *SU : G->users())
                  if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(SU))
                    if (S->getPointerOperand() == G || stripCasts(S->getPointerOperand()) == G)
                      if (const llvm::Function *Fn = asFunction(S->getValueOperand()))
                        out.push_back(Fn);
          }
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(U);
        if (!C)
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto it = fnPut.find(D);
        if (it == fnPut.end())
          continue;
        for (const FnPut &p : it->second) {
          if (p.off != off || p.arg < 0 || static_cast<unsigned>(p.arg) >= C->arg_size())
            continue;
          if (C->getArgOperand(static_cast<unsigned>(p.arg)) != V)
            continue;
          if (p.fn)
            out.push_back(p.fn);
        }
      }
    }
  }

 private:
  llvm::Module &M;
  const llvm::DataLayout &DL;
  struct SpecFn {
    const llvm::Function *fn = nullptr;
    std::string spec;
    bool init = false;
  };
  std::unordered_map<Field, std::vector<SpecFn>, FieldHash> fieldFn;
  std::map<std::pair<const llvm::GlobalVariable *, int64_t>, const llvm::Function *> fnAt;
  mutable bool slotsReady = false;
  mutable std::unordered_map<const llvm::Function *, std::vector<std::pair<const llvm::GlobalVariable *, int64_t>>> slotsOf;
  mutable std::unordered_map<const llvm::Function *, std::vector<const llvm::GlobalVariable *>> fnTables;
  mutable std::unordered_map<const llvm::GlobalVariable *, std::unordered_set<int64_t>> vptrBase;
  mutable std::unordered_map<const llvm::GlobalVariable *, const llvm::GlobalVariable *> vtableTI;
  mutable std::unordered_map<const llvm::GlobalVariable *, std::vector<const llvm::GlobalVariable *>> tiBases;
  std::unordered_set<const llvm::GlobalVariable *> tables;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::Function *>> retFn;
  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> retSeen;
  std::unordered_map<const llvm::Value *, std::vector<int>> tok;
  std::unordered_map<const llvm::Value *, std::unordered_set<int>> tokSeen;
  std::unordered_map<int, std::unordered_set<CodePtr, CodeHash>> vtbl;
  std::unordered_set<const llvm::Value *> slice;
  // Fields that lie on a path from an allocation to a loaded virtual table.
  // A field the pointer reaches later is not a new object.
  std::unordered_set<const llvm::Value *> demand;
  std::unordered_map<const llvm::Value *, int> rootId;
  std::unordered_set<int> allocTok;
  std::unordered_map<int, int> tokDepth;
  int nextId = 1;
  std::deque<const llvm::Value *> wl;
  std::unordered_set<const llvm::Value *> queued;
  std::unordered_map<Field, std::vector<const llvm::LoadInst *>, FieldHash> fieldLoads;
  std::unordered_map<Field, std::vector<const llvm::Value *>, FieldHash> fieldStored;
  std::unordered_map<const llvm::Value *, std::vector<Slot>> addr;
  std::unordered_map<const llvm::Value *, std::unordered_set<Slot, SlotHash>> addrSeen;
  std::unordered_map<Slot, int, SlotHash> subId;
  std::unordered_map<Slot, std::vector<int>, SlotHash> slotTok;
  std::unordered_map<Slot, std::unordered_set<int>, SlotHash> slotSeen;
  std::unordered_map<Slot, std::vector<const llvm::LoadInst *>, SlotHash> slotLoads;
  std::unordered_map<Slot, std::unordered_set<const llvm::LoadInst *>, SlotHash> slotLoadSeen;
  bool live = false;
  std::unordered_map<const llvm::AllocaInst *, std::vector<const llvm::LoadInst *>> allocaLoads;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> directSites;
  std::vector<const llvm::StoreInst *> vtableStores;

  // A function may return the pointer loaded from a byte offset of one
  // argument, or the address of that field, or store a pointer there. The
  // slot is that argument and that offset.
  struct BoxOff {
    int arg = -1;
    int64_t off = 0;
    bool operator==(const BoxOff &o) const { return arg == o.arg && off == o.off; }
  };
  struct BoxMove {
    int dst = -1;
    int src = -1;
    int64_t off = 0;
    bool operator==(const BoxMove &o) const { return dst == o.dst && src == o.src && off == o.off; }
  };
  std::unordered_map<const llvm::Function *, std::vector<BoxOff>> retBox;
  std::unordered_map<const llvm::Function *, std::vector<BoxOff>> retAddr;
  std::unordered_map<const llvm::Function *, std::vector<BoxMove>> putBox;
  std::unordered_map<const llvm::Function *, std::vector<BoxMove>> mvBox;
  struct FnPut {
    int arg = -1;
    int64_t off = 0;
    const llvm::Function *fn = nullptr;
    bool operator==(const FnPut &o) const { return arg == o.arg && off == o.off && fn == o.fn; }
  };
  std::unordered_map<const llvm::Function *, std::vector<FnPut>> fnPut;
  // Indirect calls whose function pointer flows from a store into the loaded
  // object. Absent is not the struct type: a queried load that did not reduce
  // stays open.
  std::unordered_map<const llvm::CallBase *, std::vector<const llvm::Function *>> flowAt;
  std::unordered_set<const llvm::Function *> objectStored;
  // Every function constant stored by an instruction or an initializer.
  // An all-pointer struct is not a source type, so a load that does not
  // reduce uses this set, keyed by the call's function type.
  std::unordered_set<const llvm::Function *> storedAny;
  // Stored into an all-pointer slot. The merged layout is not a field, so
  // these functions share the call's type and not the struct's name.
  struct GlobFn {
    const llvm::GlobalVariable *gv = nullptr;
    int64_t off = 0;
    const llvm::Function *fn = nullptr;
  };
  std::vector<GlobFn> globFns;
  // A function whose copy could not be reduced to an object. It stays with
  // the struct type: excluding it would drop a call the copies might reach.
  std::unordered_set<const llvm::Function *> unresolved;
  std::unordered_set<const llvm::CallBase *> openQuery;

  bool offsetOf(const llvm::GEPOperator *GEP, int64_t &off) const {
    if (!GEP || !GEP->hasAllConstantIndices())
      return false;
    llvm::APInt ap(DL.getIndexTypeSizeInBits(GEP->getType()), 0);
    if (!GEP->accumulateConstantOffset(DL, ap))
      return false;
    off = ap.getSExtValue();
    return true;
  }

  // stripPointerCasts also drops a getelementptr whose indices are all zero.
  // Field 0 is that getelementptr: the address matches the object, and the
  // instruction still names the field.
  const llvm::Value *stripCasts(const llvm::Value *V) const {
    while (V) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0) {
          V = CE->getOperand(0);
          continue;
        }
      }
      break;
    }
    return V;
  }

  std::optional<Field> fieldOf(const llvm::Value *addr) const {
    const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(addr));
    if (!GEP)
      return std::nullopt;
    const auto *ST = llvm::dyn_cast<llvm::StructType>(GEP->getSourceElementType());
    if (!ST || !ST->isSized())
      return std::nullopt;
    int64_t off = 0;
    if (!offsetOf(GEP, off) || off < 0)
      return std::nullopt;
    auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(ST));
    if (sz.isScalable() || sz.getFixedValue() == 0)
      return std::nullopt;
    return Field{ST, off % (int64_t)sz.getFixedValue()};
  }

  bool ptrIndex(const llvm::Value *addr, const llvm::Value *&base, int64_t &delta) const {
    const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(addr->stripPointerCasts());
    if (!GEP || !GEP->getSourceElementType()->isPointerTy() || !offsetOf(GEP, delta) || delta < 0)
      return false;
    base = GEP->getPointerOperand();
    return true;
  }

  void addFieldFn(Field f, const llvm::Function *F, const std::string &spec, bool init) {
    if (!F)
      return;
    auto &v = fieldFn[f];
    for (const SpecFn &e : v)
      if (e.fn == F && e.spec == spec && e.init == init)
        return;
    v.push_back(SpecFn{F, spec, init});
  }

  // An all-pointer struct is not a source type. LLVM merges every struct of
  // that layout into one type, so a lock table and an allocator become one
  // field. A struct with any other field keeps its layout.
  bool mixedStruct(const llvm::StructType *ST) const {
    if (!ST)
      return false;
    for (llvm::Type *E : ST->elements())
      if (!E->isPointerTy())
        return true;
    return false;
  }

  void place(const llvm::Constant *C, int64_t absOff, std::vector<std::pair<const llvm::StructType *, int64_t>> frames,
             const llvm::GlobalVariable *Root) {
    if (!C)
      return;
    if (const llvm::Function *F = asFunction(C)) {
      storedAny.insert(F);
      if (Root)
        globFns.push_back(GlobFn{Root, absOff, F});
      for (const auto &fr : frames) {
        if (!mixedStruct(fr.first))
          continue;
        auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(fr.first));
        if (sz.isScalable() || sz.getFixedValue() == 0 || fr.second < 0)
          continue;
        addFieldFn({fr.first, fr.second % (int64_t)sz.getFixedValue()}, F, {}, true);
      }
      return;
    }
    if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      const auto *ST = CS->getType();
      const auto *SL = DL.getStructLayout(const_cast<llvm::StructType *>(ST));
      for (unsigned i = 0; i < CS->getNumOperands(); ++i) {
        int64_t fo = (int64_t)SL->getElementOffset(i);
        auto next = frames;
        for (auto &fr : next)
          fr.second += fo;
        next.push_back({ST, fo});
        place(llvm::cast<llvm::Constant>(CS->getOperand(i)), absOff + fo, std::move(next), Root);
      }
      return;
    }
    if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
      llvm::Type *ET = const_cast<llvm::Type *>(CA->getType()->getElementType());
      if (!ET->isSized())
        return;
      auto es = DL.getTypeAllocSize(ET);
      if (es.isScalable() || es.getFixedValue() == 0)
        return;
      int64_t step = (int64_t)es.getFixedValue();
      for (unsigned i = 0; i < CA->getNumOperands(); ++i) {
        auto next = frames;
        for (auto &fr : next)
          fr.second += (int64_t)i * step;
        place(llvm::cast<llvm::Constant>(CA->getOperand(i)), absOff + (int64_t)i * step, std::move(next), Root);
      }
      return;
    }
    if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(C->stripPointerCastsAndAliases())) {
      if (tables.count(GV)) {
        for (const auto &fr : frames) {
          (void)fr;
        }
      }
    }
  }

  void indexTables(const llvm::GlobalVariable *GV, const llvm::Constant *C, int64_t off) {
    if (const llvm::Function *F = asFunction(C)) {
      fnAt[{GV, off}] = F;
      tables.insert(GV);
      return;
    }
    if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      const auto *SL = DL.getStructLayout(const_cast<llvm::StructType *>(CS->getType()));
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        indexTables(GV, llvm::cast<llvm::Constant>(CS->getOperand(i)), off + (int64_t)SL->getElementOffset(i));
      return;
    }
    if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
      llvm::Type *ET = const_cast<llvm::Type *>(CA->getType()->getElementType());
      if (!ET->isSized())
        return;
      auto es = DL.getTypeAllocSize(ET);
      if (es.isScalable() || es.getFixedValue() == 0)
        return;
      int64_t step = (int64_t)es.getFixedValue();
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        indexTables(GV, llvm::cast<llvm::Constant>(CA->getOperand(i)), off + (int64_t)i * step);
    }
  }

  CodePtr codePtr(const llvm::Value *V) const {
    if (!V || asFunction(V))
      return {};
    const llvm::Value *S = V->stripPointerCastsAndAliases();
    const llvm::GlobalVariable *GV = nullptr;
    int64_t off = 0;
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(S)) {
      GV = llvm::dyn_cast<llvm::GlobalVariable>(G->getPointerOperand()->stripPointerCastsAndAliases());
      if (!GV || !offsetOf(G, off))
        return {};
    } else
      GV = llvm::dyn_cast<llvm::GlobalVariable>(S);
    if (!GV || !tables.count(GV))
      return {};
    return {GV, off};
  }

  int idOf(const llvm::Value *V) {
    auto it = rootId.find(V);
    if (it != rootId.end())
      return it->second;
    int id = nextId++;
    rootId.emplace(V, id);
    return id;
  }

  void addTok(const llvm::Value *V, int t) {
    if (!V || t <= 0)
      return;
    if (slice.insert(V).second)
      maybeSeed(V);
    if (!tokSeen[V].insert(t).second)
      return;
    tok[V].push_back(t);
    if (queued.insert(V).second)
      wl.push_back(V);
  }

  void maybeSeed(const llvm::Value *V) {
    if (!live || !V || !slice.count(V))
      return;
    if (llvm::isa<llvm::AllocaInst>(V) ||
        (llvm::isa<llvm::CallBase>(V) && V->getType()->isPointerTy() &&
         llvm::cast<llvm::CallBase>(V)->hasRetAttr(llvm::Attribute::NoAlias) &&
         !llvm::cast<llvm::CallBase>(V)->isInlineAsm())) {
      int id = idOf(V);
      allocTok.insert(id);
      tokDepth[id] = 0;
      addTok(V, id);
    }
  }

  int subToken(int parent, Field f) {
    Slot s{parent, f};
    auto it = subId.find(s);
    if (it != subId.end())
      return it->second;
    int id = nextId++;
    subId.emplace(s, id);
    tokDepth[id] = tokDepth[parent] + 1;
    return id;
  }

  void addSlot(Slot s, int t) {
    if (!slotSeen[s].insert(t).second)
      return;
    slotTok[s].push_back(t);
    auto it = slotLoads.find(s);
    if (it == slotLoads.end())
      return;
    for (const llvm::LoadInst *L : it->second)
      addTok(L, t);
  }

  void addAddr(const llvm::Value *V, Slot s) {
    if (!V || s.id <= 0)
      return;
    slice.insert(V);
    if (!addrSeen[V].insert(s).second)
      return;
    addr[V].push_back(s);
    if (queued.insert(V).second)
      wl.push_back(V);
  }

  void addSlice(const llvm::Value *V) {
    if (!V || !slice.insert(V).second)
      return;
    maybeSeed(V);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        addSlice(inc);
      return;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
      addSlice(S->getTrueValue());
      addSlice(S->getFalseValue());
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      addSlice(C->getOperand(0));
      return;
    }
    if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      if (CE->isCast() && CE->getNumOperands() > 0)
        addSlice(CE->getOperand(0));
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      addSlice(Fr->getOperand(0));
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      addSlice(G->getPointerOperand());
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      const llvm::Value *ptr = L->getPointerOperand()->stripPointerCasts();
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(ptr)) {
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              addSlice(SI->getValueOperand());
        return;
      }
      if (fieldOf(L->getPointerOperand())) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand())))
          addSlice(G->getPointerOperand());
      }
      return;
    }
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      const llvm::Function *Parent = A->getParent();
      unsigned idx = A->getArgNo();
      auto sit = directSites.find(Parent);
      if (sit == directSites.end())
        return;
      for (const llvm::CallBase *C : sit->second)
        if (idx < C->arg_size())
          addSlice(C->getArgOperand(idx));
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
      if (const llvm::Function *D = asFunction(C->getCalledOperand())) {
        if (!D->isDeclaration()) {
          for (const llvm::Instruction &I : llvm::instructions(*D))
            if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I))
              if (R->getReturnValue())
                addSlice(R->getReturnValue());
        }
      }
    }
  }

  void flowAddr(const llvm::Value *From, const llvm::User *U, const std::vector<Slot> &tags) {
    auto put = [&](const llvm::Value *D) {
      for (const Slot &s : tags)
        addAddr(D, s);
    };
    if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U)) {
      put(U);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
      if (Sel->getTrueValue() == From || Sel->getFalseValue() == From)
        put(Sel);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
      if (G->getPointerOperand() == From || G->getPointerOperand()->stripPointerCasts() == From) {
        int64_t off = 0;
        if (offsetOf(G, off) && off == 0)
          put(G);
      }
      return;
    }
    if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
      if (S->getValueOperand() == From) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
          for (const llvm::LoadInst *L : allocaLoads[AI])
            put(L);
      }
      if (S->getPointerOperand() == From || S->getPointerOperand()->stripPointerCasts() == From) {
        addSlice(S->getValueOperand());
        auto it = tok.find(S->getValueOperand());
        if (it != tok.end())
          for (const Slot &s : tags)
            for (int t : it->second)
              addSlot(s, t);
      }
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
      if (L->getPointerOperand() != From && L->getPointerOperand()->stripPointerCasts() != From)
        return;
      for (const Slot &s : tags) {
        if (slotLoadSeen[s].insert(L).second)
          slotLoads[s].push_back(L);
        auto it = slotTok.find(s);
        if (it != slotTok.end())
          for (int t : it->second)
            addTok(L, t);
      }
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
      const llvm::Function *D = asFunction(C->getCalledOperand());
      if (!D || D->isDeclaration())
        return;
      for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i)
        if (C->getArgOperand(i) == From)
          put(D->getArg(i));
      return;
    }
    if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
      if (R->getReturnValue() != From)
        return;
      for (const llvm::CallBase *C : directSites[R->getFunction()])
        put(C);
    }
  }

  void prop(const llvm::Value *V) {
    std::vector<int> mine = tok[V];
    std::vector<Slot> tags;
    if (auto at = addr.find(V); at != addr.end())
      tags = at->second;
    for (const llvm::User *U : V->users()) {
      if (!mine.empty()) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            if (auto f = fieldOf(G))
              for (int t : mine)
                addAddr(G, Slot{t, *f});
          }
        }
      }
      if (!tags.empty())
        flowAddr(V, U, tags);
      bool structural = llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) ||
                        llvm::isa<llvm::PHINode>(U) || llvm::isa<llvm::SelectInst>(U) ||
                        llvm::isa<llvm::GEPOperator>(U);
      if (!slice.count(U) && !structural && !llvm::isa<llvm::StoreInst>(U) && !llvm::isa<llvm::CallBase>(U) &&
          !llvm::isa<llvm::ReturnInst>(U))
        continue;
      if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
          llvm::isa<llvm::GEPOperator>(U)) {
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
            for (int t : mine)
              addTok(Sel, t);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            int64_t off = 0;
            if (offsetOf(G, off) && off == 0) {
              for (int t : mine)
                addTok(G, t);
            } else if (auto f = fieldOf(G)) {
              // The field of an allocation is its own object. A field of that
              // object keeps the object: the table loaded from it is the
              // object's table. Splitting again would name every nested byte
              // offset a new object and walk that token through the module.
              if (demand.count(G))
                for (int t : mine) {
                  if (tokDepth[t] == 0)
                    addTok(G, subToken(t, *f));
                  else
                    addTok(G, t);
                }
            }
          }
          continue;
        }
        for (int t : mine)
          addTok(U, t);
        continue;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
        if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
          for (int t : mine)
            addTok(Sel, t);
        continue;
      }
      if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
        if (S->getValueOperand() == V) {
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
            for (const llvm::LoadInst *L : allocaLoads[AI])
              for (int t : mine)
                addTok(L, t);
          auto at = addr.find(S->getPointerOperand());
          if (at != addr.end())
            for (const Slot &s : at->second)
              for (int t : mine)
                addSlot(s, t);
        }
        if (S->getPointerOperand() == V || S->getPointerOperand()->stripPointerCasts() == V) {
          CodePtr cp = codePtr(S->getValueOperand());
          if (cp.gv)
            for (int t : mine)
              vtbl[t].insert(cp);
        }
        continue;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D || D->isDeclaration())
          continue;
        for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i) {
          if (C->getArgOperand(i) != V)
            continue;
          for (int t : mine)
            addTok(D->getArg(i), t);
        }
        continue;
      }
      if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
        if (R->getReturnValue() != V)
          continue;
        for (const llvm::CallBase *C : directSites[R->getFunction()])
          for (int t : mine)
            addTok(C, t);
      }
    }
  }

  bool vtableCall(const llvm::Value *V, const llvm::Value *&obj, int64_t &delta,
                  std::unordered_set<const llvm::Value *> &seen) const {
    if (!V || !seen.insert(V).second)
      return false;
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        if (vtableCall(inc, obj, delta, seen))
          return true;
      return false;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V))
      return vtableCall(S->getTrueValue(), obj, delta, seen) || vtableCall(S->getFalseValue(), obj, delta, seen);
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return vtableCall(C->getOperand(0), obj, delta, seen);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return vtableCall(Fr->getOperand(0), obj, delta, seen);
    const auto *L = llvm::dyn_cast<llvm::LoadInst>(V);
    if (!L)
      return false;
    const llvm::Value *base = nullptr;
    if (!ptrIndex(L->getPointerOperand(), base, delta))
      return false;
    const llvm::Value *B = base->stripPointerCasts();
    if (const auto *BL = llvm::dyn_cast<llvm::LoadInst>(B))
      obj = BL->getPointerOperand();
    else
      obj = B;
    return true;
  }

  // A direct call may return the address of a field. A store through that
  // pointer is a store of the field. The address may cross a cast, a phi, a
  // select, a freeze, or an alloca.
  void addrFields(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seenVals,
                  std::unordered_set<const llvm::Function *> &seenFns, std::vector<Field> &out) {
    if (!V || !seenVals.insert(V).second)
      return;
    if (auto f = fieldOf(V)) {
      out.push_back(*f);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      addrFields(C->getOperand(0), seenVals, seenFns, out);
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      addrFields(Fr->getOperand(0), seenVals, seenFns, out);
      return;
    }
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        addrFields(inc, seenVals, seenFns, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      addrFields(Sel->getTrueValue(), seenVals, seenFns, out);
      addrFields(Sel->getFalseValue(), seenVals, seenFns, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              addrFields(SI->getValueOperand(), seenVals, seenFns, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D || D->isDeclaration() || !seenFns.insert(D).second)
        return;
      for (const llvm::Instruction &I : llvm::instructions(*D)) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
        if (R && R->getReturnValue())
          addrFields(R->getReturnValue(), seenVals, seenFns, out);
      }
    }
  }

  // A stored parameter may be any function passed for it at a direct call.
  // The pointer may sit in an alloca between the parameter and the store.
  void argFns(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen,
              std::vector<const llvm::Function *> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (const llvm::Function *F = asFunction(V)) {
      out.push_back(F);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      argFns(C->getOperand(0), seen, out);
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      argFns(Fr->getOperand(0), seen, out);
      return;
    }
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        argFns(inc, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      argFns(Sel->getTrueValue(), seen, out);
      argFns(Sel->getFalseValue(), seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              argFns(SI->getValueOperand(), seen, out);
      return;
    }
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      unsigned idx = A->getArgNo();
      auto sit = directSites.find(A->getParent());
      if (sit == directSites.end())
        return;
      for (const llvm::CallBase *C : sit->second)
        if (idx < C->arg_size())
          argFns(C->getArgOperand(idx), seen, out);
    }
  }

  std::vector<const llvm::Function *> fnsOf(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen,
                                            const llvm::Function *home) const {
    std::vector<const llvm::Function *> out;
    if (!V || !seen.insert(V).second)
      return out;
    if (const llvm::Function *F = asFunction(V)) {
      out.push_back(F);
      return out;
    }
    auto take = [&](const llvm::Value *U) {
      for (const llvm::Function *F : fnsOf(U, seen, home))
        out.push_back(F);
    };
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        take(inc);
      return out;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
      take(S->getTrueValue());
      take(S->getFalseValue());
      return out;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      take(C->getOperand(0));
      return out;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      take(Fr->getOperand(0));
      return out;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (auto f = fieldOf(L->getPointerOperand())) {
        auto it = fieldFn.find(*f);
        if (it != fieldFn.end()) {
          const std::string homeSpec = classSpec(home);
          for (const SpecFn &s : it->second)
            if (fieldSpecVisible(s.spec, s.init, homeSpec))
              out.push_back(s.fn);
        }
      }
      // A function pointer may sit in an alloca between the field load and
      // the indirect call. The load may be any function stored there.
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              take(SI->getValueOperand());
      return out;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
      std::vector<const llvm::Function *> ts;
      if (const llvm::Function *D = asFunction(C->getCalledOperand()))
        ts.push_back(D);
      else {
        std::unordered_set<const llvm::Value *> w;
        ts = fnsOf(C->getCalledOperand(), w, home);
      }
      for (const llvm::Function *D : ts) {
        auto it = retFn.find(D);
        if (it != retFn.end())
          out.insert(out.end(), it->second.begin(), it->second.end());
      }
    }
    return out;
  }

  // The receiver of a vtable call is the object the table was loaded from.
  // Carry that object only along copies of the pointer: casts, phi, select,
  // freeze, a zero-offset getelementptr, an alloca store and its loads, a
  // direct call's matching parameter, and a returned pointer. A load through
  // the pointer is a field or a table, not a copy.
  void recv(const llvm::Value *Start, int t, std::deque<const llvm::Value *> &q,
            std::unordered_set<const llvm::Value *> &inq,
            const std::unordered_map<const llvm::Value *, std::vector<int>> &byObj) {
    if (!Start || t <= 0)
      return;
    std::deque<const llvm::Value *> stack;
    stack.push_back(Start);
    while (!stack.empty()) {
      const llvm::Value *V = stack.back();
      stack.pop_back();
      if (!V || !tokSeen[V].insert(t).second)
        continue;
      tok[V].push_back(t);
      if (byObj.count(V) && inq.insert(V).second)
        q.push_back(V);
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U)) {
          stack.push_back(U);
          continue;
        }
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
            stack.push_back(Sel);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            int64_t off = 0;
            if (offsetOf(G, off) && off == 0)
              stack.push_back(G);
          }
          continue;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (S->getValueOperand() != V)
            continue;
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
            for (const llvm::LoadInst *L : allocaLoads[AI])
              stack.push_back(L);
          continue;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
          const llvm::Function *D = asFunction(C->getCalledOperand());
          if (!D || D->isDeclaration())
            continue;
          for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i)
            if (C->getArgOperand(i) == V)
              stack.push_back(D->getArg(i));
          continue;
        }
        if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
          if (R->getReturnValue() != V)
            continue;
          for (const llvm::CallBase *C : directSites[R->getFunction()])
            stack.push_back(C);
        }
      }
    }
  }


  template <class T>
  bool pushNew(std::vector<T> &v, const T &x) {
    if (std::find(v.begin(), v.end(), x) != v.end())
      return false;
    v.push_back(x);
    return true;
  }

  void whichArgs(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
                 std::vector<int> &out) const {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (A->getParent() == F)
        out.push_back(static_cast<int>(A->getArgNo()));
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return whichArgs(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return whichArgs(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        whichArgs(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      whichArgs(Sel->getTrueValue(), F, seen, out);
      whichArgs(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              whichArgs(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      int64_t off = 0;
      if (offsetOf(G, off) && off == 0)
        whichArgs(G->getPointerOperand(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retAddr.find(D);
      if (it == retAddr.end())
        return;
      for (const BoxOff &b : it->second)
        if (b.off == 0 && b.arg >= 0 && static_cast<unsigned>(b.arg) < CB->arg_size())
          whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seen, out);
    }
  }

  void boxOf(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
             std::vector<BoxOff> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (auto f = fieldOf(V)) {
      const auto *G = llvm::cast<llvm::GEPOperator>(stripCasts(V));
      std::vector<int> args;
      std::unordered_set<const llvm::Value *> seenA;
      whichArgs(G->getPointerOperand(), F, seenA, args);
      for (int a : args)
        out.push_back({a, f->off});
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return boxOf(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return boxOf(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        boxOf(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      boxOf(Sel->getTrueValue(), F, seen, out);
      boxOf(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              boxOf(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retAddr.find(D);
      if (it == retAddr.end())
        return;
      for (const BoxOff &b : it->second) {
        if (b.arg < 0 || static_cast<unsigned>(b.arg) >= CB->arg_size())
          continue;
        std::vector<int> args;
        std::unordered_set<const llvm::Value *> seenA;
        whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seenA, args);
        for (int a : args)
          out.push_back({a, b.off});
      }
    }
  }

  void loadedBox(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
                 std::vector<BoxOff> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      std::unordered_set<const llvm::Value *> seenB;
      boxOf(L->getPointerOperand(), F, seenB, out);
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              loadedBox(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return loadedBox(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return loadedBox(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        loadedBox(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      loadedBox(Sel->getTrueValue(), F, seen, out);
      loadedBox(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retBox.find(D);
      if (it == retBox.end())
        return;
      for (const BoxOff &b : it->second) {
        if (b.arg < 0 || static_cast<unsigned>(b.arg) >= CB->arg_size())
          continue;
        std::vector<int> args;
        std::unordered_set<const llvm::Value *> seenA;
        whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seenA, args);
        for (int a : args)
          out.push_back({a, b.off});
      }
    }
  }

  void learnBoxes() {
    std::deque<const llvm::Function *> work;
    std::unordered_set<const llvm::Function *> queuedF;
    auto pushF = [&](const llvm::Function *F) {
      if (F && !F->isDeclaration() && queuedF.insert(F).second)
        work.push_back(F);
    };
    for (llvm::Function &F : M)
      pushF(&F);
    while (!work.empty()) {
      const llvm::Function *F = work.front();
      work.pop_front();
      queuedF.erase(F);
      bool grew = false;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
          if (!R->getReturnValue())
            continue;
          std::vector<BoxOff> ls;
          std::unordered_set<const llvm::Value *> seen;
          loadedBox(R->getReturnValue(), F, seen, ls);
          for (const BoxOff &b : ls)
            grew = pushNew(retBox[F], b) || grew;
          std::vector<BoxOff> as;
          seen.clear();
          boxOf(R->getReturnValue(), F, seen, as);
          for (const BoxOff &b : as)
            grew = pushNew(retAddr[F], b) || grew;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          std::vector<BoxOff> dst;
          std::unordered_set<const llvm::Value *> seen;
          boxOf(S->getPointerOperand(), F, seen, dst);
          std::vector<int> srcA;
          seen.clear();
          whichArgs(S->getValueOperand(), F, seen, srcA);
          for (const BoxOff &b : dst)
            for (int s : srcA)
              grew = pushNew(putBox[F], BoxMove{b.arg, s, b.off}) || grew;
          std::vector<BoxOff> srcL;
          seen.clear();
          loadedBox(S->getValueOperand(), F, seen, srcL);
          for (const BoxOff &b : dst)
            for (const BoxOff &s : srcL)
              if (s.arg != b.arg && s.off == b.off)
                grew = pushNew(mvBox[F], BoxMove{b.arg, s.arg, b.off}) || grew;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto lift = [&](int d, int s, int64_t off, bool asMove) {
          if (d < 0 || s < 0 || static_cast<unsigned>(d) >= C->arg_size() || static_cast<unsigned>(s) >= C->arg_size())
            return;
          std::vector<int> ds;
          std::unordered_set<const llvm::Value *> seenD;
          whichArgs(C->getArgOperand(static_cast<unsigned>(d)), F, seenD, ds);
          std::vector<int> ss;
          std::unordered_set<const llvm::Value *> seenS;
          whichArgs(C->getArgOperand(static_cast<unsigned>(s)), F, seenS, ss);
          for (int dst : ds)
            for (int src : ss)
              if (dst != src)
                grew = pushNew(asMove ? mvBox[F] : putBox[F], BoxMove{dst, src, off}) || grew;
          if (asMove)
            return;
          std::vector<BoxOff> loaded;
          seenS.clear();
          loadedBox(C->getArgOperand(static_cast<unsigned>(s)), F, seenS, loaded);
          for (int dst : ds)
            for (const BoxOff &src : loaded)
              if (dst != src.arg && src.off == off)
                grew = pushNew(mvBox[F], BoxMove{dst, src.arg, off}) || grew;
        };
        auto pit = putBox.find(D);
        if (pit != putBox.end())
          for (const BoxMove &m : pit->second)
            lift(m.dst, m.src, m.off, false);
        auto mit = mvBox.find(D);
        if (mit != mvBox.end())
          for (const BoxMove &m : mit->second)
            lift(m.dst, m.src, m.off, true);
      }
      if (!grew)
        continue;
      auto sit = directSites.find(F);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second)
        pushF(C->getFunction());
    }
  }

  void give(const llvm::Value *obj, const llvm::Value *src) {
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> seen;
    q.push_back(src);
    seen.insert(src);
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      auto it = tok.find(V);
      if (it != tok.end())
        for (int t : it->second) {
          if (vtbl.count(t) && tokSeen[obj].insert(t).second)
            tok[obj].push_back(t);
        }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
        if (seen.insert(C->getOperand(0)).second)
          q.push_back(C->getOperand(0));
      } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
        if (seen.insert(Fr->getOperand(0)).second)
          q.push_back(Fr->getOperand(0));
      } else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values())
          if (seen.insert(inc).second)
            q.push_back(inc);
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        if (seen.insert(Sel->getTrueValue()).second)
          q.push_back(Sel->getTrueValue());
        if (seen.insert(Sel->getFalseValue()).second)
          q.push_back(Sel->getFalseValue());
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          for (const llvm::User *U : AI->users())
            if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
              if (SI->getPointerOperand()->stripPointerCasts() == AI && seen.insert(SI->getValueOperand()).second)
                q.push_back(SI->getValueOperand());
      }
    }
  }

  void storedInto(const llvm::Value *box, int64_t off, std::set<std::pair<const llvm::Value *, int64_t>> &seenBox,
                  const llvm::Value *obj) {
    if (!box || !seenBox.insert({box, off}).second)
      return;
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> seen;
    q.push_back(box);
    seen.insert(box);
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
            llvm::isa<llvm::SelectInst>(U)) {
          if (seen.insert(U).second)
            q.push_back(U);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          int64_t go = 0;
          if ((G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) && offsetOf(G, go) &&
              go == 0 && seen.insert(G).second)
            q.push_back(G);
          continue;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (S->getValueOperand() == V) {
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
              for (const llvm::User *LU : AI->users())
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(LU))
                  if (L->getPointerOperand()->stripPointerCasts() == AI && seen.insert(L).second)
                    q.push_back(L);
          }
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(U);
        if (!C)
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto pit = putBox.find(D);
        if (pit != putBox.end())
          for (const BoxMove &m : pit->second)
            if (m.off == off && m.dst >= 0 && m.src >= 0 && static_cast<unsigned>(m.dst) < C->arg_size() &&
                static_cast<unsigned>(m.src) < C->arg_size() && C->getArgOperand(static_cast<unsigned>(m.dst)) == V)
              give(obj, C->getArgOperand(static_cast<unsigned>(m.src)));
        auto mit = mvBox.find(D);
        if (mit == mvBox.end())
          continue;
        for (const BoxMove &m : mit->second)
          if (m.off == off && m.dst >= 0 && m.src >= 0 && static_cast<unsigned>(m.dst) < C->arg_size() &&
              static_cast<unsigned>(m.src) < C->arg_size() && C->getArgOperand(static_cast<unsigned>(m.dst)) == V)
            storedInto(C->getArgOperand(static_cast<unsigned>(m.src)), off, seenBox, obj);
      }
    }
  }

  void fromField(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen, const llvm::Value *obj,
                 std::set<std::pair<const llvm::Value *, int64_t>> &seenBox) {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return fromField(C->getOperand(0), seen, obj, seenBox);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return fromField(Fr->getOperand(0), seen, obj, seenBox);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        fromField(inc, seen, obj, seenBox);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      fromField(Sel->getTrueValue(), seen, obj, seenBox);
      fromField(Sel->getFalseValue(), seen, obj, seenBox);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              fromField(SI->getValueOperand(), seen, obj, seenBox);
      return;
    }
    const auto *CB = llvm::dyn_cast<llvm::CallBase>(V);
    if (!CB)
      return;
    const llvm::Function *D = asFunction(CB->getCalledOperand());
    if (!D)
      return;
    auto it = retBox.find(D);
    if (it == retBox.end())
      return;
    for (const BoxOff &b : it->second)
      if (b.arg >= 0 && static_cast<unsigned>(b.arg) < CB->arg_size())
        storedInto(CB->getArgOperand(static_cast<unsigned>(b.arg)), b.off, seenBox, obj);
  }

  // A virtual call's receiver may be a pointer loaded from one object's field.
  // Copy onto that receiver only the objects stored into that field.
  void carryFields() {
    learnBoxes();
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (!vtableCall(C->getCalledOperand(), obj, delta, seenV) || !obj)
          continue;
        std::unordered_set<const llvm::Value *> seen;
        std::set<std::pair<const llvm::Value *, int64_t>> seenBox;
        fromField(obj, seen, obj, seenBox);
      }
    }
  }

  // A function pointer stored into an object reaches a load of that object
  // along copies of the pointer and along direct calls that take the object.
  // The struct type is not the carrier: one LLVM struct can be every
  // instantiation.
  void learnObjects() {
    struct Addr {
      const llvm::Value *obj = nullptr;
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
      bool operator==(const Addr &o) const {
        return obj == o.obj && storage == o.storage && off == o.off && inner == o.inner;
      }
    };
    struct AddrHash {
      size_t operator()(const Addr &a) const {
        size_t h = (size_t)(uintptr_t)a.obj ^ ((size_t)a.off * 1315423911u) ^ ((size_t)a.inner * 2654435761u);
        return a.storage ? h ^ 0x9e3779b97f4a7c15ull : h;
      }
    };
    struct Ret {
      bool has = false;
      int arg = -1;
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
    };
    std::unordered_map<const llvm::Function *, Ret> retOf;
    std::unordered_map<const llvm::Value *, std::optional<Addr>> rmemo;

    std::function<std::optional<Addr>(const llvm::Value *, const llvm::Function *,
                                      std::unordered_set<const llvm::Value *> &, bool)>
        root;
    root = [&](const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
               bool calls) -> std::optional<Addr> {
      if (!V)
        return std::nullopt;
      if (auto it = rmemo.find(V); it != rmemo.end())
        return it->second;
      if (!seen.insert(V).second)
        return std::nullopt;
      struct Save {
        std::unordered_map<const llvm::Value *, std::optional<Addr>> &m;
        const llvm::Value *v;
        std::optional<Addr> r;
        ~Save() { m[v] = r; }
      } save{rmemo, V, std::nullopt};
      auto ok = [&](std::optional<Addr> r) {
        save.r = std::move(r);
        return save.r;
      };
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == F)
          return ok(Addr{A, false, 0, 0});
        return ok(std::nullopt);
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V))
        return ok(Addr{AI, false, 0, 0});
      if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(V))
        return ok(Addr{GV, false, 0, 0});
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
        return ok(root(C->getOperand(0), F, seen, calls));
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0)
          return ok(root(CE->getOperand(0), F, seen, calls));
      }
      if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        return ok(root(Fr->getOperand(0), F, seen, calls));
      if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        std::optional<Addr> acc;
        for (const llvm::Value *inc : P->incoming_values()) {
          auto one = root(inc, F, seen, calls);
          if (!one)
            return ok(std::nullopt);
          if (!acc)
            acc = one;
          else if (!(*acc == *one))
            return ok(std::nullopt);
        }
        return ok(acc);
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        auto a = root(Sel->getTrueValue(), F, seen, calls);
        auto b = root(Sel->getFalseValue(), F, seen, calls);
        if (!a || !b || !(*a == *b))
          return ok(std::nullopt);
        return ok(a);
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        auto base = root(G->getPointerOperand(), F, seen, calls);
        if (!base)
          return ok(std::nullopt);
        int64_t delta = 0;
        if (offsetOf(G, delta)) {
          if (base->storage)
            base->inner += delta;
          else
            base->off += delta;
          return ok(base);
        }
        if (!base->storage) {
          base->storage = true;
          base->inner = 0;
        } else
          base->inner = 0;
        return ok(base);
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          std::optional<Addr> acc;
          bool any = false;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
              continue;
            any = true;
            auto one = root(SI->getValueOperand(), F, seen, calls);
            if (!one)
              return ok(std::nullopt);
            if (!acc)
              acc = one;
            else if (!(*acc == *one))
              return ok(std::nullopt);
          }
          if (any)
            return ok(acc);
        }
        auto addr = root(L->getPointerOperand(), F, seen, calls);
        if (!addr || !L->getType()->isPointerTy())
          return ok(std::nullopt);
        // begin and finish are two fields of one all-pointer struct and one
        // allocation. The load is the buffer of the object that contains
        // that struct, not a distinct buffer per field.
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand()))) {
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType())) {
            if (!mixedStruct(ST)) {
              int64_t delta = 0;
              if (offsetOf(G, delta)) {
                if (addr->storage)
                  addr->inner -= delta;
                else
                  addr->off -= delta;
              }
            }
          }
        }
        if (!addr->storage) {
          addr->storage = true;
          addr->inner = 0;
        } else
          addr->inner = 0;
        return ok(addr);
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (!calls)
          return ok(std::nullopt);
        if (const llvm::Function *D = asFunction(CB->getCalledOperand())) {
          // Itanium __dynamic_cast(src, srcType, dstType, src2dst). A
          // non-negative src2dst is the offset of the source subobject in
          // the destination, so the destination is src minus that offset.
          // -1 and -2 are not a known adjustment.
          if (D->getName() == "__dynamic_cast" && CB->arg_size() >= 4) {
            if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(3))) {
              int64_t src2dst = CI->getSExtValue();
              if (src2dst >= 0) {
                auto src = root(CB->getArgOperand(0), F, seen, calls);
                if (src) {
                  if (src->storage)
                    src->inner -= src2dst;
                  else
                    src->off -= src2dst;
                  return ok(src);
                }
              }
            }
          }
          auto it = retOf.find(D);
          if (it != retOf.end() && it->second.has && it->second.arg >= 0 &&
              static_cast<unsigned>(it->second.arg) < CB->arg_size()) {
            const Ret &r = it->second;
            auto arg = root(CB->getArgOperand(static_cast<unsigned>(r.arg)), F, seen, calls);
            if (arg) {
              if (r.storage) {
                if (!arg->storage) {
                  arg->storage = true;
                  arg->inner = r.inner;
                } else
                  arg->inner += r.inner;
                return ok(arg);
              }
              if (arg->storage)
                arg->inner += r.off;
              else
                arg->off += r.off;
              return ok(arg);
            }
          }
        }
        // A noalias allocation is an object of its own. operator new is not an
        // argument of its caller, and a field of the allocated object is still
        // that allocation.
        if (CB->getType()->isPointerTy() && CB->hasRetAttr(llvm::Attribute::NoAlias) && !CB->isInlineAsm())
          return ok(Addr{CB, false, 0, 0});
        return ok(std::nullopt);
      }
      return ok(std::nullopt);
    };

    auto summarize = [&](const llvm::Function *F) -> bool {
      if (retOf.count(F))
        return false;
      Ret acc;
      bool saw = false;
      bool bad = false;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
        if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
          continue;
        if (llvm::isa<llvm::ConstantPointerNull>(R->getReturnValue()))
          continue;
        std::unordered_set<const llvm::Value *> seen;
        auto one = root(R->getReturnValue(), F, seen, true);
        if (!one || !llvm::isa<llvm::Argument>(one->obj) ||
            llvm::cast<llvm::Argument>(one->obj)->getParent() != F) {
          bad = true;
          break;
        }
        Ret cur;
        cur.has = true;
        cur.arg = (int)llvm::cast<llvm::Argument>(one->obj)->getArgNo();
        cur.storage = one->storage;
        cur.off = one->off;
        cur.inner = one->inner;
        if (!saw)
          acc = cur;
        else if (acc.arg != cur.arg || acc.storage != cur.storage || acc.off != cur.off || acc.inner != cur.inner) {
          bad = true;
          break;
        }
        saw = true;
      }
      if (bad || !saw)
        return false;
      retOf[F] = acc;
      return true;
    };
    std::deque<const llvm::Function *> retQ;
    for (llvm::Function &F : M)
      if (!F.isDeclaration())
        retQ.push_back(&F);
    while (!retQ.empty()) {
      const llvm::Function *F = retQ.front();
      retQ.pop_front();
      if (!summarize(F))
        continue;
      auto sit = directSites.find(F);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second)
        if (!retOf.count(C->getFunction()))
          retQ.push_back(C->getFunction());
    }

    // A relative address names a field of an argument. Applied to the actual
    // at one callsite, it is that field of that object. Two calls stay two
    // objects: the argument is not a location shared by its callers.
    auto apply = [](Addr base, const Addr &rel) {
      if (rel.storage) {
        if (!base.storage) {
          base.storage = true;
          base.inner = rel.inner;
          base.off += rel.off;
        } else
          base.inner += rel.off + rel.inner;
        return base;
      }
      if (base.storage)
        base.inner += rel.off;
      else
        base.off += rel.off;
      return base;
    };

    // Every object a value may name. A phi or a select is the union of its
    // inputs, not a failure: dropping one input would lose a copy.
    std::unordered_map<const llvm::Value *, std::vector<Addr>> pmemo;
    std::function<std::vector<Addr>(const llvm::Value *, const llvm::Function *,
                                    std::unordered_set<const llvm::Value *> &)>
        places;
    places = [&](const llvm::Value *V, const llvm::Function *F,
                 std::unordered_set<const llvm::Value *> &seen) -> std::vector<Addr> {
      if (!V)
        return {};
      if (auto it = pmemo.find(V); it != pmemo.end())
        return it->second;
      if (!seen.insert(V).second)
        return {};
      std::vector<Addr> result;
      auto commit = [&]() {
        std::vector<Addr> uniq;
        for (const Addr &a : result) {
          if (!a.obj)
            continue;
          bool dup = false;
          for (const Addr &b : uniq)
            if (a == b)
              dup = true;
          if (!dup)
            uniq.push_back(a);
        }
        pmemo.emplace(V, uniq);
        return uniq;
      };
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == F)
          result.push_back(Addr{A, false, 0, 0});
        return commit();
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
        result.push_back(Addr{AI, false, 0, 0});
        return commit();
      }
      if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(V)) {
        result.push_back(Addr{GV, false, 0, 0});
        return commit();
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
        result = places(C->getOperand(0), F, seen);
      else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0)
          result = places(CE->getOperand(0), F, seen);
      } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        result = places(Fr->getOperand(0), F, seen);
      else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values()) {
          auto one = places(inc, F, seen);
          result.insert(result.end(), one.begin(), one.end());
        }
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        auto a = places(Sel->getTrueValue(), F, seen);
        auto b = places(Sel->getFalseValue(), F, seen);
        result = std::move(a);
        result.insert(result.end(), b.begin(), b.end());
      } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        auto bases = places(G->getPointerOperand(), F, seen);
        int64_t delta = 0;
        bool constant = offsetOf(G, delta);
        for (Addr b : bases) {
          if (constant) {
            if (b.storage)
              b.inner += delta;
            else
              b.off += delta;
          } else if (!b.storage) {
            b.storage = true;
            b.inner = 0;
          } else
            b.inner = 0;
          result.push_back(b);
        }
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          bool any = false;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
              continue;
            any = true;
            auto one = places(SI->getValueOperand(), F, seen);
            result.insert(result.end(), one.begin(), one.end());
          }
          if (any)
            return commit();
        }
        if (!L->getType()->isPointerTy())
          return commit();
        auto bases = places(L->getPointerOperand(), F, seen);
        int64_t sub = 0;
        bool fold = false;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand()))) {
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType())) {
            if (!mixedStruct(ST)) {
              int64_t delta = 0;
              if (offsetOf(G, delta)) {
                fold = true;
                sub = delta;
              }
            }
          }
        }
        for (Addr addr : bases) {
          if (fold) {
            if (addr.storage)
              addr.inner -= sub;
            else
              addr.off -= sub;
          }
          if (!addr.storage) {
            addr.storage = true;
            addr.inner = 0;
          } else
            addr.inner = 0;
          result.push_back(addr);
        }
      } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (const llvm::Function *D = asFunction(CB->getCalledOperand())) {
          if (D->getName() == "__dynamic_cast" && CB->arg_size() >= 4) {
            if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(3))) {
              int64_t src2dst = CI->getSExtValue();
              if (src2dst >= 0) {
                auto srcs = places(CB->getArgOperand(0), F, seen);
                for (Addr s : srcs) {
                  if (s.storage)
                    s.inner -= src2dst;
                  else
                    s.off -= src2dst;
                  result.push_back(s);
                }
                if (!result.empty())
                  return commit();
              }
            }
          }
          auto it = retOf.find(D);
          if (it != retOf.end() && it->second.has && it->second.arg >= 0 &&
              static_cast<unsigned>(it->second.arg) < CB->arg_size()) {
            const Ret &r = it->second;
            auto args = places(CB->getArgOperand(static_cast<unsigned>(r.arg)), F, seen);
            for (Addr arg : args) {
              if (r.storage) {
                if (!arg.storage) {
                  arg.storage = true;
                  arg.inner = r.inner;
                } else
                  arg.inner += r.inner;
              } else if (arg.storage)
                arg.inner += r.off;
              else
                arg.off += r.off;
              result.push_back(arg);
            }
            if (!result.empty())
              return commit();
          }
        }
        if (CB->getType()->isPointerTy() && CB->hasRetAttr(llvm::Attribute::NoAlias) && !CB->isInlineAsm())
          result.push_back(Addr{CB, false, 0, 0});
      }
      return commit();
    };

    // A load/store copy puts one pointer in two cells. The component is one
    // pointer. A global or a noalias allocation names it; a load of either
    // cell is that object. Other components keep the address they already
    // had, so a parameter that was not copied from such an object stays one.
    bool canonReady = false;
    std::unordered_map<Addr, Addr, AddrHash> ufParent;
    auto ufFind = [&](Addr a) {
      std::vector<Addr> path;
      while (true) {
        auto it = ufParent.find(a);
        if (it == ufParent.end()) {
          ufParent[a] = a;
          break;
        }
        if (it->second == a)
          break;
        path.push_back(a);
        a = it->second;
      }
      for (const Addr &p : path)
        ufParent[p] = a;
      return a;
    };
    auto canonAddr = [&](Addr a) {
      if (!canonReady || !a.storage || !a.obj)
        return a;
      Addr cell{a.obj, false, a.off, 0};
      if (!ufParent.count(cell))
        return a;
      Addr r = ufFind(cell);
      if (r == cell || !r.obj)
        return a;
      if (!llvm::isa<llvm::GlobalVariable>(r.obj) && !llvm::isa<llvm::CallBase>(r.obj))
        return a;
      a.obj = r.obj;
      a.off = r.off;
      a.storage = true;
      return a;
    };

    struct Sub {
      std::vector<Addr> out;
      bool failed = false;
    };
    // failed: the actual does not reduce to an object. An empty result that
    // is not failed is the same address passed back. A different offset of
    // that parameter is a different field.
    auto substPlaces = [&](const llvm::CallBase *C, Addr a) {
      Sub r;
      const auto *A = llvm::dyn_cast<llvm::Argument>(a.obj);
      if (!A) {
        r.out.push_back(a);
        return r;
      }
      const llvm::Function *Cal = asFunction(C->getCalledOperand());
      if (!Cal || A->getParent() != Cal) {
        r.out.push_back(a);
        return r;
      }
      if (A->getArgNo() >= C->arg_size()) {
        r.failed = true;
        return r;
      }
      std::unordered_set<const llvm::Value *> seen;
      auto found = places(C->getArgOperand(A->getArgNo()), C->getFunction(), seen);
      if (found.empty()) {
        r.failed = true;
        return r;
      }
      for (Addr b : found) {
        // The same address is the parameter passed back: no new object.
        // A different offset is that field of the same parameter.
        Addr got = canonAddr(apply(b, a));
        if (got == a)
          continue;
        r.out.push_back(got);
      }
      return r;
    };

    struct Copy {
      Addr src, dst;
      const llvm::Function *fn = nullptr;
    };
    std::vector<std::pair<Addr, const llvm::Function *>> seeds;
    std::vector<Copy> copies;
    // A noalias allocation stored into a cell. Functions at an offset of the
    // allocation are at that offset of the cell's pointee.
    std::unordered_map<const llvm::Value *, std::vector<Addr>> heldIn;
    std::vector<std::pair<const llvm::CallBase *, Addr>> queries;
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (!S->getValueOperand()->getType()->isPointerTy())
            continue;
          std::unordered_set<const llvm::Value *> seenD, seenS;
          auto dsts = places(S->getPointerOperand(), &F, seenD);
          if (const llvm::Function *Fn = asFunction(S->getValueOperand())) {
            objectStored.insert(Fn);
            storedAny.insert(Fn);
            if (dsts.empty())
              unresolved.insert(Fn);
            else
              for (const Addr &d : dsts)
                seeds.push_back({d, Fn});
          } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(S->getValueOperand())) {
            auto srcs = places(L->getPointerOperand(), &F, seenS);
            for (const Addr &s : srcs)
              for (const Addr &d : dsts)
                copies.push_back(Copy{s, d, &F});
          } else {
            // A store of a noalias allocation itself. Casts do not change
            // the object. A function at an offset of the allocation is at
            // that offset of this cell's pointee.
            const llvm::Value *v = S->getValueOperand();
            std::unordered_set<const llvm::Value *> seenV;
            while (v && seenV.insert(v).second) {
              if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v))
                v = C->getOperand(0);
              else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(v))
                v = Fr->getOperand(0);
              else
                break;
            }
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(v);
            if (CB && !CB->isInlineAsm() && CB->hasRetAttr(llvm::Attribute::NoAlias))
              for (const Addr &d : dsts)
                if (d.obj)
                  heldIn[CB].push_back(d);
          }
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        std::unordered_set<const llvm::Value *> seen;
        const llvm::Value *op = C->getCalledOperand();
        const llvm::LoadInst *load = nullptr;
        std::vector<const llvm::Value *> stack{op};
        std::unordered_set<const llvm::Value *> walked;
        while (!stack.empty()) {
          const llvm::Value *V = stack.back();
          stack.pop_back();
          if (!V || !walked.insert(V).second)
            continue;
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            load = L;
            break;
          }
          if (const auto *X = llvm::dyn_cast<llvm::CastInst>(V))
            stack.push_back(X->getOperand(0));
          else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
            stack.push_back(Fr->getOperand(0));
        }
        if (!load)
          continue;
        std::unordered_set<const llvm::Value *> seenA;
        auto addrs = places(load->getPointerOperand(), &F, seenA);
        if (addrs.empty())
          openQuery.insert(C);
        else
          for (const Addr &a : addrs)
            queries.push_back({C, a});
      }
    }

    for (const GlobFn &g : globFns)
      if (g.gv && g.fn)
        seeds.push_back({Addr{g.gv, false, g.off, 0}, g.fn});

    // Inclusion edges. An edge inside a function may name its parameters.
    // At each direct call those parameters are the actuals, so the edge
    // becomes an edge between the caller's objects. A callsite whose actual
    // does not reduce keeps the functions that reach that actual on the
    // parameter. The LLVM type is not that set.
    std::unordered_map<Addr, std::vector<Addr>, AddrHash> intraSucc;
    std::unordered_map<Addr, std::vector<Addr>, AddrHash> cross;
    std::unordered_set<Addr, AddrHash> leakAt;
    // Functions that reach an actual the call cannot name. They stay on that
    // parameter. A function that does not reach the actual is not carried,
    // and the LLVM type is not that set.
    auto reaching = [&](const llvm::Value *rootV, const llvm::Function *in) {
      std::vector<const llvm::Function *> out;
      std::unordered_set<const llvm::Function *> have;
      std::unordered_set<const llvm::Value *> seen;
      std::vector<const llvm::Value *> st{rootV};
      while (!st.empty()) {
        const llvm::Value *V = st.back();
        st.pop_back();
        if (!V || !seen.insert(V).second)
          continue;
        if (const llvm::Function *Fn = asFunction(V)) {
          if (have.insert(Fn).second)
            out.push_back(Fn);
          continue;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
          st.push_back(C->getOperand(0));
        else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
          if (CE->isCast() && CE->getNumOperands() > 0)
            st.push_back(CE->getOperand(0));
        } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
          st.push_back(Fr->getOperand(0));
        else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
          for (const llvm::Value *inc : P->incoming_values())
            st.push_back(inc);
        } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
          st.push_back(S->getTrueValue());
          st.push_back(S->getFalseValue());
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          // An alloca is one object. A store through any other pointer is
          // not proved to be this value, and the LLVM type is not the set.
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(stripCasts(L->getPointerOperand()));
          if (!AI)
            continue;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getFunction() != in)
              continue;
            if (stripCasts(SI->getPointerOperand()) != AI)
              continue;
            st.push_back(SI->getValueOperand());
          }
        }
      }
      return out;
    };
    for (const Copy &c : copies) {
      if (!c.src.obj || !c.dst.obj)
        continue;
      intraSucc[c.src].push_back(c.dst);
      const auto *A = llvm::dyn_cast<llvm::Argument>(c.src.obj);
      if (!A || !c.fn)
        continue;
      auto sit = directSites.find(c.fn);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second) {
        auto ss = substPlaces(C, c.src);
        auto ds = substPlaces(C, c.dst);
        if (ss.failed) {
          if (A->getArgNo() < C->arg_size())
            for (const llvm::Function *Fn : reaching(C->getArgOperand(A->getArgNo()), C->getFunction()))
              seeds.push_back({c.src, Fn});
          continue;
        }
        if (ds.failed) {
          // The caller-side destination has no object. The functions at the
          // source stay on the named destination inside this function.
          for (const Addr &s : ss.out)
            cross[s].push_back(c.dst);
          continue;
        }
        for (const Addr &s : ss.out)
          for (const Addr &d : ds.out)
            cross[s].push_back(d);
      }
    }

    auto betterCell = [](Addr a, Addr b) {
      auto rank = [](const llvm::Value *v) {
        if (llvm::isa<llvm::GlobalVariable>(v))
          return 0;
        if (llvm::isa<llvm::CallBase>(v))
          return 1;
        return 2;
      };
      int ra = a.obj ? rank(a.obj) : 3;
      int rb = b.obj ? rank(b.obj) : 3;
      if (ra != rb)
        return ra < rb ? a : b;
      auto stableId = [&](const llvm::Value *v) {
        std::string n;
        int kind = 2;
        int ix = 0;
        if (const auto *G = llvm::dyn_cast<llvm::GlobalValue>(v)) {
          kind = 0;
          n = G->hasName() ? G->getName().str() : "";
        } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(v)) {
          kind = 1;
          const llvm::Function *PF = I->getFunction();
          n = PF && PF->hasName() ? PF->getName().str() : "";
          if (PF)
            for (const llvm::Instruction &J : llvm::instructions(*PF)) {
              if (&J == I)
                break;
              ++ix;
            }
        }
        return std::make_tuple(kind, n, ix);
      };
      return stableId(a.obj) <= stableId(b.obj) ? a : b;
    };
    auto uniteCell = [&](Addr a, Addr b) {
      if (!a.obj || !b.obj || a.storage || b.storage)
        return;
      a = ufFind(a);
      b = ufFind(b);
      if (a == b)
        return;
      Addr w = betterCell(a, b);
      Addr l = (w == a) ? b : a;
      ufParent[l] = w;
    };
    for (const auto &kv : intraSucc)
      for (const Addr &d : kv.second)
        uniteCell(kv.first, d);
    for (const auto &kv : cross)
      for (const Addr &d : kv.second)
        uniteCell(kv.first, d);
    canonReady = true;

    // Copies out of a parameter, in the callee's frame. At a call the
    // parameter is the actual, so two calls stay two objects. A callee of
    // that callee is the same equation. The set of destinations is finite:
    // a field offset is one a copy already names, and a walk that returns
    // to a function at a new offset does not name a field.
    std::unordered_map<const llvm::Function *, std::vector<std::pair<Addr, Addr>>> argCopy;
    struct Pat {
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
      bool operator<(const Pat &o) const {
        if (storage != o.storage)
          return storage < o.storage;
        if (off != o.off)
          return off < o.off;
        return inner < o.inner;
      }
    };
    std::set<Pat> patterns;
    for (const Copy &c : copies) {
      if (!llvm::isa<llvm::Argument>(c.src.obj) || !c.fn)
        continue;
      argCopy[c.fn].push_back({c.src, c.dst});
      if (c.src.off != 0 || c.src.inner != 0 || c.src.storage)
        patterns.insert(Pat{c.src.storage, c.src.off, c.src.inner});
    }
    struct Site {
      const llvm::CallBase *C = nullptr;
      const llvm::Function *D = nullptr;
      std::vector<std::pair<const llvm::Argument *, std::vector<Addr>>> args;
    };
    std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> callsIn;
    for (const auto &kv : directSites)
      for (const llvm::CallBase *C : kv.second)
        if (C->getFunction())
          callsIn[C->getFunction()].push_back(C);
    std::unordered_map<const llvm::Function *, std::vector<Site>> sitesIn;
    auto ensureSites = [&](const llvm::Function *F) {
      if (!F || sitesIn.count(F))
        return;
      std::vector<Site> out;
      auto cit = callsIn.find(F);
      if (cit != callsIn.end()) {
        for (const llvm::CallBase *C : cit->second) {
          const llvm::Function *D = asFunction(C->getCalledOperand());
          if (!D || D->isDeclaration())
            continue;
          Site s;
          s.C = C;
          s.D = D;
          unsigned n = C->arg_size();
          if (D->arg_size() < n)
            n = static_cast<unsigned>(D->arg_size());
          for (unsigned i = 0; i < n; ++i) {
            const llvm::Value *arg = C->getArgOperand(i);
            if (!arg->getType()->isPointerTy())
              continue;
            std::unordered_set<const llvm::Value *> seenP;
            auto ps = places(arg, F, seenP);
            if (ps.empty())
              continue;
            s.args.push_back({D->getArg(i), std::move(ps)});
          }
          if (!s.args.empty())
            out.push_back(std::move(s));
        }
      }
      sitesIn.emplace(F, std::move(out));
    };

    struct SeenKey {
      const llvm::Value *obj = nullptr;
      int64_t off = 0;
      int64_t inner = 0;
      bool storage = false;
      const llvm::Function *fn = nullptr;
      bool operator==(const SeenKey &o) const {
        return obj == o.obj && off == o.off && inner == o.inner && storage == o.storage && fn == o.fn;
      }
    };
    struct SeenHash {
      size_t operator()(const SeenKey &k) const {
        return AddrHash{}(Addr{k.obj, k.storage, k.off, k.inner}) ^ (size_t)(uintptr_t)k.fn;
      }
    };
    struct Edge {
      const llvm::CallBase *call = nullptr;
      Addr formal;
      const llvm::Function *callee = nullptr;
    };
    struct Node {
      int state = 0;
      bool leak = false;
      std::vector<Addr> dst;
      std::vector<Edge> edges;
    };
    std::unordered_map<SeenKey, Node, SeenHash> nodes;
    std::unordered_map<SeenKey, std::vector<SeenKey>, SeenHash> parents;
    std::unordered_set<const llvm::Function *> gray;
    std::deque<SeenKey> kq;
    std::unordered_set<SeenKey, SeenHash> inQ;
    auto enqueue = [&](const SeenKey &k) {
      if (inQ.insert(k).second)
        kq.push_back(k);
    };
    auto keyOf = [](const llvm::Function *D, Addr a) {
      return SeenKey{a.obj, a.off, a.inner, a.storage, D};
    };
    // The relative field is the one difference of the actual and the address
    // that holds the function. A difference no copy names is not a field.
    auto formalsFor = [&](const llvm::Argument *arg, const std::vector<Addr> &locs, Addr target,
                          const llvm::Function *callee) {
      std::vector<Addr> cands;
      std::unordered_set<Addr, AddrHash> seen;
      auto add = [&](Addr f) {
        if (f.obj && seen.insert(f).second)
          cands.push_back(f);
      };
      for (const Addr &base : locs) {
        if (!arg || base.obj != target.obj)
          continue;
        Addr rel{arg, false, 0, 0};
        bool ok = false;
        if (!base.storage && !target.storage && base.inner == target.inner) {
          rel.off = target.off - base.off;
          ok = true;
        } else if (base.storage && target.storage && base.off == target.off) {
          rel.off = target.inner - base.inner;
          ok = true;
        } else if (!base.storage && target.storage) {
          rel.storage = true;
          rel.off = target.off - base.off;
          rel.inner = target.inner;
          ok = true;
        }
        if (!ok)
          continue;
        bool whole = !rel.storage && rel.off == 0 && rel.inner == 0;
        if (whole || patterns.count(Pat{rel.storage, rel.off, rel.inner}))
          add(rel);
      }
      if (callee) {
        if (auto it = argCopy.find(callee); it != argCopy.end())
          for (const auto &e : it->second)
            if (e.first.obj == arg)
              add(e.first);
      }
      return cands;
    };
    std::function<void(const llvm::Function *, Addr)> build;
    build = [&](const llvm::Function *D, Addr src) {
      if (!D || !llvm::isa<llvm::Argument>(src.obj) ||
          llvm::cast<llvm::Argument>(src.obj)->getParent() != D)
        return;
      SeenKey key = keyOf(D, src);
      if (auto it = nodes.find(key); it != nodes.end() && it->second.state != 0)
        return;
      if (gray.count(D)) {
        nodes[key].leak = true;
        nodes[key].state = 2;
        return;
      }
      nodes[key].state = 1;
      gray.insert(D);
      std::vector<Addr> direct;
      std::unordered_set<Addr, AddrHash> have;
      if (auto it = argCopy.find(D); it != argCopy.end()) {
        for (const auto &e : it->second)
          if (e.first == src && e.second.obj && have.insert(e.second).second)
            direct.push_back(e.second);
      }
      std::vector<Edge> edges;
      ensureSites(D);
      if (auto sit = sitesIn.find(D); sit != sitesIn.end()) {
        std::vector<Site> mine = sit->second;
        for (const Site &site : mine) {
          for (const auto &ag : site.args) {
            bool touch = false;
            for (const Addr &loc : ag.second)
              if (loc.obj == src.obj)
                touch = true;
            if (!touch)
              continue;
            for (const Addr &formal : formalsFor(ag.first, ag.second, src, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed) {
                nodes[key].leak = true;
                continue;
              }
              bool eq = false;
              for (const Addr &s : ss.out)
                if (s == src)
                  eq = true;
              if (!eq)
                continue;
              SeenKey child = keyOf(site.D, formal);
              build(site.D, formal);
              // The same address again adds no object. A summary that was
              // not built, or that is still open, is not a proof that the
              // copy went somewhere else.
              if (child == key)
                continue;
              auto cit = nodes.find(child);
              if (cit == nodes.end() || cit->second.state != 2) {
                nodes[key].leak = true;
                continue;
              }
              if (cit->second.leak)
                nodes[key].leak = true;
              edges.push_back(Edge{site.C, formal, site.D});
              parents[child].push_back(key);
            }
          }
        }
      }
      gray.erase(D);
      {
        auto &n = nodes[key];
        n.dst = std::move(direct);
        n.edges = std::move(edges);
        n.state = 2;
      }
      enqueue(key);
    };
    auto solve = [&]() {
      while (!kq.empty()) {
        SeenKey k = kq.front();
        kq.pop_front();
        inQ.erase(k);
        auto nit = nodes.find(k);
        if (nit == nodes.end() || nit->second.state != 2)
          continue;
        Node &n = nit->second;
        std::unordered_set<Addr, AddrHash> have(n.dst.begin(), n.dst.end());
        bool grew = false;
        bool wasLeak = n.leak;
        for (const Edge &e : n.edges) {
          auto cit = nodes.find(keyOf(e.callee, e.formal));
          if (cit == nodes.end()) {
            n.leak = true;
            continue;
          }
          if (cit->second.leak)
            n.leak = true;
          for (const Addr &d : cit->second.dst) {
            auto ds = substPlaces(e.call, d);
            if (ds.failed) {
              n.leak = true;
              continue;
            }
            for (const Addr &x : ds.out) {
              if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(x.obj)) {
                if (Arg->getParent() != e.call->getFunction()) {
                  n.leak = true;
                  continue;
                }
              }
              if (have.insert(x).second) {
                n.dst.push_back(x);
                grew = true;
              }
            }
          }
        }
        if (grew || (n.leak && !wasLeak))
          for (const SeenKey &p : parents[k])
            enqueue(p);
      }
    };

    std::unordered_map<Addr, std::vector<const llvm::Function *>, AddrHash> cellFn;
    std::unordered_set<SeenKey, SeenHash> cellSeen;
    std::deque<std::pair<Addr, const llvm::Function *>> wl;
    for (const auto &s : seeds)
      wl.push_back(s);
    while (!wl.empty()) {
      Addr a = wl.front().first;
      const llvm::Function *Fn = wl.front().second;
      wl.pop_front();
      if (!a.obj || !Fn)
        continue;
      if (!cellSeen.insert(SeenKey{a.obj, a.off, a.inner, a.storage, Fn}).second)
        continue;
      if (leakAt.count(a))
        unresolved.insert(Fn);
      cellFn[a].push_back(Fn);
      Addr named = canonAddr(a);
      if (!(named == a)) {
        if (leakAt.count(named))
          unresolved.insert(Fn);
        cellFn[named].push_back(Fn);
      }
      // A global initializer is already named by the struct type. Walking
      // every use of the global is the module. Copies that name it as an
      // address are edges and are followed below.
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(a.obj)) {
        auto sit = directSites.find(A->getParent());
        if (sit != directSites.end()) {
          for (const llvm::CallBase *C : sit->second) {
            auto ps = substPlaces(C, a);
            if (ps.failed)
              continue;
            for (const Addr &p : ps.out)
              wl.push_back({p, Fn});
          }
        }
      }
      if (auto it = intraSucc.find(a); it != intraSucc.end())
        for (const Addr &d : it->second)
          wl.push_back({d, Fn});
      if (auto it = cross.find(a); it != cross.end())
        for (const Addr &d : it->second)
          wl.push_back({d, Fn});
      if (auto hit = heldIn.find(a.obj); hit != heldIn.end()) {
        for (Addr cell : hit->second) {
          if (!cell.storage) {
            cell.storage = true;
            cell.inner = 0;
          }
          // The offset of the function in the allocation is the offset in
          // the pointee. A storage address already names that pointee offset.
          Addr rel{nullptr, a.storage, a.off, a.inner};
          wl.push_back({apply(cell, rel), Fn});
        }
      }
      const llvm::Function *home = nullptr;
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(a.obj))
        home = AI->getFunction();
      else if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(a.obj))
        home = Arg->getParent();
      else if (const auto *Ins = llvm::dyn_cast<llvm::Instruction>(a.obj))
        home = Ins->getFunction();
      if (!home)
        continue;
      ensureSites(home);
      auto cit = sitesIn.find(home);
      if (cit == sitesIn.end())
        continue;
      std::vector<Site> mine = cit->second;
      for (const Site &site : mine) {
        for (const auto &ag : site.args) {
          bool touch = false;
          for (const Addr &loc : ag.second)
            if (loc.obj == a.obj)
              touch = true;
          if (!touch)
            continue;
          for (const Addr &formal : formalsFor(ag.first, ag.second, a, site.D)) {
            auto ss = substPlaces(site.C, formal);
            if (ss.failed)
              continue;
            bool eq = false;
            for (const Addr &s : ss.out)
              if (s == a)
                eq = true;
            if (!eq)
              continue;
            build(site.D, formal);
            solve();
            auto nit = nodes.find(keyOf(site.D, formal));
            if (nit == nodes.end() || nit->second.state != 2) {
              unresolved.insert(Fn);
              continue;
            }
            if (nit->second.leak)
              unresolved.insert(Fn);
            for (const Addr &d : nit->second.dst) {
              auto ds = substPlaces(site.C, d);
              if (ds.failed)
                continue;
              for (const Addr &x : ds.out) {
                if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(x.obj)) {
                  if (Arg->getParent() != home) {
                    unresolved.insert(Fn);
                    continue;
                  }
                }
                wl.push_back({x, Fn});
              }
            }
          }
        }
      }
    }

    // A load/store copy may sit in a callee that was handed the object.
    // `dest` is the parameter the pointer is written into. The sources are
    // the addresses in this function, or a global, that were stored there.
    auto identityOf = [](Addr a) {
      if (a.storage)
        return Addr{a.obj, false, a.off, 0};
      return a;
    };
    auto covers = [](Addr written, Addr target) {
      if (!written.obj || written.obj != target.obj || written.off != target.off ||
          written.storage != target.storage)
        return false;
      if (!written.storage)
        return written.inner == target.inner;
      return written.inner == target.inner || written.inner == 0;
    };
    auto asPointee = [](Addr src, Addr query) {
      if (query.storage && !src.storage) {
        src.storage = true;
        src.inner = query.inner;
      }
      return src;
    };
    struct FromNode {
      int state = 0;
      bool leak = false;
      std::vector<Addr> srcs;
    };
    std::unordered_map<SeenKey, FromNode, SeenHash> fromNodes;
    std::unordered_set<const llvm::Function *> fromGray;
    std::function<void(const llvm::Function *, Addr)> fromBuild;
    fromBuild = [&](const llvm::Function *D, Addr dest) {
      if (!D || !llvm::isa<llvm::Argument>(dest.obj) ||
          llvm::cast<llvm::Argument>(dest.obj)->getParent() != D)
        return;
      SeenKey key = keyOf(D, dest);
      if (auto it = fromNodes.find(key); it != fromNodes.end() && it->second.state != 0)
        return;
      if (fromGray.count(D)) {
        fromNodes[key].leak = true;
        fromNodes[key].state = 2;
        return;
      }
      fromNodes[key].state = 1;
      fromGray.insert(D);
      std::vector<Addr> srcs;
      std::unordered_set<Addr, AddrHash> have;
      if (auto it = argCopy.find(D); it != argCopy.end())
        for (const auto &e : it->second)
          if (covers(e.second, dest) && e.first.obj && have.insert(e.first).second)
            srcs.push_back(e.first);
      ensureSites(D);
      if (auto sit = sitesIn.find(D); sit != sitesIn.end()) {
        std::vector<Site> mine = sit->second;
        for (const Site &site : mine) {
          for (const auto &ag : site.args) {
            for (const Addr &formal : formalsFor(ag.first, ag.second, dest, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed) {
                fromNodes[key].leak = true;
                continue;
              }
              bool hit = false;
              for (const Addr &s : ss.out)
                if (s == dest || covers(s, dest))
                  hit = true;
              if (!hit)
                continue;
              SeenKey child = keyOf(site.D, formal);
              fromBuild(site.D, formal);
              if (child == key)
                continue;
              auto cit = fromNodes.find(child);
              if (cit == fromNodes.end() || cit->second.state != 2) {
                fromNodes[key].leak = true;
                continue;
              }
              if (cit->second.leak)
                fromNodes[key].leak = true;
              for (const Addr &s : cit->second.srcs) {
                auto ps = substPlaces(site.C, s);
                if (ps.failed) {
                  fromNodes[key].leak = true;
                  continue;
                }
                for (const Addr &p : ps.out)
                  if (p.obj && have.insert(p).second)
                    srcs.push_back(p);
              }
            }
          }
        }
      }
      fromGray.erase(D);
      auto &n = fromNodes[key];
      n.srcs = std::move(srcs);
      n.state = 2;
    };

    struct QKey {
      const llvm::Value *obj = nullptr;
      int64_t off = 0;
      int64_t inner = 0;
      bool storage = false;
      bool operator==(const QKey &o) const {
        return obj == o.obj && off == o.off && inner == o.inner && storage == o.storage;
      }
    };
    struct QHash {
      size_t operator()(const QKey &k) const { return AddrHash{}(Addr{k.obj, k.storage, k.off, k.inner}); }
    };
    std::unordered_set<const llvm::CallBase *> grounded;
    std::unordered_map<const llvm::CallBase *, std::vector<const llvm::Function *>> found;
    for (const auto &q : queries) {
      if (openQuery.count(q.first))
        continue;
      std::deque<Addr> wq;
      std::unordered_set<QKey, QHash> st;
      std::unordered_set<const llvm::Function *> haveFn;
      wq.push_back(q.second);
      bool open = false;
      while (!wq.empty() && !open) {
        Addr a = wq.front();
        wq.pop_front();
        if (!a.obj || !st.insert(QKey{a.obj, a.off, a.inner, a.storage}).second)
          continue;
        auto take = [&](const Addr &key) {
          if (auto it = cellFn.find(key); it != cellFn.end())
            for (const llvm::Function *Fn : it->second)
              if (haveFn.insert(Fn).second)
                found[q.first].push_back(Fn);
        };
        take(a);
        Addr named = canonAddr(a);
        if (!(named == a))
          take(named);
        auto groundOf = [](const Addr &key) {
          return key.obj && (llvm::isa<llvm::GlobalVariable>(key.obj) || llvm::isa<llvm::CallBase>(key.obj));
        };
        if (groundOf(a) || groundOf(named))
          grounded.insert(q.first);
        // The union of every callsite's actual is already on this parameter.
        if (open)
          break;
        if (!llvm::isa<llvm::AllocaInst>(a.obj) && !llvm::isa<llvm::CallBase>(a.obj))
          continue;
        const llvm::Function *home = nullptr;
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(a.obj))
          home = AI->getFunction();
        else if (const auto *Ins = llvm::dyn_cast<llvm::Instruction>(a.obj))
          home = Ins->getFunction();
        if (!home)
          continue;
        Addr id = identityOf(a);
        ensureSites(home);
        auto cit = sitesIn.find(home);
        if (cit == sitesIn.end())
          continue;
        std::vector<Site> mine = cit->second;
        for (const Site &site : mine) {
          if (open)
            break;
          for (const auto &ag : site.args) {
            if (open)
              break;
            for (const Addr &formal : formalsFor(ag.first, ag.second, id, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed)
                continue;
              bool hit = false;
              for (const Addr &s : ss.out)
                if (s == id || covers(s, id))
                  hit = true;
              if (!hit)
                continue;
              fromBuild(site.D, formal);
              auto fit = fromNodes.find(keyOf(site.D, formal));
              if (fit == fromNodes.end() || fit->second.state != 2)
                continue;
              if (fit->second.leak)
                continue;
              for (const Addr &src : fit->second.srcs) {
                auto ps = substPlaces(site.C, src);
                if (ps.failed)
                  continue;
                for (const Addr &p : ps.out)
                  wq.push_back(asPointee(p, a));
              }
            }
          }
        }
      }
      if (open)
        openQuery.insert(q.first);
    }
    for (auto &kv : found) {
      std::unordered_set<const llvm::Function *> seen;
      std::vector<const llvm::Function *> uniq;
      for (const llvm::Function *Fn : kv.second)
        if (seen.insert(Fn).second)
          uniq.push_back(Fn);
      flowAt[kv.first] = std::move(uniq);
    }
    for (const auto &q : queries) {
      if (openQuery.count(q.first) || flowAt.count(q.first) || !grounded.count(q.first))
        continue;
      // The load reduced to a global or a noalias allocation, and no copy
      // put a function there. An instruction-stored function is absent only
      // when every copy of it reduced. A copy whose actual does not reduce
      // keeps the functions that reach that actual on the parameter.
      flowAt[q.first] = {};
    }
  }

  void run() {
    for (llvm::GlobalVariable &GV : M.globals())
      if (GV.hasInitializer())
        indexTables(&GV, GV.getInitializer(), 0);
    for (llvm::GlobalVariable &GV : M.globals())
      if (GV.hasInitializer()) {
        const llvm::Constant *C = GV.getInitializer();
        if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C))
          place(CS, 0, {}, &GV);
        else if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C))
          place(CA, 0, {}, &GV);
        else
          place(C, 0, {}, &GV);
      }

    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        if (const llvm::Function *D = asFunction(C->getCalledOperand()))
          if (!D->isDeclaration())
            directSites[D].push_back(C);
      }
    }
    learnObjects();
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          std::vector<Field> fields;
          if (auto f = fieldOf(S->getPointerOperand()))
            fields.push_back(*f);
          else {
            std::unordered_set<const llvm::Value *> seenVals;
            std::unordered_set<const llvm::Function *> seenFns;
            addrFields(S->getPointerOperand(), seenVals, seenFns, fields);
          }
          for (const Field &f : fields) {
            fieldStored[f].push_back(S->getValueOperand());
            if (!mixedStruct(f.ty))
              continue;
            std::unordered_set<const llvm::Value *> seen;
            const std::string spec = classSpec(S->getFunction());
            for (const llvm::Function *Fn : fnsOf(S->getValueOperand(), seen, S->getFunction()))
              addFieldFn(f, Fn, spec, false);
            std::unordered_set<const llvm::Value *> seenA;
            std::vector<const llvm::Function *> passed;
            argFns(S->getValueOperand(), seenA, passed);
            for (const llvm::Function *Fn : passed)
              addFieldFn(f, Fn, spec, false);
            if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(S->getPointerOperand()))) {
              std::vector<int> args;
              std::unordered_set<const llvm::Value *> seenB;
              whichArgs(G->getPointerOperand(), S->getFunction(), seenB, args);
              // A load of the same field is the type-wide set. Recording that
              // here would copy every std::function target into every object.
              // Only a function constant, or a parameter that is one, is a
              // store into this argument.
              std::vector<const llvm::Function *> stored = passed;
              if (const llvm::Function *Fn = asFunction(S->getValueOperand()))
                stored.push_back(Fn);
              for (int a : args)
                for (const llvm::Function *Fn : stored)
                  pushNew(fnPut[S->getFunction()], FnPut{a, f.off, Fn});
            }
          }
          if (codePtr(S->getValueOperand()).gv)
            vtableStores.push_back(S);
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
            allocaLoads[AI].push_back(L);
          if (auto f = fieldOf(L->getPointerOperand()))
            fieldLoads[*f].push_back(L);
        }
      }
    }

    bool grew = true;
    while (grew) {
      grew = false;
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
          if (!R || !R->getReturnValue())
            continue;
          std::unordered_set<const llvm::Value *> seen;
          for (const llvm::Function *Fn : fnsOf(R->getReturnValue(), seen, &F)) {
            if (retSeen[&F].insert(Fn).second) {
              retFn[&F].push_back(Fn);
              grew = true;
            }
          }
        }
      }
    }

    for (const llvm::StoreInst *S : vtableStores)
      addSlice(S->getPointerOperand());
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seen;
        if (vtableCall(C->getCalledOperand(), obj, delta, seen) && obj)
          addSlice(obj);
      }
    }

    demand = slice;
    live = true;
    std::vector<const llvm::Value *> roots(slice.begin(), slice.end());
    for (const llvm::Value *V : roots)
      maybeSeed(V);
    while (!wl.empty()) {
      const llvm::Value *V = wl.front();
      wl.pop_front();
      queued.erase(V);
      prop(V);
    }
    for (const llvm::StoreInst *S : vtableStores) {
      CodePtr cp = codePtr(S->getValueOperand());
      auto it = tok.find(S->getPointerOperand());
      if (it == tok.end())
        continue;
      for (int t : it->second)
        vtbl[t].insert(cp);
    }
    // An indirect call returns the objects its targets return, the same way a
    // direct call does. A factory stored in a map is not a direct call, and
    // the allocated object would otherwise die at the call. Only an object
    // that holds a table is copied. Function-pointer fields still do not
    // carry a receiver in the other direction.
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        std::unordered_set<const llvm::Value *> walked;
        std::vector<const llvm::Function *> ts = fnsOf(C->getCalledOperand(), walked, &F);
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (vtableCall(C->getCalledOperand(), obj, delta, seenV) && obj) {
          auto it = tok.find(obj);
          if (it != tok.end())
            for (int t : it->second) {
              auto vt = vtbl.find(t);
              if (vt == vtbl.end())
                continue;
              for (const CodePtr &cp : vt->second) {
                auto fit = fnAt.find({cp.gv, cp.off + delta});
                if (fit != fnAt.end() && fit->second)
                  ts.push_back(fit->second);
              }
            }
        }
        for (const llvm::Function *D : ts) {
          if (!D || D->isDeclaration() || D->getFunctionType() != C->getFunctionType())
            continue;
          for (const llvm::Instruction &RI : llvm::instructions(*D)) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&RI);
            if (!R || !R->getReturnValue())
              continue;
            auto rt = tok.find(R->getReturnValue());
            if (rt == tok.end())
              continue;
            for (int t : rt->second)
              if (vtbl.count(t))
                addTok(C, t);
          }
        }
      }
    }
    while (!wl.empty()) {
      const llvm::Value *V = wl.front();
      wl.pop_front();
      queued.erase(V);
      prop(V);
    }
    carryFields();
    // A vtable call passes its receiver into each function at that slot, so a
    // later vtable call on the same object can see the table. Function-pointer
    // fields stay shared by struct type and do not carry an object.
    struct Site {
      const llvm::CallBase *call;
      const llvm::Value *obj;
      int64_t delta;
      int arg;
    };
    std::vector<Site> sites;
    std::unordered_map<const llvm::Value *, std::vector<int>> byObj;
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (!vtableCall(C->getCalledOperand(), obj, delta, seenV) || !obj)
          continue;
        int arg = -1;
        const llvm::Value *base = stripCasts(obj);
        for (unsigned i = 0; i < C->arg_size(); ++i)
          if (stripCasts(C->getArgOperand(i)) == base) {
            arg = static_cast<int>(i);
            break;
          }
        byObj[obj].push_back(static_cast<int>(sites.size()));
        sites.push_back({C, obj, delta, arg});
      }
    }
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> inq;
    for (const auto &kv : byObj) {
      if (!tok.count(kv.first))
        continue;
      q.push_back(kv.first);
      inq.insert(kv.first);
    }
    while (!q.empty()) {
      const llvm::Value *obj = q.front();
      q.pop_front();
      inq.erase(obj);
      auto have = tok.find(obj);
      if (have == tok.end())
        continue;
      std::vector<int> mine = have->second;
      for (int si : byObj[obj]) {
        const Site &site = sites[si];
        if (site.arg < 0)
          continue;
        std::unordered_set<const llvm::Function *> ts;
        for (int t : mine) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + site.delta});
            if (fit != fnAt.end() && fit->second && !fit->second->isDeclaration())
              ts.insert(fit->second);
          }
        }
        for (const llvm::Function *D : ts) {
          if (static_cast<unsigned>(site.arg) >= D->arg_size())
            continue;
          const llvm::Argument *formal = D->getArg(static_cast<unsigned>(site.arg));
          for (int t : mine)
            recv(formal, t, q, inq, byObj);
        }
      }
    }
  }
};

// Entry parameters that reach a call to the chop. The search space is the
// downstream functions that reach the chop. A parameter flows through casts,
// freezes, phis, selects, a field address, a store and load of a local or a
// global, the matching argument and the returned value of a call, and a load
// through the parameter. memcpy makes the destination carry the source.
struct Bits {
  std::vector<uint64_t> w;
  bool unite(const Bits &o) {
    bool grew = false;
    if (w.size() < o.w.size()) {
      w.resize(o.w.size());
      grew = true;
    }
    for (size_t i = 0; i < o.w.size(); ++i) {
      uint64_t n = w[i] | o.w[i];
      if (n != w[i]) {
        w[i] = n;
        grew = true;
      }
    }
    return grew;
  }
  bool empty() const {
    for (uint64_t x : w)
      if (x)
        return false;
    return true;
  }
  template <class F>
  void each(F f) const {
    for (size_t i = 0; i < w.size(); ++i) {
      uint64_t x = w[i];
      while (x) {
        int b = __builtin_ctzll(x);
        f(static_cast<int>(i * 64 + b));
        x &= x - 1;
      }
    }
  }
};

struct Loc {
  const llvm::Value *base = nullptr;
  int64_t off = 0;
  bool known = false;
};

struct SlotKey {
  const llvm::Value *base = nullptr;
  int64_t off = 0;
  bool operator==(const SlotKey &o) const { return base == o.base && off == o.off; }
};

struct MemHash {
  size_t operator()(const SlotKey &s) const {
    return static_cast<size_t>(reinterpret_cast<uintptr_t>(s.base)) ^
           (static_cast<size_t>(s.off) * 1315423911u);
  }
};

Loc locate(const llvm::Value *V, const llvm::DataLayout &DL) {
  Loc loc;
  if (!V)
    return loc;
  const llvm::Value *cur = V->stripPointerCasts();
  int64_t off = 0;
  bool known = true;
  while (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
    if (known) {
      llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
      if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
        known = false;
      else
        off += ap.getSExtValue();
    }
    cur = G->getPointerOperand()->stripPointerCasts();
  }
  if (!llvm::isa<llvm::AllocaInst>(cur) && !llvm::isa<llvm::GlobalVariable>(cur))
    return loc;
  loc.base = cur;
  loc.off = off;
  loc.known = known;
  return loc;
}

bool byteCopy(const llvm::CallBase *C, const llvm::Value *&dst, const llvm::Value *&src) {
  dst = src = nullptr;
  if (!C || C->arg_size() < 2)
    return false;
  const llvm::Function *F = asFunction(C->getCalledOperand());
  if (!F)
    return false;
  bool copy = false;
  if (F->isIntrinsic()) {
    llvm::Intrinsic::ID id = F->getIntrinsicID();
    copy = id == llvm::Intrinsic::memcpy || id == llvm::Intrinsic::memmove;
  } else {
    // A byte copy is the compiler's own library-function model, not a name
    // list. TargetLibraryInfo classifies the callee by its prototype on the
    // module's target, honoring nobuiltin. Every copy below writes argument 0
    // from argument 1.
    static std::string triple;
    static std::unique_ptr<llvm::TargetLibraryInfoImpl> impl;
    static std::unique_ptr<llvm::TargetLibraryInfo> info;
    const std::string &t = F->getParent()->getTargetTriple();
    if (!info || t != triple) {
      triple = t;
      impl = std::make_unique<llvm::TargetLibraryInfoImpl>(llvm::Triple(t));
      info = std::make_unique<llvm::TargetLibraryInfo>(*impl);
    }
    llvm::LibFunc lf;
    if (info->getLibFunc(*F, lf)) {
      switch (lf) {
      case llvm::LibFunc_memcpy:
      case llvm::LibFunc_memmove:
      case llvm::LibFunc_mempcpy:
      case llvm::LibFunc_memccpy:
      case llvm::LibFunc_strcpy:
      case llvm::LibFunc_strncpy:
      case llvm::LibFunc_stpcpy:
      case llvm::LibFunc_strcat:
      case llvm::LibFunc_strncat:
      case llvm::LibFunc_memcpy_chk:
      case llvm::LibFunc_memmove_chk:
      case llvm::LibFunc_mempcpy_chk:
      case llvm::LibFunc_strcpy_chk:
      case llvm::LibFunc_strncpy_chk:
      case llvm::LibFunc_stpcpy_chk:
        copy = true;
        break;
      default:
        break;
      }
    }
  }
  if (!copy)
    return false;
  dst = C->getArgOperand(0);
  src = C->getArgOperand(1);
  return true;
}

// A call that returns fresh storage. The memory it returns holds no bytes
// yet, so an allocation without a body is not an outside source of bytes.
// This is the compiler's own library model, under the same rules as above.
const llvm::TargetLibraryInfo *libraryInfo(const llvm::Function *F) {
  static std::string triple;
  static std::unique_ptr<llvm::TargetLibraryInfoImpl> impl;
  static std::unique_ptr<llvm::TargetLibraryInfo> info;
  const std::string &t = F->getParent()->getTargetTriple();
  if (!info || t != triple) {
    triple = t;
    impl = std::make_unique<llvm::TargetLibraryInfoImpl>(llvm::Triple(t));
    info = std::make_unique<llvm::TargetLibraryInfo>(*impl);
  }
  return info.get();
}

// The compiler's model of a library allocation. Since LLVM 16 the
// allocating library functions are described by the attributes the
// compiler infers for them (allockind, allocsize, allocptr) rather than by
// a table; modules compiled without optimization carry none of those, so
// they are inferred here on a copy of the declaration, in a scratch module
// with the same layout, leaving the analysed modules untouched. The
// remaining table entries (operator new, strdup) are still found by the
// library-info lookup.
struct LibAlloc {
  bool alloc = false;    // returns fresh memory
  bool realloc = false;  // ... holding the contents of its pointer argument
  int ptrArg = -1;       // the argument a reallocation replaces
  std::optional<unsigned> sizeArg, countArg;  // allocsize operands
};
const LibAlloc &libAlloc(const llvm::Function *F) {
  static std::map<std::pair<std::string, const llvm::FunctionType *>, LibAlloc> memo;
  auto key = std::make_pair(F->getName().str(), F->getFunctionType());
  auto it = memo.find(key);
  if (it != memo.end())
    return it->second;
  LibAlloc m;
  // A scratch module of the function's context, alive only for this
  // question: one kept across calls would outlive the context.
  llvm::LLVMContext &Ctx = F->getContext();
  auto S = std::make_unique<llvm::Module>("libmodel", Ctx);
  S->setDataLayout(F->getParent()->getDataLayout());
  S->setTargetTriple(F->getParent()->getTargetTriple());
  llvm::Function *copy =
      llvm::Function::Create(F->getFunctionType(), llvm::GlobalValue::ExternalLinkage, F->getName(), *S);
  llvm::inferNonMandatoryLibFuncAttrs(*copy, *libraryInfo(F));
  if (copy->hasFnAttribute(llvm::Attribute::AllocKind)) {
    const llvm::AllocFnKind k = copy->getFnAttribute(llvm::Attribute::AllocKind).getAllocKind();
    m.alloc = (k & llvm::AllocFnKind::Alloc) != llvm::AllocFnKind::Unknown;
    m.realloc = (k & llvm::AllocFnKind::Realloc) != llvm::AllocFnKind::Unknown;
  }
  if (copy->hasFnAttribute(llvm::Attribute::AllocSize)) {
    auto sz = copy->getFnAttribute(llvm::Attribute::AllocSize).getAllocSizeArgs();
    m.sizeArg = sz.first;
    m.countArg = sz.second;
  }
  for (unsigned i = 0; i < copy->arg_size(); ++i)
    if (copy->getArg(i)->hasAttribute(llvm::Attribute::AllocatedPointer))
      m.ptrArg = static_cast<int>(i);
  copy->eraseFromParent();
  return memo.emplace(key, m).first->second;
}

// A call that returns fresh storage, by the compiler's library model.
bool allocates(const llvm::CallBase *C) {
  const llvm::Function *F = C ? C->getCalledFunction() : nullptr;
  if (!F)
    return false;
  if (llvm::isAllocationFn(C, libraryInfo(F)))
    return true;
  const LibAlloc &m = libAlloc(F);
  return m.alloc || m.realloc;
}

// The memory whose contents an allocating call's result holds. A plain
// allocation (malloc, calloc, new) holds none; a reallocation holds the
// memory it replaces; a string duplication holds the string.
const llvm::Value *allocSource(const llvm::CallBase *C) {
  const llvm::Function *F = C ? C->getCalledFunction() : nullptr;
  if (!F)
    return nullptr;
  const llvm::TargetLibraryInfo *TLI = libraryInfo(F);
  const LibAlloc &m = libAlloc(F);
  if (m.realloc && m.ptrArg >= 0 && static_cast<unsigned>(m.ptrArg) < C->arg_size())
    return C->getArgOperand(static_cast<unsigned>(m.ptrArg));
  if (m.alloc || m.realloc)
    return nullptr;
  if (!llvm::isAllocationFn(C, TLI) || llvm::isMallocOrCallocLikeFn(C, TLI))
    return nullptr;
  for (const llvm::Value *a : C->args())
    if (a->getType()->isPointerTy())
      return a;
  return nullptr;
}

// The operands of an allocating call that give its size.
std::optional<std::pair<unsigned, std::optional<unsigned>>> allocSizeArgs(const llvm::CallBase *C) {
  const llvm::Function *F = C ? C->getCalledFunction() : nullptr;
  if (!F)
    return std::nullopt;
  const LibAlloc &m = libAlloc(F);
  if (m.sizeArg)
    return std::make_pair(*m.sizeArg, m.countArg);
  return std::nullopt;
}

// The size an allocating call requests, when it is a constant.
std::optional<uint64_t> allocSize(const llvm::CallBase *C) {
  const llvm::Function *F = C ? C->getCalledFunction() : nullptr;
  if (!F)
    return std::nullopt;
  const LibAlloc &m = libAlloc(F);
  if (m.sizeArg) {
    if (*m.sizeArg >= C->arg_size())
      return std::nullopt;
    const auto *S = llvm::dyn_cast<llvm::ConstantInt>(C->getArgOperand(*m.sizeArg));
    if (!S || S->getValue().getActiveBits() > 62)
      return std::nullopt;
    uint64_t sz = S->getZExtValue();
    if (m.countArg) {
      if (*m.countArg >= C->arg_size())
        return std::nullopt;
      const auto *N = llvm::dyn_cast<llvm::ConstantInt>(C->getArgOperand(*m.countArg));
      if (!N || N->getValue().getActiveBits() > 62)
        return std::nullopt;
      llvm::APInt prod = S->getValue().zext(128) * N->getValue().zext(128);
      if (prod.getActiveBits() > 62)
        return std::nullopt;
      sz = prod.getZExtValue();
    }
    return sz;
  }
  const llvm::TargetLibraryInfo *TLI = libraryInfo(F);
  if (!llvm::isAllocationFn(C, TLI))
    return std::nullopt;
  std::optional<llvm::APInt> sz = llvm::getAllocSize(C, TLI);
  if (!sz || sz->getActiveBits() > 62)
    return std::nullopt;
  return sz->getZExtValue();
}

void fillInputs(Solve &solve, llvm::Module &M, llvm::Module &upstream,
                const std::unordered_set<const llvm::Function *> &backward,
                const std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> &namedCallers,
                const std::unordered_map<std::string, std::unordered_set<std::string>> &entriesOf,
                const std::unordered_map<std::string, std::unordered_set<std::string>> &initialOf,
                std::unordered_map<std::string, std::vector<Input>> &inputs,
                std::unordered_map<std::string, std::vector<Input>> &unreduced,
                std::unordered_map<std::string, std::vector<Witness>> &witnesses,
                std::unordered_map<std::string, std::vector<Cell>> &cells) {
  const llvm::DataLayout &DL = M.getDataLayout();
  // A declaration in M is the function of the same name in the upstream
  // module, when that function has a body. The body is not a callee set.
  std::unordered_map<std::string, const llvm::Function *> upstreamBody;
  for (const llvm::Function &F : upstream)
    if (!F.isDeclaration() && F.hasName())
      upstreamBody.emplace(F.getName().str(), &F);
  auto definedBody = [&](const llvm::Function *D) -> const llvm::Function * {
    if (!D)
      return nullptr;
    if (!D->isDeclaration())
      return D;
    if (!D->hasName())
      return nullptr;
    auto it = upstreamBody.find(D->getName().str());
    return it == upstreamBody.end() ? nullptr : it->second;
  };
  // Roots are read from the actual at each call of the chop. The search
  // space of one export is the functions reachable from it. A helper that
  // does not itself call the chop is still in that space: AcquireImage is
  // one. A declaration contributes no copy.
  std::unordered_set<const llvm::Function *> space = backward;
  {
    std::vector<const llvm::Function *> q(backward.begin(), backward.end());
    for (size_t i = 0; i < q.size(); ++i) {
      const llvm::Function *F = q[i];
      if (!F || F->isDeclaration())
        continue;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        std::vector<const llvm::Function *> cs = solve.callees(C, false);
        if (const llvm::Function *D = C->getCalledFunction()) {
          bool have = false;
          for (const llvm::Function *E : cs)
            if (E == D)
              have = true;
          if (!have && !D->isDeclaration() && !D->isIntrinsic())
            cs.push_back(D);
        }
        for (const llvm::Function *D : cs)
          if (D && !D->isDeclaration() && space.insert(D).second)
            q.push_back(D);
      }
    }
  }

  std::unordered_map<const llvm::Function *, int> modOrd;
  {
    int n = 0;
    for (const llvm::Function &F : M)
      modOrd.emplace(&F, n++);
  }
  auto byFn = [&](const llvm::Function *A, const llvm::Function *B) {
    std::string an = A && A->hasName() ? A->getName().str() : "";
    std::string bn = B && B->hasName() ? B->getName().str() : "";
    if (an != bn)
      return an < bn;
    return modOrd[A] < modOrd[B];
  };
  std::vector<const llvm::Function *> spaceOrd(space.begin(), space.end());
  std::sort(spaceOrd.begin(), spaceOrd.end(), byFn);
  std::unordered_map<const llvm::CallBase *, std::vector<const llvm::Function *>> resolved;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> sites;
  for (const llvm::Function *F : spaceOrd) {
    if (!F || F->isDeclaration())
      continue;
    for (const llvm::Instruction &I : llvm::instructions(*F)) {
      const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!C || C->isInlineAsm())
        continue;
      auto callees = solve.callees(C, false);
      if (const llvm::Function *D = C->getCalledFunction()) {
        bool have = false;
        for (const llvm::Function *E : callees)
          if (E == D)
            have = true;
        if (!have && !D->isDeclaration() && !D->isIntrinsic())
          callees.push_back(D);
      }
      resolved[C] = callees;
      for (const llvm::Function *D : callees)
        if (D && space.count(D))
          sites[D].push_back(C);
    }
  }

  std::unordered_map<std::string, int> entryId;
  std::vector<const llvm::Function *> entryFns;
  std::vector<std::string> entryNames;
  for (const llvm::Function *F : backward) {
    if (!strongExport(F))
      continue;
    std::string name = show(F);
    bool used = false;
    for (const auto &kv : initialOf)
      if (kv.second.count(name))
        used = true;
    if (!used || entryId.count(name))
      continue;
    entryId.emplace(name, static_cast<int>(entryFns.size()));
    entryFns.push_back(F);
    entryNames.push_back(name);
  }
  std::vector<size_t> order(entryFns.size());
  std::iota(order.begin(), order.end(), 0);
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) { return entryNames[a] < entryNames[b]; });
  {
    std::vector<const llvm::Function *> fns;
    std::vector<std::string> names;
    fns.reserve(order.size());
    names.reserve(order.size());
    for (size_t i : order) {
      fns.push_back(entryFns[i]);
      names.push_back(entryNames[i]);
    }
    entryFns.swap(fns);
    entryNames.swap(names);
    entryId.clear();
    for (size_t i = 0; i < entryNames.size(); ++i)
      entryId.emplace(entryNames[i], static_cast<int>(i));
  }

  std::unordered_map<const llvm::Function *, std::vector<const llvm::Function *>> succs;
  for (const auto &kv : resolved) {
    const llvm::Function *caller = kv.first->getFunction();
    auto &out = succs[caller];
    for (const llvm::Function *D : kv.second)
      if (D && !D->isDeclaration())
        out.push_back(D);
  }
  for (const auto &kv : namedCallers)
    for (const llvm::Function *caller : kv.second)
      succs[caller].push_back(kv.first);
  std::unordered_map<const llvm::Function *, std::vector<uint64_t>> reachMask;
  for (size_t ei = 0; ei < entryFns.size(); ++ei) {
    std::unordered_set<const llvm::Function *> seenF;
    std::vector<const llvm::Function *> fq{entryFns[ei]};
    seenF.insert(entryFns[ei]);
    for (size_t i = 0; i < fq.size(); ++i) {
      size_t w = ei / 64;
      unsigned b = static_cast<unsigned>(ei) % 64;
      auto &mask = reachMask[fq[i]];
      if (mask.size() <= w)
        mask.resize(w + 1, 0);
      mask[w] |= 1ull << b;
      auto sit = succs.find(fq[i]);
      if (sit == succs.end())
        continue;
      for (const llvm::Function *D : sit->second)
        if (seenF.insert(D).second)
          fq.push_back(D);
    }
  }

  llvm::LoopAnalysisManager lam;
  llvm::FunctionAnalysisManager fam;
  llvm::CGSCCAnalysisManager cgam;
  llvm::ModuleAnalysisManager mam;
  llvm::PassBuilder pb;
  pb.registerModuleAnalyses(mam);
  pb.registerCGSCCAnalyses(cgam);
  pb.registerFunctionAnalyses(fam);
  pb.registerLoopAnalyses(lam);
  pb.crossRegisterProxies(lam, fam, cgam, mam);

  struct Status {
    bool any = false;
    bool open = false;
    bool local = false;
    bool hasConst = false;
    bool none = false;
    const llvm::Value *slot = nullptr;
    const llvm::Instruction *at = nullptr;
    int64_t off = 0;
    bool offKnown = true;
    std::set<std::pair<std::string, int>> args;
  };
  auto bare = []() { return Status(); };
  auto opened = []() {
    Status s;
    s.any = true;
    s.open = true;
    return s;
  };
  auto constant = []() {
    Status s;
    s.any = true;
    s.hasConst = true;
    return s;
  };
  auto nothing = []() {
    Status s;
    s.any = true;
    s.none = true;
    return s;
  };
  auto meet = [](Status a, Status b) {
    if (!a.any)
      return b;
    if (!b.any)
      return a;
    Status s;
    s.any = true;
    s.open = a.open || b.open;
    s.local = a.local || b.local;
    s.hasConst = a.hasConst || b.hasConst;
    s.none = a.none || b.none;
    s.args = a.args;
    s.args.insert(b.args.begin(), b.args.end());
    if (a.slot && a.slot == b.slot && a.offKnown && b.offKnown && a.off == b.off) {
      s.slot = a.slot;
      s.off = a.off;
      s.offKnown = true;
      if (a.at == b.at)
        s.at = a.at;
      else if (!a.at)
        s.at = b.at;
      else if (!b.at)
        s.at = a.at;
    }
    return s;
  };
  // Alternative definitions of one value. The value is those bytes only when
  // every alternative is that same predictable set. A choice between different
  // sets depends on memory that is not those bytes. The union is not the value.
  // Alternative definitions of one value. They determine that value only when
  // every alternative is the same predictable set. A choice between different
  // sets depends on other memory, so the union is not a proof. The arguments
  // stay so one invocation can still be separated from another.
  auto alt = [&](Status a, Status b) {
    if (!a.any)
      return b;
    if (!b.any)
      return a;
    auto predictable = [](const Status &x) {
      return !x.open && !x.local && !x.hasConst && !x.none && !x.args.empty();
    };
    if (predictable(a) && predictable(b) && a.args == b.args)
      return a;
    Status s = meet(a, b);
    if (predictable(a) && predictable(b))
      s.open = true;
    return s;
  };
  auto slotFn = [](const llvm::Value *slot) -> const llvm::Function * {
    if (const auto *I = llvm::dyn_cast_or_null<llvm::Instruction>(slot))
      return I->getFunction();
    if (const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(slot))
      return A->getParent();
    return nullptr;
  };
  auto handed = [](const llvm::CallBase *C, const llvm::Value *slot) {
    if (!C || !slot)
      return true;
    std::function<bool(const llvm::Value *, std::unordered_set<const llvm::Value *> &)> reach;
    reach = [&](const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen) {
      if (!V || !seen.insert(V).second)
        return false;
      if (const auto *M = llvm::dyn_cast<llvm::MetadataAsValue>(V)) {
        if (const auto *MV = llvm::dyn_cast<llvm::ValueAsMetadata>(M->getMetadata()))
          return reach(MV->getValue(), seen);
        return false;
      }
      V = V->stripPointerCasts();
      if (V == slot)
        return true;
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V))
        return reach(G->getPointerOperand(), seen);
      return false;
    };
    for (const llvm::Use &U : C->args()) {
      std::unordered_set<const llvm::Value *> seen;
      if (reach(U.get(), seen))
        return true;
    }
    return false;
  };
  // A field of a heap object is a constant offset from that allocation.
  // An alloca or a global is a different object.
  auto fromObject = [](const llvm::Value *V, const llvm::Value *slot) {
    if (!V || !slot)
      return false;
    const llvm::Value *root = slot->stripPointerCasts();
    std::unordered_set<const llvm::Value *> seen;
    std::function<bool(const llvm::Value *)> reach;
    reach = [&](const llvm::Value *U) {
      if (!U || !seen.insert(U).second)
        return false;
      U = U->stripPointerCasts();
      if (U == root)
        return true;
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U))
        return reach(G->getPointerOperand());
      // A pointer loaded from a field of the object was stored there.
      // Writing through it writes that field's buffer.
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U))
        return reach(L->getPointerOperand());
      return false;
    };
    return reach(V);
  };
  // The allocation, alloca, argument, or global a pointer is derived from.
  // A phi of two objects does not reduce.
  auto objectRoot = [](const llvm::Value *V) -> const llvm::Value * {
    std::unordered_set<const llvm::Value *> seen;
    while (V && seen.insert(V).second) {
      V = V->stripPointerCasts();
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        V = G->getPointerOperand();
        continue;
      }
      if (llvm::isa<llvm::AllocaInst>(V) || llvm::isa<llvm::GlobalVariable>(V) ||
          llvm::isa<llvm::Argument>(V) || llvm::isa<llvm::CallBase>(V))
        return V;
      break;
    }
    return nullptr;
  };
  // A constant written into one field is not a root of the object.
  // It does not erase an entry argument written into another field.
  auto entryRoots = [&](Status val) -> Status {
    Status keep;
    for (const auto &a : val.args)
      if (a.second >= 0)
        keep.args.insert(a);
    if (keep.args.empty())
      return val.open ? opened() : bare();
    keep.any = true;
    // A constant or a local mixed into this same value is not the parameter.
    keep.open = val.open || val.local || val.hasConst || val.none;
    return keep;
  };

  struct VKey {
    int entry = -1;
    const llvm::Value *v = nullptr;
    bool carry = false;
    bool operator==(const VKey &o) const {
      return entry == o.entry && v == o.v && carry == o.carry;
    }
  };
  struct VHash {
    size_t operator()(const VKey &k) const {
      return static_cast<size_t>(k.entry) * 1315423911u ^
             static_cast<size_t>(reinterpret_cast<uintptr_t>(k.v)) ^
             (k.carry ? 0x9e3779b97f4a7c15ull : 0u);
    }
  };
  std::unordered_map<VKey, Status, VHash> memo;
  std::unordered_set<VKey, VHash> active;
  int ei = -1;
  // An address that did not reduce stays open. One surviving entry argument
  // does not erase that open.
  bool carry = false;
  const llvm::Function *entryFn = nullptr;
  std::string entryName;
  auto cone = [&](const llvm::Function *F) {
    if (!F || ei < 0)
      return false;
    auto it = reachMask.find(F);
    if (it == reachMask.end())
      return false;
    size_t w = static_cast<size_t>(ei) / 64;
    unsigned b = static_cast<unsigned>(ei) % 64;
    return w < it->second.size() && ((it->second[w] >> b) & 1ull);
  };
  // Entry activation of F: an invocation reached from the current entry by a
  // call path that does not already contain F. Its arguments are the actuals
  // at callsites whose callers are reachable from the entry without entering
  // F. A callsite in a function that is reached only by entering F belongs to
  // a later invocation and does not define this parameter.
  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> entryReach;
  auto entryCall = [&](const llvm::Function *caller, const llvm::Function *callee) -> bool {
    if (!caller || !callee || !entryFn)
      return false;
    auto it = entryReach.find(callee);
    if (it == entryReach.end()) {
      std::unordered_set<const llvm::Function *> seen;
      std::vector<const llvm::Function *> q{entryFn};
      seen.insert(entryFn);
      for (size_t i = 0; i < q.size(); ++i) {
        if (q[i] == callee)
          continue;
        auto sit = succs.find(q[i]);
        if (sit == succs.end())
          continue;
        for (const llvm::Function *D : sit->second)
          if (D && seen.insert(D).second)
            q.push_back(D);
      }
      it = entryReach.emplace(callee, std::move(seen)).first;
    }
    return it->second.count(caller) != 0;
  };
  auto activates = [&](const llvm::CallBase *C, const llvm::Function *F) -> bool {
    if (!C || !F)
      return false;
    if (C->getCalledFunction() == F)
      return true;
    auto it = resolved.find(C);
    if (it == resolved.end())
      return false;
    for (const llvm::Function *D : it->second) {
      if (!D)
        continue;
      if (D == F || definedBody(D) == F)
        return true;
    }
    return false;
  };
  auto nameable = [](const llvm::GlobalVariable *G) {
    return G && G->hasName() && !G->isConstant() && !G->hasLocalLinkage() &&
           !G->hasHiddenVisibility();
  };
  auto pretty = [](llvm::StringRef n) {
    std::string d = llvm::demangle(n.str());
    if (d.empty() || d == n)
      return n.str();
    return d;
  };

  std::function<Status(const llvm::Instruction *, const llvm::Value *, bool, const int64_t *)> memRoots;
  std::function<Status(const llvm::Value *)> walk;
  // One entry activation of the function that contains the chop. Formals of
  // that function are the actuals at this call, not the union of every call.
  const llvm::CallBase *activation = nullptr;
  // Body currently being summarized, innermost last. A spill of that
  // function's argument is the actual at the call that entered the body.
  std::vector<std::pair<const llvm::CallBase *, const llvm::Function *>> summarizing;
  // The call on the use-def trace that entered a function. A formal of that
  // function is the actual at this call. Other callers pass other objects.
  auto boundCall = [&](const llvm::Function *F) -> const llvm::CallBase * {
    if (!F)
      return nullptr;
    auto same = [&](const llvm::Function *B) {
      if (!B)
        return false;
      if (B == F)
        return true;
      const llvm::Function *D = definedBody(B);
      return D == F;
    };
    for (size_t i = summarizing.size(); i > 0; --i)
      if (same(summarizing[i - 1].second))
        return summarizing[i - 1].first;
    if (activation && activates(activation, F))
      return activation;
    return nullptr;
  };
  std::unordered_map<const llvm::Value *, Status> actMemo;
  std::map<std::pair<const llvm::Argument *, int64_t>, Status> actRf;
  // A call writes an object only through a pointer it was given. The bytes
  // are the values that body stores through that formal. A declaration has
  // no such store: the write stays open, and the other arguments are not
  // the bytes. The returned pointer is not those arguments.
  struct CWKey {
    int entry = -1;
    const llvm::Function *fn = nullptr;
    unsigned arg = 0;
    bool operator==(const CWKey &o) const {
      return entry == o.entry && fn == o.fn && arg == o.arg;
    }
  };
  struct CWHash {
    size_t operator()(const CWKey &k) const {
      return static_cast<size_t>(k.entry) * 1315423911u ^
             static_cast<size_t>(reinterpret_cast<uintptr_t>(k.fn)) ^
             (static_cast<size_t>(k.arg) << 1);
    }
  };
  struct CallGuard {
    int entry = -1;
    const llvm::CallBase *call = nullptr;
    unsigned arg = 0;
    bool operator==(const CallGuard &o) const {
      return entry == o.entry && call == o.call && arg == o.arg;
    }
  };
  struct CallGuardHash {
    size_t operator()(const CallGuard &k) const {
      return static_cast<size_t>(k.entry) * 1315423911u ^
             static_cast<size_t>(reinterpret_cast<uintptr_t>(k.call)) ^
             (static_cast<size_t>(k.arg) << 1);
    }
  };
  std::unordered_set<CallGuard, CallGuardHash> callWriteStack;
  std::function<Status(const llvm::CallBase *, const llvm::Function *, unsigned, const int64_t *)> storedThrough;
  // A declaration has no body. Each argument the caller passed is a root
  // of the returned value, walked on its own. A constant or a local is not
  // a root. One argument that does not reduce does not erase another.
  // The returned pointer is not those arguments.
  std::function<Status(const llvm::CallBase *)> fromArgs;
  std::function<Status(const llvm::CallBase *, int64_t, llvm::StructType *, uint64_t)> fieldBytes;
  // The field being asked. A store defines that field only along the same
  // access path. A different constant field of this struct is not these bytes.
  struct FieldAsk {
    llvm::StructType *ty = nullptr;
    uint64_t size = 0;
  };
  std::vector<FieldAsk> fieldAsk;
  std::function<Status(const llvm::Argument *, int64_t)> readField;
  std::function<Status(Status, const llvm::CallBase *, const llvm::Value *)> ground;
  // Calls whose returned objects are being summarized. A field of the callee's
  // own argument is that field of the actual at this call.
  std::vector<std::pair<const llvm::CallBase *, int64_t>> fbStack;
  std::function<Status(const llvm::Argument *, int64_t)> fieldOfCall;
  auto spillValue = [](const llvm::AllocaInst *AI) -> const llvm::Value * {
    const llvm::Value *st = nullptr;
    int n = 0;
    for (const llvm::User *U : AI->users()) {
      const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
      if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
        continue;
      st = SI->getValueOperand();
      ++n;
    }
    return n == 1 ? st : nullptr;
  };
  walk = [&](const llvm::Value *V) -> Status {
    if (!V)
      return opened();
    VKey key{ei, V, carry};
    bool actHere = false;
    if (activation) {
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V))
        actHere = activates(activation, I->getFunction());
      else if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(V))
        actHere = activates(activation, Arg->getParent());
    }
    // A formal bound to one call on the trace is that call's actual. The
    // union of every caller is a different invocation and must not be reused.
    bool frameArg = false;
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (!entryFn || A->getParent() != entryFn) {
        const llvm::CallBase *via = boundCall(A->getParent());
        if (via && via != activation)
          frameArg = true;
        else if (!actHere && via && !sites.count(A->getParent()))
          frameArg = true;
      }
    }
    if (!frameArg) {
      // An activation rewalk must not reuse a value computed from the union
      // of every caller. That union is a different invocation.
      if (activation) {
        auto it = actMemo.find(V);
        if (it != actMemo.end())
          return it->second;
      } else {
        auto found = memo.find(key);
        if (found != memo.end())
          return found->second;
      }
    }
    if (!active.insert(key).second)
      return bare();
    Status s = opened();
    bool noMemo = false;
    // Callers recorded for this entry did not reduce the argument. The call
    // whose body is on the stack did pass an actual. That actual is this
    // invocation, computed without this frame so the body cannot explain it
    // through the same argument. Only a pure actual replaces the open result,
    // and it is not memoized: a later activation may prove a different actual.
    auto forwardPure = [&](const llvm::Argument *A) -> Status {
      Status none;
      const llvm::CallBase *via = nullptr;
      size_t keep = summarizing.size();
      for (size_t i = summarizing.size(); i > 0; --i) {
        if (summarizing[i - 1].second == A->getParent()) {
          via = summarizing[i - 1].first;
          keep = i - 1;
          break;
        }
      }
      if (!via || A->getArgNo() >= via->arg_size())
        return none;
      auto saved = summarizing;
      summarizing.resize(keep);
      Status fwd = walk(via->getArgOperand(A->getArgNo()));
      summarizing = std::move(saved);
      bool ent = false;
      for (const auto &a : fwd.args)
        if (a.second >= 0)
          ent = true;
      if (!ent || fwd.open || fwd.local || fwd.hasConst || fwd.none)
        return none;
      Status keepS;
      keepS.any = true;
      for (const auto &a : fwd.args)
        if (a.second >= 0)
          keepS.args.insert(a);
      noMemo = true;
      return keepS;
    };
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      const llvm::Value *cur = G;
      int64_t fieldOff = 0;
      bool fieldKnown = true;
      // A zero-index GEP is a field at offset 0. stripPointerCasts drops it,
      // which would make that scalar the whole object.
      while (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
        if (fieldKnown) {
          llvm::APInt ap(DL.getIndexSizeInBits(GG->getPointerAddressSpace()), 0);
          if (!GG->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
            fieldKnown = false;
          else
            fieldOff += ap.getSExtValue();
        }
        cur = GG->getPointerOperand()->stripPointerCasts();
      }
      llvm::StructType *sty = nullptr;
      uint64_t fsz = 0;
      if (fieldKnown) {
        const llvm::Value *base = G;
        uint64_t outerSz = 0;
        if (const auto *SG = llvm::dyn_cast<llvm::GEPOperator>(base))
          if (SG->getResultElementType()->isSized())
            outerSz = DL.getTypeAllocSize(SG->getResultElementType());
        std::unordered_set<const llvm::Value *> seenTy;
        while (base && seenTy.insert(base).second) {
          const auto *SG = llvm::dyn_cast<llvm::GEPOperator>(base);
          if (!SG)
            break;
          if (SG->getSourceElementType()->isStructTy()) {
            sty = llvm::cast<llvm::StructType>(SG->getSourceElementType());
            break;
          }
          base = SG->getPointerOperand()->stripPointerCasts();
        }
        if (sty)
          fsz = outerSz;
      }
      if (fieldKnown && llvm::isa<llvm::CallBase>(cur)) {
        // A field of a returned object is the value stored at that offset.
        // The rest of the object is not this value. The struct GEP is the
        // access path of this field.
        s = fieldBytes(llvm::cast<llvm::CallBase>(cur), fieldOff, sty, fsz);
      } else if (fieldKnown && llvm::isa<llvm::Argument>(cur) &&
                 (fieldOff != 0 ||
                  [&]() {
                    const auto *SG = llvm::dyn_cast<llvm::GEPOperator>(G);
                    llvm::Type *ety = SG ? SG->getResultElementType() : nullptr;
                    return ety && (ety->isFloatingPointTy() || ety->isIntegerTy());
                  }())) {
        // A field of an argument is the value stored at that offset. The
        // argument pointer is a different root. Inside a call whose return
        // is being summarized, this is that call's actual, not every caller.
        const auto *Arg = llvm::cast<llvm::Argument>(cur);
        fieldAsk.push_back(FieldAsk{sty, fsz});
        Status via = fieldOfCall(Arg, fieldOff);
        Status f = via.any ? via : readField(Arg, fieldOff);
        fieldAsk.pop_back();
        bool got = false;
        for (const auto &a : f.args)
          if (a.second >= 0)
            got = true;
        if (got && !f.local && !f.hasConst && !f.none)
          s = f;
        else if (f.hasConst && !f.open && !f.local && !f.none && f.args.empty())
          s = constant();
        else {
          // No store replaced this field. A scalar field of the object the
          // entry passed still holds that argument. The same offset of the
          // actual at this call is that field. A write of the field is not.
          auto resultIsScalar = [&]() {
            const auto *SG = llvm::dyn_cast<llvm::GEPOperator>(G);
            if (!SG)
              return false;
            llvm::Type *ety = SG->getResultElementType();
            return ety && (ety->isFloatingPointTy() || ety->isIntegerTy());
          };
          auto written = [&](const llvm::Argument *A, int64_t off) {
            const llvm::Function *Fn = A ? A->getParent() : nullptr;
            if (!Fn || Fn->isDeclaration())
              return true;
            auto offOf = [&](const llvm::Value *V) -> std::optional<std::pair<int64_t, bool>> {
              int64_t o = 0;
              bool known = true;
              bool field = false;
              std::unordered_set<const llvm::Value *> seenA;
              while (V && seenA.insert(V).second) {
                V = V->stripPointerCasts();
                if (V == A)
                  return known ? std::optional<std::pair<int64_t, bool>>({field ? o : 0, field})
                               : std::nullopt;
                if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                  field = true;
                  if (known) {
                    llvm::APInt ap(DL.getIndexSizeInBits(GG->getPointerAddressSpace()), 0);
                    if (!GG->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
                      known = false;
                    else
                      o += ap.getSExtValue();
                  }
                  V = GG->getPointerOperand();
                  continue;
                }
                if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(V)) {
                  if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
                    V = CI->getOperand(0);
                    continue;
                  }
                }
                break;
              }
              return std::nullopt;
            };
            struct CW {
              const llvm::Function *f = nullptr;
              unsigned ai = 0;
              int64_t off = 0;
              bool operator<(const CW &o) const {
                if (f != o.f)
                  return f < o.f;
                if (ai != o.ai)
                  return ai < o.ai;
                return off < o.off;
              }
            };
            std::set<CW> cwStack;
            std::map<CW, bool> cwMemo;
            std::function<bool(const llvm::Function *, unsigned, int64_t, int)> calleeWrites;
            calleeWrites = [&](const llvm::Function *D, unsigned ai, int64_t off, int) -> bool {
              if (!D || D->isDeclaration() || ai >= D->arg_size())
                return true;
              CW key{D, ai, off};
              auto known = cwMemo.find(key);
              if (known != cwMemo.end())
                return known->second;
              if (!cwStack.insert(key).second)
                return false;
              auto answer = [&](bool v) {
                cwStack.erase(key);
                cwMemo.emplace(key, v);
                return v;
              };
              const llvm::Argument *FA = D->getArg(ai);
              auto formalOff = [&](const llvm::Value *V) -> std::optional<std::pair<int64_t, bool>> {
                int64_t o = 0;
                bool known = true;
                bool field = false;
                std::unordered_set<const llvm::Value *> seenF;
                while (V && seenF.insert(V).second) {
                  V = V->stripPointerCasts();
                  if (V == FA)
                    return known ? std::optional<std::pair<int64_t, bool>>({field ? o : 0, field})
                                 : std::nullopt;
                  if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                    field = true;
                    if (known) {
                      llvm::APInt ap(DL.getIndexSizeInBits(GG->getPointerAddressSpace()), 0);
                      if (!GG->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
                        known = false;
                      else
                        o += ap.getSExtValue();
                    }
                    V = GG->getPointerOperand();
                    continue;
                  }
                  if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(V)) {
                    if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
                      V = CI->getOperand(0);
                      continue;
                    }
                  }
                  break;
                }
                return std::nullopt;
              };
              for (const llvm::Instruction &DI : llvm::instructions(*D)) {
                if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&DI)) {
                  if (auto o = formalOff(SI->getPointerOperand()))
                    if ((!o->second && o->first == 0) || (o->second && o->first == off))
                      return answer(true);
                } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(&DI)) {
                  const llvm::Value *dst = nullptr;
                  const llvm::Value *src = nullptr;
                  if (byteCopy(CB, dst, src)) {
                    if (auto o = formalOff(dst))
                      if ((!o->second && o->first == 0) || (o->second && o->first == off))
                        return answer(true);
                  }
                  if (CB->onlyReadsMemory() || CB->doesNotAccessMemory())
                    continue;
                  for (unsigned fj = 0; fj < CB->arg_size(); ++fj) {
                    if (CB->paramHasAttr(fj, llvm::Attribute::ReadOnly) ||
                        CB->paramHasAttr(fj, llvm::Attribute::ReadNone))
                      continue;
                    if (auto o = formalOff(CB->getArgOperand(fj))) {
                      if (o->second && o->first != off)
                        continue;
                      const llvm::Function *Cal = CB->getCalledFunction();
                      if (calleeWrites(Cal, fj, o->second ? off - o->first : off, 0))
                        return answer(true);
                    }
                  }
                }
              }
              return answer(false);
            };
            for (const llvm::Instruction &BI : llvm::instructions(*Fn)) {
              const llvm::Value *ptr = nullptr;
              bool copy = false;
              if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&BI))
                ptr = SI->getPointerOperand();
              else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(&BI)) {
                const llvm::Value *dst = nullptr;
                const llvm::Value *src = nullptr;
                if (byteCopy(CB, dst, src)) {
                  ptr = dst;
                  copy = true;
                } else if (!CB->onlyReadsMemory() && !CB->doesNotAccessMemory()) {
                  for (unsigned ai = 0; ai < CB->arg_size(); ++ai) {
                    if (CB->paramHasAttr(ai, llvm::Attribute::ReadOnly) ||
                        CB->paramHasAttr(ai, llvm::Attribute::ReadNone))
                      continue;
                    if (auto o = offOf(CB->getArgOperand(ai))) {
                      if (o->second && o->first != off)
                        continue;
                      if (calleeWrites(CB->getCalledFunction(), ai, o->second ? off - o->first : off, 0))
                        return true;
                    }
                  }
                }
              }
              if (!ptr)
                continue;
              if (auto o = offOf(ptr)) {
                if (!o->second && (copy || o->first == 0))
                  return true;
                if (o->second && o->first == off)
                  return true;
              }
            }
            return false;
          };
          std::set<std::pair<const llvm::Argument *, int64_t>> goStack;
          std::function<Status(const llvm::Argument *, int64_t, int)> go;
          go = [&](const llvm::Argument *A, int64_t off, int) -> Status {
            if (!A)
              return opened();
            auto gk = std::make_pair(A, off);
            if (!goStack.insert(gk).second)
              return bare();
            struct GoPop {
              std::set<std::pair<const llvm::Argument *, int64_t>> &s;
              std::pair<const llvm::Argument *, int64_t> k;
              ~GoPop() { s.erase(k); }
            } goPop{goStack, gk};
            if (A->getParent() == entryFn) {
              if (written(A, off))
                return opened();
              Status r = bare();
              r.any = true;
              r.args.insert({entryName, static_cast<int>(A->getArgNo())});
              return r;
            }
            auto oneActual = [&](const llvm::CallBase *C) -> Status {
              if (!C || A->getArgNo() >= C->arg_size())
                return opened();
              const llvm::Value *V = C->getArgOperand(A->getArgNo());
              int64_t extra = off;
              std::unordered_set<const llvm::Value *> seenV;
              while (V && seenV.insert(V).second) {
                V = V->stripPointerCasts();
                if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                  llvm::APInt ap(DL.getIndexSizeInBits(GG->getPointerAddressSpace()), 0);
                  if (!GG->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
                    return opened();
                  extra += ap.getSExtValue();
                  V = GG->getPointerOperand();
                  continue;
                }
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
                  const llvm::Value *st = AI ? spillValue(AI) : nullptr;
                  if (!st)
                    return opened();
                  V = st;
                  continue;
                }
                if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(V)) {
                  if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
                    V = CI->getOperand(0);
                    continue;
                  }
                }
                break;
              }
              if (const auto *B = llvm::dyn_cast_or_null<llvm::Argument>(V))
                return go(B, extra, 0);
              if (const auto *AI = llvm::dyn_cast_or_null<llvm::AllocaInst>(V)) {
                int64_t o = extra;
                Status m = memRoots(C, AI, true, &o);
                return m;
              }
              return opened();
            };
            if (const llvm::CallBase *via = boundCall(A->getParent()))
              return oneActual(via);
            auto sit = sites.find(A->getParent());
            if (sit == sites.end())
              return opened();
            Status acc;
            bool saw = false;
            bool bad = false;
            for (const llvm::CallBase *C : sit->second) {
              if (!C || !cone(C->getFunction()) || !entryCall(C->getFunction(), A->getParent()))
                continue;
              if (activation && activates(activation, A->getParent()) && C != activation)
                continue;
              Status one = oneActual(C);
              if (!one.any)
                continue;
              if (one.hasConst && !one.open && !one.local && !one.none && one.args.empty())
                continue;
              if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
                continue;
              bool clean = !one.open && !one.local && !one.hasConst && !one.none && !one.args.empty();
              // Another invocation that does not reduce stays open. It does
              // not erase an invocation that is this entry argument: the
              // activation walk separates them.
              if (!clean) {
                bad = true;
                continue;
              }
              if (saw && acc.args != one.args)
                bad = true;
              if (!saw)
                acc = one;
              saw = true;
            }
            if (!saw)
              return opened();
            if (bad)
              acc.open = true;
            return acc;
          };
          Status g = resultIsScalar() ? go(Arg, fieldOff, 0) : opened();
          bool gpure = g.any && !g.open && !g.local && !g.hasConst && !g.none && !g.args.empty();
          if (gpure)
            s = g;
          else if (fieldOff == 0)
            s = walk(G->getPointerOperand());
          else
            s = opened();
        }
      } else
      s = walk(G->getPointerOperand());
      if (s.slot && s.offKnown) {
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63)) {
          s.offKnown = false;
          s.slot = nullptr;
        } else {
          s.off += ap.getSExtValue();
        }
      }
    } else if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(V)) {
      s = bare();
      s.any = true;
      if (nameable(GV)) {
        s.args.insert({pretty(GV->getName()), -1});
      } else if (!GV->isConstant()) {
        s.local = true;
        s.slot = GV;
        s.off = 0;
        s.offKnown = true;
      } else {
        s.hasConst = true;
      }
    } else if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (A->getParent() == entryFn) {
        s = bare();
        s.any = true;
        s.args.insert({entryName, static_cast<int>(A->getArgNo())});
      } else if (!cone(A->getParent())) {
        Status fwd = forwardPure(A);
        s = fwd.any ? fwd : opened();
      } else if (const llvm::CallBase *via = boundCall(A->getParent())) {
        // This formal is the actual at the call on the trace. Another
        // caller of the same function passes a different object.
        size_t keep = summarizing.size();
        for (size_t i = summarizing.size(); i > 0; --i) {
          if (summarizing[i - 1].first == via) {
            keep = i - 1;
            break;
          }
        }
        auto saved = summarizing;
        summarizing.resize(keep);
        const llvm::CallBase *savedAct = activation;
        if (via == activation)
          activation = nullptr;
        Status one = A->getArgNo() < via->arg_size() ? walk(via->getArgOperand(A->getArgNo())) : opened();
        activation = savedAct;
        summarizing = std::move(saved);
        s = one.any ? one : opened();
        noMemo = true;
      } else {
        // Each caller is a separate actual. A caller that passes this
        // export's parameter stays. A caller that passes a local or does
        // not reduce stays open and does not erase that parameter.
        Status acc;
        bool bad = false;
        bool site = false;
        auto sit = sites.find(A->getParent());
        auto take = [&](Status one) {
          if (!one.any)
            return;
          if (one.hasConst && !one.open && !one.local && !one.none && one.args.empty())
            return;
          if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
            return;
          if (one.local && !one.open && one.args.empty() && !one.hasConst && !one.none) {
            bad = true;
            return;
          }
          bool ent = false;
          bool glob = false;
          for (const auto &a : one.args) {
            if (a.second >= 0)
              ent = true;
            else
              glob = true;
          }
          if (ent && !glob && !one.local && !one.hasConst && !one.none) {
            Status keep;
            keep.any = true;
            for (const auto &a : one.args)
              if (a.second >= 0)
                keep.args.insert(a);
            acc = meet(acc, keep);
            if (one.open)
              bad = true;
            return;
          }
          if (glob && !ent && !one.open && !one.local && !one.hasConst && !one.none && acc.args.empty()) {
            acc = meet(acc, one);
            return;
          }
          bad = true;
        };
        if (sit != sites.end()) {
          for (const llvm::CallBase *C : sit->second) {
            if (!cone(C->getFunction()) || A->getArgNo() >= C->arg_size())
              continue;
            if (const llvm::CallBase *via = boundCall(A->getParent())) {
              if (C != via)
                continue;
            } else if (!entryCall(C->getFunction(), A->getParent())) {
              continue;
            }
            if (activation && activates(activation, A->getParent()) && C != activation)
              continue;
            site = true;
            const llvm::Value *actual = C->getArgOperand(A->getArgNo());
            Status one = walk(actual);
            if (one.local && !one.open && one.args.empty() && !one.hasConst && !one.none && one.slot) {
              if (slotFn(one.slot) == C->getFunction())
                one.at = C;
              one = ground(one, C, actual);
            }
            take(one);
          }
        }
        if (!site || acc.args.empty()) {
          Status fwd = forwardPure(A);
          s = fwd.any ? fwd : opened();
        } else {
          bool ent = false;
          for (const auto &a : acc.args)
            if (a.second >= 0)
              ent = true;
          if (ent) {
            s = bare();
            s.any = true;
            s.open = bad;
            for (const auto &a : acc.args)
              if (a.second >= 0)
                s.args.insert(a);
          } else if (bad) {
            s = opened();
          } else {
            s = acc;
          }
        }
      }
    } else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      s = CE->isCast() ? walk(CE->getOperand(0)) : constant();
    } else if (llvm::isa<llvm::Constant>(V)) {
      s = constant();
    } else if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
      s = bare();
      s.any = true;
      s.local = true;
      s.slot = AI;
      s.off = 0;
      s.offKnown = true;
    } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
      if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
        s = walk(I->getOperand(0));
      } else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(I)) {
        // Equal alternatives are that value whatever selects them. Different
        // alternatives are a function of the entry bytes when every branch
        // that selects them is itself those bytes. A constant arm is then
        // one value of that function, not a second definition.
        auto clean = [](const Status &x) {
          if (!x.any || x.open || x.local || x.none)
            return false;
          if (x.hasConst && !x.args.empty())
            return false;
          return x.hasConst || !x.args.empty();
        };
        auto sameClean = [&](const Status &a, const Status &b) {
          if (!clean(a) || !clean(b) || a.hasConst != b.hasConst)
            return false;
          return a.hasConst || a.args == b.args;
        };
        std::vector<Status> incoming;
        bool identical = true;
        for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
          Status one = walk(P->getIncomingValue(i));
          if (!incoming.empty() && !sameClean(incoming.front(), one))
            identical = false;
          incoming.push_back(one);
        }
        if (incoming.empty()) {
          s = opened();
        } else if (identical && clean(incoming.front())) {
          s = incoming.front();
        } else {
          Status choice;
          bool haveChoice = false;
          bool known = true;
          Status acc;
          for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
            const llvm::Instruction *term = P->getIncomingBlock(i)->getTerminator();
            const llvm::Value *cond = nullptr;
            if (const auto *Br = llvm::dyn_cast<llvm::BranchInst>(term)) {
              if (Br->isConditional())
                cond = Br->getCondition();
            } else if (const auto *Sw = llvm::dyn_cast<llvm::SwitchInst>(term)) {
              cond = Sw->getCondition();
            }
            if (!cond) {
              known = false;
              break;
            }
            Status c = llvm::isa<llvm::Constant>(cond) ? constant() : walk(cond);
            if (!clean(c) || !clean(incoming[i])) {
              known = false;
              break;
            }
            if (!haveChoice) {
              choice = c;
              haveChoice = true;
            } else if (!sameClean(choice, c)) {
              if (choice.hasConst)
                choice = c;
              else if (!c.hasConst) {
                choice.args.insert(c.args.begin(), c.args.end());
              }
            }
            if (acc.any && !sameClean(acc, incoming[i]) && !incoming[i].hasConst && !acc.hasConst)
              acc.args.insert(incoming[i].args.begin(), incoming[i].args.end());
            else if (!incoming[i].hasConst)
              acc = incoming[i];
            else if (!acc.any)
              acc = incoming[i];
          }
          if (!known) {
            s = opened();
          } else if (!choice.hasConst) {
            s = bare();
            s.any = true;
            s.args = choice.args;
            if (!acc.hasConst)
              s.args.insert(acc.args.begin(), acc.args.end());
            if (s.args.empty())
              s = opened();
          } else if (!acc.hasConst && acc.any) {
            s = acc;
          } else {
            s = constant();
          }
        }
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(I)) {
        auto clean = [](const Status &x) {
          if (!x.any || x.open || x.local || x.none)
            return false;
          if (x.hasConst && !x.args.empty())
            return false;
          return x.hasConst || !x.args.empty();
        };
        if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(Sel->getCondition())) {
          s = walk(CI->isZero() ? Sel->getFalseValue() : Sel->getTrueValue());
        } else {
          Status tv = walk(Sel->getTrueValue());
          Status fv = walk(Sel->getFalseValue());
          Status c = walk(Sel->getCondition());
          bool same = clean(tv) && clean(fv) && tv.hasConst == fv.hasConst &&
                      (tv.hasConst || tv.args == fv.args);
          if (same)
            s = tv;
          else if (clean(c) && clean(tv) && clean(fv)) {
            s = bare();
            s.any = true;
            if (!c.hasConst)
              s.args = c.args;
            if (!tv.hasConst)
              s.args.insert(tv.args.begin(), tv.args.end());
            if (!fv.hasConst)
              s.args.insert(fv.args.begin(), fv.args.end());
            if (s.args.empty())
              s = constant();
          } else {
            s = opened();
          }
        }
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(I)) {
        s = memRoots(L, L->getPointerOperand(), false, nullptr);
      } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(I)) {
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (byteCopy(C, dst, src) && !C->getType()->isVoidTy()) {
          s = walk(dst);
        } else if (C->getType()->isVoidTy()) {
          s = opened();
        } else {
          auto it = resolved.find(C);
          // A call inside an upstream body was not in the downstream cone
          // map. Its direct callee is still that function.
          std::vector<const llvm::Function *> targets;
          if (it != resolved.end())
            targets = it->second;
          else if (const llvm::Function *Direct = C->getCalledFunction())
            targets.push_back(Direct);
          s = bare();
          bool saw = false;
          if (!targets.empty()) {
            for (const llvm::Function *D : targets) {
              saw = true;
              if (!D) {
                s = meet(s, opened());
                continue;
              }
              if (D->isDeclaration()) {
                const llvm::Function *B = definedBody(D);
                if (!B || B->isDeclaration()) {
                  s = meet(s, fromArgs(C));
                  continue;
                }
                D = B;
              }
              // A body in this module counts only inside the entry's cone.
              // The upstream body of a declaration is that function.
              if (D->getParent() == &M && !cone(D)) {
                s = meet(s, opened());
                continue;
              }
              struct SumGuard {
                std::vector<std::pair<const llvm::CallBase *, const llvm::Function *>> &st;
                SumGuard(std::vector<std::pair<const llvm::CallBase *, const llvm::Function *>> &st,
                         const llvm::CallBase *C, const llvm::Function *D)
                    : st(st) {
                  st.emplace_back(C, D);
                }
                ~SumGuard() { st.pop_back(); }
              } sum(summarizing, C, D);
              // A byte copy of an argument into the returned object is a root
              // of that object. The source is this call's actual. A constant
              // written beside it is not a root.
              auto copiedArgs = [&]() -> Status {
                Status none;
                std::unordered_set<const llvm::Value *> owned;
                std::unordered_set<const llvm::Value *> seenR;
                std::function<void(const llvm::Value *)> takeRet;
                takeRet = [&](const llvm::Value *U) {
                  if (!U || !seenR.insert(U).second)
                    return;
                  U = U->stripPointerCasts();
                  if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
                    if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(
                            L->getPointerOperand()->stripPointerCasts())) {
                      for (const llvm::User *Usr : AI->users()) {
                        const auto *SI = llvm::dyn_cast<llvm::StoreInst>(Usr);
                        if (SI && SI->getPointerOperand()->stripPointerCasts() == AI)
                          takeRet(SI->getValueOperand());
                      }
                    }
                    return;
                  }
                  if (const auto *P = llvm::dyn_cast<llvm::PHINode>(U)) {
                    for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
                      takeRet(P->getIncomingValue(i));
                    return;
                  }
                  if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U)) {
                    if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
                      takeRet(I->getOperand(0));
                      return;
                    }
                  }
                  if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
                    if (CB->getFunction() == D)
                      owned.insert(CB);
                };
                for (const llvm::BasicBlock &RBB : *D) {
                  const auto *RI = llvm::dyn_cast<llvm::ReturnInst>(RBB.getTerminator());
                  if (RI && RI->getReturnValue())
                    takeRet(RI->getReturnValue());
                }
                if (owned.empty())
                  return none;
                auto inside = [&](const llvm::Value *V) {
                  std::unordered_set<const llvm::Value *> seenI;
                  std::function<bool(const llvm::Value *, int)> go;
                  go = [&](const llvm::Value *U, int loads) -> bool {
                    if (!U || loads > 3 || !seenI.insert(U).second)
                      return false;
                    U = U->stripPointerCasts();
                    if (owned.count(U))
                      return true;
                    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U))
                      return go(G->getPointerOperand(), loads);
                    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
                      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(
                              L->getPointerOperand()->stripPointerCasts())) {
                        for (const llvm::User *Usr : AI->users()) {
                          const auto *SI = llvm::dyn_cast<llvm::StoreInst>(Usr);
                          if (SI && SI->getPointerOperand()->stripPointerCasts() == AI &&
                              go(SI->getValueOperand(), loads))
                            return true;
                        }
                        return false;
                      }
                      return go(L->getPointerOperand(), loads + 1);
                    }
                    if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U)) {
                      if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I))
                        return go(I->getOperand(0), loads);
                    }
                    return false;
                  };
                  return go(V, 0);
                };
                auto sourceArg = [&](const llvm::Value *V) -> const llvm::Argument * {
                  std::unordered_set<const llvm::Value *> seenS;
                  std::function<const llvm::Argument *(const llvm::Value *)> go;
                  go = [&](const llvm::Value *U) -> const llvm::Argument * {
                    if (!U || !seenS.insert(U).second)
                      return nullptr;
                    U = U->stripPointerCasts();
                    if (const auto *A = llvm::dyn_cast<llvm::Argument>(U))
                      return A->getParent() == D ? A : nullptr;
                    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
                      const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(
                          L->getPointerOperand()->stripPointerCasts());
                      if (!AI)
                        return nullptr;
                      const llvm::Argument *found = nullptr;
                      for (const llvm::User *Usr : AI->users()) {
                        const auto *SI = llvm::dyn_cast<llvm::StoreInst>(Usr);
                        if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
                          continue;
                        const llvm::Value *st = SI->getValueOperand();
                        if (llvm::isa<llvm::ConstantPointerNull>(st))
                          continue;
                        const llvm::Argument *a = go(st);
                        if (!a || (found && found != a))
                          return nullptr;
                        found = a;
                      }
                      return found;
                    }
                    if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U)) {
                      if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I))
                        return go(I->getOperand(0));
                    }
                    return nullptr;
                  };
                  return go(V);
                };
                Status acc;
                bool sawC = false;
                bool bad = false;
                for (const llvm::Instruction &I : llvm::instructions(*D)) {
                  const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
                  if (!CB)
                    continue;
                  const llvm::Value *dst = nullptr;
                  const llvm::Value *src = nullptr;
                  if (!byteCopy(CB, dst, src) || !dst || !src || !inside(dst))
                    continue;
                  sawC = true;
                  const llvm::Argument *A = sourceArg(src);
                  if (!A || A->getArgNo() >= C->arg_size()) {
                    if (!llvm::isa<llvm::Constant>(src->stripPointerCasts()))
                      bad = true;
                    continue;
                  }
                  const llvm::Value *op = C->getArgOperand(A->getArgNo());
                  Status w;
                  if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(op)) {
                    const llvm::CallBase *via = nullptr;
                    for (size_t i = summarizing.size(); i > 0; --i) {
                      if (summarizing[i - 1].second == Arg->getParent() &&
                          Arg->getArgNo() < summarizing[i - 1].first->arg_size()) {
                        via = summarizing[i - 1].first;
                        break;
                      }
                    }
                    if (via)
                      w = walk(via->getArgOperand(Arg->getArgNo()));
                    else
                      w = walk(op);
                  } else {
                    w = walk(op);
                  }
                  bool ent = false;
                  for (const auto &a : w.args)
                    if (a.second >= 0)
                      ent = true;
                  if (!ent || w.local || w.hasConst || w.none || w.open)
                    bad = true;
                  if (ent) {
                    Status keep;
                    keep.any = true;
                    for (const auto &a : w.args)
                      if (a.second >= 0)
                        keep.args.insert(a);
                    acc = meet(acc, keep);
                  }
                }
                if (!sawC || acc.args.empty())
                  return none;
                acc.any = true;
                acc.open = bad;
                return acc;
              };
              Status copied = copiedArgs();
              bool cent0 = false;
              for (const auto &a : copied.args)
                if (a.second >= 0)
                  cent0 = true;
              // A byte copy of an entry argument into the returned object is
              // that argument. Another return value does not open those bytes.
              if (cent0 && !copied.open && !copied.local && !copied.hasConst && !copied.none) {
                s = bare();
                s.any = true;
                for (const auto &a : copied.args)
                  if (a.second >= 0)
                    s.args.insert(a);
              } else {
              bool got = false;
              for (const llvm::BasicBlock &BB : *D) {
                const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                if (!R || !R->getReturnValue())
                  continue;
                got = true;
                const llvm::Value *rv = R->getReturnValue();
                Status one = walk(rv);
                // A function that returns a pointer it just obtained has
                // written that object in this body. The roots of those
                // bytes are the arguments of the calls that were handed
                // the object. The pointer itself is not those arguments.
                const llvm::Value *base = rv->stripPointerCasts();
                bool pointerHasEntry = false;
                for (const auto &a : one.args)
                  if (a.second >= 0)
                    pointerHasEntry = true;
                bool cent = false;
                for (const auto &a : copied.args)
                  if (a.second >= 0)
                    cent = true;
                if (!pointerHasEntry && cent) {
                  Status only;
                  only.any = true;
                  only.open = copied.open;
                  for (const auto &a : copied.args)
                    if (a.second >= 0)
                      only.args.insert(a);
                  one = only;
                } else if (!pointerHasEntry && rv->getType()->isPointerTy() &&
                    llvm::isa<llvm::CallBase>(base)) {
                  Status bytes = memRoots(R, base, true, nullptr);
                  bool ent = false;
                  for (const auto &a : bytes.args)
                    if (a.second >= 0)
                      ent = true;
                  // A constant written into another field is not a root and
                  // does not erase an argument that is.
                  if (ent) {
                    Status only;
                    only.any = true;
                    // A constant or a local in another field is not unknown and
                    // does not erase an entry argument stored in this object.
                    only.open = bytes.open;
                    for (const auto &a : bytes.args)
                      if (a.second >= 0)
                        only.args.insert(a);
                    one = only;
                  }
                }
                s = alt(s, one);
              }
              if (!got)
                s = alt(s, opened());
              }
            }
          }
          if (!saw)
            s = opened();
        }
      } else {
        s = bare();
        bool saw = false;
        for (const llvm::Use &U : I->operands()) {
          const llvm::Value *Op = U.get();
          if (!Op || llvm::isa<llvm::BasicBlock>(Op) || llvm::isa<llvm::MetadataAsValue>(Op))
            continue;
          if (llvm::isa<llvm::Constant>(Op) && !llvm::isa<llvm::GlobalVariable>(Op) &&
              !llvm::isa<llvm::ConstantExpr>(Op))
            continue;
          saw = true;
          s = meet(s, walk(Op));
        }
        if (!saw)
          s = constant();
        else if (!s.any)
          s = opened();
      }
    }
    active.erase(key);
    if (frameArg)
      noMemo = true;
    if (!noMemo) {
      if (activation)
        actMemo.emplace(V, s);
      else
        memo.emplace(key, s);
    }
    return s;
  };

  fromArgs = [&](const llvm::CallBase *C) -> Status {
    Status entries;
    bool unresolved = false;
    unsigned begin = C->hasStructRetAttr() ? 1u : 0u;
    for (unsigned i = begin; i < C->arg_size(); ++i) {
      if (C->paramHasAttr(i, llvm::Attribute::StructRet) ||
          C->paramHasAttr(i, llvm::Attribute::WriteOnly))
        continue;
      Status one = walk(C->getArgOperand(i));
      if (!one.any)
        continue;
      if (one.hasConst && !one.open && !one.local && !one.none && one.args.empty())
        continue;
      if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
        continue;
      if (one.local && !one.open && one.args.empty() && !one.hasConst && !one.none)
        continue;
      bool ent = false;
      bool glob = false;
      for (const auto &a : one.args) {
        if (a.second >= 0)
          ent = true;
        else
          glob = true;
      }
      if (ent && !glob && !one.local && !one.hasConst && !one.none) {
        Status keep;
        keep.any = true;
        for (const auto &a : one.args)
          if (a.second >= 0)
            keep.args.insert(a);
        entries = meet(entries, keep);
        if (one.open)
          unresolved = true;
        continue;
      }
      if (glob && !ent && !one.open && !one.local && !one.hasConst && !one.none) {
        if (entries.args.empty())
          entries = meet(entries, one);
        continue;
      }
      unresolved = true;
    }
    // No argument carried a root. A pointer argument that did not reduce is
    // unknown. Constants only mean this value is not an input.
    if (entries.args.empty())
      return unresolved ? opened() : nothing();
    bool ent = false;
    for (const auto &a : entries.args)
      if (a.second >= 0)
        ent = true;
    if (ent) {
      Status only;
      only.any = true;
      only.open = unresolved;
      for (const auto &a : entries.args)
        if (a.second >= 0)
          only.args.insert(a);
      return only;
    }
    if (unresolved)
      return opened();
    return entries;
  };

  // A load of a field of a formal is the value stored at that field by the
  // callers in this cone. A local slot stored there is read in the function
  // that owns the slot. One caller that does not reduce stays open and does
  // not erase a caller that passes this entry's parameter.
  struct RFKey {
    int entry = -1;
    const llvm::Argument *arg = nullptr;
    int64_t off = 0;
    bool carry = false;
    bool operator==(const RFKey &o) const {
      return entry == o.entry && arg == o.arg && off == o.off && carry == o.carry;
    }
  };
  struct RFHash {
    size_t operator()(const RFKey &k) const {
      return static_cast<size_t>(k.entry) * 1315423911u ^
             static_cast<size_t>(reinterpret_cast<uintptr_t>(k.arg)) ^
             static_cast<size_t>(k.off) * 2654435761u ^
             (k.carry ? 0x9e3779b97f4a7c15ull : 0u);
    }
  };
  std::unordered_map<RFKey, Status, RFHash> rfMemo;
  std::unordered_set<RFKey, RFHash> rfStack;
  // A field summary that is already on the stack still has the callsites
  // that pass an argument. Those do not need the object this summary is
  // computing. A second arrival of the same field is empty, not a disproof.
  int rfReentry = 0;
  int stDepth = 0;
  std::function<Status(const llvm::Argument *, int64_t)> argumentField;
  auto argField = [&](const llvm::Value *V) -> std::optional<std::pair<const llvm::Argument *, int64_t>> {
    int64_t off = 0;
    std::unordered_set<const llvm::Value *> seen;
    while (V && seen.insert(V).second) {
      V = V->stripPointerCasts();
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
          return std::nullopt;
        off += ap.getSExtValue();
        V = G->getPointerOperand();
        continue;
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (!AI)
          return std::nullopt;
        const llvm::Value *st = spillValue(AI);
        if (!st)
          return std::nullopt;
        V = st;
        continue;
      }
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
          V = I->getOperand(0);
          continue;
        }
        return std::nullopt;
      }
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (!cone(A->getParent()))
          return std::nullopt;
        return std::make_pair(A, off);
      }
      return std::nullopt;
    }
    return std::nullopt;
  };

  // Which formals of D are stored through argument argNo. A constant is
  // not a root. A phi is those formals only when every incoming value has
  // the same ones. The result is this call's actuals, not every caller.
  struct FSet {
    bool any = false;
    bool open = false;
    bool con = false;
    // args: the formal itself was stored. loaded: bytes were loaded through it.
    std::set<unsigned> args;
    std::set<unsigned> loaded;
  };
  std::unordered_map<CWKey, FSet, CWHash> touchMemo;
  // A callsite that passes a constant selects the feasible blocks of the
  // callee. The cache key is that constant vector.
  struct SpecKey {
    const llvm::Function *fn = nullptr;
    unsigned arg = 0;
    bool hasOff = false;
    int64_t off = 0;
    std::vector<std::pair<unsigned, uint64_t>> cs;
    bool operator<(const SpecKey &o) const {
      if (fn != o.fn)
        return fn < o.fn;
      if (arg != o.arg)
        return arg < o.arg;
      if (hasOff != o.hasOff)
        return hasOff < o.hasOff;
      if (off != o.off)
        return off < o.off;
      return cs < o.cs;
    }
  };
  std::map<SpecKey, FSet> specTouch;
  // Which formals a function's returned value depends on. A call result is
  // those formals, not an unknown and not every argument.
  std::unordered_map<const llvm::Function *, FSet> retDepMemo;
  std::unordered_set<const llvm::Function *> retDepStack;
  std::function<FSet(const llvm::Function *)> returnDeps;
  returnDeps = [&](const llvm::Function *F) -> FSet {
    FSet unknown;
    unknown.any = true;
    unknown.open = true;
    if (!F)
      return unknown;
    const llvm::Function *B = definedBody(F);
    if (!B || B->isDeclaration())
      return unknown;
    auto memo = retDepMemo.find(B);
    if (memo != retDepMemo.end())
      return memo->second;
    if (!retDepStack.insert(B).second)
      return unknown;
    auto unite = [](FSet a, FSet b) {
      if (!a.any)
        return b;
      if (!b.any)
        return a;
      FSet s;
      s.any = true;
      s.open = a.open || b.open;
      s.con = a.con || b.con;
      s.args = a.args;
      s.args.insert(b.args.begin(), b.args.end());
      s.loaded = a.loaded;
      s.loaded.insert(b.loaded.begin(), b.loaded.end());
      return s;
    };
    auto pureCon = [](const FSet &s) {
      return s.any && s.con && !s.open && s.args.empty() && s.loaded.empty();
    };
    // A constant, including null, has no formal. It does not erase a formal
    // and it is not an unknown. Two different formals stay open, and the
    // formals remain: an unknown does not erase a proved one.
    auto agree = [&](FSet a, FSet b) {
      if (!a.any || pureCon(a))
        return b;
      if (!b.any || pureCon(b))
        return a;
      FSet s;
      s.any = true;
      s.open = a.open || b.open;
      s.args = a.args;
      s.args.insert(b.args.begin(), b.args.end());
      s.loaded = a.loaded;
      s.loaded.insert(b.loaded.begin(), b.loaded.end());
      if (a.args != b.args || a.loaded != b.loaded)
        s.open = true;
      return s;
    };
    std::unordered_map<const llvm::Value *, FSet> memoV;
    std::unordered_set<const llvm::Value *> stackV;
    std::function<FSet(const llvm::Value *)> ofv;
    ofv = [&](const llvm::Value *V) -> FSet {
      FSet none;
      if (!V)
        return none;
      auto it = memoV.find(V);
      if (it != memoV.end())
        return it->second;
      if (!stackV.insert(V).second)
        return none;
      FSet s;
      s.any = true;
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == B)
          s.args.insert(A->getArgNo());
        else
          s.open = true;
      } else if (llvm::isa<llvm::Constant>(V) && !llvm::isa<llvm::GlobalVariable>(V) &&
                 !llvm::isa<llvm::ConstantExpr>(V)) {
        s.con = true;
      } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
          s = ofv(I->getOperand(0));
        } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(I)) {
          s = ofv(G->getPointerOperand());
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(I)) {
          FSet a = ofv(L->getPointerOperand());
          s.open = a.open;
          s.loaded = a.loaded;
          s.loaded.insert(a.args.begin(), a.args.end());
        } else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(I)) {
          s = none;
          for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
            s = agree(s, ofv(P->getIncomingValue(i)));
          if (!s.any) {
            s.any = true;
            s.open = true;
          }
        } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(I)) {
          s = agree(ofv(Sel->getTrueValue()), ofv(Sel->getFalseValue()));
        } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(I)) {
          const llvm::Function *Cal = CB->getCalledFunction();
          FSet d = Cal ? returnDeps(Cal) : unknown;
          if (!d.any || (d.args.empty() && d.loaded.empty())) {
            s = d.open ? unknown : d;
          } else {
            s = none;
            auto take = [&](unsigned fj, bool loaded) {
              if (fj >= CB->arg_size()) {
                s = unite(s, unknown);
                return;
              }
              FSet a = ofv(CB->getArgOperand(fj));
              if (loaded) {
                FSet b;
                b.any = true;
                b.open = a.open;
                b.loaded = a.loaded;
                b.loaded.insert(a.args.begin(), a.args.end());
                s = unite(s, b);
              } else {
                s = unite(s, a);
              }
            };
            for (unsigned fj : d.args)
              take(fj, false);
            for (unsigned fj : d.loaded)
              take(fj, true);
            if (d.open)
              s = unite(s, unknown);
          }
        } else {
          s = none;
          bool sawOp = false;
          for (const llvm::Use &U : I->operands()) {
            const llvm::Value *Op = U.get();
            if (!Op || llvm::isa<llvm::BasicBlock>(Op) || llvm::isa<llvm::MetadataAsValue>(Op) ||
                (llvm::isa<llvm::Constant>(Op) && !llvm::isa<llvm::GlobalVariable>(Op) &&
                 !llvm::isa<llvm::ConstantExpr>(Op)))
              continue;
            sawOp = true;
            s = agree(s, ofv(Op));
          }
          if (!sawOp) {
            s.any = true;
            s.con = true;
          }
        }
      } else {
        s.open = true;
      }
      stackV.erase(V);
      memoV.emplace(V, s);
      return s;
    };
    FSet acc;
    bool saw = false;
    for (const llvm::BasicBlock &BB : *B) {
      const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      saw = true;
      acc = unite(acc, ofv(R->getReturnValue()));
    }
    if (!saw)
      acc = unknown;
    retDepStack.erase(B);
    retDepMemo.emplace(B, acc);
    return acc;
  };
  auto formalsTouching = [&](const llvm::Function *D, unsigned argNo,
                             const llvm::CallBase *At, const int64_t *fieldOff) -> FSet {
    std::vector<std::pair<unsigned, uint64_t>> consts;
    if (At && D) {
      unsigned n = At->arg_size();
      if (D->arg_size() < n)
        n = static_cast<unsigned>(D->arg_size());
      for (unsigned i = 0; i < n; ++i) {
        const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(At->getArgOperand(i));
        if (CI && CI->getBitWidth() <= 64)
          consts.push_back({i, CI->getZExtValue()});
      }
    }
    bool speced = !consts.empty() || fieldOff;
    SpecKey spec{D, argNo, fieldOff != nullptr, fieldOff ? *fieldOff : 0, consts};
    if (speced) {
      auto found = specTouch.find(spec);
      if (found != specTouch.end())
        return found->second;
    } else {
      CWKey key{-1, D, argNo};
      auto found = touchMemo.find(key);
      if (found != touchMemo.end())
        return found->second;
    }
    auto remember = [&](const FSet &acc) {
      if (speced)
        specTouch.emplace(spec, acc);
      else
        touchMemo.emplace(CWKey{-1, D, argNo}, acc);
    };
    FSet acc;
    acc.any = true;
    acc.open = true;
    if (!D || D->isDeclaration() || argNo >= D->arg_size()) {
      remember(acc);
      return acc;
    }
    const llvm::Argument *FA = D->getArg(argNo);
    // A constant actual selects one successor of a compare or a switch on
    // that formal. Stores in the other successor are not this callsite.
    std::unordered_set<const llvm::BasicBlock *> live;
    bool restrictLive = !consts.empty();
    if (restrictLive) {
      std::unordered_map<unsigned, std::pair<uint64_t, unsigned>> foldArg;
      for (unsigned i = 0; i < At->arg_size() && i < D->arg_size(); ++i) {
        const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(At->getArgOperand(i));
        if (CI && CI->getBitWidth() <= 64)
          foldArg.emplace(i, std::make_pair(CI->getZExtValue(), CI->getBitWidth()));
      }
      auto fold = [&](const llvm::Value *V) -> std::optional<std::pair<uint64_t, unsigned>> {
        std::unordered_set<const llvm::Value *> seenF;
        while (V && seenF.insert(V).second) {
          if (const auto *FI = llvm::dyn_cast<llvm::FreezeInst>(V)) {
            V = FI->getOperand(0);
            continue;
          }
          if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
            if (CI->getBitWidth() > 64)
              return std::nullopt;
            return std::make_pair(CI->getZExtValue(), CI->getBitWidth());
          }
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
            if (A->getParent() != D)
              return std::nullopt;
            auto it = foldArg.find(A->getArgNo());
            if (it == foldArg.end())
              return std::nullopt;
            return it->second;
          }
          break;
        }
        return std::nullopt;
      };
      std::vector<const llvm::BasicBlock *> work;
      work.push_back(&D->getEntryBlock());
      live.insert(&D->getEntryBlock());
      for (size_t qi = 0; qi < work.size(); ++qi) {
        const llvm::BasicBlock *BB = work[qi];
        const llvm::Instruction *T = BB->getTerminator();
        std::vector<const llvm::BasicBlock *> next;
        if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(T)) {
          if (!BI->isConditional()) {
            next.push_back(BI->getSuccessor(0));
          } else {
            bool folded = false;
            if (const auto *Cmp = llvm::dyn_cast<llvm::ICmpInst>(BI->getCondition())) {
              auto a = fold(Cmp->getOperand(0));
              auto b = fold(Cmp->getOperand(1));
              if (a && b && a->second == b->second &&
                  (Cmp->getPredicate() == llvm::CmpInst::ICMP_EQ ||
                   Cmp->getPredicate() == llvm::CmpInst::ICMP_NE)) {
                bool eq = a->first == b->first;
                bool takeTrue = Cmp->getPredicate() == llvm::CmpInst::ICMP_EQ ? eq : !eq;
                next.push_back(BI->getSuccessor(takeTrue ? 0 : 1));
                folded = true;
              }
            }
            if (!folded) {
              next.push_back(BI->getSuccessor(0));
              next.push_back(BI->getSuccessor(1));
            }
          }
        } else if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(T)) {
          auto c = fold(SW->getCondition());
          bool folded = false;
          if (c && SW->getCondition()->getType()->getIntegerBitWidth() == c->second) {
            for (const auto &cas : SW->cases()) {
              const llvm::ConstantInt *CV = cas.getCaseValue();
              if (CV->getBitWidth() == c->second && CV->getZExtValue() == c->first) {
                next.push_back(cas.getCaseSuccessor());
                folded = true;
                break;
              }
            }
            if (!folded)
              next.push_back(SW->getDefaultDest());
            folded = true;
          }
          if (!folded)
            for (unsigned si = 0; si < SW->getNumSuccessors(); ++si)
              next.push_back(SW->getSuccessor(si));
        } else if (T) {
          for (unsigned si = 0; si < T->getNumSuccessors(); ++si)
            next.push_back(T->getSuccessor(si));
        }
        for (const llvm::BasicBlock *S : next)
          if (S && live.insert(S).second)
            work.push_back(S);
      }
    }
    // 1: this object. 0: not. 2: a cycle, proved only if another incoming is.
    // A phi is this object when no incoming is a different pointer and one
    // incoming is this object.
    std::function<int(const llvm::Value *, const llvm::Value *, std::unordered_set<const llvm::Value *> &)> sameObj;
    sameObj = [&](const llvm::Value *V, const llvm::Value *Root, std::unordered_set<const llvm::Value *> &seenV) -> int {
      if (!V || !Root)
        return 0;
      if (!seenV.insert(V).second)
        return 2;
      if (V == Root || V->stripPointerCasts() == Root->stripPointerCasts())
        return 1;
      V = V->stripPointerCasts();
      if (V == Root)
        return 1;
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V))
        return sameObj(G->getPointerOperand(), Root, seenV);
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        const llvm::Value *st = AI ? spillValue(AI) : nullptr;
        return st ? sameObj(st, Root, seenV) : 0;
      }
      auto join = [&](const llvm::Value *a, const llvm::Value *b) {
        int x = sameObj(a, Root, seenV);
        int y = sameObj(b, Root, seenV);
        if (x == 0 || y == 0)
          return 0;
        if (x == 1 || y == 1)
          return 1;
        return 2;
      };
      if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        if (P->getNumIncomingValues() == 0)
          return 0;
        int r = 2;
        for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
          int x = sameObj(P->getIncomingValue(i), Root, seenV);
          if (x == 0)
            return 0;
          if (x == 1)
            r = 1;
        }
        return r;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V))
        return join(Sel->getTrueValue(), Sel->getFalseValue());
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I))
          return sameObj(I->getOperand(0), Root, seenV);
      }
      return 0;
    };
    auto isObj = [&](const llvm::Value *V, const llvm::Value *Root) {
      std::unordered_set<const llvm::Value *> seenV;
      return sameObj(V, Root, seenV) == 1;
    };
    auto pureConF = [](const FSet &s) {
      return s.any && s.con && !s.open && s.args.empty() && s.loaded.empty();
    };
    auto meetF = [&](FSet a, FSet b) {
      if (!a.any || pureConF(a))
        return b;
      if (!b.any || pureConF(b))
        return a;
      FSet s;
      s.any = true;
      s.open = a.open || b.open;
      s.args = a.args;
      s.args.insert(b.args.begin(), b.args.end());
      s.loaded = a.loaded;
      s.loaded.insert(b.loaded.begin(), b.loaded.end());
      // A phi is those formals only when every incoming value has the same ones.
      // A different formal is unknown. It does not erase the ones that remain.
      if (a.args != b.args || a.loaded != b.loaded)
        s.open = true;
      return s;
    };
    std::unordered_map<const llvm::Value *, FSet> fmemo;
    std::unordered_set<const llvm::Value *> fstack;
    std::function<FSet(const llvm::Value *)> of;
    of = [&](const llvm::Value *V) -> FSet {
      FSet none;
      if (!V)
        return none;
      auto it = fmemo.find(V);
      if (it != fmemo.end())
        return it->second;
      if (!fstack.insert(V).second)
        return none;
      FSet s;
      s.any = true;
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == D)
          s.args.insert(A->getArgNo());
        else
          s.open = true;
      } else if (llvm::isa<llvm::Constant>(V) && !llvm::isa<llvm::GlobalVariable>(V) &&
                 !llvm::isa<llvm::ConstantExpr>(V)) {
        s.con = true;
      } else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        s = CE->isCast() ? of(CE->getOperand(0)) : [&]() {
          FSet c;
          c.any = true;
          c.con = true;
          return c;
        }();
      } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
          s = of(I->getOperand(0));
        } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(I)) {
          s = of(G->getPointerOperand());
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(I)) {
          // A load of the slot an argument was spilled into is that argument.
          // A load through a formal is the bytes at that formal, not the pointer.
          const llvm::Value *ptr = L->getPointerOperand()->stripPointerCasts();
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(ptr)) {
            if (const llvm::Value *st = spillValue(AI))
              s = of(st);
            else
              s.open = true;
          } else {
            FSet a = of(ptr);
            s.any = true;
            s.open = a.open;
            s.loaded = a.loaded;
            s.loaded.insert(a.args.begin(), a.args.end());
          }
        } else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(I)) {
          s = none;
          bool sawIn = false;
          for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
            if (restrictLive && !live.count(P->getIncomingBlock(i)))
              continue;
            sawIn = true;
            s = meetF(s, of(P->getIncomingValue(i)));
          }
          if (!sawIn || !s.any) {
            s.any = true;
            s.open = true;
          }
        } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(I)) {
          s = meetF(of(Sel->getTrueValue()), of(Sel->getFalseValue()));
        } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(I)) {
          // The result depends on the formals the callee's return reads.
          // It is not every argument, and a visible body is not unknown.
          const llvm::Function *Cal = CB->getCalledFunction();
          FSet d = Cal ? returnDeps(Cal) : [&]() {
            FSet u;
            u.any = true;
            u.open = true;
            return u;
          }();
          auto unite = [](FSet a, FSet b) {
            if (!a.any)
              return b;
            if (!b.any)
              return a;
            FSet r;
            r.any = true;
            r.open = a.open || b.open;
            r.con = a.con || b.con;
            r.args = a.args;
            r.args.insert(b.args.begin(), b.args.end());
            r.loaded = a.loaded;
            r.loaded.insert(b.loaded.begin(), b.loaded.end());
            return r;
          };
          if (!d.any || (d.args.empty() && d.loaded.empty())) {
            s = d;
          } else {
            s = none;
            auto take = [&](unsigned fj, bool loaded) {
              if (fj >= CB->arg_size()) {
                FSet u;
                u.any = true;
                u.open = true;
                s = unite(s, u);
                return;
              }
              FSet a = of(CB->getArgOperand(fj));
              if (loaded) {
                FSet b;
                b.any = true;
                b.open = a.open;
                b.loaded = a.loaded;
                b.loaded.insert(a.args.begin(), a.args.end());
                s = unite(s, b);
              } else {
                s = unite(s, a);
              }
            };
            for (unsigned fj : d.args)
              take(fj, false);
            for (unsigned fj : d.loaded)
              take(fj, true);
            if (d.open) {
              FSet u;
              u.any = true;
              u.open = true;
              s = unite(s, u);
            }
          }
        } else {
          s = none;
          bool sawOp = false;
          for (const llvm::Use &U : I->operands()) {
            const llvm::Value *Op = U.get();
            if (!Op || llvm::isa<llvm::BasicBlock>(Op) || llvm::isa<llvm::MetadataAsValue>(Op))
              continue;
            if (llvm::isa<llvm::Constant>(Op) && !llvm::isa<llvm::GlobalVariable>(Op) &&
                !llvm::isa<llvm::ConstantExpr>(Op))
              continue;
            sawOp = true;
            s = meetF(s, of(Op));
          }
          if (!sawOp) {
            s.any = true;
            s.con = true;
          }
        }
      } else {
        s.open = true;
      }
      fstack.erase(V);
      fmemo.emplace(V, s);
      return s;
    };
    auto meetStore = [](FSet a, FSet b) {
      if (!a.any)
        return b;
      if (!b.any)
        return a;
      FSet s;
      s.any = true;
      s.open = a.open || b.open;
      s.con = a.con || b.con;
      s.args = a.args;
      s.args.insert(b.args.begin(), b.args.end());
      s.loaded = a.loaded;
      s.loaded.insert(b.loaded.begin(), b.loaded.end());
      return s;
    };
    // Offset of a store through this formal. The formal itself is offset 0.
    // A variable index is unknown and may be the field being asked.
    auto addrOff = [&](const llvm::Value *addr) -> std::optional<int64_t> {
      int64_t o = 0;
      bool known = true;
      bool field = false;
      std::unordered_set<const llvm::Value *> seenA;
      while (addr && seenA.insert(addr).second) {
        addr = addr->stripPointerCasts();
        if (addr == FA)
          return known ? std::optional<int64_t>(field ? o : 0) : std::nullopt;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(addr)) {
          field = true;
          if (known) {
            llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
              known = false;
            else
              o += ap.getSExtValue();
          }
          addr = G->getPointerOperand();
          continue;
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(addr)) {
          // The formal was spilled to a slot and reloaded. The offset above
          // this reload is the offset from that formal. A load of any other
          // pointer is a different object.
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          const llvm::Value *st = AI ? spillValue(AI) : nullptr;
          if (!st || st->stripPointerCasts() != FA)
            break;
          addr = st;
          continue;
        }
        if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(addr)) {
          if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
            addr = CI->getOperand(0);
            continue;
          }
        }
        break;
      }
      return std::nullopt;
    };
    auto keepStore = [&](const llvm::Instruction &I, const llvm::Value *addr) {
      if (restrictLive && !live.count(I.getParent()))
        return false;
      if (!fieldOff)
        return true;
      auto o = addrOff(addr);
      if (!o)
        return true;
      return *o == *fieldOff;
    };
    FSet got;
    bool saw = false;
    for (const llvm::Instruction &I : llvm::instructions(*D)) {
      const llvm::Value *src = nullptr;
      const llvm::Value *addr = nullptr;
      if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (!isObj(SI->getPointerOperand(), FA) || isObj(SI->getValueOperand(), FA))
          continue;
        src = SI->getValueOperand();
        addr = SI->getPointerOperand();
      } else if (const auto *IC = llvm::dyn_cast<llvm::CallBase>(&I)) {
        const llvm::Value *dst = nullptr;
        if (!IC->isInlineAsm() && byteCopy(IC, dst, src) && isObj(dst, FA) && src && !isObj(src, FA)) {
          addr = dst;
        } else {
          continue;
        }
      } else {
        continue;
      }
      if (!keepStore(I, addr))
        continue;
      saw = true;
      got = meetStore(got, of(src));
    }
    // A pointer stored into this object may be a fresh allocation. The values
    // stored into that allocation are stored into this object. The allocation's
    // identity is not those values.
    auto barePtr = [](const llvm::Value *V) -> const llvm::Value * {
      std::unordered_set<const llvm::Value *> seenV;
      while (V && seenV.insert(V).second) {
        V = V->stripPointerCasts();
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
          V = G->getPointerOperand();
          continue;
        }
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
          if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            V = I->getOperand(0);
            continue;
          }
        }
        break;
      }
      return V;
    };
    std::unordered_set<const llvm::Value *> box;
    for (const llvm::Instruction &I : llvm::instructions(*D)) {
      const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI || !isObj(SI->getPointerOperand(), FA))
        continue;
      if (!keepStore(I, SI->getPointerOperand()))
        continue;
      const llvm::Value *r = barePtr(SI->getValueOperand());
      if (!r || r == FA)
        continue;
      if (llvm::isa<llvm::AllocaInst>(r) ||
          (llvm::isa<llvm::CallBase>(r) && llvm::cast<llvm::Instruction>(r)->getFunction() == D))
        box.insert(r);
    }
    bool grew = true;
    while (grew) {
      grew = false;
      for (const llvm::Instruction &I : llvm::instructions(*D)) {
        const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!SI)
          continue;
        if (restrictLive && !live.count(I.getParent()))
          continue;
        const llvm::Value *addr = barePtr(SI->getPointerOperand());
        if (!addr || !box.count(addr))
          continue;
        const llvm::Value *r = barePtr(SI->getValueOperand());
        if (!r || box.count(r) || r == FA)
          continue;
        if (llvm::isa<llvm::AllocaInst>(r) ||
            (llvm::isa<llvm::CallBase>(r) && llvm::cast<llvm::Instruction>(r)->getFunction() == D)) {
          box.insert(r);
          grew = true;
        }
      }
    }
    for (const llvm::Instruction &I : llvm::instructions(*D)) {
      const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI)
        continue;
      if (restrictLive && !live.count(I.getParent()))
        continue;
      const llvm::Value *addr = barePtr(SI->getPointerOperand());
      if (!addr || !box.count(addr))
        continue;
      if (isObj(SI->getValueOperand(), FA) || box.count(barePtr(SI->getValueOperand())))
        continue;
      saw = true;
      got = meetStore(got, of(SI->getValueOperand()));
    }
    if (!saw || !got.any) {
      acc.open = true;
    } else {
      acc.open = got.open;
      acc.con = got.con && got.args.empty() && got.loaded.empty() && !got.open;
      acc.args = got.args;
      acc.loaded = got.loaded;
    }
    acc.any = true;
    remember(acc);
    return acc;
  };
  // 1: the named parameter is the address of a store or a byte copy.
  // 0: the body does not store through it. An unnamed argument is not a
  // destination. A readonly parameter is not a destination. 2: no body, or
  // an indirect call, so the write is unknown.
  std::unordered_map<const llvm::Function *, std::unordered_map<unsigned, int>> wfMemo;
  std::vector<std::pair<const llvm::Function *, unsigned>> wfStack;
  std::function<int(const llvm::Function *, unsigned)> writesFormal;
  writesFormal = [&](const llvm::Function *B0, unsigned ai) -> int {
    const llvm::Function *B = definedBody(B0);
    auto readOnlyParam = [&](const llvm::Function *Attr) {
      return Attr && ai < Attr->arg_size() &&
             (Attr->hasParamAttribute(ai, llvm::Attribute::ReadOnly) ||
              Attr->hasParamAttribute(ai, llvm::Attribute::ReadNone) ||
              Attr->onlyReadsMemory());
    };
    // A vararg has no formal. It is not a store through a parameter.
    if (B0 && ai >= B0->arg_size())
      return 0;
    if (!B || B->isDeclaration())
      return readOnlyParam(B0) || readOnlyParam(B) ? 0 : 2;
    if (ai >= B->arg_size())
      return 0;
    auto &memo = wfMemo[B];
    auto mit = memo.find(ai);
    if (mit != memo.end())
      return mit->second;
    for (const auto &p : wfStack)
      if (p.first == B && p.second == ai)
        return 2;
    wfStack.emplace_back(B, ai);
    const llvm::Argument *FA = B->getArg(ai);
    auto reaches = [&](const llvm::Value *V) {
      std::unordered_set<const llvm::Value *> seenW;
      std::function<int(const llvm::Value *)> code;
      code = [&](const llvm::Value *U) -> int {
        if (!U)
          return 0;
        if (!seenW.insert(U).second)
          return 2;
        U = U->stripPointerCasts();
        if (U == FA)
          return 1;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U))
          return code(G->getPointerOperand());
        if (const auto *P = llvm::dyn_cast<llvm::PHINode>(U)) {
          if (P->getNumIncomingValues() == 0)
            return 0;
          int r = 2;
          for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
            int x = code(P->getIncomingValue(i));
            if (x == 0)
              return 0;
            if (x == 1)
              r = 1;
          }
          return r;
        }
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          int x = code(Sel->getTrueValue());
          int y = code(Sel->getFalseValue());
          if (x == 0 || y == 0)
            return 0;
          return (x == 1 || y == 1) ? 1 : 2;
        }
        if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(U)) {
          if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI))
            return code(CI->getOperand(0));
        }
        return 0;
      };
      return code(V) == 1;
    };
    int result = 0;
    for (const llvm::Instruction &BI : llvm::instructions(*B)) {
      if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&BI)) {
        if (reaches(SI->getPointerOperand())) {
          result = 1;
          break;
        }
      } else if (const auto *IC = llvm::dyn_cast<llvm::CallBase>(&BI)) {
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (byteCopy(IC, dst, src) && reaches(dst)) {
          result = 1;
          break;
        }
        if (IC->isInlineAsm())
          continue;
        unsigned fj = 0;
        for (const llvm::Use &AU : IC->args()) {
          if (reaches(AU.get())) {
            int w = writesFormal(IC->getCalledFunction(), fj);
            if (w == 1) {
              result = 1;
              break;
            }
            if (w == 2)
              result = 2;
          }
          ++fj;
        }
        if (result == 1)
          break;
      }
    }
    wfStack.pop_back();
    memo[ai] = result;
    return result;
  };
  storedThrough = [&](const llvm::CallBase *C, const llvm::Function *D, unsigned argNo,
                      const int64_t *fieldOff) -> Status {
    CallGuard guard{ei, C, argNo};
    // This callsite is already being summarized. The bytes are the source
    // it copies, which does not need this destination.
    bool re = !callWriteStack.insert(guard).second;
    FSet fs = formalsTouching(D, argNo, C, fieldOff);
    auto fieldAt = [&](const llvm::Value *V, int64_t off) -> Status {
      int64_t extra = off;
      std::unordered_set<const llvm::Value *> seenV;
      while (V && seenV.insert(V).second) {
        V = V->stripPointerCasts();
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
            return opened();
          extra += ap.getSExtValue();
          V = G->getPointerOperand();
          continue;
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          const llvm::Value *st = AI ? spillValue(AI) : nullptr;
          if (!st)
            return opened();
          V = st;
          continue;
        }
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
          if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            V = I->getOperand(0);
            continue;
          }
        }
        break;
      }
      if (const auto *B = llvm::dyn_cast_or_null<llvm::Argument>(V)) {
        if (!cone(B->getParent()))
          return opened();
        return readField(B, extra);
      }
      if (const auto *CB = llvm::dyn_cast_or_null<llvm::CallBase>(V))
        return fieldBytes(CB, extra, nullptr, 0);
      return opened();
    };
    // Bytes loaded through a pointer are the value stored at that address.
    // The pointer's own identity is a different root. A field of the formal
    // at this callsite is the same field of the actual passed here. Other
    // calls of this function pass other objects.
    auto bytesAt = [&](const llvm::Value *V) -> Status {
      if (auto af = argField(V)) {
        if (af->second != 0) {
          if (C && D && af->first->getParent() == D && af->first->getArgNo() < C->arg_size())
            return fieldAt(C->getArgOperand(af->first->getArgNo()), af->second);
          Status via = fieldOfCall(af->first, af->second);
          Status f = via.any ? via : readField(af->first, af->second);
          bool got = false;
          for (const auto &a : f.args)
            if (a.second >= 0)
              got = true;
          if (got && !f.local && !f.hasConst && !f.none)
            return f;
        }
      }
      return walk(V);
    };
    auto oneArg = [&](unsigned fj, bool loaded) {
      if (!C || fj >= C->arg_size())
        return opened();
      const llvm::Value *actual = C->getArgOperand(fj);
      return loaded ? bytesAt(actual) : walk(actual);
    };
    if (re) {
      // The destination is already on the stack. Name the source only, once.
      if (stDepth) {
        // Already naming some copy. This copy's source is a field of an
        // argument, read here, without walking the destination again.
        if (fs.loaded.size() == 1 && C) {
          unsigned fj = *fs.loaded.begin();
          if (fj < C->arg_size()) {
            if (auto af = argField(C->getArgOperand(fj))) {
              if (af->second != 0) {
                Status via = fieldOfCall(af->first, af->second);
                Status f = via.any ? via : readField(af->first, af->second);
                bool ent = false;
                for (const auto &a : f.args)
                  if (a.second >= 0)
                    ent = true;
                if (ent && !f.local && !f.hasConst && !f.none)
                  return f;
              }
            }
          }
        }
        return bare();
      }
      ++stDepth;
      Status acc;
      for (unsigned fj : fs.loaded)
        acc = alt(acc, oneArg(fj, true));
      for (unsigned fj : fs.args)
        acc = alt(acc, oneArg(fj, false));
      --stDepth;
      return acc.any ? acc : bare();
    }
    // A call handed the whole object writes this field only where it passes
    // this offset to a callee that stores through it, or where it stores at
    // this offset itself. A constant actual makes the contradictory branch
    // infeasible, so that branch's write is not this callsite.
    if (fieldOff && D && !D->isDeclaration() && C && argNo < D->arg_size()) {
      const llvm::Argument *FA = D->getArg(argNo);
      std::unordered_map<unsigned, std::pair<uint64_t, unsigned>> foldArg;
      for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i) {
        const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(C->getArgOperand(i));
        if (CI && CI->getBitWidth() <= 64)
          foldArg.emplace(i, std::make_pair(CI->getZExtValue(), CI->getBitWidth()));
      }
      auto fold = [&](const llvm::Value *V) -> std::optional<std::pair<uint64_t, unsigned>> {
        std::unordered_set<const llvm::Value *> seenF;
        while (V && seenF.insert(V).second) {
          if (const auto *FI = llvm::dyn_cast<llvm::FreezeInst>(V)) {
            V = FI->getOperand(0);
            continue;
          }
          if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
            if (CI->getBitWidth() > 64)
              return std::nullopt;
            return std::make_pair(CI->getZExtValue(), CI->getBitWidth());
          }
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
            if (A->getParent() != D)
              return std::nullopt;
            auto it = foldArg.find(A->getArgNo());
            if (it == foldArg.end())
              return std::nullopt;
            return it->second;
          }
          break;
        }
        return std::nullopt;
      };
      std::unordered_set<const llvm::BasicBlock *> live;
      bool restrictLive = !foldArg.empty();
      if (restrictLive) {
        std::vector<const llvm::BasicBlock *> work{&D->getEntryBlock()};
        live.insert(&D->getEntryBlock());
        for (size_t qi = 0; qi < work.size(); ++qi) {
          const llvm::Instruction *T = work[qi]->getTerminator();
          std::vector<const llvm::BasicBlock *> next;
          if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(T)) {
            if (!BI->isConditional()) {
              next.push_back(BI->getSuccessor(0));
            } else {
              bool folded = false;
              if (const auto *Cmp = llvm::dyn_cast<llvm::ICmpInst>(BI->getCondition())) {
                auto a = fold(Cmp->getOperand(0));
                auto b = fold(Cmp->getOperand(1));
                if (a && b && a->second == b->second &&
                    (Cmp->getPredicate() == llvm::CmpInst::ICMP_EQ ||
                     Cmp->getPredicate() == llvm::CmpInst::ICMP_NE)) {
                  bool eq = a->first == b->first;
                  bool takeTrue = Cmp->getPredicate() == llvm::CmpInst::ICMP_EQ ? eq : !eq;
                  next.push_back(BI->getSuccessor(takeTrue ? 0 : 1));
                  folded = true;
                }
              }
              if (!folded) {
                next.push_back(BI->getSuccessor(0));
                next.push_back(BI->getSuccessor(1));
              }
            }
          } else if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(T)) {
            auto c = fold(SW->getCondition());
            bool folded = false;
            if (c && SW->getCondition()->getType()->getIntegerBitWidth() == c->second) {
              for (const auto &cas : SW->cases()) {
                const llvm::ConstantInt *CV = cas.getCaseValue();
                if (CV->getBitWidth() == c->second && CV->getZExtValue() == c->first) {
                  next.push_back(cas.getCaseSuccessor());
                  folded = true;
                  break;
                }
              }
              if (!folded)
                next.push_back(SW->getDefaultDest());
              folded = true;
            }
            if (!folded)
              for (unsigned si = 0; si < SW->getNumSuccessors(); ++si)
                next.push_back(SW->getSuccessor(si));
          } else if (T) {
            for (unsigned si = 0; si < T->getNumSuccessors(); ++si)
              next.push_back(T->getSuccessor(si));
          }
          for (const llvm::BasicBlock *S : next)
            if (S && live.insert(S).second)
              work.push_back(S);
        }
      }
      auto atOff = [&](const llvm::Value *addr) -> bool {
        int64_t o = 0;
        bool known = true;
        bool field = false;
        std::unordered_set<const llvm::Value *> seenA;
        while (addr && seenA.insert(addr).second) {
          addr = addr->stripPointerCasts();
          if (addr == FA)
            return !known || (field ? o : 0) == *fieldOff;
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(addr)) {
            field = true;
            if (known) {
              llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
              if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
                known = false;
              else
                o += ap.getSExtValue();
            }
            addr = G->getPointerOperand();
            continue;
          }
          if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(addr)) {
            if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
              addr = CI->getOperand(0);
              continue;
            }
          }
          break;
        }
        return false;
      };
      Status fromCalls;
      bool callSaw = false;
      for (const llvm::Instruction &I : llvm::instructions(*D)) {
        if (restrictLive && !live.count(I.getParent()))
          continue;
        const auto *IC = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!IC || IC->isInlineAsm())
          continue;
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (byteCopy(IC, dst, src))
          continue;
        unsigned fj = 0;
        for (const llvm::Use &AU : IC->args()) {
          if (atOff(AU.get())) {
            const llvm::Function *Cal = IC->getCalledFunction();
            int wr = writesFormal(Cal, fj);
            if (wr == 1) {
              const llvm::Function *B = definedBody(Cal);
              if (B && !B->isDeclaration()) {
                callSaw = true;
                fromCalls = meet(fromCalls, storedThrough(IC, B, fj, nullptr));
              }
            } else if (wr == 2) {
              callSaw = true;
              fromCalls = meet(fromCalls, opened());
            }
          }
          ++fj;
        }
      }
      if (callSaw) {
        bool direct = !fs.args.empty() || !fs.loaded.empty();
        Status acc;
        if (direct) {
          for (unsigned fj : fs.args)
            acc = meet(acc, oneArg(fj, false));
          for (unsigned fj : fs.loaded)
            acc = meet(acc, oneArg(fj, true));
          if (fs.open)
            acc = meet(acc, opened());
        }
        bool pureCall = fromCalls.any && !fromCalls.open && !fromCalls.local &&
                        !fromCalls.hasConst && !fromCalls.none;
        if (pureCall) {
          bool ent = false;
          for (const auto &a : fromCalls.args)
            if (a.second >= 0)
              ent = true;
          pureCall = ent;
        }
        if (pureCall && !(direct && (acc.open || acc.local || acc.hasConst || acc.none)))
          acc = fromCalls;
        else
          acc = acc.any ? meet(acc, fromCalls) : fromCalls;
        callWriteStack.erase(guard);
        return acc.any ? acc : opened();
      }
    }
    if (!fs.any || (fs.args.empty() && fs.loaded.empty())) {
      callWriteStack.erase(guard);
      return fs.con && !fs.open ? constant() : opened();
    }
    Status acc;
    for (unsigned fj : fs.args)
      acc = meet(acc, oneArg(fj, false));
    for (unsigned fj : fs.loaded)
      acc = meet(acc, oneArg(fj, true));
    if (fs.open)
      acc = meet(acc, opened());
    callWriteStack.erase(guard);
    return acc.any ? acc : opened();
  };

  memRoots = [&](const llvm::Instruction *At, const llvm::Value *Ptr, bool objectBytes,
                 const int64_t *onlyOff) -> Status {
    if (!At || !Ptr || !At->getFunction())
      return opened();
    llvm::Function *F = const_cast<llvm::Function *>(At->getFunction());
    if (F->isDeclaration())
      return opened();
    llvm::MemorySSA &mssa = fam.getResult<llvm::MemorySSAAnalysis>(*F).getMSSA();
    // A load or a call is a memory access. A return is not: the bytes of the
    // object are the last write in the block before the return.
    llvm::MemoryAccess *start = nullptr;
    if (llvm::MemoryUseOrDef *acc = mssa.getMemoryAccess(At)) {
      start = acc->getDefiningAccess();
    } else {
      llvm::MemoryAccess *prev = nullptr;
      for (const llvm::Instruction &I : *At->getParent()) {
        if (&I == At)
          break;
        if (llvm::MemoryUseOrDef *a = mssa.getMemoryAccess(&I))
          prev = a;
      }
      if (auto *def = llvm::dyn_cast_or_null<llvm::MemoryDef>(prev))
        start = def;
      else if (auto *use = llvm::dyn_cast_or_null<llvm::MemoryUse>(prev))
        start = use->getDefiningAccess();
      else
        start = mssa.getMemoryAccess(At->getParent());
    }
    if (!start)
      return opened();
    llvm::AliasAnalysis &AA = mssa.getAA();
    llvm::MemoryLocation watched = llvm::MemoryLocation::getBeforeOrAfter(Ptr);
    Loc want = locate(Ptr, DL);
    // Constant byte offset of V from Ptr. Empty when V is not that object
    // or the offset is not constant. The object itself is offset 0 only
    // when V is Ptr; a field is the GEP offset.
    auto relOff = [&](const llvm::Value *V) -> std::optional<std::pair<int64_t, bool>> {
      int64_t off = 0;
      bool known = true;
      bool field = false;
      std::unordered_set<const llvm::Value *> seenR;
      const llvm::Value *root = Ptr->stripPointerCasts();
      while (V && seenR.insert(V).second) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
          field = true;
          if (known) {
            llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
              known = false;
            else
              off += ap.getSExtValue();
          }
          V = G->getPointerOperand()->stripPointerCasts();
          continue;
        }
        V = V->stripPointerCasts();
        if (V == root)
          return std::make_pair(off, field);
        break;
      }
      return std::nullopt;
    };
    std::unordered_map<llvm::MemoryAccess *, Status> done;
    std::unordered_set<llvm::MemoryAccess *> stack;
    std::function<Status(llvm::MemoryAccess *)> along;
    along = [&](llvm::MemoryAccess *A) -> Status {
      if (!A)
        return opened();
      auto it = done.find(A);
      if (it != done.end())
        return it->second;
      if (!stack.insert(A).second)
        return bare();
      Status s = opened();
      if (const auto *Phi = llvm::dyn_cast<llvm::MemoryPhi>(A)) {
        s = bare();
        if (!onlyOff) {
          for (unsigned i = 0; i < Phi->getNumIncomingValues(); ++i)
            s = alt(s, along(Phi->getIncomingValue(i)));
          if (!s.any)
            s = opened();
        } else {
          // A constant fill of this field is not a root and does not open a
          // proved store on another incoming path.
          Status proved;
          bool sawProved = false;
          bool sawConst = false;
          bool sawNone = false;
          bool bad = false;
          for (unsigned i = 0; i < Phi->getNumIncomingValues(); ++i) {
            Status one = along(Phi->getIncomingValue(i));
            if (!one.any)
              continue;
            bool ent = false;
            for (const auto &a : one.args)
              if (a.second >= 0)
                ent = true;
            bool filler = (one.hasConst || one.none) && !one.open && !one.local && !ent;
            if (filler) {
              if (one.hasConst)
                sawConst = true;
              if (one.none)
                sawNone = true;
              continue;
            }
            if (ent && !one.open && !one.local && !one.hasConst && !one.none) {
              if (sawProved && proved.args != one.args)
                bad = true;
              if (!sawProved)
                proved = one;
              sawProved = true;
              continue;
            }
            bad = true;
            s = meet(s, one);
          }
          if (sawProved && !bad)
            s = proved;
          else if (sawProved)
            s = meet(s, proved);
          else if (!bad && sawConst)
            s = constant();
          else if (!bad && sawNone)
            s = nothing();
          else if (!s.any)
            s = opened();
        }
      } else if (const auto *Def = llvm::dyn_cast<llvm::MemoryDef>(A)) {
        const llvm::Instruction *I = Def->getMemoryInst();
        if (!I) {
          if (objectBytes) {
            s = bare();
          } else {
            Status p = walk(Ptr);
            bool ent = false;
            bool glob = false;
            for (const auto &a : p.args) {
              if (a.second >= 0)
                ent = true;
              else
                glob = true;
            }
            // An address that did not reduce is still unknown. A resolved
            // local or a constant is not an input of this load.
            if (p.open)
              s = opened();
            else if (p.local || p.hasConst || p.none || (ent && glob) || !p.any)
              s = (ent || glob) ? opened() : nothing();
            else
              s = p;
            bool have = false;
            for (const auto &a : s.args)
              if (a.second >= 0)
                have = true;
            // A field of an entry argument is the value stored there. The
            // object is that value only when no store names a parameter.
            if (auto af = argField(Ptr)) {
              Status f = readField(af->first, af->second);
              bool got = false;
              for (const auto &a : f.args)
                if (a.second >= 0)
                  got = true;
              if (got && !f.local && !f.hasConst && !f.none) {
                s = f;
                have = true;
              }
            }
            // A local slot that holds one entry argument denotes that object.
            // A load of one of its fields is a load of that object. The slot
            // is not a second input.
            if (!have) {
              Loc base = locate(Ptr, DL);
              if (base.base && base.known && base.off != 0 && llvm::isa<llvm::AllocaInst>(base.base)) {
                Status held = memRoots(At, base.base, false, nullptr);
                bool clean = held.any && !held.open && !held.local && !held.hasConst && !held.none;
                int nent = 0;
                for (const auto &a : held.args) {
                  if (a.second < 0)
                    clean = false;
                  else
                    ++nent;
                }
                if (clean && nent == 1)
                  s = held;
              }
            }
          }
        } else if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(I)) {
          Loc st = locate(SI->getPointerOperand(), DL);
          bool other = want.base && st.base == want.base && want.known && st.known && want.off != st.off;
          llvm::AliasResult ar = AA.alias(watched, llvm::MemoryLocation::get(SI));
          if (objectBytes && fromObject(SI->getPointerOperand(), Ptr)) {
            // This field of the object. A constant is not an input. A write
            // at another known offset does not touch the field being asked.
            auto ro = relOff(SI->getPointerOperand());
            if (onlyOff && ro && ro->second && ro->first != *onlyOff) {
              s = along(Def->getDefiningAccess());
            } else if (onlyOff && ro && ro->second && ro->first == *onlyOff) {
              Status val = entryRoots(walk(SI->getValueOperand()));
              s = val.any ? val : nothing();
            } else if (onlyOff) {
              // The address reaches this object through a loaded pointer.
              // That write is the referent, not the inline field.
              s = along(Def->getDefiningAccess());
            } else {
              Status val = entryRoots(walk(SI->getValueOperand()));
              s = val.any ? meet(val, along(Def->getDefiningAccess()))
                          : along(Def->getDefiningAccess());
            }
          } else if (other || ar == llvm::AliasResult::NoAlias) {
            s = along(Def->getDefiningAccess());
          } else if (ar == llvm::AliasResult::MayAlias) {
            // An unknown address may be this object. A different constant
            // field of the same struct is another access path: it does not
            // write the field being asked, and it does not open that field.
            const llvm::Value *root = objectBytes ? objectRoot(SI->getPointerOperand()) : nullptr;
            const llvm::Value *mine = Ptr->stripPointerCasts();
            if (objectBytes && root && root != mine)
              s = along(Def->getDefiningAccess());
            else if (objectBytes && onlyOff)
              // No access path from this store to the field. A may-alias
              // write does not replace the bytes at the known offset.
              s = along(Def->getDefiningAccess());
            else
              s = objectBytes ? meet(opened(), along(Def->getDefiningAccess())) : opened();
          } else if (onlyOff && objectBytes) {
            // Alias without an access path to this field is not a write of it.
            s = along(Def->getDefiningAccess());
          } else {
            Status val = walk(SI->getValueOperand());
            bool same = want.base && st.base == want.base && want.known && st.known && want.off == st.off;
            bool kill = same || ar == llvm::AliasResult::MustAlias;
            if (kill && objectBytes && !onlyOff) {
              // A constant in one field does not erase an entry argument
              // stored in another field, and it is not a root of the object.
              Status roots = entryRoots(val);
              if (roots.any)
                s = meet(roots, along(Def->getDefiningAccess()));
              else if (!val.open)
                s = along(Def->getDefiningAccess());
              else
                s = meet(opened(), along(Def->getDefiningAccess()));
            } else if (kill)
              s = val;
            else
              s = meet(val, along(Def->getDefiningAccess()));
          }
        } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(I)) {
          if (onlyOff && objectBytes) {
            if (const llvm::Function *CF = CB->getCalledFunction()) {
              if (CF->isIntrinsic() &&
                  (CF->getIntrinsicID() == llvm::Intrinsic::memset ||
                   CF->getIntrinsicID() == llvm::Intrinsic::memset_element_unordered_atomic) &&
                  CB->arg_size() > 1 && llvm::isa<llvm::Constant>(CB->getArgOperand(1)) &&
                  fromObject(CB->getArgOperand(0), Ptr)) {
                auto ro = relOff(CB->getArgOperand(0));
                if (!ro || !ro->second || ro->first == *onlyOff) {
                  s = constant();
                  stack.erase(A);
                  done.emplace(A, s);
                  return s;
                }
              }
            }
          }
          const llvm::Value *dst = nullptr;
          const llvm::Value *src = nullptr;
          if (byteCopy(CB, dst, src)) {
            if (objectBytes && fromObject(dst, Ptr)) {
              auto ro = relOff(dst);
              Status val = entryRoots(walk(src));
              if (onlyOff && ro && ro->second && ro->first != *onlyOff)
                s = along(Def->getDefiningAccess());
              else if (onlyOff && ro && ro->second && ro->first == *onlyOff)
                s = val.any ? val : nothing();
              else
                s = val.any ? meet(val, along(Def->getDefiningAccess()))
                            : along(Def->getDefiningAccess());
            } else {
            llvm::AliasResult ar = AA.alias(watched, llvm::MemoryLocation::getBeforeOrAfter(dst));
            if (ar == llvm::AliasResult::NoAlias) {
              s = along(Def->getDefiningAccess());
            } else if (ar == llvm::AliasResult::MayAlias) {
              // The copy's destination was not located in this object. It
              // does not replace a field at a known offset.
              s = onlyOff ? along(Def->getDefiningAccess()) : opened();
            } else {
              Status val = walk(src);
              if (!objectBytes || ar == llvm::AliasResult::MustAlias)
                s = val;
              else
                s = meet(val, along(Def->getDefiningAccess()));
            }
            }
          } else if (!handed(CB, Ptr)) {
            // A call writes this object only through a pointer it was given.
            s = along(Def->getDefiningAccess());
          } else {
            // The bytes are the values the body stores through that formal.
            // A declaration stores nothing we can name. An argument that is
            // not stored is not a byte of this object. A value already
            // written stays; this write does not replace it with the
            // call's other arguments.
            Status w;
            bool saw = false;
            auto reachArg = [&](const llvm::Value *V) {
              std::unordered_set<const llvm::Value *> seenR;
              std::function<bool(const llvm::Value *)> reach;
              reach = [&](const llvm::Value *U) {
                if (!U || !seenR.insert(U).second)
                  return false;
                if (const auto *M = llvm::dyn_cast<llvm::MetadataAsValue>(U)) {
                  if (const auto *MV = llvm::dyn_cast<llvm::ValueAsMetadata>(M->getMetadata()))
                    return reach(MV->getValue());
                  return false;
                }
                U = U->stripPointerCasts();
                if (U == Ptr)
                  return true;
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U))
                  return reach(G->getPointerOperand());
                return false;
              };
              return reach(V);
            };
            int reached = 0;
            int skipped = 0;
            auto offOf = [&](const llvm::Argument *FA, const llvm::Value *addr) -> std::optional<int64_t> {
              int64_t o = 0;
              bool known = true;
              bool field = false;
              std::unordered_set<const llvm::Value *> seenA;
              while (addr && seenA.insert(addr).second) {
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(addr)) {
                  field = true;
                  if (known) {
                    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
                    if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
                      known = false;
                    else
                      o += ap.getSExtValue();
                  }
                  addr = G->getPointerOperand()->stripPointerCasts();
                  continue;
                }
                addr = addr->stripPointerCasts();
                if (addr == FA)
                  return field && known ? std::optional<int64_t>(o) : std::nullopt;
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(addr)) {
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
                  const llvm::Value *st = AI ? spillValue(AI) : nullptr;
                  if (!st || st->stripPointerCasts() != FA)
                    break;
                  addr = st;
                  continue;
                }
                if (const auto *CI = llvm::dyn_cast<llvm::Instruction>(addr)) {
                  if (llvm::isa<llvm::CastInst>(CI) || llvm::isa<llvm::FreezeInst>(CI)) {
                    addr = CI->getOperand(0);
                    continue;
                  }
                }
                break;
              }
              return std::nullopt;
            };
            auto consider = [&](const llvm::Function *D0) {
              const llvm::Function *D = definedBody(D0);
              if (!D || D->isDeclaration())
                return;
              for (unsigned ai = 0; ai < CB->arg_size(); ++ai) {
                if (!reachArg(CB->getArgOperand(ai)))
                  continue;
                ++reached;
                if (onlyOff) {
                  auto ro = relOff(CB->getArgOperand(ai));
                  if (ro && ro->second && ro->first != *onlyOff) {
                    ++skipped;
                    continue;
                  }
                  if (ro && ro->second && ro->first == *onlyOff) {
                    // Passing this field to a function writes it only when
                    // that function stores through the parameter. A read,
                    // including an unnamed argument, does not.
                    int wr = ai < D->arg_size() ? writesFormal(D, ai) : 0;
                    if (wr == 0) {
                      ++skipped;
                      continue;
                    }
                    if (wr == 2) {
                      bool proved = false;
                      if (w.any && !w.open && !w.local && !w.hasConst && !w.none)
                        for (const auto &a : w.args)
                          if (a.second >= 0)
                            proved = true;
                      if (!proved) {
                        saw = true;
                        w = opened();
                      }
                      continue;
                    }
                  }
                  if (!ro || !ro->second) {
                    bool hit = false;
                    bool unknown = false;
                    const llvm::Argument *FA = D->getArg(ai);
                    for (const llvm::Instruction &BI : llvm::instructions(*D)) {
                      if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&BI)) {
                        if (auto o = offOf(FA, SI->getPointerOperand()))
                          if (*o == *onlyOff)
                            hit = true;
                      } else if (const auto *IC = llvm::dyn_cast<llvm::CallBase>(&BI)) {
                        unsigned fj = 0;
                        for (const llvm::Use &AU : IC->args()) {
                          if (auto o = offOf(FA, AU.get())) {
                            if (*o == *onlyOff) {
                              int w = writesFormal(IC->getCalledFunction(), fj);
                              if (w == 1)
                                hit = true;
                              else if (w == 2)
                                unknown = true;
                            }
                          }
                          ++fj;
                        }
                      }
                      if (hit)
                        break;
                    }
                    if (!hit && !unknown) {
                      ++skipped;
                      continue;
                    }
                  }
                }
                // The callee was handed the whole object. This field is only
                // the stores at this offset. A store at another offset is a
                // different access path.
                const int64_t *touchOff = nullptr;
                if (onlyOff) {
                  auto whole = relOff(CB->getArgOperand(ai));
                  if (!whole || !whole->second)
                    touchOff = onlyOff;
                }
                Status got = storedThrough(CB, D, ai, touchOff);
                // A callsite already on the stack has not failed. It is not a
                // write of this field, and it is not a constant.
                if (!got.any) {
                  ++skipped;
                  continue;
                }
                bool proved = false;
                if (onlyOff && w.any && !w.open && !w.local && !w.hasConst && !w.none)
                  for (const auto &a : w.args)
                    if (a.second >= 0)
                      proved = true;
                if (proved && got.open) {
                  ++skipped;
                  continue;
                }
                saw = true;
                w = onlyOff ? got : meet(w, got);
              }
            };
            auto rit = resolved.find(CB);
            if (rit != resolved.end()) {
              for (const llvm::Function *D : rit->second)
                consider(D);
            } else if (const llvm::Function *D = CB->getCalledFunction()) {
              consider(D);
            }
            if (onlyOff && !saw) {
              // This call does not store the field. The bytes are the
              // earlier store.
              s = along(Def->getDefiningAccess());
            } else {
              if (!saw) {
                bool constantFill = false;
                if (objectBytes) {
                  if (const llvm::Function *CF = CB->getCalledFunction()) {
                    if (CF->isIntrinsic() &&
                        (CF->getIntrinsicID() == llvm::Intrinsic::memset ||
                         CF->getIntrinsicID() == llvm::Intrinsic::memset_element_unordered_atomic) &&
                        CB->arg_size() > 1 && llvm::isa<llvm::Constant>(CB->getArgOperand(1)))
                      constantFill = true;
                  }
                }
                w = constantFill ? bare() : opened();
              }
              if (objectBytes)
                w = entryRoots(w);
              s = (onlyOff && saw) ? (w.any ? w : nothing())
                                  : meet(w, along(Def->getDefiningAccess()));
            }
          }
        } else if (!llvm::isModSet(AA.getModRefInfo(I, watched))) {
          s = along(Def->getDefiningAccess());
        } else if (objectBytes) {
          s = meet(opened(), along(Def->getDefiningAccess()));
        } else {
          s = opened();
        }
      }
      stack.erase(A);
      done.emplace(A, s);
      return s;
    };
    return along(start);
  };

  fieldBytes = [&](const llvm::CallBase *C, int64_t off, llvm::StructType *sty, uint64_t fsz) -> Status {
    if (!sty && !fieldAsk.empty()) {
      sty = fieldAsk.back().ty;
      if (fsz == 0)
        fsz = fieldAsk.back().size;
    }
    for (const auto &p : fbStack)
      if (p.first == C && p.second == off) {
        // This object is already being summarized from its stores. The bytes
        // at this offset are the same offset of the argument the callers
        // passed, which does not need this object.
        if (rfReentry)
          return bare();
        const llvm::Function *Fn = C->getCalledFunction();
        if (!Fn)
          return bare();
        ++rfReentry;
        Status acc;
        bool any = false;
        for (const llvm::Argument &Arg : Fn->args()) {
          if (!Arg.getType()->isPointerTy())
            continue;
          Status f = argumentField(&Arg, off);
          if (f.args.empty())
            continue;
          any = true;
          acc = meet(acc, f);
        }
        --rfReentry;
        return any ? acc : bare();
      }
    fbStack.emplace_back(C, off);
    fieldAsk.push_back(FieldAsk{sty, fsz});
    struct Guard {
      std::vector<std::pair<const llvm::CallBase *, int64_t>> &s;
      std::vector<FieldAsk> &ask;
      ~Guard() {
        s.pop_back();
        ask.pop_back();
      }
    } guard{fbStack, fieldAsk};
    std::vector<const llvm::Function *> bodies;
    auto add = [&](const llvm::Function *D) {
      if (!D)
        return;
      if (D->isDeclaration() || (D->getParent() == &M && !cone(D)))
        D = definedBody(D);
      if (!D || D->isDeclaration())
        return;
      if (D->getParent() == &M && !cone(D))
        return;
      bodies.push_back(D);
    };
    auto it = resolved.find(C);
    if (it != resolved.end()) {
      for (const llvm::Function *D : it->second)
        add(D);
    } else {
      add(C->getCalledFunction());
    }
    Status acc;
    bool saw = false;
    for (const llvm::Function *B : bodies) {
      for (const llvm::BasicBlock &BB : *B) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
          continue;
        saw = true;
        Status part = memRoots(R, R->getReturnValue()->stripPointerCasts(), true, &off);
        auto pure = [](const Status &t) {
          if (!t.any || t.open || t.local || t.hasConst || t.none)
            return false;
          bool ent = false;
          for (const auto &a : t.args) {
            if (a.second < 0)
              return false;
            ent = true;
          }
          return ent;
        };
        // A return that is not this object does not open a proved field.
        if (pure(acc) && !pure(part))
          continue;
        if (!pure(acc) && pure(part)) {
          acc = part;
          continue;
        }
        if (pure(acc) && pure(part) && acc.args != part.args) {
          acc = meet(acc, part);
          acc.open = true;
          continue;
        }
        acc = meet(acc, part);
      }
    }
    if (!saw)
      return opened();
    // A constant or a local in another part of this same answer is not a root
    // and does not erase an entry argument stored at this offset.
    bool ent = false;
    for (const auto &a : acc.args)
      if (a.second >= 0)
        ent = true;
    if (ent) {
      Status only;
      only.any = true;
      only.open = acc.open;
      for (const auto &a : acc.args)
        if (a.second >= 0)
          only.args.insert(a);
      return only;
    }
    return acc.any ? acc : nothing();
  };

  readField = [&](const llvm::Argument *A, int64_t off) -> Status {
    RFKey key{ei, A, off, carry};
    // While one activation is being explained, a field summary from the
    // union of callers belongs to a different invocation.
    bool actCache = activation != nullptr;
    if (actCache) {
      auto it = actRf.find({A, off});
      if (it != actRf.end())
        return it->second;
    } else {
      auto found = rfMemo.find(key);
      if (found != rfMemo.end())
        return found->second;
    }
    if (!rfStack.insert(key).second) {
      if (rfReentry)
        return bare();
      ++rfReentry;
      Status p = argumentField(A, off);
      --rfReentry;
      return p;
    }
    // Stores into a field of this entry's own argument are inside this
    // entry. Callers of the entry are not that store.
    if (A && A->getParent() == entryFn) {
      Status w;
      bool saw = false;
      auto note = [&](Status one) {
        if (!one.any)
          return;
        saw = true;
        w = meet(w, one);
      };
      for (const llvm::Instruction &I : llvm::instructions(*entryFn)) {
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (auto af = argField(SI->getPointerOperand()))
            if (af->first == A && af->second == off)
              note(walk(SI->getValueOperand()));
          continue;
        }
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || CB->isInlineAsm())
          continue;
        auto consider = [&](const llvm::Function *D0) {
          const llvm::Function *B = definedBody(D0);
          if (!B || B->isDeclaration())
            return;
          for (unsigned ai = 0; ai < CB->arg_size() && ai < B->arg_size(); ++ai) {
            if (auto af = argField(CB->getArgOperand(ai)))
              if (af->first == A && af->second == off) {
                int w = writesFormal(D0, ai);
                if (w == 0)
                  return;
                note(w == 1 ? storedThrough(CB, B, ai, nullptr) : opened());
              }
          }
        };
        auto rit = resolved.find(CB);
        if (rit != resolved.end()) {
          for (const llvm::Function *D : rit->second)
            consider(D);
        } else if (const llvm::Function *D = CB->getCalledFunction()) {
          consider(D);
        }
      }
      Status out = saw ? w : opened();
      rfStack.erase(key);
      rfMemo.emplace(key, out);
      return out;
    }
    Status acc;
    bool bad = false;
    bool site = false;
    auto take = [&](Status one) {
      if (!one.any)
        return;
      if (one.hasConst && !one.open && !one.local && !one.none && one.args.empty())
        return;
      if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
        return;
      if (one.local && !one.open && one.args.empty() && !one.hasConst && !one.none) {
        bad = true;
        return;
      }
      bool ent = false;
      bool glob = false;
      for (const auto &a : one.args) {
        if (a.second >= 0)
          ent = true;
        else
          glob = true;
      }
      if (ent && !glob) {
        Status keep;
        keep.any = true;
        for (const auto &a : one.args)
          if (a.second >= 0)
            keep.args.insert(a);
        acc = meet(acc, keep);
        // A constant, a local, or an unreduced part of the same value does
        // not erase the entry argument. It leaves the value open.
        if (one.open || one.local || one.hasConst || one.none)
          bad = true;
        return;
      }
      if (glob && !ent && !one.open && !one.local && !one.hasConst && !one.none && acc.args.empty()) {
        acc = meet(acc, one);
        return;
      }
      bad = true;
    };
    auto drain = [&](Status one, const llvm::Instruction *at) {
      std::unordered_set<const llvm::Value *> seenSlot;
      while (one.local && !one.open && one.args.empty() && !one.hasConst && !one.none && one.slot &&
             one.offKnown) {
        if (!seenSlot.insert(one.slot).second)
          return opened();
        const llvm::Instruction *use = at;
        if (slotFn(one.slot) != at->getFunction()) {
          use = nullptr;
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(one.slot)) {
            for (const llvm::User *U : AI->users()) {
              const auto *UI = llvm::dyn_cast<llvm::Instruction>(U);
              if (!UI || llvm::isa<llvm::StoreInst>(UI) || UI->getFunction() != slotFn(one.slot))
                continue;
              use = UI;
              break;
            }
          }
          if (!use)
            return opened();
        }
        one = memRoots(use, one.slot, false, nullptr);
      }
      return one;
    };
    // This offset only. A store or a call that writes another field of the
    // same object is a different access path and does not define this one.
    auto readAt = [&](const llvm::Instruction *at, const llvm::Value *slot, int64_t field) {
      int64_t o = field;
      return memRoots(at, slot, true, &o);
    };
    auto sit = sites.find(A->getParent());
    if (sit != sites.end()) {
      for (const llvm::CallBase *C : sit->second) {
        if (!cone(C->getFunction()) || A->getArgNo() >= C->arg_size())
          continue;
        if (const llvm::CallBase *via = boundCall(A->getParent())) {
          if (C != via)
            continue;
        } else if (!entryCall(C->getFunction(), A->getParent())) {
          continue;
        }
        if (activation && activates(activation, A->getParent()) && C != activation)
          continue;
        site = true;
        const llvm::Value *V = C->getArgOperand(A->getArgNo());
        int64_t extra = 0;
        std::unordered_set<const llvm::Value *> seenV;
        while (V && seenV.insert(V).second) {
          V = V->stripPointerCasts();
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63)) {
              V = nullptr;
              break;
            }
            extra += ap.getSExtValue();
            V = G->getPointerOperand();
            continue;
          }
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            const llvm::Value *st = AI ? spillValue(AI) : nullptr;
            if (!st) {
              V = nullptr;
              break;
            }
            V = st;
            continue;
          }
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
            if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
              V = I->getOperand(0);
              continue;
            }
          }
          break;
        }
        Status got;
        if (const auto *AI = llvm::dyn_cast_or_null<llvm::AllocaInst>(V)) {
          got = drain(readAt(C, AI, off + extra), C);
          take(got);
        } else if (const auto *B = llvm::dyn_cast_or_null<llvm::Argument>(V)) {
          if (cone(B->getParent())) {
            got = readField(B, off + extra);
            take(got);
          } else {
            bad = true;
            got = opened();
          }
        } else if (const auto *CB = llvm::dyn_cast_or_null<llvm::CallBase>(V)) {
          got = fieldBytes(CB, off + extra, nullptr, 0);
          take(got);
        } else if (V) {
          got = walk(V);
          take(got);
        } else {
          bad = true;
          got = opened();
        }
      }
    }
    Status out;
    if (!site || acc.args.empty()) {
      out = opened();
    } else {
      bool ent = false;
      for (const auto &a : acc.args)
        if (a.second >= 0)
          ent = true;
      if (ent) {
        out = bare();
        out.any = true;
        out.open = bad;
        for (const auto &a : acc.args)
          if (a.second >= 0)
            out.args.insert(a);
      } else if (bad) {
        out = opened();
      } else {
        out = acc;
      }
    }
    rfStack.erase(key);
    if (actCache)
      actRf.emplace(std::pair<const llvm::Argument *, int64_t>{A, off}, out);
    else
      rfMemo.emplace(key, out);
    return out;
  };

  // The object returned by a call on fbStack. A field of that callee's
  // argument is the same field of the actual this call passed.
  fieldOfCall = [&](const llvm::Argument *A, int64_t off) -> Status {
    if (!A)
      return bare();
    const llvm::CallBase *C = nullptr;
    for (auto it = fbStack.rbegin(); it != fbStack.rend(); ++it) {
      const llvm::CallBase *Call = it->first;
      if (!Call)
        continue;
      auto same = [&](const llvm::Function *Fn) {
        if (!Fn)
          return false;
        if (Fn == A->getParent())
          return true;
        const llvm::Function *B = definedBody(Fn);
        return B == A->getParent();
      };
      if (same(Call->getCalledFunction())) {
        C = Call;
        break;
      }
      auto rit = resolved.find(Call);
      if (rit == resolved.end())
        continue;
      for (const llvm::Function *D : rit->second)
        if (same(D)) {
          C = Call;
          break;
        }
      if (C)
        break;
    }
    if (!C || A->getArgNo() >= C->arg_size()) {
      return bare();
    }
    const llvm::Value *V = C->getArgOperand(A->getArgNo());
    int64_t extra = off;
    std::unordered_set<const llvm::Value *> seenV;
    while (V && seenV.insert(V).second) {
      V = V->stripPointerCasts();
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
          return opened();
        extra += ap.getSExtValue();
        V = G->getPointerOperand();
        continue;
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        const llvm::Value *st = AI ? spillValue(AI) : nullptr;
        if (!st)
          return opened();
        V = st;
        continue;
      }
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
          V = I->getOperand(0);
          continue;
        }
      }
      break;
    }
    if (const auto *B = llvm::dyn_cast_or_null<llvm::Argument>(V)) {
      if (!cone(B->getParent()))
        return opened();
      Status r = readField(B, extra);
      return r;
    }
    if (const auto *CB = llvm::dyn_cast_or_null<llvm::CallBase>(V))
      return fieldBytes(CB, extra, nullptr, 0);
    return opened();
  };

  // Callsites that pass an argument, while this field is already being
  // computed. A call that returns the object needs this same field, so it
  // is not part of the answer. An empty status from that cycle is not a
  // caller that failed.
  argumentField = [&](const llvm::Argument *A, int64_t off) -> Status {
    if (!A)
      return bare();
    Status acc;
    bool site = false;
    bool bad = false;
    auto take = [&](Status one) {
      if (!one.any && one.args.empty())
        return;
      bool ent = false;
      bool glob = false;
      for (const auto &a : one.args) {
        if (a.second >= 0)
          ent = true;
        else
          glob = true;
      }
      if (one.open || one.local || one.hasConst || one.none || !ent || glob) {
        bad = true;
        if (!ent)
          return;
      }
      std::set<std::pair<std::string, int>> keep;
      for (const auto &a : one.args)
        if (a.second >= 0)
          keep.insert(a);
      site = true;
      acc.any = true;
      acc.args.insert(keep.begin(), keep.end());
    };
    auto calls = sites.find(A->getParent());
    if (calls != sites.end()) {
      for (const llvm::CallBase *C : calls->second) {
        if (!C || !cone(C->getFunction()) || A->getArgNo() >= C->arg_size())
          continue;
        if (const llvm::CallBase *via = boundCall(A->getParent())) {
          if (C != via)
            continue;
        } else if (!entryCall(C->getFunction(), A->getParent())) {
          continue;
        }
        if (activation && activates(activation, A->getParent()) && C != activation)
          continue;
        const llvm::Value *V = C->getArgOperand(A->getArgNo());
        int64_t extra = 0;
        std::unordered_set<const llvm::Value *> seenV;
        while (V && seenV.insert(V).second) {
          V = V->stripPointerCasts();
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63)) {
              V = nullptr;
              break;
            }
            extra += ap.getSExtValue();
            V = G->getPointerOperand();
            continue;
          }
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            const llvm::Value *st = AI ? spillValue(AI) : nullptr;
            if (!st) {
              V = nullptr;
              break;
            }
            V = st;
            continue;
          }
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
            if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
              V = I->getOperand(0);
              continue;
            }
          }
          break;
        }
        const auto *B = llvm::dyn_cast_or_null<llvm::Argument>(V);
        if (!B || !cone(B->getParent()))
          continue;
        take(readField(B, off + extra));
      }
    }
    if (!site || acc.args.empty())
      return bare();
    Status out;
    out.any = true;
    out.open = bad;
    out.args = acc.args;
    return out;
  };

  ground = [&](Status s, const llvm::CallBase *C, const llvm::Value *actual) -> Status {
    std::unordered_set<const llvm::Value *> seenSlot;
    while (s.local && !s.open && !s.hasConst && !s.none && s.args.empty() && s.slot && s.offKnown) {
      if (!seenSlot.insert(s.slot).second)
        return opened();
      const llvm::Instruction *use = s.at ? s.at : C;
      if (!use || slotFn(s.slot) != use->getFunction())
        return opened();
      Status bytes = memRoots(use, s.slot, true, nullptr);
      if (!bytes.any)
        return nothing();
      s = bytes;
    }
    if (s.local && s.args.empty() && !s.open && !s.hasConst && !s.none)
      return opened();
    return s;
  };

  auto pureEntry = [](const Status &s) {
    if (!s.any || s.open || s.local || s.hasConst || s.none)
      return false;
    bool ent = false;
    for (const auto &a : s.args) {
      if (a.second < 0)
        return false;
      ent = true;
    }
    return ent;
  };
  auto pureGlobal = [](const Status &s) {
    if (!s.any || s.open || s.local || s.hasConst || s.none)
      return false;
    bool glob = false;
    for (const auto &a : s.args) {
      if (a.second >= 0)
        return false;
      glob = true;
    }
    return glob;
  };
  // The object a pointer refers to, once it reduces to one parameter of this
  // entry. Two loads of the same field of that parameter are the same object.
  // A getter returns the pointer stored in the object it was given.
  struct OKey {
    int arg = -1;
    int64_t off = 0;
    bool pointee = false;
    bool operator==(const OKey &o) const {
      return arg == o.arg && off == o.off && pointee == o.pointee;
    }
  };
  struct OHash {
    size_t operator()(const OKey &k) const {
      return (static_cast<size_t>(k.arg) * 1315423911u) ^
             (static_cast<size_t>(k.off) << 1) ^ (k.pointee ? 1u : 0u);
    }
  };
  struct Frame {
    const llvm::CallBase *call = nullptr;
    const Frame *outer = nullptr;
  };
  std::function<std::optional<OKey>(const llvm::Value *, const Frame *, bool,
                                    std::unordered_set<const llvm::Value *> &)>
      orig;
  orig = [&](const llvm::Value *V, const Frame *subst, bool pointee,
             std::unordered_set<const llvm::Value *> &seen) -> std::optional<OKey> {
    if (!V)
      return std::nullopt;
    V = V->stripPointerCasts();
    if (!seen.insert(V).second)
      return std::nullopt;
    struct Erase {
      std::unordered_set<const llvm::Value *> &s;
      const llvm::Value *v;
      ~Erase() { s.erase(v); }
    } erase{seen, V};
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      auto k = orig(G->getPointerOperand(), subst, false, seen);
      if (!k)
        return std::nullopt;
      llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
      if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
        return std::nullopt;
      k->off += ap.getSExtValue();
      if (pointee)
        k->pointee = true;
      return k;
    }
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      for (const Frame *f = subst; f; f = f->outer) {
        const llvm::Function *cf = f->call->getCalledFunction();
        if (cf && A->getParent() == cf && A->getArgNo() < f->call->arg_size())
          return orig(f->call->getArgOperand(A->getArgNo()), f->outer, pointee, seen);
      }
      Status st = walk(A);
      // Another caller that does not reduce leaves the formal open. The one
      // parameter of this entry that remains is still the object.
      if (!st.any || st.local || st.hasConst || st.none || st.args.size() != 1)
        return std::nullopt;
      auto it = st.args.begin();
      if (it->first != entryName || it->second < 0)
        return std::nullopt;
      OKey k;
      k.arg = it->second;
      k.pointee = pointee;
      return k;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      const llvm::Value *addr = L->getPointerOperand()->stripPointerCasts();
      auto k = orig(addr, subst, false, seen);
      if (!k)
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(addr)) {
          const llvm::Value *only = nullptr;
          int n = 0;
          for (const llvm::Use &U : C->args()) {
            if (!U.get()->getType()->isPointerTy())
              continue;
            only = U.get();
            ++n;
          }
          if (n == 1)
            k = orig(only, subst, false, seen);
        }
      if (!k)
        return std::nullopt;
      k->pointee = true;
      return k;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = C->getCalledFunction();
      if (!D || D->isDeclaration())
        return std::nullopt;
      const llvm::Value *rv = nullptr;
      bool saw = false;
      for (const llvm::BasicBlock &BB : *D) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue())
          continue;
        const llvm::Value *one = R->getReturnValue()->stripPointerCasts();
        if (!saw) {
          rv = one;
          saw = true;
        } else if (rv != one) {
          return std::nullopt;
        }
      }
      if (!rv)
        return std::nullopt;
      Frame frame{C, subst};
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(rv))
        return orig(Ld, &frame, pointee, seen);
      return orig(rv, &frame, pointee, seen);
    }
    if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
      if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I))
        return orig(I->getOperand(0), subst, pointee, seen);
    }
    return std::nullopt;
  };
  auto origin = [&](const llvm::Value *V) {
    std::unordered_set<const llvm::Value *> seen;
    return orig(V, nullptr, false, seen);
  };
  auto onlyEntry = [](Status bytes) {
    Status only;
    bool ent = false;
    for (const auto &a : bytes.args)
      if (a.second >= 0)
        ent = true;
    if (!ent)
      return only;
    only.any = true;
    only.open = bytes.open || bytes.local || bytes.hasConst || bytes.none;
    for (const auto &a : bytes.args)
      if (a.second >= 0)
        only.args.insert(a);
    return only;
  };

  // A field of an argument, after callsites that forward the argument
  // itself have been identified. The index is the field, not a layout guess:
  // only a constant GEP index sequence is a field.
  struct FKey {
    const llvm::Argument *root = nullptr;
    const llvm::Type *ty = nullptr;
    std::vector<uint64_t> idx;
    bool operator<(const FKey &o) const {
      if (ty != o.ty)
        return ty < o.ty;
      if (root != o.root)
        return root < o.root;
      return idx < o.idx;
    }
  };
  std::map<const llvm::Argument *, const llvm::Argument *> argParent;
  bool fieldBuilt = false;
  std::map<FKey, std::vector<const llvm::Value *>> fieldComp;
  std::set<FKey> fieldBad;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> allSites;
  std::unordered_map<std::string, std::unordered_set<std::string>> seenIn;
  std::unordered_map<std::string, std::unordered_set<std::string>> seenOpen;
  std::unordered_map<std::string, std::unordered_set<std::string>> seenWit;
  // The witness walk asks where memory comes from: which object a pointer
  // points at, and which stores write that object. Those questions are
  // answered by one points-to analysis over both modules, by allocation
  // site and byte offset, shared by every entry. A call through a pointer
  // reaches the functions the solution puts in that pointer, and nothing
  // else: binding every function of the call's type as well would merge
  // every object such calls are handed into one. Its bodies are looked up
  // across the two modules; its harness formals are the exports' formals.
  std::unique_ptr<Points> points;
  auto pointsOf = [&]() -> Points & {
    if (!points) {
      Points::Hooks h;
      h.body = [&](const llvm::Function *F) { return definedBody(F); };
      // Export pointer formals contain one harness object, so a store of
      // a function or of a field (a flag, a pointer) through one export
      // is visible at the same offset of any other export. Other functions
      // are entered only when a query's value flows through them.
      h.harness = [&](const llvm::Function *F) {
        return F && F->getParent() == &M && strongExport(F);
      };
      h.allocates = [](const llvm::CallBase *C) { return allocates(C); };
      h.allocSize = [](const llvm::CallBase *C) { return allocSize(C); };
      h.allocSource = [](const llvm::CallBase *C) { return allocSource(C); };
      h.allocSizeArgs = [](const llvm::CallBase *C) { return allocSizeArgs(C); };
      h.byteCopy = [](const llvm::CallBase *C, const llvm::Value *&d, const llvm::Value *&s) {
        return byteCopy(C, d, s);
      };
      points = std::make_unique<Points>(M, upstream, std::move(h));
      // Queries solve the values they touch. There is no whole-module pass.
      points->saturate();
    }
    return *points;
  };
  // The witness of a chop actual depends on that value alone; every export
  // whose walk reaches the same call shares it.
  std::unordered_map<const llvm::Value *, std::map<std::pair<std::string, int>, int>> witMemo;
  for (size_t id = 0; id < entryFns.size(); ++id) {
    ei = static_cast<int>(id);
    entryFn = entryFns[id];
    entryName = entryNames[id];
    entryReach.clear();
    // The value memo is keyed by the entry. Keeping every entry's memo
    // retains a copy of the module for each export.
    memo.clear();
    active.clear();
    bool indexed = false;
    std::unordered_map<OKey, Status, OHash> byOrigin;
    auto handedBytes = [&](const OKey &key) {
      if (!indexed) {
        indexed = true;
        for (const llvm::Function *F : spaceOrd) {
          if (!cone(F))
            continue;
          for (const llvm::Instruction &I : llvm::instructions(*F)) {
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB || CB->isInlineAsm())
              continue;
            for (const llvm::Use &U : CB->args()) {
              if (!U.get()->getType()->isPointerTy())
                continue;
              auto k = origin(U.get());
              if (!k)
                continue;
              Status got = onlyEntry(fromArgs(CB));
              if (!got.any)
                continue;
              auto it = byOrigin.find(*k);
              if (it == byOrigin.end())
                byOrigin.emplace(*k, got);
              else
                it->second = meet(it->second, got);
            }
          }
        }
      }
      auto it = byOrigin.find(key);
      if (it == byOrigin.end())
        return bare();
      return it->second;
    };
    // Bytes written into the object a pointer denotes. Identity stays on
    // the pointer. A declaration has no body, so another pointer it is handed
    // is a value written into the object. A defined function returns the
    // pointer it stored, and the calls it makes on that pointer write their
    // other arguments into it. A field of one actual is the same field in
    // every function that actual is passed to. A pointer that is already an
    // entry argument is not a copy.
    auto copied = [&](const llvm::Value *start) {
      Status acc;
      std::unordered_set<const llvm::Value *> seen;
      std::function<void(const llvm::Value *, bool)> flow;
      auto calleesOf = [&](const llvm::CallBase *C) {
        std::vector<const llvm::Function *> out;
        auto it = resolved.find(C);
        if (it != resolved.end())
          return it->second;
        if (const llvm::Function *D = asFunction(C->getCalledOperand()))
          out.push_back(D);
        return out;
      };
      auto derived = [&](const llvm::Value *V, const llvm::Value *Root) {
        if (!V || !Root)
          return false;
        std::unordered_set<const llvm::Value *> seenV;
        while (V && seenV.insert(V).second) {
          if (V == Root || V->stripPointerCasts() == Root->stripPointerCasts())
            return true;
          V = V->stripPointerCasts();
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            V = G->getPointerOperand();
            continue;
          }
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            // A spill reloads this pointer. A load through it is a different pointer.
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            const llvm::Value *st = AI ? spillValue(AI) : nullptr;
            if (!st)
              return false;
            V = st;
            continue;
          }
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
            if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
              V = I->getOperand(0);
              continue;
            }
          }
          break;
        }
        return false;
      };
      auto isChop = [&](const llvm::CallBase *C) {
        for (const llvm::Function *D : calleesOf(C)) {
          if (!D)
            continue;
          auto init = initialOf.find(show(D));
          if (init != initialOf.end() && init->second.count(entryName))
            return true;
        }
        return false;
      };
      const char *why = "?";
      auto note = [&](const llvm::Value *V) {
        if (!V || !V->getType()->isPointerTy())
          return;
        Status hard = walk(V);
        if (pureEntry(hard))
          return;
        flow(V, false);
      };
      std::function<void(const llvm::Function *, unsigned, const llvm::CallBase *,
                         std::unordered_set<const llvm::Function *> &)>
          dig;
      auto readable = [&](const llvm::Function *D) -> const llvm::Function * {
        const llvm::Function *B = definedBody(D);
        if (!B || B->isDeclaration())
          return nullptr;
        // A body in this module counts only inside the entry's cone. A body
        // that exists only in the upstream module is the declaration's function.
        if (B->getParent() == &M && !cone(B))
          return nullptr;
        return B;
      };
      dig = [&](const llvm::Function *D, unsigned formalNo, const llvm::CallBase *binding,
                std::unordered_set<const llvm::Function *> &seenFn) {
        D = readable(D);
        if (!D || !binding || formalNo >= D->arg_size() || !seenFn.insert(D).second)
          return;
        const llvm::Argument *FA = D->getArg(formalNo);
        auto asFormal = [&](const llvm::Value *P) -> const llvm::Argument * {
          P = P->stripPointerCasts();
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(P)) {
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (const llvm::Value *st = AI ? spillValue(AI) : nullptr)
              P = st->stripPointerCasts();
          }
          const auto *BA = llvm::dyn_cast<llvm::Argument>(P);
          return BA && BA->getParent() == D ? BA : nullptr;
        };
        for (const llvm::Instruction &I : llvm::instructions(*D)) {
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            if (!SI->getValueOperand()->getType()->isPointerTy() || !derived(SI->getPointerOperand(), FA) ||
                derived(SI->getValueOperand(), FA))
              continue;
            const llvm::Value *src = SI->getValueOperand();
            std::unordered_set<const llvm::Value *> seenP;
            std::function<const llvm::Value *(const llvm::Value *)> peel;
            peel = [&](const llvm::Value *P) -> const llvm::Value * {
              while (P && seenP.insert(P).second) {
                P = P->stripPointerCasts();
                if (llvm::isa<llvm::Argument>(P))
                  return P;
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(P)) {
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
                  if (const llvm::Value *st = AI ? spillValue(AI) : nullptr) {
                    P = st;
                    continue;
                  }
                  const llvm::Value *addr = L->getPointerOperand()->stripPointerCasts();
                  if (llvm::isa<llvm::CallBase>(addr)) {
                    P = addr;
                    continue;
                  }
                  return P;
                }
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P)) {
                  P = G->getPointerOperand();
                  continue;
                }
                if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(P)) {
                  for (const llvm::Function *G0 : calleesOf(RC)) {
                    const llvm::Function *G = readable(G0);
                    if (!G)
                      continue;
                    for (const llvm::BasicBlock &BB : *G) {
                      const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                      if (!R || !R->getReturnValue())
                        continue;
                      if (const llvm::Argument *BA = llvm::dyn_cast<llvm::Argument>(peel(R->getReturnValue())))
                        if (BA->getParent() == G && BA->getArgNo() < RC->arg_size())
                          return peel(RC->getArgOperand(BA->getArgNo()));
                    }
                  }
                  return P;
                }
                break;
              }
              return P;
            };
            const llvm::Value *peeled = peel(src);
            if (const auto *BA = llvm::dyn_cast<llvm::Argument>(peeled)) {
              if (BA->getParent() == D && BA->getArgNo() < binding->arg_size()) {
                why = "dig-arg";
                note(binding->getArgOperand(BA->getArgNo()));
                continue;
              }
            }
            why = "dig-val";
            note(SI->getValueOperand());
            continue;
          }
          const auto *IC = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!IC || IC->isInlineAsm() || isChop(IC))
            continue;
          const llvm::Value *cdst = nullptr;
          const llvm::Value *csrc = nullptr;
          if (byteCopy(IC, cdst, csrc) && derived(cdst, FA) && csrc->getType()->isPointerTy() &&
              !derived(csrc, FA)) {
            if (const auto *BA = llvm::dyn_cast<llvm::Argument>(csrc->stripPointerCasts())) {
              if (BA->getParent() == D && BA->getArgNo() < binding->arg_size()) {
                why = "dig-arg";
                note(binding->getArgOperand(BA->getArgNo()));
                continue;
              }
            }
            why = "dig-val";
            note(csrc);
            continue;
          }
          int objArg = -1;
          for (unsigned ai = 0; ai < IC->arg_size(); ++ai)
            if (derived(IC->getArgOperand(ai), FA))
              objArg = static_cast<int>(ai);
          if (objArg < 0)
            continue;
          for (const llvm::Function *G0 : calleesOf(IC)) {
            const llvm::Function *G = readable(G0);
            if (!G)
              continue;
            dig(G, static_cast<unsigned>(objArg), IC, seenFn);
          }
        }
      };
      auto fieldOff = [&](const llvm::Value *Ptr, int64_t &off, const llvm::Value *&base) {
        off = 0;
        base = Ptr ? Ptr->stripPointerCasts() : nullptr;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(base)) {
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
            return false;
          off = ap.getSExtValue();
          base = G->getPointerOperand()->stripPointerCasts();
        }
        return base != nullptr;
      };
      // A reload of an argument is that argument. A field of the reload is
      // the same field of the argument.
      auto argField = [&](const llvm::Value *Ptr, int64_t &off) -> const llvm::Argument * {
        off = 0;
        const llvm::Value *base = nullptr;
        if (!fieldOff(Ptr, off, base))
          return nullptr;
        std::unordered_set<const llvm::Value *> seenB;
        while (base && seenB.insert(base).second) {
          base = base->stripPointerCasts();
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(base))
            return A;
          const auto *L = llvm::dyn_cast<llvm::LoadInst>(base);
          if (!L)
            return nullptr;
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          const llvm::Value *st = AI ? spillValue(AI) : nullptr;
          if (!st)
            return nullptr;
          int64_t extra = 0;
          const llvm::Value *nb = nullptr;
          if (!fieldOff(st, extra, nb))
            return nullptr;
          off += extra;
          base = nb;
        }
        return nullptr;
      };
      flow = [&](const llvm::Value *V, bool root) {
        if (!V || !seen.insert(V).second)
          return;
        V = V->stripPointerCasts();
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          const llvm::Value *ptr = L->getPointerOperand()->stripPointerCasts();
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(ptr)) {
            if (const llvm::Value *st = spillValue(AI))
              flow(st, root);
            return;
          }
          int64_t off = 0;
          const llvm::Argument *A = argField(ptr, off);
          if (A) {
            const llvm::Function *PF = A->getParent();
            auto sit = sites.find(PF);
            if (sit == sites.end())
              return;
            for (const llvm::CallBase *C : sit->second) {
              if (!C || A->getArgNo() >= C->arg_size())
                continue;
              const llvm::Value *actual = C->getArgOperand(A->getArgNo());
              flow(actual, root);
              const llvm::Function *Caller = C->getFunction();
              if (!Caller || !actual)
                continue;
              for (const llvm::Instruction &SI : llvm::instructions(*Caller)) {
                const auto *SC = llvm::dyn_cast<llvm::CallBase>(&SI);
                if (!SC || SC == C || SC->isInlineAsm())
                  continue;
                int which = -1;
                for (unsigned ai = 0; ai < SC->arg_size(); ++ai)
                  if (derived(SC->getArgOperand(ai), actual))
                    which = static_cast<int>(ai);
                if (which < 0)
                  continue;
                for (const llvm::Function *G : calleesOf(SC)) {
                  if (!G || G->isDeclaration() || !cone(G) || which >= static_cast<int>(G->arg_size()))
                    continue;
                  const llvm::Argument *FA = G->getArg(static_cast<unsigned>(which));
                  for (const llvm::Instruction &GI : llvm::instructions(*G)) {
                    const auto *GL = llvm::dyn_cast<llvm::LoadInst>(&GI);
                    if (!GL)
                      continue;
                    int64_t goff = 0;
                    const llvm::Argument *gb = argField(GL->getPointerOperand(), goff);
                    if (gb != FA || goff != off)
                      continue;
                    for (const llvm::User *U : GL->users()) {
                      const auto *UC = llvm::dyn_cast<llvm::CallBase>(U);
                      if (!UC || UC->isInlineAsm() || isChop(UC))
                        continue;
                      for (const llvm::Use &Arg : UC->args()) {
                        if (Arg.get() == GL || !Arg.get()->getType()->isPointerTy())
                          continue;
                        why = "sibling";
                        note(Arg.get());
                      }
                    }
                  }
                }
              }
            }
            return;
          }
          int64_t ignored = 0;
          const llvm::Value *base = nullptr;
          if (fieldOff(ptr, ignored, base))
            flow(base, root);
          return;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
          if (isChop(C))
            return;
          for (const llvm::Function *D0 : calleesOf(C)) {
            const llvm::Function *D = readable(D0);
            if (!D)
              continue;
            std::unordered_set<const llvm::Value *> seenF;
            std::function<const llvm::Argument *(const llvm::Value *)> fromFormal;
            fromFormal = [&](const llvm::Value *P) -> const llvm::Argument * {
              while (P && seenF.insert(P).second) {
                P = P->stripPointerCasts();
                if (const auto *FA = llvm::dyn_cast<llvm::Argument>(P))
                  return FA->getParent() == D ? FA : nullptr;
                if (const auto *RL = llvm::dyn_cast<llvm::LoadInst>(P)) {
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(RL->getPointerOperand()->stripPointerCasts());
                  if (const llvm::Value *st = AI ? spillValue(AI) : nullptr) {
                    P = st;
                    continue;
                  }
                  P = RL->getPointerOperand();
                  continue;
                }
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P)) {
                  P = G->getPointerOperand();
                  continue;
                }
                if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(P)) {
                  for (const llvm::Use &Arg : RC->args())
                    if (Arg.get()->getType()->isPointerTy())
                      if (const llvm::Argument *FA = fromFormal(Arg.get()))
                        return FA;
                  return nullptr;
                }
                break;
              }
              return nullptr;
            };
            for (const llvm::BasicBlock &BB : *D) {
              const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
              if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                continue;
              seenF.clear();
              if (const llvm::Argument *FA = fromFormal(R->getReturnValue())) {
                if (FA->getArgNo() < C->arg_size())
                  flow(C->getArgOperand(FA->getArgNo()), root);
              }
              const llvm::AllocaInst *slot = nullptr;
              const llvm::Value *cur = R->getReturnValue()->stripPointerCasts();
              std::unordered_set<const llvm::Value *> seenR;
              while (cur && seenR.insert(cur).second) {
                if (const auto *RL = llvm::dyn_cast<llvm::LoadInst>(cur)) {
                  if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(RL->getPointerOperand()->stripPointerCasts()))
                    slot = AI;
                  cur = RL->getPointerOperand();
                  continue;
                }
                cur = cur->stripPointerCasts();
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
                  cur = G->getPointerOperand();
                  continue;
                }
                break;
              }
              if (!slot)
                continue;
              std::vector<const llvm::AllocaInst *> slots{slot};
              std::unordered_set<const llvm::AllocaInst *> seenSlot{slot};
              for (size_t si = 0; si < slots.size(); ++si) {
                for (const llvm::User *U : slots[si]->users()) {
                  const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
                  if (!SI || SI->getPointerOperand()->stripPointerCasts() != slots[si])
                    continue;
                  const auto *SL = llvm::dyn_cast<llvm::LoadInst>(SI->getValueOperand()->stripPointerCasts());
                  if (!SL)
                    continue;
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(SL->getPointerOperand()->stripPointerCasts());
                  if (AI && seenSlot.insert(AI).second)
                    slots.push_back(AI);
                }
                for (const llvm::Instruction &I : llvm::instructions(*D)) {
                  const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                  if (!SI)
                    continue;
                  const auto *SL = llvm::dyn_cast<llvm::LoadInst>(SI->getValueOperand()->stripPointerCasts());
                  if (!SL || SL->getPointerOperand()->stripPointerCasts() != slots[si])
                    continue;
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(SI->getPointerOperand()->stripPointerCasts());
                  if (AI && seenSlot.insert(AI).second)
                    slots.push_back(AI);
                }
              }
              for (const llvm::Instruction &I : llvm::instructions(*D)) {
                const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
                if (!UC || UC->isInlineAsm() || isChop(UC))
                  continue;
                bool handed = false;
                for (const llvm::AllocaInst *S : slots)
                  for (const llvm::Use &Arg : UC->args())
                    if (derived(Arg.get(), S))
                      handed = true;
                if (!handed)
                  continue;
                for (unsigned ai = 0; ai < UC->arg_size(); ++ai) {
                  const llvm::Value *Arg = UC->getArgOperand(ai);
                  if (!Arg->getType()->isPointerTy())
                    continue;
                  bool self = false;
                  for (const llvm::AllocaInst *S : slots)
                    if (derived(Arg, S))
                      self = true;
                  if (self)
                    continue;
                  const llvm::Value *sp = Arg->stripPointerCasts();
                  if (const auto *SL = llvm::dyn_cast<llvm::LoadInst>(sp)) {
                    const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(SL->getPointerOperand()->stripPointerCasts());
                    if (AI)
                      if (const llvm::Value *st = spillValue(AI))
                        sp = st->stripPointerCasts();
                  }
                  if (const auto *FA = llvm::dyn_cast<llvm::Argument>(sp)) {
                    if (FA->getParent() == D && FA->getArgNo() < C->arg_size()) {
                      why = "return-arg";
                      note(C->getArgOperand(FA->getArgNo()));
                    }
                    continue;
                  }
                  why = "return-other";
                  note(Arg);
                }
              }
            }
          }
          return;
        }
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
          auto sit = sites.find(A->getParent());
          if (sit == sites.end())
            return;
          for (const llvm::CallBase *C : sit->second)
            if (C && A->getArgNo() < C->arg_size())
              flow(C->getArgOperand(A->getArgNo()), root);
          return;
        }
        for (const llvm::User *U : V->users()) {
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
            if (derived(SI->getPointerOperand(), V) && SI->getValueOperand()->getType()->isPointerTy() &&
                !derived(SI->getValueOperand(), V)) {
              why = "store";
              note(SI->getValueOperand());
            }
            continue;
          }
          const auto *UC = llvm::dyn_cast<llvm::CallBase>(U);
          if (!UC || UC->isInlineAsm())
            continue;
          const llvm::Value *dst = nullptr;
          const llvm::Value *src = nullptr;
          if (byteCopy(UC, dst, src) && derived(dst, V) && src->getType()->isPointerTy() && !derived(src, V)) {
            why = "store";
            note(src);
          }
          if (isChop(UC))
            continue;
          bool handed = false;
          for (const llvm::Use &Arg : UC->args())
            if (derived(Arg.get(), V))
              handed = true;
          if (!handed)
            continue;
          for (const llvm::Function *D0 : calleesOf(UC)) {
            const llvm::Function *D = readable(D0);
            if (!D)
              continue;
            int which = -1;
            for (unsigned ai = 0; ai < UC->arg_size(); ++ai)
              if (derived(UC->getArgOperand(ai), V))
                which = static_cast<int>(ai);
            if (which < 0 || which >= static_cast<int>(D->arg_size()))
              continue;
            std::unordered_set<const llvm::Function *> seenFn;
            dig(D, static_cast<unsigned>(which), UC, seenFn);
          }
        }
      };
      flow(start, true);
      return onlyEntry(acc);
    };
    // The first pass stores field summaries. A summary that is still open was
    // taken while a callee was on the stack, so it is dropped and the chop
    // actuals are walked again with those summaries in place.
    auto provedMemo = [](const Status &s) {
      if (!s.any || s.open || s.local || s.hasConst || s.none)
        return false;
      for (const auto &a : s.args)
        if (a.second >= 0)
          return true;
      return false;
    };
    // The bits of an unwritten inline field are a function of the object that
    // holds them. A later load through a pointer field is a different object
    // and is not these bits. This is used only to decide whether a branch
    // condition is predictable. It is not a chop-argument proof.
    struct FieldRoot {
      const llvm::Argument *arg = nullptr;
      int64_t off = 0;
      bool field = false;
    };
    auto pointerRoot = [&](const llvm::Value *V) -> std::optional<FieldRoot> {
      int64_t off = 0;
      bool field = false;
      std::unordered_set<const llvm::Value *> seenR;
      while (V && seenR.insert(V).second) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
          field = true;
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(DL, ap) || !ap.isSignedIntN(63))
            return std::nullopt;
          off += ap.getSExtValue();
          V = G->getPointerOperand();
          continue;
        }
        V = V->stripPointerCasts();
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
          FieldRoot r;
          r.arg = A;
          r.off = field ? off : 0;
          r.field = field;
          return r;
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          const llvm::Value *st = AI ? spillValue(AI) : nullptr;
          if (!st)
            return std::nullopt;
          V = st;
          continue;
        }
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
          if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            V = I->getOperand(0);
            continue;
          }
        }
        break;
      }
      return std::nullopt;
    };
    auto mayWriteField = [&](const llvm::Argument *A, int64_t off) -> bool {
      const llvm::Function *Fn = A ? A->getParent() : nullptr;
      if (!Fn || Fn->isDeclaration())
        return true;
      for (const llvm::Instruction &I : llvm::instructions(*Fn)) {
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          const llvm::Value *ptr = SI->getPointerOperand()->stripPointerCasts();
          if (llvm::isa<llvm::AllocaInst>(ptr))
            continue;
          auto r = pointerRoot(SI->getPointerOperand());
          if (!r)
            return true;
          if (r->arg != A)
            continue;
          if (!r->field || r->off == off)
            return true;
        } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
          if (CB->isInlineAsm() || CB->onlyReadsMemory() || CB->doesNotAccessMemory())
            continue;
          for (unsigned ai = 0; ai < CB->arg_size(); ++ai) {
            if (CB->paramHasAttr(ai, llvm::Attribute::ReadOnly) ||
                CB->paramHasAttr(ai, llvm::Attribute::ReadNone))
              continue;
            const llvm::Value *op = CB->getArgOperand(ai);
            if (!op->getType()->isPointerTy())
              continue;
            auto r = pointerRoot(op);
            if (!r)
              return true;
            if (r->arg != A)
              continue;
            if (!r->field || r->off == off) {
              if (writesFormal(CB->getCalledFunction(), ai) != 0)
                return true;
            }
          }
        }
      }
      return false;
    };
    using PredEnv = std::unordered_map<const llvm::Function *, const llvm::CallBase *>;
    std::function<bool(const llvm::Value *, const PredEnv &, int, std::unordered_set<const llvm::Value *> &)> pred;
    pred = [&](const llvm::Value *V, const PredEnv &env, int depth,
               std::unordered_set<const llvm::Value *> &seen) -> bool {
      if (!V)
        return false;
      if (llvm::isa<llvm::UndefValue>(V) || llvm::isa<llvm::PoisonValue>(V))
        return false;
      if (llvm::isa<llvm::Constant>(V))
        return true;
      if (!seen.insert(V).second)
        return false;
      struct Guard {
        std::unordered_set<const llvm::Value *> &s;
        const llvm::Value *v;
        ~Guard() { s.erase(v); }
      } guard{seen, V};
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == entryFn)
          return true;
        auto it = env.find(A->getParent());
        if (it == env.end() || A->getArgNo() >= it->second->arg_size())
          return false;
        PredEnv up = env;
        up.erase(A->getParent());
        return pred(it->second->getArgOperand(A->getArgNo()), up, depth + 1, seen);
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          const llvm::Value *st = spillValue(AI);
          return st && pred(st, env, depth + 1, seen);
        }
        auto r = pointerRoot(L->getPointerOperand());
        if (!r || !r->arg)
          return false;
        PredEnv up = env;
        if (!pred(r->arg, up, depth + 1, seen))
          return false;
        return !mayWriteField(r->arg, r->off);
      }
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (C->isInlineAsm() || C->getType()->isVoidTy())
          return false;
        std::vector<const llvm::Function *> targets;
        if (const llvm::Function *D = C->getCalledFunction())
          targets.push_back(D);
        else {
          auto it = resolved.find(C);
          if (it != resolved.end())
            targets = it->second;
        }
        if (targets.empty())
          return false;
        for (const llvm::Function *D0 : targets) {
          const llvm::Function *D = definedBody(D0);
          if (!D || D->isDeclaration())
            return false;
          PredEnv down = env;
          down[D] = C;
          bool any = false;
          for (const llvm::BasicBlock &BB : *D) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
            if (!R || !R->getReturnValue())
              continue;
            any = true;
            if (!pred(R->getReturnValue(), down, depth + 1, seen))
              return false;
          }
          if (!any)
            return false;
        }
        return true;
      }
      if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        if (P->getNumIncomingValues() == 0)
          return false;
        for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
          if (!pred(P->getIncomingValue(i), env, depth + 1, seen))
            return false;
        const llvm::Value *first = P->getIncomingValue(0);
        bool same = true;
        for (unsigned i = 1; i < P->getNumIncomingValues(); ++i)
          if (P->getIncomingValue(i) != first)
            same = false;
        if (same)
          return true;
        for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
          const llvm::BasicBlock *B = P->getIncomingBlock(i);
          const llvm::Value *cond = nullptr;
          std::unordered_set<const llvm::BasicBlock *> up;
          while (B && up.insert(B).second) {
            const llvm::Instruction *T = B->getTerminator();
            if (const auto *Br = llvm::dyn_cast<llvm::BranchInst>(T)) {
              if (Br->isConditional()) {
                cond = Br->getCondition();
                break;
              }
            } else if (const auto *Sw = llvm::dyn_cast<llvm::SwitchInst>(T)) {
              cond = Sw->getCondition();
              break;
            }
            if (!T || T->getNumSuccessors() != 1)
              break;
            B = B->getSinglePredecessor();
          }
          if (!cond || !pred(cond, env, depth + 1, seen))
            return false;
        }
        return true;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V))
        return pred(Sel->getCondition(), env, depth + 1, seen) &&
               pred(Sel->getTrueValue(), env, depth + 1, seen) &&
               pred(Sel->getFalseValue(), env, depth + 1, seen);
      if (const auto *IC = llvm::dyn_cast<llvm::ICmpInst>(V))
        return pred(IC->getOperand(0), env, depth + 1, seen) &&
               pred(IC->getOperand(1), env, depth + 1, seen);
      if (const auto *FC = llvm::dyn_cast<llvm::FCmpInst>(V))
        return pred(FC->getOperand(0), env, depth + 1, seen) &&
               pred(FC->getOperand(1), env, depth + 1, seen);
      if (const auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V))
        return pred(BO->getOperand(0), env, depth + 1, seen) &&
               pred(BO->getOperand(1), env, depth + 1, seen);
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I))
          return pred(I->getOperand(0), env, depth + 1, seen);
      }
      return false;
    };
    struct Jdg {
      const llvm::CallBase *C = nullptr;
      std::string chop;
      int chopArg = 0;
      Status s;
      int kind = 0;
    };
    auto classify = [&](bool record) {
    std::vector<Jdg> jdgs;
    // A getter of a local object returns the pointer planted in it. A fresh
    // object built from one other object carries that object's bytes. Stopping
    // at the getter would drop the entry parameter those bytes belong to.
    auto pureNone = [](const Status &st) {
      return st.any && st.none && !st.open && !st.local && !st.hasConst && st.args.empty();
    };
    auto planted = [&](const llvm::Value *V) -> const llvm::Value * {
      const auto *Call = llvm::dyn_cast<llvm::CallBase>(V);
      if (!Call || !Call->getType()->isPointerTy())
        return nullptr;
      const llvm::AllocaInst *AI = nullptr;
      for (const llvm::Use &U : Call->args()) {
        const auto *A = llvm::dyn_cast<llvm::AllocaInst>(U.get()->stripPointerCasts());
        if (A) {
          AI = A;
          break;
        }
      }
      if (!AI)
        return nullptr;
      const llvm::Value *found = nullptr;
      for (const llvm::User *Usr : AI->users()) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(Usr);
        if (!CB || CB == Call)
          continue;
        for (const llvm::Use &A : CB->args()) {
          const llvm::Value *Op = A.get();
          if (!Op->getType()->isPointerTy() || Op->stripPointerCasts() == AI)
            continue;
          if (llvm::isa<llvm::Constant>(Op) || llvm::isa<llvm::AllocaInst>(Op->stripPointerCasts()))
            continue;
          if (found && found != Op)
            return nullptr;
          found = Op;
        }
      }
      return found;
    };
    // The bytes a pointer denotes. The address of a fresh object is not an
    // entry parameter. A load reads the pointer stored in that cell. Every
    // store to the cell must be the same entry parameter. A cell with no
    // store belongs to the object that contains it. A formal belongs to the
    // actual this entry passes.
    auto peel = [](const llvm::Value *P) -> const llvm::Value * {
      std::unordered_set<const llvm::Value *> sc;
      while (P && sc.insert(P).second) {
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(P)) {
          if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            P = I->getOperand(0);
            continue;
          }
        }
        if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(P)) {
          if (CE->isCast()) {
            P = CE->getOperand(0);
            continue;
          }
        }
        break;
      }
      return P;
    };
    auto derivedFrom = [&](const llvm::Value *Val, const llvm::Value *Root) {
      if (!Val || !Root)
        return false;
      std::unordered_set<const llvm::Value *> sc;
      while (Val && sc.insert(Val).second) {
        Val = peel(Val);
        if (!Val)
          return false;
        if (Val == Root)
          return true;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(Val)) {
          Val = G->getPointerOperand();
          continue;
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(Val)) {
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!AI)
            return false;
          const llvm::Value *st = spillValue(AI);
          if (!st)
            return false;
          Val = st;
          continue;
        }
        break;
      }
      return false;
    };
    struct Cell {
      const llvm::Value *root = nullptr;
      std::vector<uint64_t> idx;
    };
    auto cellOf = [&](const llvm::Value *addr) -> Cell {
      Cell c;
      const llvm::Value *cur = peel(addr);
      std::unordered_set<const llvm::Value *> sc;
      while (cur && sc.insert(cur).second) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
          bool all = true;
          std::vector<uint64_t> add;
          for (unsigned oi = 1; oi < G->getNumOperands(); ++oi) {
            const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(oi));
            if (!CI) {
              all = false;
              break;
            }
            add.push_back(CI->getZExtValue());
          }
          if (!all)
            break;
          c.idx.insert(c.idx.begin(), add.begin(), add.end());
          cur = peel(G->getPointerOperand());
          continue;
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(cur)) {
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand()));
          if (AI) {
            if (const llvm::Value *st = spillValue(AI)) {
              cur = peel(st);
              continue;
            }
          }
        }
        break;
      }
      c.root = cur;
      return c;
    };
    struct WForm {
      unsigned obj = 0;
      unsigned src = 0;
      std::vector<uint64_t> idx;
      // The stored value is the pointer loaded from src, so the bytes live in
      // the object src points at.
      bool loaded = false;
    };
    std::unordered_map<const llvm::Function *, std::vector<WForm>> formMemo;
    auto formWrites = [&](const llvm::Function *F) -> const std::vector<WForm> & {
      F = definedBody(F);
      static const std::vector<WForm> empty;
      if (!F || F->isDeclaration())
        return empty;
      auto it = formMemo.find(F);
      if (it != formMemo.end())
        return it->second;
      std::vector<WForm> w;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!SI || !SI->getValueOperand()->getType()->isPointerTy())
          continue;
        Cell dst = cellOf(SI->getPointerOperand());
        const auto *obj = llvm::dyn_cast<llvm::Argument>(dst.root);
        if (!obj || obj->getParent() != F)
          continue;
        for (const llvm::Argument &Src : F->args()) {
          if (&Src == obj || !Src.getType()->isPointerTy())
            continue;
          bool loaded = false;
          if (!derivedFrom(SI->getValueOperand(), &Src)) {
            const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(peel(SI->getValueOperand()));
            if (!Ld || !derivedFrom(Ld->getPointerOperand(), &Src))
              continue;
            loaded = true;
          }
          WForm f;
          f.obj = obj->getArgNo();
          f.src = Src.getArgNo();
          f.idx = dst.idx;
          f.loaded = loaded;
          w.push_back(std::move(f));
        }
      }
      auto ins = formMemo.emplace(F, std::move(w));
      return ins.first->second;
    };
    using CellKey = std::pair<const llvm::Value *, std::vector<uint64_t>>;
    std::map<CellKey, std::vector<const llvm::Value *>> cellMemo;
    std::function<void(const llvm::Value *, const std::vector<uint64_t> &, std::vector<const llvm::Value *> &, int)>
        collect;
    collect = [&](const llvm::Value *root, const std::vector<uint64_t> &idx, std::vector<const llvm::Value *> &out,
                  int depth) {
      if (!root)
        return;
      root = peel(root);
      if (!root)
        return;
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(root)) {
        const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand()));
        if (AI) {
          if (const llvm::Value *st = spillValue(AI)) {
            if (st != root)
              collect(st, idx, out, depth + 1);
            return;
          }
        }
      }
      CellKey key{root, idx};
      auto memo = cellMemo.find(key);
      if (memo != cellMemo.end()) {
        for (const llvm::Value *V : memo->second)
          if (V) {
            bool seen = false;
            for (const llvm::Value *E : out)
              if (E == V)
                seen = true;
            if (!seen)
              out.push_back(V);
          } else if (out.empty() || out.back())
            out.push_back(nullptr);
        return;
      }
      cellMemo.emplace(key, std::vector<const llvm::Value *>{});
      std::vector<const llvm::Value *> local;
      bool constOnly = false;
      auto addV = [&](const llvm::Value *V) {
        if (!V || !V->getType()->isPointerTy() || llvm::isa<llvm::Constant>(V))
          return;
        for (const llvm::Value *E : local)
          if (E == V)
            return;
        local.push_back(V);
      };
      const llvm::Function *Fn = nullptr;
      if (const auto *I = llvm::dyn_cast<llvm::Instruction>(root))
        Fn = I->getFunction();
      else if (const auto *A = llvm::dyn_cast<llvm::Argument>(root))
        Fn = A->getParent();
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(root)) {
        if (idx.empty()) {
          if (A->getParent() == entryFn)
            addV(A);
          else {
            auto sit = sites.find(A->getParent());
            if (sit != sites.end()) {
              for (const llvm::CallBase *Call : sit->second) {
                if (!Call || A->getArgNo() >= Call->arg_size())
                  continue;
                if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), A->getParent()))
                  continue;
                addV(Call->getArgOperand(A->getArgNo()));
              }
            }
          }
          cellMemo[key] = local;
          for (const llvm::Value *V : local)
            out.push_back(V);
          return;
        }
      }
      if (Fn && !Fn->isDeclaration()) {
        for (const llvm::Instruction &I : llvm::instructions(*Fn)) {
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            Cell dst = cellOf(SI->getPointerOperand());
            if (dst.root != root || dst.idx != idx)
              continue;
            if (!SI->getValueOperand()->getType()->isPointerTy() ||
                llvm::isa<llvm::Constant>(SI->getValueOperand()))
              constOnly = true;
            else
              addV(SI->getValueOperand());
            continue;
          }
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          const llvm::Value *dst = nullptr;
          const llvm::Value *src = nullptr;
          if (byteCopy(CB, dst, src)) {
            Cell d = cellOf(dst);
            Cell s = cellOf(src);
            auto offsetOf = [&](const llvm::AllocaInst *AI, const std::vector<uint64_t> &ix, uint64_t &off,
                                llvm::Type *&ty) -> bool {
              ty = AI->getAllocatedType();
              off = 0;
              for (size_t i = 0; i < ix.size(); ++i) {
                if (i == 0) {
                  if (ix[0] != 0)
                    return false;
                  continue;
                }
                if (auto *ST = llvm::dyn_cast<llvm::StructType>(ty)) {
                  if (ix[i] >= ST->getNumElements())
                    return false;
                  off += DL.getStructLayout(ST)->getElementOffset(ix[i]);
                  ty = ST->getElementType(ix[i]);
                } else if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(ty)) {
                  off += ix[i] * DL.getTypeAllocSize(AT->getElementType());
                  ty = AT->getElementType();
                } else
                  return false;
              }
              return ty != nullptr;
            };
            bool take = false;
            std::vector<uint64_t> si;
            if (d.root == root && s.root && d.idx.size() <= idx.size()) {
              bool prefix = true;
              for (size_t i = 0; i < d.idx.size(); ++i)
                if (d.idx[i] != idx[i])
                  prefix = false;
              if (prefix && d.idx == idx)
                take = true;
              else if (prefix) {
                const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(root);
                const auto *N = CB->arg_size() > 2 ? llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(2))
                                                   : nullptr;
                llvm::Type *fty = nullptr;
                llvm::Type *cty = nullptr;
                uint64_t fieldOff = 0;
                uint64_t copyOff = 0;
                if (AI && N && offsetOf(AI, idx, fieldOff, fty) && offsetOf(AI, d.idx, copyOff, cty)) {
                  uint64_t fsz = DL.getTypeStoreSize(fty);
                  uint64_t n = N->getZExtValue();
                  if (copyOff <= fieldOff && fieldOff + fsz <= copyOff + n)
                    take = true;
                }
              }
              if (take) {
                si = s.idx;
                si.insert(si.end(), idx.begin() + d.idx.size(), idx.end());
              }
            }
            if (take && s.root)
              collect(s.root, si, local, depth + 1);
            continue;
          }
          int objIx = -1;
          bool fieldPtr = false;
          for (unsigned ai = 0; ai < CB->arg_size(); ++ai) {
            Cell c = cellOf(CB->getArgOperand(ai));
            if (c.root != root)
              continue;
            if (c.idx.empty())
              objIx = static_cast<int>(ai);
            else if (c.idx == idx) {
              objIx = static_cast<int>(ai);
              fieldPtr = true;
            }
          }
          if (objIx < 0)
            continue;
          std::vector<const llvm::Function *> cs;
          auto rit = resolved.find(CB);
          if (rit != resolved.end())
            cs = rit->second;
          if (const llvm::Function *D = CB->getCalledFunction()) {
            bool have = false;
            for (const llvm::Function *E : cs)
              if (E == D)
                have = true;
            if (!have)
              cs.push_back(D);
          }
          for (const llvm::Function *D0 : cs) {
            for (const WForm &f : formWrites(D0)) {
              if (f.obj != static_cast<unsigned>(objIx) || f.src >= CB->arg_size())
                continue;
              if (fieldPtr) {
                if (!f.idx.empty())
                  continue;
              } else if (f.idx != idx)
                continue;
              const llvm::Value *srcV = CB->getArgOperand(f.src);
              if (!srcV->getType()->isPointerTy() || llvm::isa<llvm::Constant>(srcV))
                constOnly = true;
              else
                addV(srcV);
            }
          }
        }
      }
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(root)) {
        if (A->getParent() != entryFn) {
          auto sit = sites.find(A->getParent());
          if (sit != sites.end()) {
            for (const llvm::CallBase *Call : sit->second) {
              if (!Call || A->getArgNo() >= Call->arg_size())
                continue;
              if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), A->getParent()))
                continue;
              collect(Call->getArgOperand(A->getArgNo()), idx, local, depth + 1);
            }
          }
        }
      }
      if (local.empty() && constOnly)
        local.push_back(nullptr);
      cellMemo[key] = local;
      for (const llvm::Value *V : local) {
        bool seen = false;
        for (const llvm::Value *E : out)
          if (E == V)
            seen = true;
        if (!seen)
          out.push_back(V);
      }
    };
    // Bytes copied into an object. The copy is a byte copy, or a call that
    // itself copies one of its arguments into the object. A field load of the
    // object is still that object: the buffer pointer lives in the field.
    struct PKey {
      const llvm::Function *F = nullptr;
      unsigned obj = 0;
      std::vector<uint64_t> idx;
      bool operator<(const PKey &o) const {
        if (F != o.F)
          return F < o.F;
        if (obj != o.obj)
          return obj < o.obj;
        return idx < o.idx;
      }
    };
    std::map<PKey, std::vector<const llvm::Value *>> srcMemo;
    std::map<PKey, std::vector<const llvm::Value *>> srcMemoOn;
    std::map<PKey, std::set<int>> plantMemo;
    std::map<PKey, std::set<int>> plantMemoOn;
    struct Guard {
      int64_t k = 0;
      std::vector<uint64_t> idx;
      bool cell = false;
      bool operator==(const Guard &o) const { return k == o.k && cell == o.cell && idx == o.idx; }
    };
    Guard memoOnFor;
    bool memoReady = false;
    std::set<PKey> plantStack;
    std::map<std::pair<const llvm::Function *, unsigned>, bool> retFromMemo;
    std::set<std::pair<const llvm::Function *, unsigned>> retFromStack;
    std::function<bool(const llvm::Function *, unsigned)> returnsArg;
    returnsArg = [&](const llvm::Function *D, unsigned ix) -> bool {
      D = definedBody(D);
      if (!D || D->isDeclaration() || ix >= D->arg_size())
        return false;
      auto it = retFromMemo.find({D, ix});
      if (it != retFromMemo.end())
        return it->second;
      if (!retFromStack.insert({D, ix}).second)
        return false;
      std::unordered_set<const llvm::Value *> walkSeen;
      std::function<bool(const llvm::Value *, int)> walkR;
      walkR = [&](const llvm::Value *V0, int d) -> bool {
        if (!V0)
          return false;
        const llvm::Value *peeled = peel(V0);
        if (!peeled || !walkSeen.insert(peeled).second)
          return false;
        struct WalkPop {
          std::unordered_set<const llvm::Value *> &s;
          const llvm::Value *v;
          ~WalkPop() { s.erase(v); }
        } walkPop{walkSeen, peeled};
        V0 = peel(V0);
        if (!V0)
          return false;
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(V0))
          return A->getParent() == D && A->getArgNo() == ix;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V0))
          return walkR(G->getPointerOperand(), d + 1);
        if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V0)) {
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
            if (const llvm::Value *st = spillValue(AI))
              return walkR(st, d + 1);
          return walkR(LI->getPointerOperand(), d + 1);
        }
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V0)) {
          if (C->isInlineAsm())
            return false;
          std::vector<const llvm::Function *> cs;
          auto rit = resolved.find(C);
          if (rit != resolved.end())
            cs = rit->second;
          else if (const llvm::Function *Cal = C->getCalledFunction())
            cs.push_back(Cal);
          for (const llvm::Function *D0 : cs) {
            const llvm::Function *Cal = definedBody(D0);
            if (!Cal)
              continue;
            for (unsigned ai = 0; ai < C->arg_size() && ai < Cal->arg_size(); ++ai) {
              if (!returnsArg(Cal, ai))
                continue;
              if (walkR(C->getArgOperand(ai), d + 1))
                return true;
            }
          }
        }
        return false;
      };
      bool yes = false;
      for (const llvm::BasicBlock &BB : *D) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
          continue;
        if (walkR(R->getReturnValue(), 0))
          yes = true;
      }
      retFromStack.erase({D, ix});
      retFromMemo[{D, ix}] = yes;
      return yes;
    };
    std::optional<Guard> activeWant;
    std::function<std::optional<int64_t>(const llvm::Function *, unsigned, const std::vector<uint64_t> &)> discOf;
    std::function<void(const llvm::Function *, unsigned, const std::vector<uint64_t> &, int,
                       std::vector<const llvm::Value *> &)>
        collectSources;
    std::function<std::set<int>(const llvm::Function *, unsigned, const std::vector<uint64_t> &, int)>
        plantedFormals;
    collectSources = [&](const llvm::Function *F, unsigned objIx, const std::vector<uint64_t> &idx, int pd,
                         std::vector<const llvm::Value *> &out) {
      F = definedBody(F);
      if (!F || F->isDeclaration() || objIx >= F->arg_size())
        return;
      PKey key{F, objIx, idx};
      if (activeWant && (!memoReady || !(memoOnFor == *activeWant))) {
        srcMemoOn.clear();
        plantMemoOn.clear();
        memoOnFor = *activeWant;
        memoReady = true;
      }
      auto &sm = activeWant ? srcMemoOn : srcMemo;
      {
        auto itS = sm.find(key);
        if (itS != sm.end()) {
          for (const llvm::Value *S : itS->second)
            out.push_back(S);
          return;
        }
      }
      if (!plantStack.insert(key).second)
        return;
      const llvm::Argument *Obj = F->getArg(objIx);
      std::unordered_set<const llvm::Value *> objV;
      auto addObj = [&](const llvm::Value *V0) {
        if (const llvm::Value *Q = peel(V0))
          objV.insert(Q);
      };
      if (idx.empty())
        addObj(Obj);
      for (;;) {
        size_t before = objV.size();
        for (const llvm::Instruction &I : llvm::instructions(*F)) {
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(&I)) {
            if (!idx.empty()) {
              Cell cg = cellOf(G);
              if (cg.root == Obj && cg.idx == idx)
                addObj(G);
            }
            if (const llvm::Value *Q = peel(G->getPointerOperand()))
              if (objV.count(Q))
                addObj(G);
          } else if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
            if (!idx.empty()) {
              Cell cg = cellOf(LI->getPointerOperand());
              if (cg.root == Obj && cg.idx == idx)
                addObj(LI);
            }
            if (const llvm::Value *Q = peel(LI->getPointerOperand()))
              if (objV.count(Q))
                addObj(LI);
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
              if (const llvm::Value *st = spillValue(AI))
                if (const llvm::Value *Q = peel(st))
                  if (objV.count(Q))
                    addObj(LI);
            if (const llvm::Value *Lv = peel(LI))
              if (objV.count(Lv))
                if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
                  addObj(AI);
          } else if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            if (const llvm::Value *Q = peel(I.getOperand(0)))
              if (objV.count(Q))
                addObj(&I);
          } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
            if (C->isInlineAsm() || !C->getType()->isPointerTy())
              continue;
            for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
              const llvm::Value *Op = C->getArgOperand(ai);
              if (!Op->getType()->isPointerTy())
                continue;
              const llvm::Value *Q = peel(Op);
              if (!Q || !objV.count(Q))
                continue;
              std::vector<const llvm::Function *> cs;
              auto rit = resolved.find(C);
              if (rit != resolved.end())
                cs = rit->second;
              else if (const llvm::Function *D = C->getCalledFunction())
                cs.push_back(D);
              for (const llvm::Function *D0 : cs)
                if (returnsArg(D0, ai))
                  addObj(C);
            }
          }
        }
        if (objV.size() == before)
          break;
      }
      auto inObj = [&](const llvm::Value *V0) {
        const llvm::Value *Q = peel(V0);
        return Q && objV.count(Q);
      };
      std::vector<const llvm::Value *> local;
      auto pushSrc = [&](const llvm::Value *S) {
        if (!S || !S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S) || inObj(S))
          return;
        for (const llvm::Value *E : local)
          if (E == S)
            return;
        local.push_back(S);
      };
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (byteCopy(C, dst, src)) {
          bool into = inObj(dst) || derivedFrom(dst, Obj);
          if (!into && !idx.empty()) {
            Cell cg = cellOf(dst);
            into = cg.root == Obj && cg.idx == idx;
          }
          if (into)
            pushSrc(src);
          continue;
        }
        int oi = -1;
        std::vector<uint64_t> next;
        for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
          const llvm::Value *Op = C->getArgOperand(ai);
          if (!Op->getType()->isPointerTy())
            continue;
          if (inObj(Op)) {
            oi = static_cast<int>(ai);
            next.clear();
            break;
          }
          if (!idx.empty()) {
            Cell cg = cellOf(Op);
            if (cg.root == Obj && cg.idx == idx) {
              oi = static_cast<int>(ai);
              next.clear();
              break;
            }
          }
        }
        if (oi < 0)
          continue;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        if (const llvm::Function *D = C->getCalledFunction()) {
          bool have = false;
          for (const llvm::Function *E : cs)
            if (E == D)
              have = true;
          if (!have)
            cs.push_back(D);
        }
        for (const llvm::Function *D0 : cs) {
          // The branch tested one cell for one constant. A callee that stores
          // a different constant into that same cell, on a path that reaches
          // its return, does not produce the value this branch uses.
          if (activeWant && activeWant->cell && discOf) {
            std::optional<int64_t> disc = discOf(D0, static_cast<unsigned>(oi), activeWant->idx);
            if (disc && *disc != activeWant->k)
              continue;
          }
          std::set<int> inner = plantedFormals(D0, static_cast<unsigned>(oi), next, pd + 1);
          for (int fi : inner) {
            if (fi < 0 || fi >= static_cast<int>(C->arg_size()) || fi == oi)
              continue;
            pushSrc(C->getArgOperand(static_cast<unsigned>(fi)));
          }
          // A copy whose source is a field of the object, not a formal, is
          // still the bytes. The value stays in the callee; the caller reads it.
          std::vector<const llvm::Value *> raw;
          collectSources(D0, static_cast<unsigned>(oi), next, pd + 1, raw);
          const llvm::Function *D = definedBody(D0);
          for (const llvm::Value *S : raw) {
            bool isFormal = false;
            if (D) {
              for (const llvm::Argument &A : D->args()) {
                if (!A.getType()->isPointerTy())
                  continue;
                if (peel(S) == &A || derivedFrom(S, &A)) {
                  isFormal = true;
                  break;
                }
              }
            }
            if (!isFormal)
              pushSrc(S);
          }
        }
      }
      plantStack.erase(key);
      (activeWant ? srcMemoOn : srcMemo)[key] = local;
      for (const llvm::Value *S : local)
        out.push_back(S);
    };
    plantedFormals = [&](const llvm::Function *F, unsigned objIx, const std::vector<uint64_t> &idx,
                         int pd) -> std::set<int> {
      F = definedBody(F);
      std::set<int> none;
      if (!F || F->isDeclaration() || objIx >= F->arg_size())
        return none;
      PKey key{F, objIx, idx};
      if (activeWant && (!memoReady || !(memoOnFor == *activeWant))) {
        srcMemoOn.clear();
        plantMemoOn.clear();
        memoOnFor = *activeWant;
        memoReady = true;
      }
      auto &pm = activeWant ? plantMemoOn : plantMemo;
      {
        auto it = pm.find(key);
        if (it != pm.end())
          return it->second;
      }
      if (plantStack.count(key))
        return none;
      std::vector<const llvm::Value *> srcs;
      collectSources(F, objIx, idx, pd, srcs);
      std::unordered_set<const llvm::Value *> formalSeen;
      std::function<int(const llvm::Value *, int)> formalIx;
      formalIx = [&](const llvm::Value *S, int d) -> int {
        if (!S || !formalSeen.insert(S).second)
          return -1;
        for (const llvm::Argument &A : F->args()) {
          if (!A.getType()->isPointerTy())
            continue;
          if (peel(S) == &A || derivedFrom(S, &A))
            return static_cast<int>(A.getArgNo());
        }
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(peel(S))) {
          std::vector<const llvm::Function *> cs;
          auto rit = resolved.find(C);
          if (rit != resolved.end())
            cs = rit->second;
          else if (const llvm::Function *D = C->getCalledFunction())
            cs.push_back(D);
          for (const llvm::Function *D0 : cs) {
            const llvm::Function *D = definedBody(D0);
            if (!D)
              continue;
            for (unsigned ai = 0; ai < C->arg_size() && ai < D->arg_size(); ++ai) {
              if (!returnsArg(D, ai))
                continue;
              int g = formalIx(C->getArgOperand(ai), d + 1);
              if (g >= 0)
                return g;
            }
          }
        }
        return -1;
      };
      std::set<int> got;
      for (const llvm::Value *S : srcs) {
        int g = formalIx(S, 0);
        if (g >= 0)
          got.insert(g);
      }
      (activeWant ? plantMemoOn : plantMemo)[key] = got;
      return got;
    };
    // Bytes copied into an object whose pointer is not itself an entry
    // parameter. The sources are the values those copies read.
    struct VKey {
      const llvm::Function *F = nullptr;
      const llvm::Value *seed = nullptr;
      bool on = false;
      int64_t k = 0;
      std::vector<uint64_t> idx;
      bool operator<(const VKey &o) const {
        if (F != o.F)
          return F < o.F;
        if (seed != o.seed)
          return seed < o.seed;
        if (on != o.on)
          return on < o.on;
        if (k != o.k)
          return k < o.k;
        return idx < o.idx;
      }
    };
    std::map<VKey, std::vector<const llvm::Value *>> valSrcMemo;
    std::set<VKey> valSrcStack;
    // The constant written to the cell a branch compares, on a path that
    // reaches a return. A different constant is a different alternative.
    struct DiscKey {
      const llvm::Function *F = nullptr;
      unsigned obj = 0;
      std::vector<uint64_t> idx;
      bool operator<(const DiscKey &o) const {
        if (F != o.F)
          return F < o.F;
        if (obj != o.obj)
          return obj < o.obj;
        return idx < o.idx;
      }
    };
    struct Disc {
      enum Kind { None, Const, Unknown, Depth } kind = None;
      int64_t k = 0;
    };
    std::map<DiscKey, Disc> discMemo;
    std::set<DiscKey> discStack;
    std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::BasicBlock *>> retReach;
    auto reachesRet = [&](const llvm::Instruction *I) -> bool {
      const llvm::Function *Fn = I->getFunction();
      auto it = retReach.find(Fn);
      if (it == retReach.end()) {
        std::unordered_set<const llvm::BasicBlock *> reach;
        std::vector<const llvm::BasicBlock *> q;
        for (const llvm::BasicBlock &BB : *Fn)
          if (llvm::isa<llvm::ReturnInst>(BB.getTerminator()))
            q.push_back(&BB);
        for (size_t i = 0; i < q.size(); ++i) {
          if (!reach.insert(q[i]).second)
            continue;
          for (const llvm::BasicBlock *P : llvm::predecessors(q[i]))
            q.push_back(P);
        }
        it = retReach.emplace(Fn, std::move(reach)).first;
      }
      return it->second.count(I->getParent()) != 0;
    };
    std::function<Disc(const llvm::Function *, unsigned, const std::vector<uint64_t> &, int)> discStored;
    discStored = [&](const llvm::Function *F, unsigned objIx, const std::vector<uint64_t> &idx,
                     int d) -> Disc {
      auto depthCut = []() {
        Disc r;
        r.kind = Disc::Depth;
        return r;
      };
      F = definedBody(F);
      if (!F || F->isDeclaration() || objIx >= F->arg_size())
        return Disc();
      DiscKey key{F, objIx, idx};
      auto itD = discMemo.find(key);
      if (itD != discMemo.end())
        return itD->second;
      if (!discStack.insert(key).second)
        return depthCut();
      const llvm::Argument *Obj = F->getArg(objIx);
      std::optional<int64_t> got;
      bool conflict = false;
      bool cutD = false;
      auto take = [&](int64_t k) {
        if (conflict)
          return;
        if (!got)
          got = k;
        else if (*got != k) {
          conflict = true;
          got.reset();
        }
      };
      auto isPrefix = [](const std::vector<uint64_t> &pre, const std::vector<uint64_t> &full) {
        if (pre.size() > full.size())
          return false;
        for (size_t i = 0; i < pre.size(); ++i)
          if (pre[i] != full[i])
            return false;
        return true;
      };
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (!reachesRet(SI))
            continue;
          Cell c = cellOf(SI->getPointerOperand());
          if (c.root != Obj || c.idx != idx)
            continue;
          if (const auto *K = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand()))
            take(K->getSExtValue());
          else
            conflict = true;
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || !reachesRet(C))
          continue;
        if (const llvm::Function *CF = C->getCalledFunction())
          if (CF->isIntrinsic())
            continue;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        if (const llvm::Function *D = C->getCalledFunction()) {
          bool have = false;
          for (const llvm::Function *E : cs)
            if (E == D)
              have = true;
          if (!have)
            cs.push_back(D);
        }
        for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
          const llvm::Value *Op = C->getArgOperand(ai);
          if (!Op->getType()->isPointerTy())
            continue;
          Cell c = cellOf(Op);
          if (c.root != Obj || !isPrefix(c.idx, idx))
            continue;
          std::vector<uint64_t> rest(idx.begin() + static_cast<std::ptrdiff_t>(c.idx.size()), idx.end());
          for (const llvm::Function *D0 : cs) {
            Disc sub = discStored(D0, ai, rest, d + 1);
            if (sub.kind == Disc::Const)
              take(sub.k);
            else if (sub.kind == Disc::Unknown)
              conflict = true;
            else if (sub.kind == Disc::Depth)
              cutD = true;
          }
        }
      }
      discStack.erase(key);
      Disc out;
      // An unfinished callee is not a constant. Remembering that keeps the
      // same question from being walked again; it does not select an alternative.
      if (cutD && !conflict)
        out.kind = Disc::Unknown;
      else if (conflict)
        out.kind = Disc::Unknown;
      else if (got) {
        out.kind = Disc::Const;
        out.k = *got;
      }
      discMemo[key] = out;
      return out;
    };
    discOf = [&](const llvm::Function *F, unsigned objIx, const std::vector<uint64_t> &idx) {
      Disc r = discStored(F, objIx, idx, 0);
      if (r.kind == Disc::Const)
        return std::optional<int64_t>(r.k);
      return std::optional<int64_t>();
    };
    // The cell the branch predicate loads, and the constant it compares that
    // cell with. The indices are the path from the object the predicate is
    // applied to. A predicate whose cell cannot be recovered does not select.
    struct Pred {
      std::optional<int64_t> k;
      std::vector<uint64_t> idx;
      int arg = -1;
      bool cell = false;
    };
    std::function<Pred(const llvm::Value *, int)> predOf;
    std::unordered_set<const llvm::Value *> predSeen;
    predOf = [&](const llvm::Value *V, int d) -> Pred {
      Pred none;
      if (!V || !predSeen.insert(V).second)
        return none;
      struct PredPop {
        std::unordered_set<const llvm::Value *> &s;
        const llvm::Value *v;
        ~PredPop() { s.erase(v); }
      } predPop{predSeen, V};
      V = peel(V);
      if (!V)
        return none;
      if (const auto *IC = llvm::dyn_cast<llvm::ICmpInst>(V)) {
        if (IC->getPredicate() != llvm::ICmpInst::ICMP_EQ)
          return none;
        const llvm::ConstantInt *K = llvm::dyn_cast<llvm::ConstantInt>(IC->getOperand(1));
        const llvm::Value *other = IC->getOperand(0);
        if (!K) {
          K = llvm::dyn_cast<llvm::ConstantInt>(IC->getOperand(0));
          other = IC->getOperand(1);
        }
        if (!K)
          return none;
        Pred p = predOf(other, d + 1);
        p.k = K->getSExtValue();
        return p;
      }
      if (const auto *CI = llvm::dyn_cast<llvm::CastInst>(V))
        return predOf(CI->getOperand(0), d + 1);
      if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
        Cell c = cellOf(LI->getPointerOperand());
        Pred p;
        if (!c.root)
          return p;
        p.idx = c.idx;
        p.cell = true;
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(c.root))
          if (A->getParent() == LI->getFunction())
            p.arg = static_cast<int>(A->getArgNo());
        return p;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (C->isInlineAsm())
          return none;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        if (const llvm::Function *D = C->getCalledFunction()) {
          bool have = false;
          for (const llvm::Function *E : cs)
            if (E == D)
              have = true;
          if (!have)
            cs.push_back(D);
        }
        Pred acc;
        bool any = false;
        for (const llvm::Function *D0 : cs) {
          const llvm::Function *D = definedBody(D0);
          if (!D || D->isDeclaration())
            continue;
          for (const llvm::BasicBlock &BB : *D) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
            if (!R || !R->getReturnValue())
              continue;
            Pred inner = predOf(R->getReturnValue(), d + 1);
            if (!inner.k && !inner.cell)
              continue;
            if (inner.cell && inner.arg >= 0 && static_cast<unsigned>(inner.arg) < C->arg_size()) {
              Cell b = cellOf(C->getArgOperand(static_cast<unsigned>(inner.arg)));
              std::vector<uint64_t> full = b.idx;
              full.insert(full.end(), inner.idx.begin(), inner.idx.end());
              inner.idx = std::move(full);
              inner.arg = -1;
              inner.cell = b.root != nullptr;
              if (const auto *A = llvm::dyn_cast<llvm::Argument>(b.root))
                if (A->getParent() == C->getFunction())
                  inner.arg = static_cast<int>(A->getArgNo());
            } else if (inner.cell) {
              inner.cell = false;
              inner.idx.clear();
              inner.arg = -1;
            }
            if (!any) {
              acc = inner;
              any = true;
              continue;
            }
            if (acc.k && inner.k && *acc.k != *inner.k)
              acc.k.reset();
            else if (!acc.k)
              acc.k = inner.k;
            if (!(acc.cell && inner.cell && acc.idx == inner.idx && acc.arg == inner.arg))
              acc.cell = false;
          }
        }
        return acc;
      }
      return none;
    };
    auto guardOf = [&](const llvm::Value *seed) -> std::optional<Guard> {
      const auto *I = llvm::dyn_cast<llvm::Instruction>(peel(seed));
      if (!I)
        return std::nullopt;
      std::vector<const llvm::BasicBlock *> q{I->getParent()};
      std::unordered_set<const llvm::BasicBlock *> seen;
      for (size_t i = 0; i < q.size(); ++i) {
        const llvm::BasicBlock *BB = q[i];
        if (!seen.insert(BB).second)
          continue;
        for (const llvm::BasicBlock *P : llvm::predecessors(BB)) {
          if (const auto *Br = llvm::dyn_cast<llvm::BranchInst>(P->getTerminator())) {
            if (Br->isConditional() && Br->getSuccessor(0) == BB) {
              Pred pr = predOf(Br->getCondition(), 0);
              if (pr.k && pr.cell) {
                Guard g;
                g.k = *pr.k;
                g.idx = std::move(pr.idx);
                g.cell = true;
                return g;
              }
            }
          }
          q.push_back(P);
        }
      }
      return std::nullopt;
    };
    std::function<void(const llvm::Function *, const llvm::Value *, std::vector<const llvm::Value *> &)> valueSources;
    valueSources = [&](const llvm::Function *F, const llvm::Value *seed, std::vector<const llvm::Value *> &out) {
      if (!F || !seed || F->isDeclaration())
        return;
      const llvm::Value *seedP = peel(seed);
      if (!seedP)
        return;
      std::optional<Guard> want = guardOf(seedP);
      struct WantRst {
        std::optional<Guard> *slot;
        std::optional<Guard> old;
        ~WantRst() { *slot = old; }
      } wantRst{&activeWant, activeWant};
      if (want && want->cell)
        activeWant = want;
      VKey key;
      key.F = F;
      key.seed = seedP;
      if (activeWant && activeWant->cell) {
        key.on = true;
        key.k = activeWant->k;
        key.idx = activeWant->idx;
      }
      auto it = valSrcMemo.find(key);
      if (it != valSrcMemo.end()) {
        out.insert(out.end(), it->second.begin(), it->second.end());
        return;
      }
      if (!valSrcStack.insert(key).second)
        return;
      std::unordered_set<const llvm::Value *> objV;
      auto addObj = [&](const llvm::Value *V0) {
        if (const llvm::Value *Q = peel(V0))
          objV.insert(Q);
      };
      addObj(seedP);
      if (const auto *C0 = llvm::dyn_cast<llvm::CallBase>(seedP)) {
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C0);
        if (rit != resolved.end())
          cs = rit->second;
        else if (const llvm::Function *D = C0->getCalledFunction())
          cs.push_back(D);
        for (const llvm::Function *D0 : cs) {
          const llvm::Function *D = definedBody(D0);
          if (!D)
            continue;
          for (unsigned ai = 0; ai < C0->arg_size() && ai < D->arg_size(); ++ai)
            if (returnsArg(D, ai))
              addObj(C0->getArgOperand(ai));
        }
      }
      for (;;) {
        size_t before = objV.size();
        for (const llvm::Instruction &I : llvm::instructions(*F)) {
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(&I)) {
            if (const llvm::Value *Q = peel(G->getPointerOperand()))
              if (objV.count(Q))
                addObj(G);
          } else if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
            if (const llvm::Value *Q = peel(LI->getPointerOperand()))
              if (objV.count(Q))
                addObj(LI);
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
              if (const llvm::Value *st = spillValue(AI))
                if (const llvm::Value *Q = peel(st))
                  if (objV.count(Q))
                    addObj(LI);
            if (const llvm::Value *Lv = peel(LI))
              if (objV.count(Lv))
                if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
                  addObj(AI);
          } else if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
            if (const llvm::Value *Q = peel(I.getOperand(0)))
              if (objV.count(Q))
                addObj(&I);
          } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
            if (C->isInlineAsm() || !C->getType()->isPointerTy())
              continue;
            for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
              const llvm::Value *Op = C->getArgOperand(ai);
              if (!Op->getType()->isPointerTy())
                continue;
              const llvm::Value *Q = peel(Op);
              if (!Q || !objV.count(Q))
                continue;
              std::vector<const llvm::Function *> cs;
              auto rit = resolved.find(C);
              if (rit != resolved.end())
                cs = rit->second;
              else if (const llvm::Function *D = C->getCalledFunction())
                cs.push_back(D);
              for (const llvm::Function *D0 : cs)
                if (returnsArg(D0, ai))
                  addObj(C);
            }
          }
        }
        if (objV.size() == before)
          break;
      }
      auto inObj = [&](const llvm::Value *V0) {
        const llvm::Value *Q = peel(V0);
        return Q && objV.count(Q);
      };
      std::vector<const llvm::Value *> local;
      auto pushSrc = [&](const llvm::Value *S) {
        if (!S || !S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S) || inObj(S))
          return;
        for (const llvm::Value *E : local)
          if (E == S)
            return;
        local.push_back(S);
      };
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (byteCopy(C, dst, src)) {
          if (inObj(dst) || derivedFrom(dst, seedP))
            pushSrc(src);
          continue;
        }
        int oi = -1;
        for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
          const llvm::Value *Op = C->getArgOperand(ai);
          if (!Op->getType()->isPointerTy())
            continue;
          if (inObj(Op) || derivedFrom(Op, seedP)) {
            oi = static_cast<int>(ai);
            break;
          }
        }
        if (oi < 0)
          continue;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        if (const llvm::Function *D = C->getCalledFunction()) {
          bool have = false;
          for (const llvm::Function *E : cs)
            if (E == D)
              have = true;
          if (!have)
            cs.push_back(D);
        }
        for (const llvm::Function *D0 : cs) {
          std::set<int> inner = plantedFormals(D0, static_cast<unsigned>(oi), {}, 0);
          for (int fi : inner) {
            if (fi < 0 || fi >= static_cast<int>(C->arg_size()))
              continue;
            pushSrc(C->getArgOperand(static_cast<unsigned>(fi)));
          }
          std::vector<const llvm::Value *> raw;
          collectSources(D0, static_cast<unsigned>(oi), {}, 0, raw);
          const llvm::Function *D = definedBody(D0);
          for (const llvm::Value *S : raw) {
            bool isFormal = false;
            if (D) {
              for (const llvm::Argument &A : D->args()) {
                if (!A.getType()->isPointerTy())
                  continue;
                if (peel(S) == &A || derivedFrom(S, &A)) {
                  isFormal = true;
                  break;
                }
              }
            }
            if (!isFormal)
              pushSrc(S);
          }
        }
      }
      valSrcStack.erase(key);
      valSrcMemo[key] = local;
      out.insert(out.end(), local.begin(), local.end());
    };
    llvm::TargetLibraryInfoImpl tlii(llvm::Triple(M.getTargetTriple()));
    llvm::TargetLibraryInfo tli(tlii);
    std::unordered_map<const llvm::Value *, Status> byteMemo;
    std::function<Status(const llvm::Value *, int)> bytesOf;
    bytesOf = [&](const llvm::Value *V, int depth) -> Status {
      if (!V)
        return opened();
      if (!V->getType()->isPointerTy())
        return opened();
      auto itM = byteMemo.find(V);
      if (itM != byteMemo.end())
        return itM->second;
      byteMemo.emplace(V, bare());
      // A value still on the stack is bottom. Recording that empty status
      // would freeze the cycle, so a fact found on another path could not
      // replace it. Only a finished status is stored.
      auto finish = [&](Status st) {
        if (!st.any)
          byteMemo.erase(V);
        else
          byteMemo[V] = st;
        return st;
      };
      // The formal a call's returned pointer is copied from. A pointer passed
      // only as a key is not that value.
      std::unordered_map<const llvm::Function *, int> retArgMemo;
      std::unordered_set<const llvm::Function *> retStack;
      std::function<int(const llvm::Function *)> retArg;
      retArg = [&](const llvm::Function *F) -> int {
        F = definedBody(F);
        if (!F || F->isDeclaration())
          return -1;
        auto itR = retArgMemo.find(F);
        if (itR != retArgMemo.end())
          return itR->second;
        if (!retStack.insert(F).second)
          return -1;
        int ans = -1;
        bool ambig = false;
        std::unordered_map<const llvm::Value *, int> local;
        std::function<int(const llvm::Value *)> ofArg;
        ofArg = [&](const llvm::Value *cur) -> int {
          if (!cur)
            return -1;
          auto itL = local.find(cur);
          if (itL != local.end())
            return itL->second;
          local.emplace(cur, -1);
          const llvm::Value *key = cur;
          int a = -1;
          cur = peel(cur);
          if (!cur)
            return -1;
          if (const auto *GA = llvm::dyn_cast<llvm::Argument>(cur)) {
            if (GA->getParent() == F)
              a = static_cast<int>(GA->getArgNo());
          } else if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
            a = ofArg(GG->getPointerOperand());
          } else if (const auto *LL = llvm::dyn_cast<llvm::LoadInst>(cur)) {
            std::vector<const llvm::Value *> ws;
            Cell c = cellOf(LL->getPointerOperand());
            if (c.root)
              collect(c.root, c.idx, ws, 0);
            if (!ws.empty()) {
              int one = -1;
              bool many = false;
              for (const llvm::Value *w : ws) {
                if (!w) {
                  many = true;
                  break;
                }
                int g = ofArg(w);
                if (g < 0) {
                  many = true;
                  break;
                }
                if (one >= 0 && one != g)
                  many = true;
                one = g;
              }
              if (one >= 0 && !many)
                a = one;
            }
            if (a < 0)
              a = ofArg(LL->getPointerOperand());
          } else if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(cur)) {
            if (const llvm::Function *Cal = RC->getCalledFunction()) {
              int u = retArg(Cal);
              if (u >= 0 && u < static_cast<int>(RC->arg_size()))
                a = ofArg(RC->getArgOperand(static_cast<unsigned>(u)));
            }
            if (a < 0) {
              int one = -1;
              bool many = false;
              for (const llvm::Use &U : RC->args()) {
                if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                  continue;
                int g = ofArg(U.get());
                if (g < 0)
                  continue;
                if (one >= 0 && one != g)
                  many = true;
                one = g;
              }
              if (one >= 0 && !many)
                a = one;
            }
          } else if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(cur)) {
            if (const llvm::Value *st = spillValue(AI))
              a = ofArg(st);
            else if (const llvm::Function *AF = AI->getFunction()) {
              const llvm::Value *one = nullptr;
              bool many = false;
              for (const llvm::Instruction &I : llvm::instructions(*AF)) {
                const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                if (!SI || !SI->getValueOperand()->getType()->isPointerTy() ||
                    llvm::isa<llvm::Constant>(SI->getValueOperand()))
                  continue;
                Cell dst = cellOf(SI->getPointerOperand());
                if (dst.root != AI)
                  continue;
                if (one && one != SI->getValueOperand())
                  many = true;
                one = SI->getValueOperand();
              }
              if (one && !many)
                a = ofArg(one);
            }
          }
          local[key] = a;
          return a;
        };
        for (const llvm::BasicBlock &BB : *F) {
          const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
            continue;
          int a = ofArg(R->getReturnValue());
          if (a < 0)
            ambig = true;
          else if (ans >= 0 && ans != a)
            ambig = true;
          else
            ans = a;
        }
        retStack.erase(F);
        int out = ambig ? -1 : ans;
        retArgMemo[F] = out;
        return out;
      };
      const llvm::Value *P = peel(V);
      if (!P)
        return finish(opened());
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P))
        return finish(bytesOf(G->getPointerOperand(), depth + 1));
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(P)) {
        const llvm::Value *addr = L->getPointerOperand();
        std::vector<const llvm::Value *> ws;
        Cell c = cellOf(addr);
        if (c.root)
          collect(c.root, c.idx, ws, 0);
        if (!ws.empty()) {
          Status acc;
          bool saw = false;
          bool bad = false;
          for (const llvm::Value *w : ws) {
            if (!w) {
              bad = true;
              continue;
            }
            Status one = bytesOf(w, depth + 1);
            // Still computing this value. That is not a second source.
            if (!one.any)
              continue;
            if (!(pureEntry(one) || pureGlobal(one))) {
              bad = true;
              continue;
            }
            if (saw && acc.args != one.args)
              bad = true;
            if (!saw)
              acc = one;
            saw = true;
          }
          // The stored pointer is an entry parameter. A store that does not
          // reduce leaves the cell in the object that holds it.
          if (saw && !bad)
            return finish(acc);
          if (saw && bad)
            return finish(opened());
        }
        // Nothing stored in the cell is itself an entry parameter. The bytes
        // copied into that object are. A pointer passed with the same object
        // into a call that copies it is one of those bytes.
        if (!ws.empty() || c.root) {
            if (const auto *HA = llvm::dyn_cast<llvm::Argument>(c.root)) {
            std::vector<const llvm::Value *> srcs;
            auto pushU = [&](const llvm::Value *S) {
              if (!S)
                return;
              for (const llvm::Value *E : srcs)
                if (E == S)
                  return;
              srcs.push_back(S);
            };
            auto sit = sites.find(HA->getParent());
            if (sit != sites.end()) {
              for (const llvm::CallBase *Call : sit->second) {
                if (!Call || HA->getArgNo() >= Call->arg_size())
                  continue;
                if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), HA->getParent()))
                  continue;
                const llvm::Value *actual = Call->getArgOperand(HA->getArgNo());
                const llvm::Function *Caller = Call->getFunction();
                if (!Caller)
                  continue;
                // A call that returns a field of this object still carries the
                // object. Copies into that pointer are copies into the object.
                {
                  std::vector<const llvm::Value *> carried;
                  valueSources(Caller, actual, carried);
                  for (const llvm::Value *S : carried)
                    pushU(S);
                }
                for (const llvm::Instruction &I : llvm::instructions(*Caller)) {
                  const auto *C2 = llvm::dyn_cast<llvm::CallBase>(&I);
                  if (!C2 || C2 == Call || C2->isInlineAsm())
                    continue;
                  auto spilled = [&](const llvm::Value *V0) -> const llvm::Value * {
                    V0 = peel(V0);
                    if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V0))
                      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
                        return spillValue(AI);
                    return nullptr;
                  };
                  const llvm::Value *spAct = spilled(actual);
                  int oi = -1;
                  for (unsigned ai = 0; ai < C2->arg_size(); ++ai) {
                    const llvm::Value *Op = C2->getArgOperand(ai);
                    if (!Op->getType()->isPointerTy())
                      continue;
                    if (peel(Op) == peel(actual) || derivedFrom(Op, actual) || derivedFrom(actual, Op)) {
                      oi = static_cast<int>(ai);
                      break;
                    }
                    const llvm::Value *sp = spilled(Op);
                    if (sp && spAct && sp == spAct) {
                      oi = static_cast<int>(ai);
                      break;
                    }
                  }
                  if (oi < 0)
                    continue;
                  std::vector<const llvm::Function *> cs;
                  auto rit = resolved.find(C2);
                  if (rit != resolved.end())
                    cs = rit->second;
                  else if (const llvm::Function *D = C2->getCalledFunction())
                    cs.push_back(D);
                  for (const llvm::Function *D0 : cs) {
                    std::vector<const llvm::Value *> local;
                    collectSources(D0, static_cast<unsigned>(oi), c.idx, 0, local);
                    for (const llvm::Value *S : local)
                      pushU(S);
                  }
                }
              }
            }
            if (!srcs.empty()) {
              Status acc;
              bool sawS = false;
              bool badS = false;
              for (const llvm::Value *S : srcs) {
                Status one = bytesOf(S, depth + 1);
                if (!one.any)
                  continue;
                if (!(pureEntry(one) || pureGlobal(one))) {
                  badS = true;
                  continue;
                }
                if (sawS && acc.args != one.args)
                  badS = true;
                if (!sawS)
                  acc = one;
                sawS = true;
              }
              if (sawS && !badS)
                return finish(acc);
            }
          }
        }
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(addr))) {
          if (const llvm::Value *st = spillValue(AI))
            return finish(bytesOf(st, depth + 1));
          return finish(bytesOf(AI, depth + 1));
        }
        return finish(bytesOf(addr, depth + 1));
      }
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(P)) {
        if (A->getParent() == entryFn) {
          Status s;
          s.any = true;
          s.args.insert({entryName, static_cast<int>(A->getArgNo())});
          return finish(s);
        }
        Status acc;
        bool saw = false;
        bool bad = false;
        auto take = [&](Status one) {
          if (!one.any)
            return;
          if (!(pureEntry(one) || pureGlobal(one))) {
            bad = true;
            return;
          }
          if (saw && acc.args != one.args)
            bad = true;
          if (!saw)
            acc = one;
          saw = true;
        };
        auto passthrough = [&](const llvm::Value *V) {
          V = peel(V);
          if (!V)
            return false;
          if (llvm::isa<llvm::Argument>(V))
            return true;
          if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()))) {
              if (const llvm::Value *st = spillValue(AI)) {
                st = peel(st);
                if (st && llvm::isa<llvm::Argument>(st))
                  return true;
              }
            }
          }
          return false;
        };
        auto sit = sites.find(A->getParent());
        std::vector<const llvm::CallBase *> roots;
        std::vector<const llvm::CallBase *> fwds;
        if (sit != sites.end()) {
          for (const llvm::CallBase *Call : sit->second) {
            if (!Call || A->getArgNo() >= Call->arg_size())
              continue;
            if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), A->getParent()))
              continue;
            if (passthrough(Call->getArgOperand(A->getArgNo())))
              fwds.push_back(Call);
            else
              roots.push_back(Call);
          }
        }
        // A call that only forwards its own argument does not add a byte
        // source. The pointer is materialized at the calls that do not
        // forward. Those calls are the meet. Forwarders are the meet only
        // when nothing else passes the pointer.
        const std::vector<const llvm::CallBase *> &use = roots.empty() ? fwds : roots;
        for (const llvm::CallBase *Call : use)
          take(bytesOf(Call->getArgOperand(A->getArgNo()), depth + 1));
        if (saw && !bad)
          return finish(acc);
        // Every callsite is still on the stack. That is a cycle, not a
        // finished unknown. Caching open here would erase the entry a later
        // callsite reduces to.
        if (!saw && !bad && !use.empty())
          return finish(bare());
        return finish(opened());
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(P)) {
        if (const llvm::Value *st = spillValue(AI))
          return finish(bytesOf(st, depth + 1));
        // Every pointer stored here is a field of one object. The aggregate
        // is a copy of that object, so it denotes that object's bytes.
        {
          const llvm::Value *src = nullptr;
          bool many = false;
          bool any = false;
          auto objectOf = [&](const llvm::Value *V) -> const llvm::Value * {
            V = peel(V);
            const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V);
            if (!LI)
              return nullptr;
            const llvm::Value *addr = peel(LI->getPointerOperand());
            std::unordered_set<const llvm::Value *> seenA;
            while (addr && seenA.insert(addr).second) {
              if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(addr)) {
                addr = peel(GG->getPointerOperand());
                continue;
              }
              return addr;
            }
            return nullptr;
          };
          if (const llvm::Function *AF = AI->getFunction()) {
            for (const llvm::Instruction &I : llvm::instructions(*AF)) {
              const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
              if (!SI || !SI->getValueOperand()->getType()->isPointerTy() ||
                  llvm::isa<llvm::Constant>(SI->getValueOperand()))
                continue;
              Cell dst = cellOf(SI->getPointerOperand());
              if (dst.root != AI)
                continue;
              const llvm::Value *base = objectOf(SI->getValueOperand());
              if (!base) {
                many = true;
                break;
              }
              if (src && src != base)
                many = true;
              src = base;
              any = true;
            }
          }
          if (any && !many && src && src != AI)
            return finish(bytesOf(src, depth + 1));
        }
        Status acc;
        bool saw = false;
        bool bad = false;
        bool clash = false;
        const llvm::Function *Fn = AI->getFunction();
        auto takeOne = [&](Status one) {
          if (!one.any)
            return;
          if (!(pureEntry(one) || pureGlobal(one))) {
            bad = true;
            return;
          }
          if (saw && acc.args != one.args)
            clash = true;
          if (!saw)
            acc = one;
          saw = true;
        };
        if (Fn) {
          for (const llvm::Instruction &I : llvm::instructions(*Fn)) {
            if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              if (!SI->getValueOperand()->getType()->isPointerTy())
                continue;
              if (!derivedFrom(SI->getPointerOperand(), AI) || derivedFrom(SI->getValueOperand(), AI))
                continue;
              if (llvm::isa<llvm::Constant>(SI->getValueOperand()))
                continue;
              takeOne(bytesOf(SI->getValueOperand(), depth + 1));
              continue;
            }
            const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!UC || UC->isInlineAsm())
              continue;
            bool handed = false;
            for (const llvm::Use &Arg : UC->args())
              if (derivedFrom(Arg.get(), AI))
                handed = true;
            if (!handed)
              continue;
            for (const llvm::Use &Arg : UC->args()) {
              if (!Arg.get()->getType()->isPointerTy() || derivedFrom(Arg.get(), AI))
                continue;
              if (llvm::isa<llvm::Constant>(Arg.get()))
                continue;
              takeOne(bytesOf(Arg.get(), depth + 1));
            }
          }
        }
        if (saw && !bad && !clash)
          return finish(acc);
        // Pointer identity did not reduce, or a sibling pointer was not an
        // entry parameter. The bytes copied into this object may still be.
        // Two different entry parameters stored here stay unresolved.
        if (!clash && Fn) {
          std::vector<const llvm::Value *> carried;
          valueSources(Fn, AI, carried);
          Status acc2;
          bool saw2 = false;
          bool bad2 = false;
          for (const llvm::Value *S : carried) {
            Status one = bytesOf(S, depth + 1);
            if (!one.any)
              continue;
            if (!(pureEntry(one) || pureGlobal(one))) {
              bad2 = true;
              continue;
            }
            if (saw2 && acc2.args != one.args)
              bad2 = true;
            if (!saw2)
              acc2 = one;
            saw2 = true;
          }
          if (saw2 && !bad2)
            return finish(acc2);
        }
        return finish(opened());
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(P)) {
        std::vector<const llvm::Function *> cals;
        auto rit = resolved.find(CB);
        if (rit != resolved.end())
          cals = rit->second;
        else if (const llvm::Function *D = CB->getCalledFunction())
          cals.push_back(D);
        const llvm::Argument *onlyF = nullptr;
        bool amb = false;
        bool sawRet = false;
        for (const llvm::Function *D0 : cals) {
          const llvm::Function *D = definedBody(D0);
          if (!D || D->isDeclaration())
            continue;
          std::unordered_map<const llvm::Value *, const llvm::Argument *> formalOf;
          std::function<const llvm::Argument *(const llvm::Value *)> fromFormal;
          fromFormal = [&](const llvm::Value *cur) -> const llvm::Argument * {
            if (!cur)
              return nullptr;
            auto itF = formalOf.find(cur);
            if (itF != formalOf.end())
              return itF->second;
            formalOf.emplace(cur, nullptr);
            const llvm::Value *key = cur;
            const llvm::Argument *fa = nullptr;
            cur = peel(cur);
            if (!cur)
              return nullptr;
            if (const auto *GA = llvm::dyn_cast<llvm::Argument>(cur)) {
              if (GA->getParent() == D)
                fa = GA;
            } else if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
              fa = fromFormal(GG->getPointerOperand());
            } else if (const auto *LL = llvm::dyn_cast<llvm::LoadInst>(cur)) {
              std::vector<const llvm::Value *> ws;
              Cell c = cellOf(LL->getPointerOperand());
              if (c.root)
                collect(c.root, c.idx, ws, 0);
              if (!ws.empty()) {
                const llvm::Argument *one = nullptr;
                bool many = false;
                for (const llvm::Value *w : ws) {
                  if (!w) {
                    many = true;
                    break;
                  }
                  const llvm::Argument *g = fromFormal(w);
                  if (!g) {
                    many = true;
                    break;
                  }
                  if (one && one != g)
                    many = true;
                  one = g;
                }
                if (one && !many)
                  fa = one;
              }
              if (!fa)
                fa = fromFormal(LL->getPointerOperand());
            } else if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(cur)) {
              if (const llvm::Function *Cal = RC->getCalledFunction()) {
                int u = retArg(Cal);
                if (u >= 0 && u < static_cast<int>(RC->arg_size()))
                  fa = fromFormal(RC->getArgOperand(static_cast<unsigned>(u)));
              }
              const llvm::Argument *one = nullptr;
              bool many = false;
              if (!fa) {
                for (const llvm::Use &U : RC->args()) {
                  if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                    continue;
                  const llvm::Argument *g = fromFormal(U.get());
                  if (!g)
                    continue;
                  if (one && one != g)
                    many = true;
                  one = g;
                }
                if (one && !many)
                  fa = one;
              }
            } else if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(cur)) {
              if (const llvm::Value *st = spillValue(AI))
                fa = fromFormal(st);
              else if (const llvm::Function *AF = AI->getFunction()) {
                const llvm::Value *one = nullptr;
                bool many = false;
                for (const llvm::Instruction &I : llvm::instructions(*AF)) {
                  const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                  if (!SI || !SI->getValueOperand()->getType()->isPointerTy() ||
                      llvm::isa<llvm::Constant>(SI->getValueOperand()))
                    continue;
                  Cell dst = cellOf(SI->getPointerOperand());
                  if (dst.root != AI)
                    continue;
                  if (one && one != SI->getValueOperand())
                    many = true;
                  one = SI->getValueOperand();
                }
                if (one && !many)
                  fa = fromFormal(one);
              }
            }
            formalOf[key] = fa;
            return fa;
          };
          for (const llvm::BasicBlock &BB : *D) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
            if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
              continue;
            sawRet = true;
            const llvm::Argument *fa = fromFormal(R->getReturnValue());
            if (!fa)
              amb = true;
            else if (onlyF && onlyF->getArgNo() != fa->getArgNo())
              amb = true;
            else
              onlyF = fa;
          }
        }
        if (sawRet && onlyF && !amb && onlyF->getArgNo() < CB->arg_size()) {
          const llvm::Value *actual = CB->getArgOperand(onlyF->getArgNo());
          // The return is an interior pointer when the path from the returned
          // value to that formal goes through a load. The bytes are what was
          // written into the object, not the identity of the object pointer.
          bool interior = false;
          for (const llvm::Function *D0 : cals) {
            const llvm::Function *D = definedBody(D0);
            if (!D || D->isDeclaration() || interior)
              continue;
            std::function<bool(const llvm::Value *, bool, int)> touch;
            touch = [&](const llvm::Value *cur, bool sawL, int n) -> bool {
              if (!cur || n > 8)
                return false;
              cur = peel(cur);
              if (!cur)
                return false;
              if (const auto *GA = llvm::dyn_cast<llvm::Argument>(cur))
                return sawL && GA->getParent() == D && GA->getArgNo() == onlyF->getArgNo();
              if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur))
                return touch(GG->getPointerOperand(), sawL, n + 1);
              if (const auto *LL = llvm::dyn_cast<llvm::LoadInst>(cur))
                return touch(LL->getPointerOperand(), true, n + 1);
              if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(cur)) {
                if (const llvm::Function *Cal = RC->getCalledFunction()) {
                  int u = retArg(Cal);
                  if (u >= 0 && u < static_cast<int>(RC->arg_size()))
                    return touch(RC->getArgOperand(static_cast<unsigned>(u)), sawL, n + 1);
                }
              }
              if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(cur))
                if (const llvm::Value *st = spillValue(AI))
                  return touch(st, sawL, n + 1);
              return false;
            };
            for (const llvm::BasicBlock &BB : *D) {
              const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
              if (!R || !R->getReturnValue())
                continue;
              if (touch(R->getReturnValue(), false, 0))
                interior = true;
            }
          }
          if (interior) {
            // Cell = (base, byte offset). A store of a pointer is a def of that
            // cell. memcpy/memmove is a def of the buffer it writes. A call is
            // a def of that buffer only when an operand is the pointer loaded
            // from the cell. Receiving the cell address alone does not define
            // the buffer. An unresolved call that does write the buffer is
            // unknown and absorbs every entry atom.
            struct Bnd {
              int prev = -1;
              const llvm::Function *fn = nullptr;
              const llvm::CallBase *call = nullptr;
            };
            std::vector<Bnd> bnds;
            struct RetA {
              bool ok = false;
              int arg = -1;
              int64_t off = 0;
              bool known = true;
            };
            std::unordered_map<const llvm::Function *, RetA> retA;
            std::unordered_set<const llvm::Function *> retS;
            std::function<RetA(const llvm::Function *)> retOf;
            retOf = [&](const llvm::Function *F) -> RetA {
              F = definedBody(F);
              RetA no;
              if (!F || F->isDeclaration())
                return no;
              auto it = retA.find(F);
              if (it != retA.end())
                return it->second;
              if (!retS.insert(F).second)
                return no;
              RetA acc;
              bool any = false, badR = false;
              std::function<bool(const llvm::Value *, int &, int64_t &, bool &, int)> addr;
              addr = [&](const llvm::Value *V, int &arg, int64_t &off, bool &known, int n) -> bool {
                if (!V || n > 64)
                  return false;
                V = peel(V);
                if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
                  if (A->getParent() != F)
                    return false;
                  arg = static_cast<int>(A->getArgNo());
                  return true;
                }
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                  if (known) {
                    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
                    if (!G->accumulateConstantOffset(DL, ap))
                      known = false;
                    else
                      off += ap.getSExtValue();
                  }
                  return addr(G->getPointerOperand(), arg, off, known, n + 1);
                }
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
                  if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand())))
                    if (AI->getAllocatedType()->isPointerTy())
                      if (const llvm::Value *st = spillValue(AI))
                        return addr(st, arg, off, known, n + 1);
                  return false;
                }
                if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
                  if (!C->getCalledFunction() || C->getCalledFunction()->isIntrinsic())
                    return false;
                  RetA in = retOf(C->getCalledFunction());
                  if (!in.ok || in.arg < 0 || in.arg >= static_cast<int>(C->arg_size()))
                    return false;
                  if (known) {
                    if (!in.known)
                      known = false;
                    else
                      off += in.off;
                  }
                  return addr(C->getArgOperand(static_cast<unsigned>(in.arg)), arg, off, known, n + 1);
                }
                return false;
              };
              for (const llvm::BasicBlock &BB : *F) {
                const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                  continue;
                int arg = -1;
                int64_t off = 0;
                bool known = true;
                if (!addr(R->getReturnValue(), arg, off, known, 0)) {
                  badR = true;
                  break;
                }
                if (!any) {
                  acc = RetA{true, arg, off, known};
                  any = true;
                } else if (acc.arg != arg || acc.known != known || (acc.known && acc.off != off)) {
                  badR = true;
                  break;
                }
              }
              retS.erase(F);
              if (badR || !any)
                acc = no;
              retA.emplace(F, acc);
              return acc;
            };
            auto anchor = [&](const llvm::Value *V, int b) -> Loc {
              Loc loc;
              std::unordered_set<const llvm::Value *> seen;
              int64_t off = 0;
              bool known = true;
              V = peel(V);
              while (V && seen.insert(V).second) {
                if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
                  if (b >= 0 && A->getParent() == bnds[static_cast<size_t>(b)].fn && bnds[static_cast<size_t>(b)].call &&
                      A->getArgNo() < bnds[static_cast<size_t>(b)].call->arg_size()) {
                    V = peel(bnds[static_cast<size_t>(b)].call->getArgOperand(A->getArgNo()));
                    b = bnds[static_cast<size_t>(b)].prev;
                    continue;
                  }
                  break;
                }
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                  if (known) {
                    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
                    if (!G->accumulateConstantOffset(DL, ap))
                      known = false;
                    else
                      off += ap.getSExtValue();
                  }
                  V = peel(G->getPointerOperand());
                  continue;
                }
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
                  if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand()))) {
                    if (AI->getAllocatedType()->isPointerTy()) {
                      if (const llvm::Value *st = spillValue(AI)) {
                        V = peel(st);
                        continue;
                      }
                    }
                  }
                  break;
                }
                if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
                  if (C->getCalledFunction() && !C->getCalledFunction()->isIntrinsic()) {
                    RetA r = retOf(C->getCalledFunction());
                    if (r.ok && r.arg >= 0 && r.arg < static_cast<int>(C->arg_size())) {
                      if (known) {
                        if (!r.known)
                          known = false;
                        else
                          off += r.off;
                      }
                      V = peel(C->getArgOperand(static_cast<unsigned>(r.arg)));
                      continue;
                    }
                  }
                  break;
                }
                break;
              }
              if (V && (llvm::isa<llvm::AllocaInst>(V) || llvm::isa<llvm::GlobalVariable>(V) ||
                        llvm::isa<llvm::Argument>(V) || llvm::isa<llvm::CallBase>(V))) {
                loc.base = V;
                loc.off = off;
                loc.known = known;
              }
              return loc;
            };
            auto sameLoc = [](Loc a, Loc b) {
              if (!a.base || a.base != b.base)
                return false;
              if (!a.known || !b.known)
                return true;
              return a.off == b.off;
            };
            auto listed = [&](const llvm::Function *P) {
              if (!P || !strongExport(P))
                return false;
              const std::string name = show(P);
              for (const auto &kv : entriesOf)
                if (kv.second.count(name))
                  return true;
              return false;
            };
            struct MK {
              const llvm::Value *base = nullptr;
              int64_t off = 0;
              bool known = false;
              bool operator<(const MK &o) const {
                if (base != o.base)
                  return base < o.base;
                if (known != o.known)
                  return known < o.known;
                return off < o.off;
              }
            };
            std::map<MK, Status> memo;
            std::set<MK> visiting;
            std::set<std::pair<const llvm::Value *, int>> flowOn;
            std::function<Status(const llvm::Value *, int, int)> flow;
            std::function<Status(Loc, int)> atCell;
            auto absorb = [&](Status &acc, bool &saw, Status one) {
              if (!(pureEntry(one) || pureGlobal(one)))
                return;
              if (!saw)
                acc = one;
              else if (pureEntry(acc) && pureEntry(one))
                acc.args.insert(one.args.begin(), one.args.end());
              else if (pureGlobal(acc) && pureGlobal(one) && acc.slot == one.slot && acc.off == one.off)
                acc.args.insert(one.args.begin(), one.args.end());
              else {
                acc = nothing();
                saw = false;
                return;
              }
              saw = true;
            };
            flow = [&](const llvm::Value *V, int b, int d) -> Status {
              // Termination is the finite memoized cell domain below, not a
              // step count. A value met again in the same call context is a
              // cycle and contributes nothing; there is no depth number.
              if (!V)
                return nothing();
              V = peel(V);
              if (!V)
                return nothing();
              std::pair<const llvm::Value *, int> fkey{V, b};
              if (!flowOn.insert(fkey).second)
                return nothing();
              Status fr = [&]() -> Status {
              if (b >= 0) {
                if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
                  if (A->getParent() == bnds[static_cast<size_t>(b)].fn && bnds[static_cast<size_t>(b)].call &&
                      A->getArgNo() < bnds[static_cast<size_t>(b)].call->arg_size())
                    return flow(bnds[static_cast<size_t>(b)].call->getArgOperand(A->getArgNo()), bnds[static_cast<size_t>(b)].prev, d + 1);
                }
              }
              if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
                if (A->getParent() == entryFn || listed(A->getParent())) {
                  Status s;
                  s.any = true;
                  s.args.insert({A->getParent() == entryFn ? entryName : show(A->getParent()),
                                 static_cast<int>(A->getArgNo())});
                  return s;
                }
                std::vector<const llvm::CallBase *> in, outc;
                auto sit = sites.find(A->getParent());
                if (sit != sites.end()) {
                  for (const llvm::CallBase *Call : sit->second) {
                    if (!Call || A->getArgNo() >= Call->arg_size())
                      continue;
                    if (cone(Call->getFunction()) && entryCall(Call->getFunction(), A->getParent()))
                      in.push_back(Call);
                    else
                      outc.push_back(Call);
                  }
                }
                const auto &use = in.empty() ? outc : in;
                Status acc;
                bool saw = false;
                for (const llvm::CallBase *Call : use)
                  absorb(acc, saw, flow(Call->getArgOperand(A->getArgNo()), -1, d + 1));
                return saw ? acc : nothing();
              }
              if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
                if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand())))
                  if (const llvm::Value *st = spillValue(AI))
                    return flow(st, b, d + 1);
                // The loaded pointer's bytes are the contents of the cell it was
                // loaded from: stores into that cell, and copies through the
                // pointer loaded from it.
                if (L->getType()->isPointerTy()) {
                  Loc cell = anchor(L->getPointerOperand(), b);
                  if (cell.base)
                    return atCell(cell, d + 1);
                }
              }
              if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                bool var = false;
                for (unsigned oi = 1; oi < G->getNumOperands(); ++oi)
                  if (!llvm::isa<llvm::ConstantInt>(G->getOperand(oi)))
                    var = true;
                if (var)
                  return flow(G->getPointerOperand(), b, d + 1);
              }
              return atCell(anchor(V, b), d);
              }();
              flowOn.erase(fkey);
              return fr;
            };
            atCell = [&](Loc q, int d) -> Status {
              // A cell is answered once: re-entry is guarded by the visiting
              // set and the memo, so the finite set of cells bounds the
              // recursion. No step count is needed.
              if (!q.base)
                return nothing();
              MK key{q.base, q.known ? q.off : 0, q.known};
              if (visiting.count(key))
                return nothing();
              auto itM = memo.find(key);
              if (itM != memo.end())
                return itM->second;
              visiting.insert(key);
              Status acc;
              bool saw = false;
              bool unk = false;
              auto keep = [&](Status one) {
                if (one.open)
                  unk = true;
                else
                  absorb(acc, saw, one);
              };
              std::set<std::pair<const llvm::Function *, MK>> stack;
              // over is true when the callee set is every function of the call's
              // type. That set can show a copy. It does not prove a write, so a
              // bodyless call inside it does not make the cell unknown.
              std::function<void(const llvm::Function *, int, int, bool)> scan;
              scan = [&](const llvm::Function *F, int b, int sd, bool over) {
                F = definedBody(F);
                // The per-cell stack set below bounds this walk; the callee
                // set is finite, so no step count is needed.
                if (!F || F->isDeclaration())
                  return;
                if (!stack.insert({F, key}).second)
                  return;
                std::unordered_set<const llvm::Value *> fromSeen;
                std::function<bool(const llvm::Value *, int)> fromCell;
                // True only after the walk has passed a load of q: the value is
                // the buffer that cell points at, not the cell address.
                std::unordered_set<const llvm::Value *> pointeeSeen;
                std::function<bool(const llvm::Value *, int)> pointee;
                fromCell = [&](const llvm::Value *X, int depth) -> bool {
                  if (!X)
                    return false;
                  X = peel(X);
                  if (!fromSeen.insert(X).second)
                    return false;
                  struct FromPop {
                    std::unordered_set<const llvm::Value *> &s;
                    const llvm::Value *v;
                    ~FromPop() { s.erase(v); }
                  } fromPop{fromSeen, X};
                  if (b >= 0) {
                    if (const auto *A = llvm::dyn_cast<llvm::Argument>(X)) {
                      if (A->getParent() == bnds[static_cast<size_t>(b)].fn && bnds[static_cast<size_t>(b)].call &&
                          A->getArgNo() < bnds[static_cast<size_t>(b)].call->arg_size())
                        return fromCell(bnds[static_cast<size_t>(b)].call->getArgOperand(A->getArgNo()), depth + 1);
                    }
                  }
                  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(X)) {
                    bool var = false;
                    for (unsigned oi = 1; oi < G->getNumOperands(); ++oi)
                      if (!llvm::isa<llvm::ConstantInt>(G->getOperand(oi)))
                        var = true;
                    if (var)
                      return fromCell(G->getPointerOperand(), depth + 1);
                  }
                  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(X)) {
                    if (sameLoc(anchor(Ld->getPointerOperand(), b), q))
                      return true;
                    if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(Ld->getPointerOperand())))
                      if (const llvm::Value *st = spillValue(AI))
                        return fromCell(st, depth + 1);
                  }
                  return sameLoc(anchor(X, b), q);
                };
                pointee = [&](const llvm::Value *X, int depth) -> bool {
                  if (!X)
                    return false;
                  X = peel(X);
                  if (!pointeeSeen.insert(X).second)
                    return false;
                  struct PointeePop {
                    std::unordered_set<const llvm::Value *> &s;
                    const llvm::Value *v;
                    ~PointeePop() { s.erase(v); }
                  } pointeePop{pointeeSeen, X};
                  if (b >= 0) {
                    if (const auto *A = llvm::dyn_cast<llvm::Argument>(X)) {
                      if (A->getParent() == bnds[static_cast<size_t>(b)].fn && bnds[static_cast<size_t>(b)].call &&
                          A->getArgNo() < bnds[static_cast<size_t>(b)].call->arg_size())
                        return pointee(bnds[static_cast<size_t>(b)].call->getArgOperand(A->getArgNo()), depth + 1);
                    }
                  }
                  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(X))
                    return pointee(G->getPointerOperand(), depth + 1);
                  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(X)) {
                    if (sameLoc(anchor(Ld->getPointerOperand(), b), q))
                      return true;
                    if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(Ld->getPointerOperand())))
                      if (const llvm::Value *st = spillValue(AI))
                        return pointee(st, depth + 1);
                  }
                  return false;
                };
                for (const llvm::Instruction &I : llvm::instructions(*F)) {
                  if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
                    if (SI->getValueOperand()->getType()->isPointerTy() &&
                        !llvm::isa<llvm::Constant>(SI->getValueOperand()) &&
                        sameLoc(anchor(SI->getPointerOperand(), b), q))
                      keep(flow(SI->getValueOperand(), b, d + 1));
                    continue;
                  }
                  const llvm::Value *src = nullptr, *dst = nullptr;
                  if (const auto *M = llvm::dyn_cast<llvm::MemCpyInst>(&I)) {
                    dst = M->getDest();
                    src = M->getSource();
                  } else if (const auto *MV = llvm::dyn_cast<llvm::MemMoveInst>(&I)) {
                    dst = MV->getDest();
                    src = MV->getSource();
                  }
                  if (src) {
                    if (fromCell(dst, 0))
                      keep(flow(src, b, d + 1));
                    continue;
                  }
                  const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
                  if (!C || C->isInlineAsm())
                    continue;
                  if (const llvm::Function *D = C->getCalledFunction())
                    if (D->isIntrinsic())
                      continue;
                  bool pass = false;
                  for (const llvm::Use &Arg : C->args()) {
                    if (!Arg.get()->getType()->isPointerTy())
                      continue;
                    if (anchor(Arg.get(), b).base == q.base || fromCell(Arg.get(), 0))
                      pass = true;
                  }
                  if (!pass)
                    continue;
                  bool body = false;
                  bool buffer = false;
                  for (const llvm::Use &Arg : C->args())
                    if (Arg.get()->getType()->isPointerTy() && pointee(Arg.get(), 0))
                      buffer = true;
                  std::vector<const llvm::Function *> proved = solve.callees(C, false);
                  bool wide = proved.empty();
                  std::vector<const llvm::Function *> may = proved;
                  if (wide)
                    may = solve.slotMay(C);
                  for (const llvm::Function *D0 : may) {
                    const llvm::Function *D = definedBody(D0);
                    if (!D || D->isDeclaration())
                      continue;
                    body = true;
                    int slot = static_cast<int>(bnds.size());
                    bnds.push_back(Bnd{b, D, C});
                    scan(D, slot, sd + 1, over || wide);
                  }
                  if (!over && !wide && !body && buffer && !C->onlyReadsMemory() && !C->doesNotAccessMemory() &&
                      !llvm::getFreedOperand(C, &tli) && !llvm::isAllocLikeFn(C, &tli))
                    unk = true;
                }
                stack.erase({F, key});
              };
              if (const auto *I = llvm::dyn_cast<llvm::Instruction>(q.base))
                scan(I->getFunction(), -1, 0, false);
              else if (const auto *A = llvm::dyn_cast<llvm::Argument>(q.base)) {
                bool before = saw;
                scan(A->getParent(), -1, 0, false);
                // No store in this body reaches the load. The defs are the
                // stores of the same field on the object the callers pass.
                if (!unk && !saw && !before && d < 6) {
                  auto sit = sites.find(A->getParent());
                  if (sit != sites.end()) {
                    for (const llvm::CallBase *Call : sit->second) {
                      if (!Call || A->getArgNo() >= Call->arg_size())
                        continue;
                      Loc src = anchor(Call->getArgOperand(A->getArgNo()), -1);
                      if (!src.base)
                        continue;
                      if (src.known && q.known)
                        src.off += q.off;
                      else
                        src.known = false;
                      keep(atCell(src, d + 1));
                      if (unk)
                        break;
                    }
                  }
                }
              }
              visiting.erase(key);
              Status out = unk ? opened() : (saw ? acc : nothing());
              memo[key] = out;
              return out;
            };
            Status acc;
            bool saw = false;
            bool unkQ = false;
            for (const llvm::Function *D0 : cals) {
              const llvm::Function *D = definedBody(D0);
              if (!D || !onlyF)
                continue;
              std::unordered_set<const llvm::Value *> seenR;
              std::function<void(const llvm::Value *, int)> walk;
              walk = [&](const llvm::Value *V, int n) {
                if (!V || n > 16 || !seenR.insert(V).second)
                  return;
                V = peel(V);
                if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
                  for (const llvm::Value *inc : P->incoming_values())
                    walk(inc, n + 1);
                  return;
                }
                if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
                  walk(Sel->getTrueValue(), n + 1);
                  walk(Sel->getFalseValue(), n + 1);
                  return;
                }
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
                  if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand())))
                    if (const llvm::Value *st = spillValue(AI)) {
                      walk(st, n + 1);
                      return;
                    }
                  Loc c = anchor(L->getPointerOperand(), -1);
                  if (const auto *A = llvm::dyn_cast<llvm::Argument>(c.base)) {
                    if (A->getParent() == D && A->getArgNo() == onlyF->getArgNo()) {
                      Loc moved = anchor(actual, -1);
                      if (moved.base) {
                        if (moved.known && c.known)
                          moved.off += c.off;
                        else
                          moved.known = false;
                        Status one = atCell(moved, 0);
                        if (one.open)
                          unkQ = true;
                        else
                          absorb(acc, saw, one);
                      }
                    }
                  }
                  return;
                }
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
                  walk(G->getPointerOperand(), n + 1);
                  return;
                }
                if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
                  if (const llvm::Function *Cal = C->getCalledFunction()) {
                    int u = retArg(Cal);
                    if (u >= 0 && u < static_cast<int>(C->arg_size()))
                      walk(C->getArgOperand(static_cast<unsigned>(u)), n + 1);
                  }
                }
              };
              for (const llvm::BasicBlock &BB : *D) {
                const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                if (R && R->getReturnValue())
                  walk(R->getReturnValue(), 0);
              }
            }
            if (unkQ)
              return finish(opened());
            if (saw && (pureEntry(acc) || pureGlobal(acc)))
              return finish(acc);
          }
          Status inner = bytesOf(actual, depth + 1);
          if (pureEntry(inner) || pureGlobal(inner))
            return finish(inner);
          if (const llvm::Function *Caller = CB->getFunction()) {
            std::vector<const llvm::Value *> carried;
            valueSources(Caller, actual, carried);
            Status accC;
            bool sawC = false;
            bool badC = false;
            for (const llvm::Value *S : carried) {
              Status one = bytesOf(S, depth + 1);
              if (!one.any)
                continue;
              if (!(pureEntry(one) || pureGlobal(one))) {
                badC = true;
                continue;
              }
              if (sawC && accC.args != one.args)
                badC = true;
              if (!sawC)
                accC = one;
              sawC = true;
            }
            if (sawC && !badC)
              return finish(accC);
          }
        }
        // Several formals can reach the return. They are the same bytes when
        // every one of them reduces to the same entry parameter. A pointer
        // that does not reach the return, such as a key, is not in the set.
        {
          Status acc;
          bool saw = false;
          bool bad = false;
          bool anySet = false;
          for (const llvm::Function *D0 : cals) {
            const llvm::Function *D = definedBody(D0);
            if (!D || D->isDeclaration())
              continue;
            std::unordered_map<const llvm::Value *, std::set<int>> reachMemo;
            std::function<std::set<int>(const llvm::Value *)> reach;
            reach = [&](const llvm::Value *cur) -> std::set<int> {
              if (!cur)
                return {};
              auto it = reachMemo.find(cur);
              if (it != reachMemo.end())
                return it->second;
              reachMemo.emplace(cur, std::set<int>{});
              const llvm::Value *key = cur;
              std::set<int> s;
              cur = peel(cur);
              if (!cur)
                return {};
              if (const auto *GA = llvm::dyn_cast<llvm::Argument>(cur)) {
                if (GA->getParent() == D)
                  s.insert(static_cast<int>(GA->getArgNo()));
              } else if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
                s = reach(GG->getPointerOperand());
              } else if (const auto *LL = llvm::dyn_cast<llvm::LoadInst>(cur)) {
                std::vector<const llvm::Value *> ws;
                Cell c = cellOf(LL->getPointerOperand());
                if (c.root)
                  collect(c.root, c.idx, ws, 0);
                for (const llvm::Value *w : ws) {
                  if (!w)
                    continue;
                  std::set<int> t = reach(w);
                  s.insert(t.begin(), t.end());
                }
                if (s.empty())
                  s = reach(LL->getPointerOperand());
              } else if (const auto *RC = llvm::dyn_cast<llvm::CallBase>(cur)) {
                if (const llvm::Function *Cal = RC->getCalledFunction()) {
                  int u = retArg(Cal);
                  if (u >= 0 && u < static_cast<int>(RC->arg_size()))
                    s = reach(RC->getArgOperand(static_cast<unsigned>(u)));
                }
                if (s.empty()) {
                  for (const llvm::Use &U : RC->args()) {
                    if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                      continue;
                    std::set<int> t = reach(U.get());
                    s.insert(t.begin(), t.end());
                  }
                }
              } else if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(cur)) {
                if (const llvm::Value *st = spillValue(AI))
                  s = reach(st);
                else if (const llvm::Function *AF = AI->getFunction()) {
                  const llvm::Value *one = nullptr;
                  bool many = false;
                  for (const llvm::Instruction &I : llvm::instructions(*AF)) {
                    const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                    if (!SI || !SI->getValueOperand()->getType()->isPointerTy() ||
                        llvm::isa<llvm::Constant>(SI->getValueOperand()))
                      continue;
                    Cell dst = cellOf(SI->getPointerOperand());
                    if (dst.root != AI)
                      continue;
                    if (one && one != SI->getValueOperand())
                      many = true;
                    one = SI->getValueOperand();
                  }
                  if (one && !many)
                    s = reach(one);
                }
              }
              reachMemo[key] = s;
              return s;
            };
            std::set<int> formals;
            for (const llvm::BasicBlock &BB : *D) {
              const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
              if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                continue;
              std::set<int> t = reach(R->getReturnValue());
              formals.insert(t.begin(), t.end());
            }
            if (formals.empty())
              continue;
            anySet = true;
            for (int fi : formals) {
              if (fi < 0 || fi >= static_cast<int>(CB->arg_size())) {
                bad = true;
                continue;
              }
              Status one = bytesOf(CB->getArgOperand(static_cast<unsigned>(fi)), depth + 1);
              if (!one.any)
                continue;
              if (!(pureEntry(one) || pureGlobal(one))) {
                bad = true;
                continue;
              }
              if (saw && acc.args != one.args)
                bad = true;
              if (!saw)
                acc = one;
              saw = true;
            }
          }
          if (anySet && saw && !bad)
            return finish(acc);
        }
        // The returned pointer is the value stored in that cell. The store is
        // at this call, into the actual, and it is not a formal of the callee.
        {
          std::vector<const llvm::Value *> held;
          const llvm::Function *Caller = CB->getFunction();
          for (const llvm::Function *D0 : cals) {
            const llvm::Function *D = definedBody(D0);
            if (!D || D->isDeclaration() || !Caller)
              continue;
            for (const llvm::BasicBlock &BB : *D) {
              const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
              if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                continue;
              const auto *RL = llvm::dyn_cast<llvm::LoadInst>(peel(R->getReturnValue()));
              if (!RL)
                continue;
              Cell c = cellOf(RL->getPointerOperand());
              if (llvm::isa<llvm::AllocaInst>(c.root)) {
                collect(c.root, c.idx, held, 0);
                continue;
              }
              const auto *FA = llvm::dyn_cast<llvm::Argument>(c.root);
              if (!FA || FA->getParent() != D || FA->getArgNo() >= CB->arg_size())
                continue;
              const llvm::Value *actual = peel(CB->getArgOperand(FA->getArgNo()));
              if (!actual)
                continue;
              for (const llvm::Instruction &I : llvm::instructions(*Caller)) {
                const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                if (!SI || !SI->getValueOperand()->getType()->isPointerTy())
                  continue;
                if (llvm::isa<llvm::Constant>(SI->getValueOperand()))
                  continue;
                Cell dst = cellOf(SI->getPointerOperand());
                if (dst.root == actual && dst.idx == c.idx) {
                  bool seen = false;
                  for (const llvm::Value *E : held)
                    if (E == SI->getValueOperand())
                      seen = true;
                  if (!seen)
                    held.push_back(SI->getValueOperand());
                }
              }
            }
          }
          if (!held.empty()) {
            Status acc;
            bool saw = false;
            bool bad = false;
            for (const llvm::Value *w : held) {
              if (!w) {
                bad = true;
                continue;
              }
              Status one = bytesOf(w, depth + 1);
              if (!one.any)
                continue;
              if (!(pureEntry(one) || pureGlobal(one))) {
                bad = true;
                continue;
              }
              if (saw && acc.args != one.args)
                bad = true;
              if (!saw)
                acc = one;
              saw = true;
            }
            if (saw && !bad)
              return finish(acc);
            if (saw && bad)
              return finish(opened());
          }
        }
        // A fresh return. A pointer stored into the returned object, or passed
        // with it into a call, is the bytes that object carries.
        std::vector<const llvm::Value *> slots;
        std::vector<const llvm::Value *> srcs;
        auto addSlot = [&](const llvm::Value *S) {
          if (!S)
            return;
          for (const llvm::Value *E : slots)
            if (E == S)
              return;
          slots.push_back(S);
        };
        auto addSrc = [&](const llvm::Value *S) {
          if (!S)
            return;
          for (const llvm::Value *E : srcs)
            if (E == S)
              return;
          srcs.push_back(S);
        };
        addSlot(CB);
        for (const llvm::Function *D0 : cals) {
          const llvm::Function *D = definedBody(D0);
          if (!D || D->isDeclaration())
            continue;
          for (const llvm::BasicBlock &BB : *D) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
            if (!R || !R->getReturnValue())
              continue;
            const llvm::Value *cur = R->getReturnValue();
            std::unordered_set<const llvm::Value *> sc;
            while (cur && sc.insert(cur).second) {
              cur = peel(cur);
              if (!cur)
                break;
              if (const auto *LL = llvm::dyn_cast<llvm::LoadInst>(cur)) {
                if (const auto *Slot = llvm::dyn_cast<llvm::AllocaInst>(LL->getPointerOperand()->stripPointerCasts()))
                  addSlot(Slot);
                cur = LL->getPointerOperand();
                continue;
              }
              if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
                cur = GG->getPointerOperand();
                continue;
              }
              break;
            }
          }
          for (const llvm::Instruction &I : llvm::instructions(*D)) {
            const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!UC || UC->isInlineAsm())
              continue;
            int obj = -1;
            for (unsigned ai = 0; ai < UC->arg_size(); ++ai) {
              for (const llvm::Value *S : slots)
                if (derivedFrom(UC->getArgOperand(ai), S))
                  obj = static_cast<int>(ai);
            }
            if (obj < 0)
              continue;
            for (unsigned ai = 0; ai < UC->arg_size(); ++ai) {
              if (static_cast<int>(ai) == obj || !UC->getArgOperand(ai)->getType()->isPointerTy())
                continue;
              bool self = false;
              for (const llvm::Value *S : slots)
                if (derivedFrom(UC->getArgOperand(ai), S))
                  self = true;
              if (self || llvm::isa<llvm::Constant>(UC->getArgOperand(ai)))
                continue;
              const llvm::Value *sp = peel(UC->getArgOperand(ai));
              if (const auto *FA = llvm::dyn_cast<llvm::Argument>(sp)) {
                if (FA->getParent() == D && FA->getArgNo() < CB->arg_size())
                  addSrc(CB->getArgOperand(FA->getArgNo()));
              }
            }
          }
        }
        Status acc;
        bool saw = false;
        bool bad = false;
        auto takeSrc = [&](const llvm::Value *src) {
          if (!src || src == CB || !src->getType()->isPointerTy())
            return;
          Status one = bytesOf(src, depth + 1);
          if (!one.any)
            return;
          if (!(pureEntry(one) || pureGlobal(one))) {
            bad = true;
            return;
          }
          if (saw && acc.args != one.args)
            bad = true;
          if (!saw)
            acc = one;
          saw = true;
        };
        for (const llvm::Value *S : srcs)
          takeSrc(S);
        if (const llvm::Function *Fn = CB->getFunction()) {
          for (const llvm::Instruction &I : llvm::instructions(*Fn)) {
            const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!UC || UC == CB || UC->isInlineAsm())
              continue;
            bool handed = false;
            for (const llvm::Use &Arg : UC->args())
              if (derivedFrom(Arg.get(), CB))
                handed = true;
            if (!handed)
              continue;
            for (unsigned ai = 0; ai < UC->arg_size(); ++ai) {
              const llvm::Value *Arg = UC->getArgOperand(ai);
              if (derivedFrom(Arg, CB) || !Arg->getType()->isPointerTy() || llvm::isa<llvm::Constant>(Arg))
                continue;
              int objIx = -1;
              for (unsigned aj = 0; aj < UC->arg_size(); ++aj)
                if (derivedFrom(UC->getArgOperand(aj), CB))
                  objIx = static_cast<int>(aj);
              if (objIx < 0)
                continue;
              bool copiedIn = false;
              std::vector<const llvm::Function *> cs;
              auto rit2 = resolved.find(UC);
              if (rit2 != resolved.end())
                cs = rit2->second;
              else if (const llvm::Function *CD = UC->getCalledFunction())
                cs.push_back(CD);
              for (const llvm::Function *C0 : cs) {
                const llvm::Function *CD = definedBody(C0);
                if (!CD || CD->isDeclaration() || objIx >= static_cast<int>(CD->arg_size()) ||
                    ai >= CD->arg_size())
                  continue;
                const llvm::Argument *O = CD->getArg(static_cast<unsigned>(objIx));
                const llvm::Argument *S = CD->getArg(ai);
                for (const llvm::Instruction &CI : llvm::instructions(*CD)) {
                  if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&CI)) {
                    if (derivedFrom(SI->getPointerOperand(), O) && derivedFrom(SI->getValueOperand(), S))
                      copiedIn = true;
                  }
                }
              }
              if (copiedIn)
                takeSrc(Arg);
            }
          }
        }
        if (saw && !bad)
          return finish(acc);
        return finish(opened());
      }
      return finish(opened());
    };
    // A memcpy whose destination is one formal and whose source is another.
    // A call that passes those two formals on to such a memcpy is the same copy.
    struct CopyKey {
      const llvm::Function *F = nullptr;
      unsigned dst = 0;
      unsigned src = 0;
      bool operator<(const CopyKey &o) const {
        if (F != o.F)
          return F < o.F;
        if (dst != o.dst)
          return dst < o.dst;
        return src < o.src;
      }
    };
    std::map<CopyKey, char> copyMemo;
    std::set<CopyKey> copyStack;
    std::unordered_set<const llvm::AllocaInst *> reachAlloca;
    std::unordered_set<const llvm::Value *> reachHold;
    std::unordered_set<const llvm::Value *> reachPath;
    std::function<bool(const llvm::Function *, unsigned, unsigned, int)> copiesArg;
    std::function<bool(const llvm::Value *, const llvm::Function *, unsigned, int)> reachesF;
    reachesF = [&](const llvm::Value *V, const llvm::Function *F, unsigned ix, int d) -> bool {
      if (!V || !F || ix >= F->arg_size())
        return false;
      V = peel(V);
      if (!V || !reachPath.insert(V).second)
        return false;
      struct ReachPop {
        std::unordered_set<const llvm::Value *> &s;
        const llvm::Value *v;
        ~ReachPop() { s.erase(v); }
      } reachPop{reachPath, V};
      V = peel(V);
      if (!V)
        return false;
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V))
        return A->getParent() == F && A->getArgNo() == ix;
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V))
        return reachesF(G->getPointerOperand(), F, ix, d + 1);
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V))
        return reachesF(L->getPointerOperand(), F, ix, d + 1);
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
        if (const llvm::Value *st = spillValue(AI))
          return reachesF(st, F, ix, d + 1);
        // A local filled by a call that copies another value is that value.
        // The value is the formal when that other argument reaches it.
        if (!AI->getFunction())
          return false;
        if (!reachAlloca.insert(AI).second)
          return false;
        bool yes = false;
        for (const llvm::Instruction &I : llvm::instructions(*AI->getFunction())) {
          if (yes)
            break;
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            if (SI->getValueOperand()->getType()->isPointerTy() &&
                derivedFrom(SI->getPointerOperand(), AI) &&
                reachesF(SI->getValueOperand(), F, ix, d + 1))
              yes = true;
          }
          const llvm::Value *ms = nullptr;
          const llvm::Value *md = nullptr;
          if (const auto *M = llvm::dyn_cast<llvm::MemCpyInst>(&I)) {
            ms = M->getSource();
            md = M->getDest();
          } else if (const auto *MV = llvm::dyn_cast<llvm::MemMoveInst>(&I)) {
            ms = MV->getSource();
            md = MV->getDest();
          }
          if (ms && md && derivedFrom(md, AI) && reachesF(ms, F, ix, d + 1))
            yes = true;
          const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!C || C->isInlineAsm() || yes)
            continue;
          int oi = -1;
          for (unsigned ai = 0; ai < C->arg_size(); ++ai)
            if (derivedFrom(C->getArgOperand(ai), AI))
              oi = static_cast<int>(ai);
          if (oi < 0)
            continue;
          std::vector<const llvm::Function *> cs;
          auto rit = resolved.find(C);
          if (rit != resolved.end())
            cs = rit->second;
          else if (const llvm::Function *CD = C->getCalledFunction())
            cs.push_back(CD);
          for (unsigned si = 0; si < C->arg_size() && !yes; ++si) {
            if (static_cast<int>(si) == oi)
              continue;
            const llvm::Value *S = C->getArgOperand(si);
            if (!S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S))
              continue;
            if (!reachesF(S, F, ix, d + 1))
              continue;
            for (const llvm::Function *CD : cs)
              if (copiesArg(CD, static_cast<unsigned>(oi), si, 0))
                yes = true;
          }
        }
        reachAlloca.erase(AI);
        return yes;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
        const llvm::Value *only = nullptr;
        int n = 0;
        bool hit = false;
        for (const llvm::Use &U : C->args()) {
          if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
            continue;
          ++n;
          only = U.get();
          if (reachesF(U.get(), F, ix, d + 1))
            hit = true;
        }
        if (hit && n == 1 && only)
          return true;
      }
      // A pointer kept in the formal is part of that formal. The buffer a
      // constructor allocates and stores into its object is that object.
      if (V->getType()->isPointerTy() && reachHold.insert(V).second) {
        bool held = false;
        auto storedInto = [&](const llvm::Value *X) {
          if (!X)
            return;
          for (const llvm::User *U : X->users()) {
            const llvm::Value *kept = nullptr;
            if (const auto *CI = llvm::dyn_cast<llvm::CastInst>(U))
              kept = CI;
            const llvm::Value *slot = X;
            const llvm::User *SU = U;
            if (kept) {
              slot = kept;
              for (const llvm::User *U2 : kept->users()) {
                const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U2);
                if (!SI || peel(SI->getValueOperand()) != slot || SI->getFunction() != F)
                  continue;
                if (reachesF(SI->getPointerOperand(), F, ix, d + 1))
                  held = true;
              }
              continue;
            }
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(SU);
            if (!SI || peel(SI->getValueOperand()) != slot || SI->getFunction() != F)
              continue;
            if (reachesF(SI->getPointerOperand(), F, ix, d + 1))
              held = true;
          }
        };
        storedInto(V);
        reachHold.erase(V);
        if (held)
          return true;
      }
      return false;
    };
    copiesArg = [&](const llvm::Function *F0, unsigned dst, unsigned src, int d) -> bool {
      const llvm::Function *F = definedBody(F0);
      if (!F || F->isDeclaration() || dst >= F->arg_size() || src >= F->arg_size() || dst == src)
        return false;
      CopyKey key{F, dst, src};
      auto it = copyMemo.find(key);
      if (it != copyMemo.end())
        return it->second == 1;
      if (!copyStack.insert(key).second)
        return false;
      bool yes = false;
      bool cut = false;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const llvm::Value *ms = nullptr;
        const llvm::Value *md = nullptr;
        if (const auto *M = llvm::dyn_cast<llvm::MemCpyInst>(&I)) {
          ms = M->getSource();
          md = M->getDest();
        } else if (const auto *MV = llvm::dyn_cast<llvm::MemMoveInst>(&I)) {
          ms = MV->getSource();
          md = MV->getDest();
        }
        if (ms && md && reachesF(ms, F, src, 0) && reachesF(md, F, dst, 0))
          yes = true;
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (SI->getValueOperand()->getType()->isPointerTy() &&
              reachesF(SI->getPointerOperand(), F, dst, 0) &&
              reachesF(SI->getValueOperand(), F, src, 0))
            yes = true;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || yes)
          continue;
        int di = -1;
        int si = -1;
        for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
          const llvm::Value *Op = C->getArgOperand(ai);
          if (!Op->getType()->isPointerTy())
            continue;
          bool rd = reachesF(Op, F, dst, 0);
          bool rs = reachesF(Op, F, src, 0);
          if (rd && !rs && di < 0)
            di = static_cast<int>(ai);
          if (rs && !rd && si < 0)
            si = static_cast<int>(ai);
        }
        if (di < 0 || si < 0)
          continue;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        else if (const llvm::Function *CD = C->getCalledFunction())
          cs.push_back(CD);
        for (const llvm::Function *CD : cs) {
          if (d == 12)
            cut = true;
          else if (copiesArg(CD, static_cast<unsigned>(di), static_cast<unsigned>(si), d + 1))
            yes = true;
        }
      }
      copyStack.erase(key);
      if (!cut)
        copyMemo[key] = yes ? 1 : 2;
      return yes;
    };
    // The formal a copy reads or writes, and the field path inside it. A copy
    // of one field is that field, not the whole object. Sub-fields of one field
    // are that field. Two fields with no common path are not one source.
    struct FieldGot {
      bool whole = false;
      std::vector<std::vector<uint64_t>> idxs;
    };
    struct FieldPair {
      FieldGot src;
      FieldGot dst;
    };
    std::map<CopyKey, FieldPair> fieldMemo;
    std::set<CopyKey> fieldStack;
    auto fieldResolve = [](const FieldGot &g, std::vector<uint64_t> &idx) -> int {
      if (g.whole && !g.idxs.empty())
        return 3;
      if (g.whole)
        return 1;
      if (g.idxs.empty())
        return 0;
      idx = g.idxs[0];
      for (const std::vector<uint64_t> &o : g.idxs) {
        size_t n = 0;
        while (n < idx.size() && n < o.size() && idx[n] == o[n])
          ++n;
        idx.resize(n);
      }
      if (idx.empty())
        return 3;
      return 2;
    };
    std::function<FieldPair(const llvm::Function *, unsigned, unsigned, int)> copyField;
    copyField = [&](const llvm::Function *F0, unsigned dst, unsigned src, int d) -> FieldPair {
      FieldPair none;
      const llvm::Function *F = definedBody(F0);
      if (!F || F->isDeclaration() || dst >= F->arg_size() || src >= F->arg_size() || dst == src)
        return none;
      CopyKey key{F, dst, src};
      auto it = fieldMemo.find(key);
      if (it != fieldMemo.end())
        return it->second;
      if (!fieldStack.insert(key).second)
        return none;
      FieldPair got;
      bool cut = false;
      auto addIdx = [](FieldGot &g, const std::vector<uint64_t> &idx) {
        if (idx.empty())
          g.whole = true;
        else
          g.idxs.push_back(idx);
      };
      std::function<const llvm::Value *(const llvm::Value *, unsigned, int)> drill;
      drill = [&](const llvm::Value *V, unsigned ix, int left) -> const llvm::Value * {
        if (!V || left <= 0)
          return V;
        V = peel(V);
        if (!V)
          return nullptr;
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
          const llvm::Value *only = nullptr;
          int n = 0;
          bool hit = false;
          for (const llvm::Use &U : C->args()) {
            if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
              continue;
            ++n;
            if (reachesF(U.get(), F, ix, 0)) {
              only = U.get();
              hit = true;
            }
          }
          if (hit && n == 1 && only)
            return drill(only, ix, left - 1);
        }
        return V;
      };
      auto noteEnd = [&](const llvm::Value *V, unsigned ix, FieldGot &g) {
        const llvm::Value *D = drill(V, ix, 8);
        Cell c = cellOf(D ? D : V);
        const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(c.root);
        if (!A || A->getParent() != F || A->getArgNo() != ix)
          return;
        addIdx(g, c.idx);
      };
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const llvm::Value *ms = nullptr;
        const llvm::Value *md = nullptr;
        if (const auto *M = llvm::dyn_cast<llvm::MemCpyInst>(&I)) {
          ms = M->getSource();
          md = M->getDest();
        } else if (const auto *MV = llvm::dyn_cast<llvm::MemMoveInst>(&I)) {
          ms = MV->getSource();
          md = MV->getDest();
        }
        if (ms && md && reachesF(ms, F, src, 0) && reachesF(md, F, dst, 0)) {
          noteEnd(ms, src, got.src);
          noteEnd(md, dst, got.dst);
        }
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (SI->getValueOperand()->getType()->isPointerTy() &&
              reachesF(SI->getPointerOperand(), F, dst, 0) &&
              reachesF(SI->getValueOperand(), F, src, 0)) {
            noteEnd(SI->getValueOperand(), src, got.src);
            noteEnd(SI->getPointerOperand(), dst, got.dst);
          }
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        int di = -1;
        int si = -1;
        auto cellFormal = [&](const llvm::Value *Op, unsigned ix) {
          Cell o = cellOf(drill(Op, ix, 8));
          const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(o.root);
          return A && A->getParent() == F && A->getArgNo() == ix;
        };
        for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
          const llvm::Value *Op = C->getArgOperand(ai);
          if (!Op->getType()->isPointerTy())
            continue;
          bool rd = reachesF(Op, F, dst, 0);
          bool rs = reachesF(Op, F, src, 0);
          // A field of the formal is that formal even when the result is also
          // stored onward. The first operand that merely reaches both is not
          // a reason to hide the field.
          bool srcCell = cellFormal(Op, src);
          bool dstCell = cellFormal(Op, dst);
          if (srcCell && !dstCell) {
            Cell o = cellOf(drill(Op, src, 8));
            if (si < 0 || !o.idx.empty())
              si = static_cast<int>(ai);
          } else if (dstCell && !srcCell)
            di = static_cast<int>(ai);
          else if (rd && !rs && di < 0)
            di = static_cast<int>(ai);
          else if (rs && !rd && si < 0)
            si = static_cast<int>(ai);
        }
        // The callee writes this field into its sret. The sret is a local
        // whose later copy into the destination formal is a separate step.
        // The field copied out is still this field.
        int sretIx = -1;
        for (unsigned aj = 0; aj < C->arg_size(); ++aj)
          if (C->paramHasAttr(aj, llvm::Attribute::StructRet))
            sretIx = static_cast<int>(aj);
        if (sretIx >= 0) {
          std::vector<const llvm::Function *> rsCs;
          auto ritS = resolved.find(C);
          if (ritS != resolved.end())
            rsCs = ritS->second;
          else if (const llvm::Function *CD = C->getCalledFunction())
            rsCs.push_back(CD);
          for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
            if (static_cast<int>(ai) == sretIx)
              continue;
            const llvm::Value *Op = C->getArgOperand(ai);
            if (!Op->getType()->isPointerTy() || !cellFormal(Op, src))
              continue;
            for (const llvm::Function *CD : rsCs) {
              if (d == 12) {
                cut = true;
                continue;
              }
              if (copiesArg(CD, static_cast<unsigned>(sretIx), ai, d + 1))
                noteEnd(Op, src, got.src);
            }
          }
        }
        if (di < 0 || si < 0)
          continue;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        else if (const llvm::Function *CD = C->getCalledFunction())
          cs.push_back(CD);
        for (const llvm::Function *CD : cs) {
          if (d == 12) {
            cut = true;
            continue;
          }
          FieldPair inner = copyField(CD, static_cast<unsigned>(di), static_cast<unsigned>(si), d + 1);
          auto lift = [&](const FieldGot &innerG, const llvm::Value *Op, unsigned ix, FieldGot &outG) {
            Cell op = cellOf(drill(Op, ix, 8));
            const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(op.root);
            if (!A || A->getParent() != F || A->getArgNo() != ix) {
              if (innerG.whole || !innerG.idxs.empty())
                outG.whole = true;
              return;
            }
            if (innerG.whole)
              addIdx(outG, op.idx);
            for (const std::vector<uint64_t> &id : innerG.idxs) {
              std::vector<uint64_t> comb = op.idx;
              comb.insert(comb.end(), id.begin(), id.end());
              addIdx(outG, comb);
            }
          };
          lift(inner.dst, C->getArgOperand(static_cast<unsigned>(di)), dst, got.dst);
          lift(inner.src, C->getArgOperand(static_cast<unsigned>(si)), src, got.src);
          // The callee copies, and the field it names is the whole formal it
          // was given. The caller's operand is that formal, so the operand's
          // field is the copy. An empty inner field must not drop it.
          bool named = inner.src.whole || !inner.src.idxs.empty() || inner.dst.whole || !inner.dst.idxs.empty();
          if (!named && copiesArg(CD, static_cast<unsigned>(di), static_cast<unsigned>(si), d + 1)) {
            noteEnd(C->getArgOperand(static_cast<unsigned>(si)), src, got.src);
            noteEnd(C->getArgOperand(static_cast<unsigned>(di)), dst, got.dst);
          }
        }
      }
      fieldStack.erase(key);
      if (!cut)
        fieldMemo[key] = got;
      return got;
    };
    // Bytes copied into an object. The pointer's own identity may be a fresh
    // allocation. The bytes are the sources of those copies.
    std::unordered_map<const llvm::Value *, Status> obMemo;
    std::unordered_set<const llvm::Value *> obStack;
    std::function<void(const llvm::Value *, std::vector<const llvm::Value *> &,
                       std::unordered_set<const llvm::Value *> &)>
        copySources;
    copySources = [&](const llvm::Value *V, std::vector<const llvm::Value *> &out,
                      std::unordered_set<const llvm::Value *> &seen) {
      if (!V || !seen.insert(V).second)
        return;
      const llvm::Value *raw = V;
      V = peel(V);
      if (!V)
        return;
      seen.insert(V);
      auto pushS = [&](const llvm::Value *S) {
        if (!S || S == raw || S == V || !S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S))
          return;
        for (const llvm::Value *E : out)
          if (E == S)
            return;
        out.push_back(S);
      };
      auto forwarded = [&](const llvm::Value *Act) -> const llvm::Value * {
        Act = peel(Act);
        if (!Act)
          return nullptr;
        if (llvm::isa<llvm::Argument>(Act))
          return Act;
        if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(Act)) {
          if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()))) {
            if (const llvm::Value *st = spillValue(SA)) {
              st = peel(st);
              if (st && llvm::isa<llvm::Argument>(st))
                return st;
            }
          }
        }
        return nullptr;
      };
      if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        copySources(GG->getPointerOperand(), out, seen);
        return;
      }
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        auto sit = sites.find(A->getParent());
        if (sit == sites.end())
          return;
        for (const llvm::CallBase *Call : sit->second) {
          if (!Call || A->getArgNo() >= Call->arg_size())
            continue;
          if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), A->getParent()))
            continue;
          const llvm::Value *act = Call->getArgOperand(A->getArgNo());
          if (const llvm::Value *fw = forwarded(act))
            copySources(fw, out, seen);
          else
            copySources(act, out, seen);
        }
        return;
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
        const llvm::Value *only = nullptr;
        int n = 0;
        for (const llvm::Use &U : CB->args()) {
          if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
            continue;
          ++n;
          only = U.get();
        }
        if (n == 1 && only)
          copySources(only, out, seen);
        return;
      }
      std::unordered_map<const llvm::Argument *, std::vector<const llvm::Argument *>> compMemo;
      std::function<const std::vector<const llvm::Argument *> &(const llvm::Argument *)> component;
      component = [&](const llvm::Argument *A) -> const std::vector<const llvm::Argument *> & {
        static const std::vector<const llvm::Argument *> emptyComp;
        if (!A)
          return emptyComp;
        auto itC = compMemo.find(A);
        if (itC != compMemo.end())
          return itC->second;
        std::unordered_set<const llvm::Argument *> objs;
        std::function<void(const llvm::Argument *)> methods;
        methods = [&](const llvm::Argument *X) {
          if (!X || !objs.insert(X).second)
            return;
          auto sit = sites.find(X->getParent());
          if (sit != sites.end()) {
            for (const llvm::CallBase *Call : sit->second) {
              if (!Call || X->getArgNo() >= Call->arg_size())
                continue;
              if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), X->getParent()))
                continue;
              if (const llvm::Value *fw = forwarded(Call->getArgOperand(X->getArgNo())))
                if (const auto *B = llvm::dyn_cast<llvm::Argument>(fw))
                  methods(B);
            }
          }
          if (!X->getParent() || X->getParent()->isDeclaration())
            return;
          for (const llvm::Instruction &I : llvm::instructions(*X->getParent())) {
            const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!C || C->isInlineAsm())
              continue;
            std::vector<const llvm::Function *> cs;
            auto rit = resolved.find(C);
            if (rit != resolved.end())
              cs = rit->second;
            else if (const llvm::Function *CD = C->getCalledFunction())
              cs.push_back(CD);
            for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
              const llvm::Value *Op = peel(C->getArgOperand(ai));
              bool self = Op == X;
              if (!self)
                if (const auto *OL = llvm::dyn_cast<llvm::LoadInst>(Op))
                  if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(OL->getPointerOperand())))
                    if (const llvm::Value *st = spillValue(SA))
                      self = peel(st) == X;
              if (!self)
                continue;
              for (const llvm::Function *CD0 : cs) {
                const llvm::Function *CD = definedBody(CD0);
                if (!CD || CD->isDeclaration() || ai >= CD->arg_size())
                  continue;
                methods(CD->getArg(ai));
              }
            }
          }
        };
        methods(A);
        std::vector<const llvm::Argument *> list(objs.begin(), objs.end());
        std::sort(list.begin(), list.end(), [](const llvm::Argument *a, const llvm::Argument *b) {
          const llvm::Function *fa = a->getParent();
          const llvm::Function *fb = b->getParent();
          std::string an = fa && fa->hasName() ? fa->getName().str() : "";
          std::string bn = fb && fb->hasName() ? fb->getName().str() : "";
          if (an != bn)
            return an < bn;
          if (fa != fb)
            return fa < fb;
          return a->getArgNo() < b->getArgNo();
        });
        auto ins = compMemo.emplace(A, std::move(list));
        return ins.first->second;
      };
      auto fieldLoad = [&](const llvm::Value *S, const std::vector<uint64_t> &idx) -> const llvm::LoadInst * {
        const llvm::Value *P = peel(S);
        const llvm::Argument *A = llvm::dyn_cast_or_null<llvm::Argument>(P);
        if (!A)
          if (const auto *LI = llvm::dyn_cast_or_null<llvm::LoadInst>(P))
            if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand())))
              if (const llvm::Value *st = spillValue(SA))
                A = llvm::dyn_cast<llvm::Argument>(peel(st));
        if (!A || idx.empty())
          return nullptr;
        std::vector<const llvm::Argument *> comp = component(A);
        for (const llvm::Argument *B : comp) {
          if (!B->getParent() || B->getParent()->isDeclaration())
            continue;
          for (const llvm::Instruction &I : llvm::instructions(*B->getParent())) {
            const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I);
            if (!L)
              continue;
            Cell o = cellOf(L->getPointerOperand());
            if (o.root == B && o.idx == idx)
              return L;
          }
        }
        return nullptr;
      };
      auto idxPrefix = [](const std::vector<uint64_t> &a, const std::vector<uint64_t> &b) {
        if (a.size() > b.size())
          return false;
        return std::equal(a.begin(), a.end(), b.begin());
      };
      auto fromCall = [&](const llvm::CallBase *C, int oi, const std::vector<uint64_t> *needDst) {
        if (!C || oi < 0)
          return;
        std::vector<const llvm::Function *> cs;
        auto rit = resolved.find(C);
        if (rit != resolved.end())
          cs = rit->second;
        else if (const llvm::Function *CD = C->getCalledFunction())
          cs.push_back(CD);
        for (unsigned si = 0; si < C->arg_size(); ++si) {
          if (static_cast<int>(si) == oi)
            continue;
          const llvm::Value *S = C->getArgOperand(si);
          if (!S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S))
            continue;
          for (const llvm::Function *CD : cs) {
            if (!copiesArg(CD, static_cast<unsigned>(oi), si, 0))
              continue;
            FieldPair fp = copyField(CD, static_cast<unsigned>(oi), si, 0);
            std::vector<uint64_t> dstIdx;
            std::vector<uint64_t> srcIdx;
            int dk = fieldResolve(fp.dst, dstIdx);
            int sk = fieldResolve(fp.src, srcIdx);
            if (needDst) {
              if (dk != 2 || !idxPrefix(*needDst, dstIdx) && !idxPrefix(dstIdx, *needDst))
                continue;
            }
            if (sk == 2) {
              if (const llvm::LoadInst *Ld = fieldLoad(S, srcIdx))
                pushS(Ld);
              else
                pushS(S);
            } else
              pushS(S);
          }
        }
      };
      auto scanFn = [&](const llvm::Function *SF, const llvm::Value *Root, const std::vector<uint64_t> &idx) {
        if (!SF || SF->isDeclaration() || !Root)
          return;
        for (const llvm::Instruction &I : llvm::instructions(*SF)) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!C || C->isInlineAsm())
            continue;
          int exact = -1;
          std::vector<std::pair<int, std::vector<uint64_t>>> under;
          for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
            const llvm::Value *Op = C->getArgOperand(ai);
            Cell o;
            if (const auto *OL = llvm::dyn_cast<llvm::LoadInst>(peel(Op)))
              o = cellOf(OL->getPointerOperand());
            else
              o = cellOf(Op);
            if (o.root != Root)
              continue;
            if (o.idx == idx)
              exact = static_cast<int>(ai);
            else if (idxPrefix(o.idx, idx) && o.idx.size() < idx.size()) {
              std::vector<uint64_t> suf(idx.begin() + static_cast<std::ptrdiff_t>(o.idx.size()), idx.end());
              under.push_back({static_cast<int>(ai), std::move(suf)});
            }
          }
          if (exact >= 0)
            fromCall(C, exact, nullptr);
          for (const auto &u : under)
            if (u.first != exact)
              fromCall(C, u.first, &u.second);
        }
      };
      auto scanCell = [&](const Cell &c, const llvm::Function *Fn) {
        if (!c.root)
          return;
        if (const auto *RA = llvm::dyn_cast<llvm::Argument>(c.root)) {
          std::vector<const llvm::Argument *> comp = component(RA);
          for (const llvm::Argument *A : comp)
            scanFn(A->getParent(), A, c.idx);
        } else if (Fn)
          scanFn(Fn, c.root, c.idx);
      };
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand()))) {
          if (const llvm::Value *st = spillValue(SA)) {
            copySources(st, out, seen);
            return;
          }
        }
        Cell c = cellOf(L->getPointerOperand());
        const llvm::Function *Fn = L->getFunction();
        if (!c.root || !Fn)
          return;
        scanCell(c, Fn);
        return;
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
        if (const llvm::Value *st = spillValue(AI)) {
          copySources(st, out, seen);
          return;
        }
        const llvm::Function *Fn = AI->getFunction();
        if (!Fn)
          return;
        for (const llvm::Instruction &I : llvm::instructions(*Fn)) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!C || C->isInlineAsm())
            continue;
          int oi = -1;
          for (unsigned ai = 0; ai < C->arg_size(); ++ai)
            if (derivedFrom(C->getArgOperand(ai), AI))
              oi = static_cast<int>(ai);
          fromCall(C, oi, nullptr);
        }
      }
    };
    std::function<Status(const llvm::Value *, int, bool)> originBytes;
    originBytes = [&](const llvm::Value *V, int d, bool allowSelf) -> Status {
      if (!V || !V->getType()->isPointerTy())
        return opened();
      if (allowSelf) {
        auto it = obMemo.find(V);
        if (it != obMemo.end())
          return it->second;
      }
      if (!obStack.insert(V).second)
        return bare();
      if (allowSelf) {
        Status w = bytesOf(V, 0);
        if (pureEntry(w) || pureGlobal(w)) {
          obStack.erase(V);
          obMemo[V] = w;
          return w;
        }
      }
      std::vector<const llvm::Value *> srcs;
      std::unordered_set<const llvm::Value *> seen;
      copySources(V, srcs, seen);
      Status acc;
      bool saw = false;
      bool bad = false;
      for (const llvm::Value *S : srcs) {
        Status one = originBytes(S, d + 1, true);
        if (!one.any)
          continue;
        if (!(pureEntry(one) || pureGlobal(one))) {
          // A source with no bytes does not change the meet. An unknown
          // source does: the bytes are then not an entry argument.
          if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
            continue;
          bad = true;
          continue;
        }
        if (saw && acc.args != one.args)
          bad = true;
        if (!saw)
          acc = one;
        saw = true;
      }
      obStack.erase(V);
      if (saw && !bad) {
        if (allowSelf)
          obMemo[V] = acc;
        return acc;
      }
      return opened();
    };
    // A fresh object whose body registers a reader denotes the single data
    // pointer that reader copies from. The reader is a function defined here;
    // the store into the object is in a declaration, so the pair of calls is
    // the evidence. Two data pointers, or a reader that copies from anywhere
    // else, leave the object unresolved.
    std::unordered_map<const llvm::Value *, Status> regMemo;
    std::unordered_set<const llvm::Value *> regActive;
    std::function<Status(const llvm::Value *, int)> registered;
    registered = [&](const llvm::Value *V, int depth) -> Status {
      if (!V || !V->getType()->isPointerTy())
        return opened();
      auto itR = regMemo.find(V);
      if (itR != regMemo.end())
        return itR->second;
      if (!regActive.insert(V).second)
        return bare();
      auto done = [&](Status st) {
        regActive.erase(V);
        if (st.any)
          regMemo[V] = st;
        return st;
      };
      const llvm::Value *P = peel(V);
      if (!P)
        return done(opened());
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(P))
        return done(registered(G->getPointerOperand(), depth + 1));
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(P)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(peel(L->getPointerOperand())))
          if (const llvm::Value *st = spillValue(AI))
            return done(registered(st, depth + 1));
        return done(registered(L->getPointerOperand(), depth + 1));
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(P)) {
        const llvm::Value *one = nullptr;
        bool many = false;
        auto fnPtr = [&](const llvm::Value *v) {
          const llvm::Value *q = peel(v);
          if (!q)
            return false;
          if (llvm::isa<llvm::Function>(q))
            return true;
          if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(q)) {
            if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()))) {
              if (const llvm::Value *st = spillValue(SA)) {
                const llvm::Value *sq = peel(st);
                if (sq && (llvm::isa<llvm::Function>(sq) || llvm::isa<llvm::Constant>(sq)))
                  return true;
              }
            }
          }
          if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(q)) {
            if (const llvm::Value *st = spillValue(SA)) {
              const llvm::Value *sq = peel(st);
              if (sq && (llvm::isa<llvm::Function>(sq) || llvm::isa<llvm::Constant>(sq)))
                return true;
            }
          }
          return false;
        };
        if (const llvm::Function *AF = AI->getFunction()) {
          for (const llvm::Instruction &I : llvm::instructions(*AF)) {
            const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!UC || UC->isInlineAsm())
              continue;
            bool handed = false;
            for (const llvm::Use &Arg : UC->args())
              if (derivedFrom(Arg.get(), AI))
                handed = true;
            if (!handed)
              continue;
            for (const llvm::Use &Arg : UC->args()) {
              if (!Arg.get()->getType()->isPointerTy() || derivedFrom(Arg.get(), AI))
                continue;
              if (llvm::isa<llvm::Constant>(Arg.get()) || fnPtr(Arg.get()))
                continue;
              // A reload of this aggregate is its own contents, not a second
              // object handed to it.
              bool own = false;
              if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(peel(Arg.get())))
                own = derivedFrom(LI->getPointerOperand(), AI);
              if (own)
                continue;
              if (one && one != Arg.get())
                many = true;
              one = Arg.get();
            }
          }
        }
        if (one && !many)
          return done(registered(one, depth + 1));
        return done(opened());
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(P)) {
        if (const llvm::Function *D0 = CB->getCalledFunction()) {
          if (const llvm::Function *D = definedBody(D0)) {
            if (!D->isDeclaration()) {
              std::unordered_set<const llvm::AllocaInst *> holds;
              std::function<void(const llvm::Value *)> addObj;
              addObj = [&](const llvm::Value *v) {
                v = peel(v);
                if (!v)
                  return;
                const auto *LI = llvm::dyn_cast<llvm::LoadInst>(v);
                if (!LI)
                  return;
                const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()));
                if (!SA || !holds.insert(SA).second)
                  return;
                if (const llvm::Function *HF = SA->getFunction()) {
                  for (const llvm::Instruction &I : llvm::instructions(*HF)) {
                    const auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
                    if (!SI || llvm::isa<llvm::Constant>(SI->getValueOperand()))
                      continue;
                    Cell dst = cellOf(SI->getPointerOperand());
                    if (dst.root == SA)
                      addObj(SI->getValueOperand());
                  }
                }
              };
              (void)0;
              for (const llvm::BasicBlock &BB : *D) {
                const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                if (R && R->getReturnValue())
                  addObj(R->getReturnValue());
              }
              auto hands = [&](const llvm::Value *v) {
                v = peel(v);
                const auto *LI = llvm::dyn_cast<llvm::LoadInst>(v);
                if (!LI)
                  return false;
                const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()));
                return SA && holds.count(SA);
              };
              auto formalIx = [&](const llvm::Value *v) -> int {
                v = peel(v);
                if (!v)
                  return -1;
                if (const auto *A = llvm::dyn_cast<llvm::Argument>(v))
                  return A->getParent() == D ? static_cast<int>(A->getArgNo()) : -1;
                if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(v)) {
                  if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(peel(LI->getPointerOperand()))) {
                    if (const llvm::Value *st = spillValue(SA)) {
                      st = peel(st);
                      if (const auto *A = llvm::dyn_cast<llvm::Argument>(st))
                        return A->getParent() == D ? static_cast<int>(A->getArgNo()) : -1;
                    }
                  }
                }
                return -1;
              };
              std::set<int> dataIx;
              std::vector<const llvm::Function *> readers;
              bool readerMiss = false;
              for (const llvm::Instruction &I : llvm::instructions(*D)) {
                const auto *UC = llvm::dyn_cast<llvm::CallBase>(&I);
                if (!UC || UC->isInlineAsm())
                  continue;
                const llvm::Function *Cal = UC->getCalledFunction();
                if (!Cal || !Cal->isDeclaration())
                  continue;
                bool handed = false;
                for (const llvm::Use &Arg : UC->args())
                  if (hands(Arg.get()))
                    handed = true;
                if (!handed)
                  continue;
                for (const llvm::Use &Arg : UC->args()) {
                  if (hands(Arg.get()) || !Arg.get()->getType()->isPointerTy())
                    continue;
                  const llvm::Value *q = peel(Arg.get());
                  if (q && llvm::isa<llvm::Function>(q)) {
                    if (!llvm::cast<llvm::Function>(q)->isDeclaration())
                      readers.push_back(llvm::cast<llvm::Function>(q));
                    else
                      readerMiss = true;
                    continue;
                  }
                  int ix = formalIx(Arg.get());
                  if (ix >= 0)
                    dataIx.insert(ix);
                  else if (!llvm::isa<llvm::Constant>(Arg.get()))
                    dataIx.insert(-2);
                }
              }
              auto readsFormal = [&](const llvm::Function *RF) {
                if (!RF || RF->isDeclaration())
                  return false;
                bool copy = false;
                std::unordered_set<const llvm::Value *> seen;
                std::function<bool(const llvm::Value *, int)> fromArg;
                fromArg = [&](const llvm::Value *v, int d) -> bool {
                  if (!v)
                    return false;
                  v = peel(v);
                  if (!v || !seen.insert(v).second)
                    return false;
                  if (const auto *A = llvm::dyn_cast<llvm::Argument>(v))
                    return A->getParent() == RF;
                  if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(v))
                    return fromArg(GG->getPointerOperand(), d + 1);
                  if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(v))
                    return fromArg(LI->getPointerOperand(), d + 1);
                  if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(v)) {
                    if (const llvm::Value *st = spillValue(SA))
                      return fromArg(st, d + 1);
                    return false;
                  }
                  if (const auto *CC = llvm::dyn_cast<llvm::CallBase>(v)) {
                    int n = 0;
                    bool hit = false;
                    for (const llvm::Use &U : CC->args()) {
                      if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                        continue;
                      ++n;
                      if (fromArg(U.get(), d + 1))
                        hit = true;
                    }
                    return hit && n == 1;
                  }
                  return false;
                };
                for (const llvm::Instruction &I : llvm::instructions(*RF)) {
                  const auto *M = llvm::dyn_cast<llvm::MemCpyInst>(&I);
                  const auto *MV = llvm::dyn_cast<llvm::MemMoveInst>(&I);
                  const llvm::Value *src = nullptr;
                  if (M)
                    src = M->getSource();
                  else if (MV)
                    src = MV->getSource();
                  if (src && fromArg(src, 0))
                    copy = true;
                }
                return copy;
              };
              bool anyCopy = false;
              for (const llvm::Function *RF : readers)
                if (readsFormal(RF))
                  anyCopy = true;
              if (anyCopy && !readerMiss && dataIx.size() == 1 && *dataIx.begin() >= 0) {
                unsigned u = static_cast<unsigned>(*dataIx.begin());
                if (u < CB->arg_size()) {
                  Status w = originBytes(CB->getArgOperand(u), 0, true);
                  if (pureEntry(w) || pureGlobal(w))
                    return done(w);
                }
              }
              const llvm::Value *fwd = nullptr;
              int nf = 0;
              for (const llvm::BasicBlock &BB : *D) {
                const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                  continue;
                const llvm::Value *cur = R->getReturnValue();
                std::unordered_set<const llvm::Value *> sc;
                const llvm::Argument *hit = nullptr;
                while (cur && sc.insert(cur).second) {
                  cur = peel(cur);
                  if (!cur)
                    break;
                  if (const auto *A = llvm::dyn_cast<llvm::Argument>(cur)) {
                    if (A->getParent() == D)
                      hit = A;
                    break;
                  }
                  if (const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
                    cur = GG->getPointerOperand();
                    continue;
                  }
                  if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(cur)) {
                    cur = LI->getPointerOperand();
                    continue;
                  }
                  if (const auto *CC = llvm::dyn_cast<llvm::CallBase>(cur)) {
                    const llvm::Value *only = nullptr;
                    int n = 0;
                    for (const llvm::Use &U : CC->args()) {
                      if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                        continue;
                      ++n;
                      only = U.get();
                    }
                    if (n == 1 && only) {
                      cur = only;
                      continue;
                    }
                    break;
                  }
                  if (const auto *SA = llvm::dyn_cast<llvm::AllocaInst>(cur)) {
                    if (const llvm::Value *st = spillValue(SA)) {
                      cur = st;
                      continue;
                    }
                    break;
                  }
                  break;
                }
                if (!hit) {
                  nf = 2;
                  break;
                }
                if (fwd && fwd != CB->getArgOperand(hit->getArgNo()))
                  nf = 2;
                fwd = CB->getArgOperand(hit->getArgNo());
                nf = nf == 2 ? 2 : 1;
              }
              if (nf == 1 && fwd)
                return done(registered(fwd, depth + 1));
            }
          }
        }
      }
      return done(opened());
    };
    // A declaration has no body in this module. A field of an object that is
    // passed to it denotes the bytes passed with that same field to a
    // declaration. Two arguments are the same object when a callsite forwards
    // one as the other. A companion that does not reduce to an entry is not a
    // second entry. Two different entry sets leave the field open.
    auto fieldBytes = [&](const llvm::Value *actual, const std::string &chop) -> Status {
      auto findA = [&](const llvm::Argument *A) -> const llvm::Argument * {
        const llvm::Argument *R = A;
        std::vector<const llvm::Argument *> path;
        while (R) {
          auto it = argParent.find(R);
          if (it == argParent.end() || it->second == R)
            break;
          path.push_back(R);
          R = it->second;
        }
        for (const llvm::Argument *P : path)
          argParent[P] = R;
        return R;
      };
      auto asArg = [&](const llvm::Value *V) -> const llvm::Argument * {
        std::unordered_set<const llvm::Value *> seen;
        while (V && seen.insert(V).second) {
          V = V->stripPointerCasts();
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(V))
            return A;
          const auto *L = llvm::dyn_cast<llvm::LoadInst>(V);
          if (!L)
            break;
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!AI)
            break;
          const llvm::Value *st = spillValue(AI);
          if (!st)
            break;
          V = st;
        }
        return nullptr;
      };
      auto keyOf = [&](const llvm::Value *V) -> std::optional<FKey> {
        std::unordered_set<const llvm::Value *> seen;
        while (V && seen.insert(V).second) {
          V = V->stripPointerCasts();
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(V);
          if (!CB)
            break;
          const llvm::Value *only = nullptr;
          int np = 0;
          for (const llvm::Use &U : CB->args()) {
            if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
              continue;
            if (only && only != U.get()) {
              np = 2;
              break;
            }
            only = U.get();
            np = 1;
          }
          if (np != 1)
            break;
          V = only;
        }
        if (!V)
          return std::nullopt;
        V = V->stripPointerCasts();
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V))
          V = L->getPointerOperand();
        FKey k;
        std::unordered_set<const llvm::Value *> seenC;
        while (V && seenC.insert(V).second) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
            if (llvm::isa<llvm::BitCastInst>(C) || llvm::isa<llvm::AddrSpaceCastInst>(C)) {
              V = C->getOperand(0);
              continue;
            }
          }
          // An all-zero GEP is still a field. stripPointerCasts drops it.
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            bool all = true;
            std::vector<uint64_t> add;
            for (unsigned oi = 1; oi < G->getNumOperands(); ++oi) {
              const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(oi));
              if (!CI) {
                all = false;
                break;
              }
              add.push_back(CI->getZExtValue());
            }
            if (!all)
              return std::nullopt;
            // The index is a field of this struct. The same numbers in a
            // different struct are a different cell.
            k.ty = G->getSourceElementType();
            k.idx.insert(k.idx.begin(), add.begin(), add.end());
            V = G->getPointerOperand();
            continue;
          }
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!AI)
              break;
            const llvm::Value *st = spillValue(AI);
            if (!st)
              break;
            V = st;
            continue;
          }
          break;
        }
        const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(V ? V->stripPointerCasts() : nullptr);
        if (!A || k.idx.empty())
          return std::nullopt;
        k.root = findA(A);
        return k;
      };
      if (!fieldBuilt) {
        fieldBuilt = true;
        auto argRank = [](const llvm::Argument *A) {
          const llvm::Function *F = A ? A->getParent() : nullptr;
          std::string n = F && F->hasName() ? F->getName().str() : std::string();
          unsigned no = A ? A->getArgNo() : 0;
          return std::make_pair(std::move(n), no);
        };
        // The representative is the earlier name, so the class does not depend
        // on allocation order.
        auto unite = [&](const llvm::Argument *A, const llvm::Argument *B) {
          if (!A || !B)
            return;
          A = findA(A);
          B = findA(B);
          if (A == B)
            return;
          if (argRank(B) < argRank(A))
            std::swap(A, B);
          argParent[B] = A;
        };
        struct Id {
          const llvm::Argument *arg = nullptr;
          std::vector<uint64_t> idx;
          bool operator<(const Id &o) const {
            auto nm = [](const llvm::Argument *a) {
              const llvm::Function *f = a ? a->getParent() : nullptr;
              return f && f->hasName() ? f->getName().str() : std::string();
            };
            std::string an = nm(arg);
            std::string bn = nm(o.arg);
            if (an != bn)
              return an < bn;
            unsigned aa = arg ? arg->getArgNo() : 0;
            unsigned ba = o.arg ? o.arg->getArgNo() : 0;
            if (aa != ba)
              return aa < ba;
            if (arg != o.arg)
              return arg < o.arg;
            return idx < o.idx;
          }
        };
        auto localId = [&](const llvm::Value *V, const llvm::Function *Owner) -> std::optional<Id> {
          std::unordered_set<const llvm::Value *> seen;
          while (V && seen.insert(V).second) {
            V = V->stripPointerCasts();
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(V);
            if (!CB)
              break;
            const llvm::Value *only = nullptr;
            int np = 0;
            for (const llvm::Use &U : CB->args()) {
              if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                continue;
              if (only && only != U.get()) {
                np = 2;
                break;
              }
              only = U.get();
              np = 1;
            }
            if (np != 1)
              break;
            V = only;
          }
          if (!V)
            return std::nullopt;
          Id id;
          std::unordered_set<const llvm::Value *> seenC;
          while (V && seenC.insert(V).second) {
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
              if (llvm::isa<llvm::BitCastInst>(C) || llvm::isa<llvm::AddrSpaceCastInst>(C)) {
                V = C->getOperand(0);
                continue;
              }
            }
            if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
              bool all = true;
              std::vector<uint64_t> add;
              for (unsigned oi = 1; oi < G->getNumOperands(); ++oi) {
                const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(oi));
                if (!CI) {
                  all = false;
                  break;
                }
                add.push_back(CI->getZExtValue());
              }
              if (!all)
                return std::nullopt;
              id.idx.insert(id.idx.begin(), add.begin(), add.end());
              V = G->getPointerOperand();
              continue;
            }
            if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
              const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (AI) {
                const llvm::Value *st = spillValue(AI);
                if (!st)
                  break;
                V = st;
                continue;
              }
              V = L->getPointerOperand();
              continue;
            }
            break;
          }
          const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(V ? V->stripPointerCasts() : nullptr);
          if (!A || !Owner || A->getParent() != Owner)
            return std::nullopt;
          id.arg = A;
          return id;
        };
        auto targets = [&](const llvm::CallBase *C) -> std::vector<const llvm::Function *> {
          std::vector<const llvm::Function *> cs;
          auto rit = resolved.find(C);
          if (rit != resolved.end())
            return rit->second;
          if (const llvm::Function *D = C->getCalledFunction()) {
            cs.push_back(D);
            return cs;
          }
          return solve.callees(C, false);
        };
        for (const llvm::Function *Fp : spaceOrd) {
          if (!Fp || Fp->isDeclaration())
            continue;
          const llvm::Function &F = *Fp;
          std::map<Id, std::vector<const llvm::Argument *>> recv;
          for (const llvm::Instruction &I : llvm::instructions(F)) {
            const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!C || C->isInlineAsm())
              continue;
            for (const llvm::Function *D : targets(C)) {
              if (!D)
                continue;
              allSites[D].push_back(C);
              for (unsigned ai = 0; ai < C->arg_size() && ai < D->arg_size(); ++ai) {
                if (!C->getArgOperand(ai)->getType()->isPointerTy())
                  continue;
                if (D->isDeclaration())
                  continue;
                if (auto id = localId(C->getArgOperand(ai), &F))
                  recv[*id].push_back(D->getArg(ai));
                else if (const llvm::Argument *B = asArg(C->getArgOperand(ai)))
                  if (B->getParent() == &F)
                    unite(D->getArg(ai), B);
              }
            }
          }
          for (const auto &kv : recv) {
            const std::vector<const llvm::Argument *> &fs = kv.second;
            for (size_t i = 1; i < fs.size(); ++i)
              unite(fs[0], fs[i]);
          }
        }
        // A field passed out of one method is the same field of the argument
        // that method was given. The argument identity above is already united,
        // so the field is one object across those methods.
        {
          std::map<Id, std::vector<const llvm::Argument *>> recv;
          for (const llvm::Function *Fp : spaceOrd) {
            if (!Fp || Fp->isDeclaration())
              continue;
            const llvm::Function &F = *Fp;
            for (const llvm::Instruction &I : llvm::instructions(F)) {
              const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!C || C->isInlineAsm())
                continue;
              for (const llvm::Function *D : targets(C)) {
                if (!D || D->isDeclaration())
                  continue;
                for (unsigned ai = 0; ai < C->arg_size() && ai < D->arg_size(); ++ai) {
                  if (!C->getArgOperand(ai)->getType()->isPointerTy())
                    continue;
                  auto id = localId(C->getArgOperand(ai), &F);
                  if (!id || id->idx.empty())
                    continue;
                  id->arg = findA(id->arg);
                  recv[*id].push_back(D->getArg(ai));
                }
              }
            }
          }
          for (const auto &kv : recv) {
            const std::vector<const llvm::Argument *> &fs = kv.second;
            for (size_t i = 1; i < fs.size(); ++i)
              unite(fs[0], fs[i]);
          }
        }
        // 1: the value is derived from a pointer. 0: it is an integer address
        // with no pointer operand. A cycle is treated as a pointer.
        std::unordered_map<const llvm::Value *, int> provMemo;
        std::function<int(const llvm::Value *, int)> prov;
        prov = [&](const llvm::Value *V, int d) -> int {
          if (!V)
            return 1;
          auto it = provMemo.find(V);
          if (it != provMemo.end())
            return it->second;
          provMemo[V] = 1;
          int r = 1;
          if (llvm::isa<llvm::Argument>(V) || llvm::isa<llvm::AllocaInst>(V))
            r = V->getType()->isPointerTy() ? 1 : 0;
          else if (llvm::isa<llvm::GlobalVariable>(V) || llvm::isa<llvm::CallBase>(V))
            r = 1;
          else if (llvm::isa<llvm::ConstantInt>(V) || llvm::isa<llvm::ConstantPointerNull>(V) ||
                   llvm::isa<llvm::Function>(V) || llvm::isa<llvm::UndefValue>(V))
            r = 0;
          else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
            unsigned op = CE->getOpcode();
            if (op == llvm::Instruction::IntToPtr || op == llvm::Instruction::BitCast ||
                op == llvm::Instruction::GetElementPtr || op == llvm::Instruction::AddrSpaceCast ||
                op == llvm::Instruction::PtrToInt)
              r = prov(CE->getOperand(0), d + 1);
            else
              r = 0;
          }           else if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
            // A loaded pointer is a pointer. A loaded integer has the
            // provenance of the value stored into that alloca, not of the
            // address. An integer load from any other memory is unknown.
            if (LI->getType()->isPointerTy())
              r = 1;
            else {
              const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(LI->getPointerOperand()->stripPointerCasts());
              if (!AI)
                r = 2;
              else {
                r = 0;
                for (const llvm::User *U : AI->users()) {
                  const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
                  if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
                    continue;
                  int p = prov(SI->getValueOperand(), d + 1);
                  if (p > r)
                    r = p;
                }
              }
            }
          } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
            if (I->getOpcode() == llvm::Instruction::IntToPtr || I->getOpcode() == llvm::Instruction::PtrToInt ||
                I->getOpcode() == llvm::Instruction::BitCast || I->getOpcode() == llvm::Instruction::AddrSpaceCast ||
                I->getOpcode() == llvm::Instruction::GetElementPtr || I->getOpcode() == llvm::Instruction::Freeze)
              r = prov(I->getOperand(0), d + 1);
            else if (I->getNumOperands() == 0)
              r = I->getType()->isPointerTy() ? 1 : 0;
            else if (!I->getType()->isPointerTy()) {
              r = 0;
              for (const llvm::Use &U : I->operands()) {
                int p = prov(U.get(), d + 1);
                if (p > r)
                  r = p;
              }
            }
          }
          provMemo[V] = r;
          return r;
        };
        for (const llvm::Function *Fp : spaceOrd) {
          if (!Fp || Fp->isDeclaration())
            continue;
          const llvm::Function &F = *Fp;
          for (const llvm::Instruction &I : llvm::instructions(F)) {
            const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!C || C->isInlineAsm())
              continue;
            std::vector<const llvm::Function *> cs = targets(C);
            bool decl = false;
            for (const llvm::Function *D : cs)
              if (D && D->isDeclaration())
                decl = true;
            if (!decl)
              continue;
            std::vector<std::optional<FKey>> keys(C->arg_size());
            for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
              if (!C->getArgOperand(ai)->getType()->isPointerTy())
                continue;
              keys[ai] = keyOf(C->getArgOperand(ai));
            }
            for (unsigned ai = 0; ai < C->arg_size(); ++ai) {
              if (!keys[ai])
                continue;
              const FKey &k = *keys[ai];
              if (fieldBad.count(k))
                continue;
              auto &slot = fieldComp[k];
              for (unsigned bi = 0; bi < C->arg_size(); ++bi) {
                if (bi == ai)
                  continue;
                const llvm::Value *S = C->getArgOperand(bi);
                if (!S->getType()->isPointerTy() || llvm::isa<llvm::Constant>(S))
                  continue;
                if (llvm::isa<llvm::Function>(S->stripPointerCasts()))
                  continue;
                if (keys[bi] && keys[bi]->root == k.root && keys[bi]->idx == k.idx)
                  continue;
                bool have = false;
                for (const llvm::Value *E : slot)
                  if (E == S)
                    have = true;
                if (have)
                  continue;
                // An assignment copies one object representation into the
                // other. A pointer with no object size is a byte sequence.
                // A pointer with a different object size is a different object.
                bool da = C->paramHasAttr(ai, llvm::Attribute::Dereferenceable);
                bool db = C->paramHasAttr(bi, llvm::Attribute::Dereferenceable);
                uint64_t sa = da ? C->getParamDereferenceableBytes(ai) : 0;
                uint64_t sb = db ? C->getParamDereferenceableBytes(bi) : 0;
                bool assign = C->getType()->isPointerTy() && da && db && sa > 0 && sa == sb;
                if (!assign && db)
                  continue;
                // 0: this integer was never a pointer. 2: unknown, so it stays
                // and an unresolved walk poisons the meet.
                if (!assign && prov(S, 0) == 0)
                  continue;
                slot.push_back(S);
              }
            }
          }
        }
      }
      // The actual at one callsite, as a field of the caller's argument.
      // Empty idx means the actual is that argument.
      auto passed = [&](const llvm::Value *V, const llvm::Function *Owner) -> std::optional<FKey> {
        std::unordered_set<const llvm::Value *> seen;
        while (V && seen.insert(V).second) {
          V = V->stripPointerCasts();
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(V);
          if (!CB)
            break;
          const llvm::Value *only = nullptr;
          int np = 0;
          for (const llvm::Use &U : CB->args()) {
            if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
              continue;
            if (only && only != U.get()) {
              np = 2;
              break;
            }
            only = U.get();
            np = 1;
          }
          if (np != 1)
            break;
          V = only;
        }
        if (!V)
          return std::nullopt;
        FKey id;
        std::unordered_set<const llvm::Value *> seenC;
        while (V && seenC.insert(V).second) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
            if (llvm::isa<llvm::BitCastInst>(C) || llvm::isa<llvm::AddrSpaceCastInst>(C)) {
              V = C->getOperand(0);
              continue;
            }
          }
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            bool all = true;
            std::vector<uint64_t> add;
            for (unsigned oi = 1; oi < G->getNumOperands(); ++oi) {
              const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(oi));
              if (!CI) {
                all = false;
                break;
              }
              add.push_back(CI->getZExtValue());
            }
            if (!all)
              return std::nullopt;
            id.ty = G->getSourceElementType();
            id.idx.insert(id.idx.begin(), add.begin(), add.end());
            V = G->getPointerOperand();
            continue;
          }
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (AI) {
              const llvm::Value *st = spillValue(AI);
              if (!st)
                break;
              V = st;
              continue;
            }
            V = L->getPointerOperand();
            continue;
          }
          break;
        }
        const auto *A = llvm::dyn_cast_or_null<llvm::Argument>(V ? V->stripPointerCasts() : nullptr);
        if (!A || !Owner || A->getParent() != Owner)
          return std::nullopt;
        id.root = A;
        return id;
      };
      // This invocation's copy of the field. A callsite in the cone that passes
      // its own argument carries the same field onto that argument. Callers
      // outside the cone pass a different object.
      std::unordered_set<const llvm::Argument *> widenStack;
      std::function<void(FKey, std::set<FKey> &, int)> widen;
      widen = [&](FKey k, std::set<FKey> &out, int depth) {
        if (!k.root || !out.insert(k).second)
          return;
        if (!widenStack.insert(k.root).second) {
          fieldBad.insert(k);
          out.erase(k);
          return;
        }
        struct WidenPop {
          std::unordered_set<const llvm::Argument *> &s;
          const llvm::Argument *v;
          ~WidenPop() { s.erase(v); }
        } widenPop{widenStack, k.root};
        auto sit = allSites.find(k.root->getParent());
        if (sit == allSites.end())
          return;
        for (const llvm::CallBase *Call : sit->second) {
          if (!Call || k.root->getArgNo() >= Call->arg_size())
            continue;
          if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), k.root->getParent()))
            continue;
          // The argument is this object only when the callsite calls this
          // function. A call that may reach several functions does not.
          const llvm::Function *Owner = k.root->getParent();
          bool proves = Call->getCalledFunction() == Owner;
          if (!proves) {
            auto rit = resolved.find(Call);
            proves = rit != resolved.end() && rit->second.size() == 1 && rit->second[0] == Owner;
          }
          if (!proves)
            continue;
          auto id = passed(Call->getArgOperand(k.root->getArgNo()), Call->getFunction());
          if (!id)
            continue;
          FKey n;
          n.root = findA(id->root);
          // The caller's gep names the object. A whole-object actual keeps
          // the callee's struct, which is that object.
          n.ty = id->ty ? id->ty : k.ty;
          n.idx = id->idx;
          n.idx.insert(n.idx.end(), k.idx.begin(), k.idx.end());
          if (n.idx.empty() || fieldBad.count(n))
            continue;
          widen(n, out, depth + 1);
        }
      };
      auto got = keyOf(actual);
      if (!got || fieldBad.count(*got))
        return bare();
      std::set<FKey> cells;
      widen(*got, cells, 0);
      std::unordered_map<const llvm::Value *, Status> apiMemo;
      std::unordered_set<const llvm::Value *> apiActive;
      std::function<Status(const llvm::Value *, int)> apiBytes;
      apiBytes = [&](const llvm::Value *V, int d) -> Status {
        if (!V)
          return opened();
        V = V->stripPointerCasts();
        if (auto itM = apiMemo.find(V); itM != apiMemo.end())
          return itM->second;
        if (!apiActive.insert(V).second)
          return bare();
        Status out = opened();
        auto finish = [&](Status s) {
          apiActive.erase(V);
          if (s.any)
            apiMemo[V] = s;
          return s;
        };
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
          bool all = true;
          for (unsigned oi = 1; oi < G->getNumOperands(); ++oi)
            if (!llvm::isa<llvm::ConstantInt>(G->getOperand(oi)))
              all = false;
          // A variable index addresses bytes inside a buffer. A constant
          // index is a field. The bytes of that field are the values passed
          // with it, not the whole object.
          if (all)
            if (auto fk = keyOf(V)) {
              std::set<FKey> cells;
              widen(*fk, cells, 0);
              Status accF;
              bool sawF = false;
              bool badF = false;
              auto takeF = [&](const llvm::Value *S) {
                Status one = apiBytes(S, d + 1);
                if (!one.any)
                  return;
                if (!(pureEntry(one) || pureGlobal(one))) {
                  if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
                    return;
                  badF = true;
                  return;
                }
                if (sawF && accF.args != one.args)
                  badF = true;
                if (!sawF)
                  accF = one;
                sawF = true;
              };
              for (const FKey &ck : cells) {
                auto itF = fieldComp.find(ck);
                if (itF == fieldComp.end())
                  continue;
                for (const llvm::Value *S : itF->second) {
                  bool in = true;
                  if (const auto *SI = llvm::dyn_cast<llvm::Instruction>(S))
                    in = cone(SI->getFunction());
                  if (in)
                    takeF(S);
                }
              }
              // This entry does not call the function that stored the field.
              // The store still defines the cell. Its source is an entry
              // argument when every such store names the same one.
              if (!sawF && !badF) {
                for (const FKey &ck : cells) {
                  auto itF = fieldComp.find(ck);
                  if (itF == fieldComp.end())
                    continue;
                  for (const llvm::Value *S : itF->second) {
                    bool in = true;
                    if (const auto *SI = llvm::dyn_cast<llvm::Instruction>(S))
                      in = cone(SI->getFunction());
                    if (!in)
                      takeF(S);
                  }
                }
              }
              if (sawF && !badF)
                return finish(accF);
              if (badF)
                return finish(opened());
              // A field that has companions is not the whole object. Walking
              // the base would name a different cell.
              bool anyComp = false;
              for (const FKey &ck : cells) {
                auto itC = fieldComp.find(ck);
                if (itC != fieldComp.end() && !itC->second.empty())
                  anyComp = true;
              }
              if (anyComp)
                return finish(opened());
            }
          return finish(apiBytes(G->getPointerOperand(), d + 1));
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (AI)
            if (const llvm::Value *st = spillValue(AI))
              return finish(apiBytes(st, d + 1));
        }
        if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
          const llvm::Value *only = nullptr;
          int np = 0;
          for (const llvm::Use &U : CB->args()) {
            if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
              continue;
            if (only && only != U.get()) {
              np = 2;
              break;
            }
            only = U.get();
            np = 1;
          }
          if (np == 1)
            return finish(apiBytes(only, d + 1));
        }
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
          const llvm::Function *P = A->getParent();
          auto ent = entriesOf.find(chop);
          if (P && strongExport(P) && ent != entriesOf.end() && ent->second.count(show(P))) {
            Status s;
            s.any = true;
            s.args.insert({show(P), static_cast<int>(A->getArgNo())});
            return finish(s);
          }
          Status acc;
          bool saw = false;
          bool bad = false;
          auto sit = allSites.find(P);
          auto takeCall = [&](const llvm::CallBase *Call) {
            if (!Call || A->getArgNo() >= Call->arg_size())
              return;
            if (!solve.proves(Call, P))
              return;
            Status one = apiBytes(Call->getArgOperand(A->getArgNo()), d + 1);
            if (!one.any)
              return;
            if (!(pureEntry(one) || pureGlobal(one))) {
              if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
                return;
              bad = true;
              return;
            }
            // Each proved caller supplies the bytes of this parameter.
            if (!saw)
              acc = one;
            else
              for (const auto &a : one.args)
                acc.args.insert(a);
            saw = true;
          };
          if (sit != allSites.end()) {
            for (const llvm::CallBase *Call : sit->second) {
              if (!Call || A->getArgNo() >= Call->arg_size())
                continue;
              if (!cone(Call->getFunction()) || !entryCall(Call->getFunction(), P))
                continue;
              takeCall(Call);
            }
            // No call inside this entry supplies the parameter. A call
            // outside it still stored the value that this object carries.
            if (!saw && !bad) {
              for (const llvm::CallBase *Call : sit->second)
                if (Call && !(cone(Call->getFunction()) && entryCall(Call->getFunction(), P)))
                  takeCall(Call);
            }
          }
          if (saw && !bad)
            return finish(acc);
          return finish(opened());
        }
        // A local has no entry bytes until this function stores some into it.
        // An sret written from one pointer is that pointer. Constant stores
        // are not entry bytes. A declaration that merely receives the address
        // does not put entry bytes into the local.
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
          const llvm::CallBase *sretCall = nullptr;
          int nsret = 0;
          std::vector<const llvm::Value *> srcs;
          for (const llvm::User *U : AI->users()) {
            if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
              if (SI->getPointerOperand()->stripPointerCasts() != AI)
                continue;
              if (!llvm::isa<llvm::Constant>(SI->getValueOperand()))
                srcs.push_back(SI->getValueOperand());
              continue;
            }
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
            if (!CB)
              continue;
            for (unsigned i = 0; i < CB->arg_size(); ++i) {
              if (CB->getArgOperand(i)->stripPointerCasts() != AI)
                continue;
              if (CB->paramHasAttr(i, llvm::Attribute::StructRet)) {
                sretCall = CB;
                ++nsret;
              }
            }
            if (const llvm::Function *CF = CB->getCalledFunction()) {
              llvm::StringRef nm = CF->getName();
              if ((nm.starts_with("llvm.memcpy") || nm.starts_with("llvm.memmove")) && CB->arg_size() >= 2 &&
                  CB->getArgOperand(0)->stripPointerCasts() == AI &&
                  !llvm::isa<llvm::Constant>(CB->getArgOperand(1)))
                srcs.push_back(CB->getArgOperand(1));
            }
          }
          if (nsret == 1 && sretCall) {
            const llvm::Value *src = nullptr;
            int ns = 0;
            for (const llvm::Use &U : sretCall->args()) {
              if (U.get()->stripPointerCasts() == AI)
                continue;
              if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                continue;
              if (src && src != U.get()) {
                ns = 2;
                break;
              }
              src = U.get();
              ns = 1;
            }
            if (ns == 1)
              return finish(apiBytes(src, d + 1));
          }
          if (nsret == 0) {
            if (srcs.empty())
              return finish(nothing());
            Status accA;
            bool sawA = false;
            bool badA = false;
            for (const llvm::Value *S : srcs) {
              Status one = apiBytes(S, d + 1);
              if (!one.any)
                continue;
              if (!(pureEntry(one) || pureGlobal(one))) {
                if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
                  continue;
                badA = true;
                continue;
              }
              if (!sawA)
                accA = one;
              else
                for (const auto &a : one.args)
                  accA.args.insert(a);
              sawA = true;
            }
            if (sawA && !badA)
              return finish(accA);
            if (!sawA && !badA)
              return finish(nothing());
            return finish(opened());
          }
        }
        return finish(out);
      };
      Status acc;
      bool saw = false;
      bool bad = false;
      std::vector<const llvm::Value *> comps;
      for (const FKey &ck : cells) {
        auto it = fieldComp.find(ck);
        if (it == fieldComp.end())
          continue;
        for (const llvm::Value *S : it->second) {
          bool have = false;
          for (const llvm::Value *E : comps)
            if (E == S)
              have = true;
          if (!have)
            comps.push_back(S);
        }
      }
      for (const llvm::Value *S : comps) {
        if (const auto *SI = llvm::dyn_cast<llvm::Instruction>(S))
          if (!cone(SI->getFunction()))
            continue;
        Status one = apiBytes(S, 0);
        if (!(pureEntry(one) || pureGlobal(one))) {
          // A variable index is an address inside a buffer. Its copy origin is
          // the bytes. A constant field index is the object, already matched.
          const auto *SG = llvm::dyn_cast<llvm::GEPOperator>(S->stripPointerCasts());
          bool varIdx = false;
          if (SG)
            for (unsigned oi = 1; oi < SG->getNumOperands(); ++oi)
              if (!llvm::isa<llvm::ConstantInt>(SG->getOperand(oi)))
                varIdx = true;
          if (varIdx) {
            Status b = originBytes(S, 0, true);
            if (b.any)
              one = b;
          }
        }
        if (!one.any)
          continue;
        if (!(pureEntry(one) || pureGlobal(one))) {
          if (one.none && !one.open && !one.local && !one.hasConst && one.args.empty())
            continue;
          bad = true;
          continue;
        }
        if (saw && acc.args != one.args)
          bad = true;
        if (!saw)
          acc = one;
        saw = true;
      }
      if (saw && !bad)
        return acc;
      return bare();
    };
    // Each callsite is its own actual. One callsite's roots do not erase
    // another's: a callsite that reduces contributes its parameters, and a
    // callsite that does not reduce stays open.
    for (const llvm::Function *F : spaceOrd) {
      if (!cone(F))
        continue;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        auto it = resolved.find(C);
        if (it == resolved.end())
          continue;
        for (const llvm::Function *D : it->second) {
          if (!D)
            continue;
          std::string chop = show(D);
          auto init = initialOf.find(chop);
          if (init == initialOf.end() || !init->second.count(entryName))
            continue;
          auto ent = entriesOf.find(chop);
          if (ent == entriesOf.end() || !ent->second.count(entryName))
            continue;
          for (unsigned i = 0; i < C->arg_size(); ++i) {
            int chopArg = static_cast<int>(i);
            const llvm::Value *actual = C->getArgOperand(i);
            Status s = ground(walk(actual), C, actual);
            // The pointer itself is not an entry parameter. Calls that were
            // handed this same object wrote it, and their other arguments
            // are the bytes.
            if (actual->getType()->isPointerTy()) {
              bool ent = false;
              for (const auto &a : s.args)
                if (a.second >= 0)
                  ent = true;
              if (!ent)
                if (auto key = origin(actual)) {
                  Status got = handedBytes(*key);
                  if (got.any) {
                    s = got;
                    for (const auto &a : s.args)
                      if (a.second >= 0)
                        ent = true;
                  }
                }
              if (!ent) {
                Status got = copied(actual);
                if (got.any)
                  s = got;
              }
            }
            // The merged formal is open because another entry activation
            // passes a different object. This activation's actual is the
            // object that reaches the chop from this entry. A different
            // activation does not open it.
            bool entNow = false;
            for (const auto &a : s.args)
              if (a.second >= 0)
                entNow = true;
            if (s.open && entNow && !s.local && !s.hasConst && !s.none && C->getFunction() &&
                C->getFunction() != entryFn) {
              std::vector<const llvm::CallBase *> acts;
              auto sitA = sites.find(C->getFunction());
              if (sitA != sites.end()) {
                for (const llvm::CallBase *Call : sitA->second) {
                  if (!Call || !cone(Call->getFunction()))
                    continue;
                  if (!entryCall(Call->getFunction(), C->getFunction()))
                    continue;
                  acts.push_back(Call);
                }
              }
              if (!acts.empty()) {
                Status keep;
                bool anyPure = false;
                bool disagree = false;
                auto refine = [&](Status t) {
                  if (!actual->getType()->isPointerTy())
                    return t;
                  bool ent = false;
                  for (const auto &a : t.args)
                    if (a.second >= 0)
                      ent = true;
                  if (!ent)
                    if (auto key = origin(actual)) {
                      Status got = handedBytes(*key);
                      if (got.any) {
                        t = got;
                        for (const auto &a : t.args)
                          if (a.second >= 0)
                            ent = true;
                      }
                    }
                  if (!ent) {
                    Status got = copied(actual);
                    if (got.any)
                      t = got;
                  }
                  return t;
                };
                for (const llvm::CallBase *Act : acts) {
                  activation = Act;
                  actMemo.clear();
                  actRf.clear();
                  Status t = refine(ground(walk(actual), C, actual));
                  activation = nullptr;
                  if (!(pureEntry(t) || pureGlobal(t)))
                    continue;
                  if (anyPure && keep.args != t.args)
                    disagree = true;
                  if (!anyPure)
                    keep = t;
                  anyPure = true;
                }
                activation = nullptr;
                actMemo.clear();
                actRf.clear();
                if (anyPure && !disagree)
                  s = keep;
              }
            }
            if (pureNone(s)) {
              if (const llvm::Value *p = planted(actual)) {
                const llvm::Value *data = p;
                if (const auto *B = llvm::dyn_cast<llvm::CallBase>(p->stripPointerCasts())) {
                  const llvm::Value *src = nullptr;
                  int nsrc = 0;
                  for (const llvm::Use &U : B->args()) {
                    if (!U.get()->getType()->isPointerTy() || llvm::isa<llvm::Constant>(U.get()))
                      continue;
                    if (src && src != U.get()) {
                      nsrc = 2;
                      break;
                    }
                    src = U.get();
                    nsrc = 1;
                  }
                  if (nsrc == 1)
                    data = src;
                }
                Status w = bytesOf(data, 0);
                if (!(pureEntry(w) || pureGlobal(w)))
                  w = ground(walk(data), C, data);
                bool ent = false;
                for (const auto &a : w.args)
                  if (a.second >= 0)
                    ent = true;
                if (ent && !w.open && !w.local && !w.hasConst && !w.none)
                  s = w;
                else
                  s = opened();
              }
            }
            // The pointer is a fresh object. It denotes an entry parameter
            // only when a reader registered on it copies that parameter and
            // no other data pointer is registered with it.
            if (s.open && !s.local && !s.hasConst && !s.none &&
                actual->getType()->isPointerTy()) {
              bool hasEnt = false;
              for (const auto &a : s.args)
                if (a.second >= 0)
                  hasEnt = true;
              if (!hasEnt) {
                Status w = registered(actual, 0);
                if (pureEntry(w) || pureGlobal(w))
                  s = w;
                else if (D->isDeclaration()) {
                  Status c = fieldBytes(actual, chop);
                  if (pureEntry(c) || pureGlobal(c))
                    s = w = c;
                }
              }
            }
            if (!record)
              continue;
            // The value is determined by these entry arguments only when
            // every definition in this invocation reduces to them. An
            // unresolved definition in the same invocation is not that proof.
            Jdg j;
            j.C = C;
            j.chop = chop;
            j.chopArg = chopArg;
            j.s = s;
            if (pureEntry(s) || pureGlobal(s))
              j.kind = 1;
            else if (s.hasConst && !s.open && !s.local && !s.none && s.args.empty())
              j.kind = 0;
            else if (s.none && !s.open && !s.local && !s.hasConst && s.args.empty())
              j.kind = 0;
            else
              j.kind = 2;
            if (j.kind)
              jdgs.push_back(std::move(j));
          }
        }
      }
    }
    if (record) {
      auto addIn = [&](const std::string &chop, int chopArg, const std::string &func, int arg) {
        std::string k = std::to_string(chopArg) + " " + std::to_string(arg) + " " + func;
        if (!seenIn[chop].insert(k).second)
          return;
        Input in;
        in.func = func;
        in.arg = arg;
        in.chopArg = chopArg;
        inputs[chop].push_back(std::move(in));
      };
      auto addOpen = [&](const std::string &chop, int chopArg) {
        std::string k = std::to_string(chopArg) + " " + entryName;
        if (!seenOpen[chop].insert(k).second)
          return;
        Input in;
        in.func = entryName;
        in.arg = -1;
        in.chopArg = chopArg;
        unreduced[chop].push_back(std::move(in));
      };
      // s0 = <p, u>. A branch whose condition is a function of p selects one
      // arm for that p, for every u. A chop call that runs only on another
      // arm is a different p. It does not put u into the selected arm.
      auto reachesFn = [&](const llvm::CallBase *C, const llvm::Function *Target) {
        if (!C || !Target)
          return false;
        const llvm::Function *Want = definedBody(Target);
        if (!Want)
          Want = Target;
        std::unordered_set<const llvm::Function *> seenF;
        std::vector<const llvm::Function *> q;
        auto add = [&](const llvm::Function *F) {
          const llvm::Function *D = definedBody(F);
          if (!D)
            D = F;
          if (D && !D->isDeclaration() && seenF.insert(D).second)
            q.push_back(D);
        };
        if (const llvm::Function *D = C->getCalledFunction())
          add(D);
        else {
          auto it = resolved.find(C);
          if (it != resolved.end())
            for (const llvm::Function *D : it->second)
              add(D);
        }
        for (size_t i = 0; i < q.size(); ++i) {
          if (q[i] == Want)
            return true;
          auto sit = succs.find(q[i]);
          if (sit == succs.end())
            continue;
          for (const llvm::Function *D : sit->second)
            add(D);
        }
        return false;
      };
      std::map<std::pair<std::string, int>, std::vector<size_t>> groups;
      for (size_t i = 0; i < jdgs.size(); ++i)
        groups[{jdgs[i].chop, jdgs[i].chopArg}].push_back(i);
      std::unordered_set<size_t> suppress;
      for (const auto &gv : groups) {
        const std::vector<size_t> &ids = gv.second;
        bool anyP = false;
        bool anyO = false;
        for (size_t id : ids) {
          if (jdgs[id].kind == 1)
            anyP = true;
          if (jdgs[id].kind == 2)
            anyO = true;
        }
        if (!anyP || !anyO || !entryFn)
          continue;
        auto reachBlocks = [&](const llvm::BasicBlock *Start) {
          std::unordered_set<const llvm::BasicBlock *> s;
          if (!Start)
            return s;
          std::vector<const llvm::BasicBlock *> q{Start};
          s.insert(Start);
          for (size_t i = 0; i < q.size(); ++i) {
            const llvm::Instruction *T = q[i]->getTerminator();
            if (!T)
              continue;
            for (unsigned n = 0; n < T->getNumSuccessors(); ++n) {
              const llvm::BasicBlock *N = T->getSuccessor(n);
              if (N && s.insert(N).second)
                q.push_back(N);
            }
          }
          return s;
        };
        bool armed = false;
        std::unordered_set<size_t> proveIdx;
        for (const llvm::BasicBlock &BB : *entryFn) {
          const auto *Br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
          if (!Br || !Br->isConditional())
            continue;
          std::unordered_set<const llvm::Value *> seenP;
          PredEnv env;
          if (!pred(Br->getCondition(), env, 0, seenP))
            continue;
          auto ts = reachBlocks(Br->getSuccessor(0));
          auto fs = reachBlocks(Br->getSuccessor(1));
          auto sideOf = [&](const llvm::BasicBlock *B) {
            bool t = ts.count(B) != 0;
            bool f = fs.count(B) != 0;
            if (t && !f)
              return 1;
            if (f && !t)
              return -1;
            return 0;
          };
          auto feasible = [&](bool wantTrue, const llvm::CallBase *Site) {
            if (!Site)
              return true;
            int other = wantTrue ? -1 : 1;
            if (Site->getFunction() == entryFn)
              return sideOf(Site->getParent()) != other;
            bool saw = false;
            for (const llvm::Instruction &I : llvm::instructions(*entryFn)) {
              const auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!Call || Call->isInlineAsm())
                continue;
              if (!reachesFn(Call, Site->getFunction()))
                continue;
              saw = true;
              if (sideOf(Call->getParent()) == other)
                continue;
              return true;
            }
            return !saw;
          };
          for (bool wantTrue : {true, false}) {
            bool proved = false;
            bool blocked = false;
            for (size_t id : ids) {
              if (!feasible(wantTrue, jdgs[id].C))
                continue;
              if (jdgs[id].kind == 2)
                blocked = true;
              if (jdgs[id].kind == 1)
                proved = true;
            }
            if (!proved || blocked)
              continue;
            armed = true;
            for (size_t id : ids)
              if (jdgs[id].kind == 1 && feasible(wantTrue, jdgs[id].C))
                proveIdx.insert(id);
          }
        }
        if (!armed)
          continue;
        for (size_t id : ids) {
          if (jdgs[id].kind == 2)
            suppress.insert(id);
          else if (!proveIdx.count(id))
            suppress.insert(id);
        }
      }
      // Existential witness for an argument that did not reduce. This walk
      // follows the same reaching-definition edges as the analysis above:
      // peel, getelementptr to its object, a load to the stores of its cell,
      // a call result to the callee's returns under that call's context, a
      // formal to the actual of the context or to every caller, a buffer to
      // the stores, byte copies and resolved callees that write it. A buffer
      // is one object under every name the pointer takes: the pointer
      // fields loaded from it, the field it is stored into (read back by
      // every load of that field), the call results of a function that
      // returns it, and the address a callee returns behind a call result.
      // Writes through any of those names are writes into it. It
      // differs only in how alternatives combine. The determinacy above keeps
      // a value only when every definition agrees; this keeps the union, so
      // one definition that reaches an export's argument is reported even
      // when another definition does not. A frontier cell is a field read on
      // an object the harness supplies. Its definitions are every store into
      // that field of that struct type in the module: the harness passes one
      // object to both exports, which is what makes that store this read.
      // Each line is one path. The `open` line already states that other
      // definitions exist; a witness does not retract it.
      // Label -> the fewest identity-losing steps on any path to it.
      using Lab = std::map<std::pair<std::string, int>, int>;
      auto addWit = [&](const std::string &chop, int chopArg, const std::string &func, int arg, int cost) {
        std::string k = std::to_string(chopArg) + " " + entryName + " " + std::to_string(arg) + " " + func;
        if (!seenWit[chop].insert(k).second)
          return;
        Witness w;
        w.entry = entryName;
        w.func = func;
        w.arg = arg;
        w.chopArg = chopArg;
        w.cost = cost;
        witnesses[chop].push_back(std::move(w));
      };
      auto alphabet = [&](const llvm::Function *F) { return F && F->getParent() == &M && strongExport(F); };
      // The bits a choice among n alternatives gives up, in hundredths.
      auto bits = [](size_t n) -> int {
        if (n <= 1)
          return 0;
        return static_cast<int>(std::lround(std::log2(static_cast<double>(n)) * 100.0));
      };
      // One state of the walk. kind 0 is the bytes a value denotes, in the
      // context of the call through which the walk entered its function (a
      // formal of that callee is the actual of ctx; a formal reached any
      // other way is the actual of every caller). The other kinds are
      // cells of objects, described where they are expanded. States are
      // finite -- values, calls, objects and segment tree nodes -- so the
      // walk terminates.
      struct WState {
        int kind = 0;
        const llvm::Value *v = nullptr;
        const llvm::CallBase *ctx = nullptr;
        unsigned obj = 0;
        int64_t off = 0;
        bool operator<(const WState &o) const {
          if (kind != o.kind)
            return kind < o.kind;
          if (v != o.v)
            return v < o.v;
          if (ctx != o.ctx)
            return ctx < o.ctx;
          if (obj != o.obj)
            return obj < o.obj;
          return off < o.off;
        }
        bool operator==(const WState &o) const {
          return kind == o.kind && v == o.v && ctx == o.ctx && obj == o.obj && off == o.off;
        }
      };
      struct WHash {
        size_t operator()(const WState &s) const {
          size_t h = static_cast<size_t>(s.kind);
          auto mix = [&](size_t x) { h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); };
          mix(std::hash<const void *>{}(s.v));
          mix(std::hash<const void *>{}(s.ctx));
          mix(std::hash<unsigned>{}(s.obj));
          mix(std::hash<int64_t>{}(s.off));
          return h;
        }
      };
      // Each state carries the cost of the cheapest path to it: the bits
      // of identity the path gives up. A step that keeps one object or one
      // value -- an alias of one pointer, a value's own definitions, the
      // stores into one object -- costs nothing. A step that stands for N
      // alternatives at once -- a formal continued into N callers, a
      // pointer dereferenced to the N objects it may point at -- costs
      // log2 N bits, the information needed to pick the one alternative
      // the concrete path took. Costs are kept in hundredths of a bit;
      // states are processed in cost order, so a state is processed first
      // at its least cost and a label records the least cost of any path
      // to it.
      struct CellRec {
        int64_t off = 0;
        int64_t len = -1;
        std::string func;
        std::string fn;
      };
      std::vector<CellRec> keptCells;
      std::unordered_map<const llvm::Value *, std::vector<CellRec>> cellMemo;
      auto witnessOf = [&](const llvm::Value *P0) -> std::optional<Lab> {
        Points &P = pointsOf();
        Lab out;
        std::unordered_map<WState, int, WHash> best;
        std::map<int, std::vector<WState>> work;
        int curCost = 0;
        auto pushAt = [&](WState s, int extra) {
          if (s.kind == 0) {
            s.v = peel(s.v);
            if (!s.v || llvm::isa<llvm::ConstantData>(s.v))
              return;
            const llvm::Function *SF = nullptr;
            if (const auto *I = llvm::dyn_cast<llvm::Instruction>(s.v))
              SF = I->getFunction();
            else if (const auto *A = llvm::dyn_cast<llvm::Argument>(s.v))
              SF = A->getParent();
            // A call context distinguishes bytes only inside a function
            // analysed per call. Elsewhere this value is one state, and a
            // formal stands for the actual of every caller, so a context
            // carried in from a callee must not hide the other callers.
            if (!SF || !P.perCall(SF))
              s.ctx = nullptr;
          }
          int c = curCost + extra;
          auto it = best.find(s);
          if (it != best.end() && it->second <= c)
            return;
          best[s] = c;
          work[c].push_back(std::move(s));
        };
        auto val = [&](const llvm::Value *v, const llvm::CallBase *ctx, int extra) {
          WState s;
          s.kind = 0;
          s.v = v;
          s.ctx = ctx;
          pushAt(std::move(s), extra);
        };
        auto note = [&](const std::string &name, int arg) {
          auto it = out.find({name, arg});
          if (it == out.end())
            out.emplace(std::make_pair(name, arg), curCost);
          else if (curCost < it->second)
            it->second = curCost;
        };
        auto fnOf = [&](const llvm::Value *V) -> const llvm::Function * {
          if (!V)
            return nullptr;
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V))
            return I->getFunction();
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(V))
            return A->getParent();
          return nullptr;
        };
        // Bytes defined by code outside both modules: a callee with no
        // body, or a call no function reaches. Reported under the function
        // that was called, or that holds the call, with -1 for the
        // argument.
        auto external = [&](const llvm::Function *F) {
          if (F && F->hasName())
            note(F->getName().str(), -1);
        };
        auto externalCall = [&](const llvm::CallBase *C) {
          if (const llvm::Function *D = C->getCalledFunction())
            external(D);
          else
            external(C->getFunction());
        };
        // The objects a pointer may point at, each at the cost of picking
        // it among them. The same pointer is read from many states; the
        // objects and cells it names do not depend on the path, so they
        // are recorded once.
        // When the pointer may point outside both modules, the bytes there
        // are the harness's or foreign code's: which, is told by where the
        // pointer itself came from -- the export formal, the call with no
        // body -- so the pointer's own provenance is followed too.
        // The locations a pointer names, recorded once per pointer and
        // context; the walk reads the same pointer from many values.
        struct DKey {
          const llvm::Value *p;
          const llvm::CallBase *ctx;
          bool operator==(const DKey &o) const { return p == o.p && ctx == o.ctx; }
        };
        struct DHash {
          size_t operator()(const DKey &k) const {
            return std::hash<const void *>{}(k.p) ^ (std::hash<const void *>{}(k.ctx) * 0x9e3779b97f4a7c15ULL);
          }
        };
        // Many pointers name the same set of locations; the set is kept
        // once and a pointer refers to it, so that reading the same bytes
        // behind two such pointers is one read.
        struct PSet {
          std::vector<unsigned> ids;         // locations, ascending
          std::vector<unsigned> objs;        // distinct objects
          bool outside = false;
          bool objsPushed = false;           // kExt/kAny of every object taken
        };
        std::vector<PSet> sets;
        std::unordered_map<uint64_t, std::vector<unsigned>> setsByHash;
        std::unordered_map<DKey, unsigned, DHash> dcache;
        auto pointees = [&](const llvm::Value *p, const llvm::CallBase *ctx) -> unsigned {
          DKey key{p, ctx};
          auto it = dcache.find(key);
          if (it != dcache.end())
            return it->second;
          std::vector<unsigned> ids;
          uint64_t h = 1469598103934665603ULL;
          for (unsigned id : P.of(p, ctx)) {
            ids.push_back(id);
            h = (h ^ id) * 1099511628211ULL;
          }
          std::vector<unsigned> &bucket = setsByHash[h];
          for (unsigned sid : bucket)
            if (sets[sid].ids == ids) {
              dcache.emplace(key, sid);
              return sid;
            }
          PSet ps;
          std::unordered_set<unsigned> seenObj;
          for (unsigned id : ids) {
            const Points::Loc l = P.loc(id);
            if (P.obj(l.obj).kind == Points::Kind::Outside)
              ps.outside = true;
            if (seenObj.insert(l.obj).second)
              ps.objs.push_back(l.obj);
          }
          ps.ids = std::move(ids);
          const unsigned sid = static_cast<unsigned>(sets.size());
          sets.push_back(std::move(ps));
          bucket.push_back(sid);
          dcache.emplace(key, sid);
          return sid;
        };
        // Cell states. The cells of an object are its regions, the leaves
        // of the object's segment tree; a byte range of an object is the
        // nodes tiling it, and the writes covering the range are the
        // lists at those nodes and at their ancestors. A read of a byte
        // range therefore pushes O(log n) states, each expanded once at
        // its least cost like any other state. Expanding on arrival would
        // walk the object graph depth first and redo every subtree a
        // cheaper path later reaches.
        //   kDown  (obj, node): the writes at the node and below it
        //   kUp    (obj, node): the writes at its ancestors, restricted
        //                       to the node's bytes
        //   kExt   (obj):       calls with no body here given a pointer
        //                       into the object: bytes from outside
        //   kWhole (obj):       the sink's whole buffer: every cell and
        //                       the pointer fields the sink's library
        //                       loads from it
        //   kLoad  (v):         such a pointer load: the whole of every
        //                       object it may name, taken once at the
        //                       least cost of any object it is reached
        //                       from
        //   kAny   (obj):       the writes at offset Any: every byte
        enum { kDown = 1, kUp = 2, kExt = 3, kWhole = 4, kLoad = 5, kAny = 6 };
        auto cell = [&](int kind, unsigned o, size_t node, int extra) {
          WState s;
          s.kind = kind;
          s.obj = o;
          s.off = static_cast<int64_t>(node);
          pushAt(std::move(s), extra);
        };
        // Reads already taken. States are expanded in cost order, so the
        // first time a read is taken is at the least cost of any state
        // taking it; taking it again later pushes nothing new.
        struct RKey {
          unsigned set;
          int kind;
          int64_t lo, hi;
          bool hiInf;
          bool operator==(const RKey &o) const {
            return set == o.set && kind == o.kind && lo == o.lo && hi == o.hi && hiInf == o.hiInf;
          }
        };
        struct RHash {
          size_t operator()(const RKey &k) const {
            size_t h = k.set;
            auto mix = [&](size_t x) { h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); };
            mix(static_cast<size_t>(k.kind));
            mix(std::hash<int64_t>{}(k.lo));
            mix(std::hash<int64_t>{}(k.hi));
            mix(static_cast<size_t>(k.hiInf));
            return h;
          }
        };
        std::unordered_set<RKey, RHash> readsTaken;
        // The bytes [lo, hi) behind pointer p (hi unbounded when hiInf;
        // every byte when lo is Any), at the cost of picking one of the
        // locations p names. kind 2 is the sink's buffer.
        auto deref = [&](const llvm::Value *p, int kind, int64_t lo, int64_t hi, bool hiInf,
                         const llvm::CallBase *ctx) {
          // A context distinguishes pointers only in a function analysed
          // per call.
          const llvm::Function *PF = nullptr;
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(p))
            PF = I->getFunction();
          else if (const auto *A = llvm::dyn_cast<llvm::Argument>(p))
            PF = A->getParent();
          if (!P.perCall(PF))
            ctx = nullptr;
          if (lo == Points::Any) {
            hi = 0;
            hiInf = true;
          }
          const unsigned sid = pointees(p, ctx);
          // Bytes behind a pointer into memory from outside both modules
          // are supplied by whoever made the pointer.
          if (sets[sid].outside)
            val(p, ctx, 0);
          if (!readsTaken.insert(RKey{sid, kind, lo, hi, hiInf}).second)
            return;
          if (kind == 2) {
            const std::vector<unsigned> &objs = sets[sid].objs;
            const int extra = bits(objs.size());
            // The harness object is the context the exports share. Its
            // constant-offset cells are read by the loads on this path.
            // Reading every byte of it would name every export that stores
            // at any offset.
            for (unsigned o : objs)
              if (P.obj(o).kind != Points::Kind::Harness)
                cell(kWhole, o, 0, extra);
            return;
          }
          // Expanding a cell can add sets; the set is read through its
          // index below.
          const int extra = bits(sets[sid].ids.size());
          if (!sets[sid].objsPushed) {
            sets[sid].objsPushed = true;
            const std::vector<unsigned> objs = sets[sid].objs;
            for (unsigned o : objs) {
              cell(kExt, o, 0, extra);
              // A non-constant store is its own cell. It is not a definition
              // of a constant field the path read.
              if (P.obj(o).kind != Points::Kind::Harness)
                cell(kAny, o, 0, extra);
            }
          }
          const std::vector<unsigned> &ids = sets[sid].ids;
          // The leaf runs the read covers, per object. Runs of one object
          // that overlap or touch are one run: the nodes tiling the union
          // reach the same writes over the same bytes.
          struct Run {
            unsigned obj;
            size_t a, b;
            bool operator<(const Run &o) const {
              if (obj != o.obj)
                return obj < o.obj;
              return a < o.a;
            }
          };
          std::vector<Run> runs;
          std::vector<unsigned> whole;
          for (unsigned id : ids) {
            const Points::Loc l = P.loc(id);
            if (lo == Points::Any || l.off == Points::Any) {
              whole.push_back(l.obj);
              continue;
            }
            const Points::Regions &R = P.regions(l.obj);
            const size_t n = R.bounds.size() + 1;
            const size_t a = static_cast<size_t>(Points::regionIndex(R, l.off + lo) + 1);
            size_t b;
            if (hiInf || hi <= lo)
              b = n - 1;
            else
              b = static_cast<size_t>(Points::regionIndex(R, l.off + hi - 1) + 1);
            if (hi <= lo && !hiInf)
              b = a;
            runs.push_back(Run{l.obj, a, b});
          }
          std::sort(whole.begin(), whole.end());
          whole.erase(std::unique(whole.begin(), whole.end()), whole.end());
          for (unsigned o : whole)
            cell(kDown, o, 1, extra);
          std::sort(runs.begin(), runs.end());
          for (size_t i = 0; i < runs.size();) {
            Run r = runs[i];
            size_t j = i + 1;
            while (j < runs.size() && runs[j].obj == r.obj && runs[j].a <= r.b + 1) {
              r.b = std::max(r.b, runs[j].b);
              ++j;
            }
            i = j;
            const size_t leaves = P.regions(r.obj).leaves;
            for (size_t a = r.a + leaves, b = r.b + leaves + 1; a < b; a >>= 1, b >>= 1) {
              if (a & 1) {
                cell(kDown, r.obj, a, extra);
                cell(kUp, r.obj, a, extra);
                ++a;
              }
              if (b & 1) {
                --b;
                cell(kDown, r.obj, b, extra);
                cell(kUp, r.obj, b, extra);
              }
            }
          }
        };
        // A write seen through the bytes [lo, hi) of its object. A store
        // defines its value; a memset its byte; a byte copy the source
        // bytes at the same distance -- the part of the copy within
        // [lo, hi) maps to the source range at the same distance; a copy
        // of the whole source to all of it. A write made in a context is
        // walked in that context.
        std::vector<CellRec> cellAcc;
        std::set<std::tuple<int64_t, int64_t, std::string, std::string>> cellSeen;
        auto noteCell = [&](unsigned obj, const Points::Def &d) {
          if (P.obj(obj).kind != Points::Kind::Harness || !d.inst)
            return;
          const llvm::Function *WF = d.inst->getFunction();
          if (!WF || !WF->hasName())
            return;
          std::string fn;
          if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(d.inst)) {
            const llvm::Value *sv = St->getValueOperand()->stripPointerCasts();
            if (const auto *Fn = llvm::dyn_cast<llvm::Function>(sv))
              if (Fn->hasName())
                fn = Fn->getName().str();
          }
          std::string func = WF->getName().str();
          if (!cellSeen.insert({d.off, d.len, func, fn}).second)
            return;
          cellAcc.push_back(CellRec{d.off, d.len, std::move(func), std::move(fn)});
        };
        auto walkDef = [&](unsigned obj, const Points::Def &d, int64_t lo, bool loInf, int64_t hi, bool hiInf) {
          noteCell(obj, d);
          const llvm::CallBase *wctx = P.site(d.ctx);
          if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(d.inst)) {
            val(St->getValueOperand(), wctx, 0);
            return;
          }
          const auto *C = llvm::dyn_cast<llvm::CallBase>(d.inst);
          if (!C)
            return;
          if (const auto *MS = llvm::dyn_cast<llvm::MemSetInst>(C)) {
            val(MS->getValue(), wctx, 0);
            return;
          }
          const llvm::Value *dst = nullptr;
          const llvm::Value *src = nullptr;
          if (!byteCopy(C, dst, src)) {
            // A reallocation holds the bytes of the memory it replaced.
            src = allocSource(C);
            if (!src)
              return;
          }
          if (d.off == Points::Any) {
            deref(src, 1, Points::Any, 0, true, wctx);
            return;
          }
          const int64_t from = loInf ? 0 : std::max(lo, d.off) - d.off;
          bool toInf = hiInf;
          int64_t to = 0;
          if (!hiInf)
            to = hi - d.off;
          if (d.len >= 0 && (toInf || to > d.len)) {
            to = d.len;
            toInf = false;
          }
          if (!toInf && to <= from)
            return;
          deref(src, 1, from, to, toInf, wctx);
        };
        auto expandCell = [&](int kind, unsigned o, size_t node) {
          if (kind == kExt) {
            for (const llvm::CallBase *C : P.escapes(o))
              externalCall(C);
            return;
          }
          if (kind == kAny) {
            const std::vector<Points::Def> ds = P.regions(o).any;
            for (const Points::Def &d : ds)
              walkDef(o, d, 0, true, 0, true);
            return;
          }
          if (kind == kWhole) {
            cell(kDown, o, 1, 0);
            cell(kExt, o, 0, 0);
            cell(kAny, o, 0, 0);
            const std::vector<Points::PtrLoad> &pls = P.ptrLoads(o);
            for (const Points::PtrLoad &pl : pls) {
              if (pl.inst->getFunction()->getParent() == &M)
                continue;
              WState s;
              s.kind = kLoad;
              s.v = pl.inst;
              pushAt(std::move(s), 0);
            }
            return;
          }
          const Points::Regions &R = P.regions(o);
          // A node of a tree built for an earlier solution; the walk is
          // restarted on the new one.
          if (node >= 2 * R.leaves)
            return;
          const size_t n = R.bounds.size() + 1;
          size_t a, b;
          Points::nodeLeaves(R, node, a, b);
          if (a >= n)
            return;
          b = std::min(b, n - 1);
          int64_t lo, hi;
          bool loInf, hiInf;
          Points::leafBytes(R, a, b, lo, loInf, hi, hiInf);
          // Local lists: following a copy reads other objects and can
          // build their regions, which may reallocate regionsOf.
          if (kind == kDown) {
            const std::vector<Points::Def> ds = R.tree[node];
            const size_t leaves = R.leaves;
            for (const Points::Def &d : ds)
              walkDef(o, d, lo, loInf, hi, hiInf);
            if (node < leaves) {
              cell(kDown, o, 2 * node, 0);
              cell(kDown, o, 2 * node + 1, 0);
            }
            return;
          }
          std::vector<Points::Def> ds;
          for (size_t A = node >> 1; A >= 1; A >>= 1) {
            const std::vector<Points::Def> &L = P.regions(o).tree[A];
            ds.insert(ds.end(), L.begin(), L.end());
          }
          for (const Points::Def &d : ds)
            walkDef(o, d, lo, loInf, hi, hiInf);
        };
        auto actualOf = [&](const llvm::Argument *A, const llvm::CallBase *ctx) -> const llvm::Value * {
          if (!ctx || A->getArgNo() >= ctx->arg_size())
            return nullptr;
          for (const llvm::Function *D0 : P.callees(ctx))
            if (definedBody(D0) == A->getParent())
              return ctx->getArgOperand(A->getArgNo());
          return nullptr;
        };
        // Queries may extend the points-to solution while the walk runs.
        // Everything cached here belongs to one solution; when it grows,
        // the walk starts over on the new one. The solution is finite and
        // only grows, so this ends.
        const uint64_t solutionAtStart = P.solution();
        val(P0, nullptr, 0);
        // The sink is given this buffer. Its bytes are the object, read
        // by the sink's library as far as that library loads pointer
        // fields. Intermediate pointers in the dataflow are not reads.
        if (const llvm::Value *Root = peel(P0))
          if (Root->getType()->isPointerTy())
            deref(Root, 2, Points::Any, 0, true, nullptr);
        while (!work.empty()) {
          auto wb = work.begin();
          int cost = wb->first;
          WState s = std::move(wb->second.back());
          wb->second.pop_back();
          if (wb->second.empty())
            work.erase(wb);
          auto bit0 = best.find(s);
          if (bit0 != best.end() && bit0->second < cost)
            continue;
          curCost = cost;
          if (s.kind == kLoad) {
            deref(s.v, 2, Points::Any, 0, true, nullptr);
            continue;
          }
          if (s.kind != 0) {
            expandCell(s.kind, s.obj, static_cast<size_t>(s.off));
            continue;
          }
          const llvm::Value *V = s.v;
          if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
            const llvm::Function *F = A->getParent();
            // A formal of an export is one argument the harness can pass;
            // the same formal is also whatever each caller passes, so the
            // walk records the export and goes on.
            if (alphabet(F))
              note(F->getName().str(), static_cast<int>(A->getArgNo()));
            if (const llvm::Value *act = actualOf(A, s.ctx)) {
              val(act, nullptr, 0);
            } else {
              const auto &calls = P.callers(F);
              for (const llvm::CallBase *Call : calls)
                if (Call && A->getArgNo() < Call->arg_size())
                  val(Call->getArgOperand(A->getArgNo()), nullptr, bits(calls.size()));
              // A formal of a function nothing here calls is set by code
              // outside both modules.
              if (calls.empty() && !alphabet(F))
                external(F);
            }
          } else if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
            for (const llvm::Value *inc : PN->incoming_values())
              val(inc, s.ctx, 0);
          } else if (const auto *SI = llvm::dyn_cast<llvm::SelectInst>(V)) {
            val(SI->getTrueValue(), s.ctx, 0);
            val(SI->getFalseValue(), s.ctx, 0);
          } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
            val(G->getPointerOperand(), s.ctx, 0);
          } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            // A load reads the bytes [0, size) behind its address; a store
            // into any of them defines part of the value.
            const int64_t size =
                static_cast<int64_t>(L->getModule()->getDataLayout().getTypeStoreSize(L->getType()));
            deref(L->getPointerOperand(), 1, 0, size, size <= 0, s.ctx);
          } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
            if (C->isInlineAsm()) {
              external(C->getFunction());
            } else {
              if (!allocates(C) && P.unresolved(C))
                externalCall(C);
              for (const llvm::Function *D0 : P.callees(C)) {
                const llvm::Function *D = definedBody(D0);
                if (!D || D->isDeclaration()) {
                  if (allocates(C))
                    continue;
                  // A callee with no body that accesses no memory (the
                  // IR's memory(none)) computes its result from its
                  // arguments alone; its result's bytes are theirs.
                  if (C->doesNotAccessMemory()) {
                    for (const llvm::Value *a : C->args())
                      val(a, s.ctx, 0);
                    continue;
                  }
                  external(D0);
                  continue;
                }
                for (const llvm::BasicBlock &BB : *D) {
                  const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
                  if (R && R->getReturnValue())
                    val(R->getReturnValue(), C, 0);
                }
              }
            }
          } else if (const auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
            // Arithmetic, comparisons, aggregate and vector operations:
            // the result's bytes are a function of the operands' bytes.
            for (const llvm::Value *op : I->operands())
              if (!llvm::isa<llvm::BasicBlock>(op))
                val(op, s.ctx, 0);
          }
        }
        if (P.solution() != solutionAtStart)
          return std::nullopt;
        keptCells = std::move(cellAcc);
        return out;
      };
      auto witnessOfFixed = [&](const llvm::Value *P0) -> Lab {
        for (;;)
          if (std::optional<Lab> got = witnessOf(P0))
            return *got;
      };
      for (size_t i = 0; i < jdgs.size(); ++i) {
        if (suppress.count(i))
          continue;
        if (jdgs[i].kind == 1) {
          for (const auto &a : jdgs[i].s.args)
            addIn(jdgs[i].chop, jdgs[i].chopArg, a.first, a.second);
        } else if (jdgs[i].kind == 2) {
          addOpen(jdgs[i].chop, jdgs[i].chopArg);
        }
      }
    }
    };
    classify(false);
    for (auto it = memo.begin(); it != memo.end();) {
      if (it->first.entry == ei && !provedMemo(it->second))
        it = memo.erase(it);
      else
        ++it;
    }
    for (auto it = rfMemo.begin(); it != rfMemo.end();) {
      if (it->first.entry == ei && !provedMemo(it->second))
        it = rfMemo.erase(it);
      else
        ++it;
    }
    classify(true);
  }
  for (auto &kv : inputs) {
    std::sort(kv.second.begin(), kv.second.end(), [](const Input &a, const Input &b) {
      if (a.chopArg != b.chopArg)
        return a.chopArg < b.chopArg;
      if (a.arg != b.arg)
        return a.arg < b.arg;
      return a.func < b.func;
    });
  }
  for (auto &kv : unreduced) {
    std::sort(kv.second.begin(), kv.second.end(), [](const Input &a, const Input &b) {
      if (a.chopArg != b.chopArg)
        return a.chopArg < b.chopArg;
      return a.func < b.func;
    });
  }
}


} // namespace

std::vector<EntryGroup> findEntries(llvm::Module &downstream, llvm::Module &upstream,
                                   const std::vector<std::string> &chops, const std::string &sinkFile,
                                   unsigned sinkLine, const std::vector<std::string> &sinkFns) {
  std::unordered_set<std::string> want(chops.begin(), chops.end());
  Solve solve(downstream);

  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> namedCallers, mayCallers;
  std::unordered_map<std::string, std::unordered_set<const llvm::Function *>> namedSeeds, maySeeds;
  auto note = [&](const llvm::Function *caller, const llvm::Function *D, bool named) {
    std::string name = show(D);
    if (want.count(name)) {
      if (named)
        namedSeeds[name].insert(caller);
      maySeeds[name].insert(caller);
    }
    if (!D->isDeclaration() && D->getParent() == &downstream) {
      if (named)
        namedCallers[D].insert(caller);
      mayCallers[D].insert(caller);
    }
  };
  for (llvm::Function &F : downstream) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!C || C->isInlineAsm())
        continue;
      auto namedNote = [&](const llvm::Function *caller, const llvm::Function *D) { note(caller, D, true); };
      // A function stored into this argument's object is one named edge.
      solve.noteObjectField(C, namedNote);
      for (const llvm::Function *D : solve.callees(C, false))
        note(&F, D, true);
      for (const llvm::Function *D : solve.callees(C, true))
        note(&F, D, false);
    }
  }

  auto reachOf = [&](const std::unordered_set<const llvm::Function *> &seed,
                     const std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> &callers) {
    std::unordered_set<const llvm::Function *> reach = seed;
    std::queue<const llvm::Function *> q;
    for (const llvm::Function *F : reach)
      q.push(F);
    while (!q.empty()) {
      const llvm::Function *F = q.front();
      q.pop();
      auto it = callers.find(F);
      if (it == callers.end())
        continue;
      for (const llvm::Function *C : it->second)
        if (reach.insert(C).second)
          q.push(C);
    }
    return reach;
  };
  auto exports = [](const std::unordered_set<const llvm::Function *> &reach) {
    std::vector<std::string> names;
    for (const llvm::Function *F : reach)
      if (strongExport(F))
        names.push_back(show(F));
    std::sort(names.begin(), names.end());
    names.erase(std::unique(names.begin(), names.end()), names.end());
    return names;
  };

  std::vector<EntryGroup> groups;
  std::unordered_set<const llvm::Function *> reachAll;
  std::unordered_map<std::string, std::unordered_set<std::string>> entriesOf;
  for (const std::string &chop : chops) {
    EntryGroup g;
    g.chop = chop;
    g.flow = true;
    auto named = reachOf(namedSeeds[chop], namedCallers);
    auto may = reachOf(maySeeds[chop], mayCallers);
    g.entries = exports(named);
    std::unordered_set<const llvm::Function *> exp;
    for (const llvm::Function *F : named)
      if (strongExport(F))
        exp.insert(F);
    std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> reachedBy;
    for (const llvm::Function *E : exp) {
      std::unordered_set<const llvm::Function *> seen{E};
      std::vector<const llvm::Function *> fq{E};
      for (size_t i = 0; i < fq.size(); ++i) {
        auto it = namedCallers.find(fq[i]);
        if (it == namedCallers.end())
          continue;
        for (const llvm::Function *C : it->second) {
          if (!named.count(C) || !seen.insert(C).second)
            continue;
          fq.push_back(C);
          if (exp.count(C))
            reachedBy[E].insert(C);
        }
      }
    }
    for (const llvm::Function *E : exp) {
      bool maximal = true;
      auto from = reachedBy.find(E);
      if (from != reachedBy.end()) {
        for (const llvm::Function *R : from->second) {
          auto back = reachedBy.find(R);
          if (back == reachedBy.end() || !back->second.count(E))
            maximal = false;
        }
      }
      if (maximal)
        g.initial.push_back(show(E));
    }
    std::sort(g.initial.begin(), g.initial.end());
    g.initial.erase(std::unique(g.initial.begin(), g.initial.end()), g.initial.end());
    std::unordered_set<std::string> have(g.entries.begin(), g.entries.end());
    for (const std::string &n : exports(may))
      if (!have.count(n))
        g.residual.push_back(n);
    reachAll.insert(named.begin(), named.end());
    entriesOf[chop].insert(g.entries.begin(), g.entries.end());
    groups.push_back(std::move(g));
  }
  std::unordered_map<std::string, std::unordered_set<std::string>> initialOf;
  for (const EntryGroup &g : groups)
    initialOf[g.chop].insert(g.initial.begin(), g.initial.end());
  std::unordered_map<std::string, std::vector<Input>> inputs;
  std::unordered_map<std::string, std::vector<Input>> unreduced;
  std::unordered_map<std::string, std::vector<Witness>> witnesses;
  std::unordered_map<std::string, std::vector<Cell>> cells;
  if (!reachAll.empty())
    fillInputs(solve, downstream, upstream, reachAll, namedCallers, entriesOf, initialOf, inputs, unreduced,
               witnesses, cells);
  FieldReport wide = fieldCells(downstream, upstream, sinkFile, sinkLine, sinkFns, chops, inputs);
  bool widePlaced = false;
  for (EntryGroup &g : groups) {
    g.inputs = std::move(inputs[g.chop]);
    g.unreduced = std::move(unreduced[g.chop]);
    if (!widePlaced) {
      g.cells = std::move(wide.cells);
      g.seqs = std::move(wide.seqs);
      widePlaced = true;
    }
    g.witnesses = std::move(witnesses[g.chop]);
  }
  return groups;
}

std::string formatEntries(const ChopResult &chop, const std::vector<EntryGroup> &groups) {
  std::ostringstream o;
  o << "sink " << chop.sinkFile << ":" << chop.sinkLine << "\n";
  for (const std::string &f : chop.sinkFns)
    o << "sink-fn " << f << "\n";
  for (const EntryGroup &g : groups) {
    o << "chop " << g.chop << "\n";
    if (g.entries.empty())
      o << "entry (none)\n";
    for (const std::string &e : g.entries)
      o << "entry " << e << "\n";
    for (const std::string &e : g.initial)
      o << "initial " << e << "\n";
    for (const std::string &e : g.residual)
      o << "residual " << e << "\n";
    if (g.flow)
      o << "flow\n";
    for (const Input &in : g.inputs)
      o << "input " << in.chopArg << " " << in.arg << " " << in.func << "\n";
    for (const Input &in : g.unreduced)
      o << "open " << in.chopArg << " " << in.func << "\n";
    for (int a : g.openArgs)
      o << "open " << a << "\n";
    for (const Cell &c : g.cells) {
      o << "cell " << c.chopArg << " ";
      if (c.off == Points::Any)
        o << "any";
      else
        o << c.off;
      o << " " << c.func << " " << c.len;
      if (!c.type.empty())
        o << " " << c.type;
      if (!c.path.empty())
        o << " path " << c.path;
      if (!c.fn.empty())
        o << " fn " << c.fn;
      o << "\n";
      for (const std::string &r : c.roots)
        o << "root " << r << "\n";
    }
    for (const std::string &s : g.seqs)
      o << "seq " << s << "\n";
    for (const Witness &w : g.witnesses)
    {
      o << "witness " << w.chopArg << " " << w.entry << " ";
      if (w.arg < 0)
        o << "external";
      else
        o << w.arg;
      o << " " << w.func << " " << (w.cost / 100) << "." << (w.cost % 100 < 10 ? "0" : "") << (w.cost % 100) << "\n";
    }
  }
  return o.str();
}

} // namespace chain
