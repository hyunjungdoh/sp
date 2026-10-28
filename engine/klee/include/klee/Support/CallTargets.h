//===-- CallTargets.h -------------------------------------------*- C++ -*-===//
//
// The call relation of a linked program (DESIGN-D §3.10), read the same way
// by the harness synthesizer and by the KLEE sink distance.
//
// Layer 1, Tgt_sig(c): the address-taken functions of c's type, defined or
// declared (an environment function such as malloc is a target). An executed
// indirect call calls a function of its own type (C11 6.5.2.2p9), so this
// layer contains every executed edge; it alone proves that a state cannot
// reach the sink.
//
// The refined layer, Tgt(c): the may layer resolves every indirect call site
// of D and U by multi-layer type analysis, and the model carries the result
// in the bitcode. Each defined function of D and U has sp.fn !{i64 id}, each
// indirect call site of D and U has sp.tgt !{i64 id, ...}. The client and
// the environment lie outside the may layer, so a site of D or U may also
// call any of their address-taken functions (Out, those without sp.fn):
//
//   Tgt(c) = (sp.tgt(c) ∪ Out) ∩ Tgt_sig(c).
//
// An empty Tgt(c) is the least solution's answer that no function reaches the
// callee of c: under H_mlta the call has no target. A site without sp.tgt
// lies outside D and U and keeps layer 1. Tgt(c) ⊆ Tgt_sig(c) at every site,
// so a distance over Tgt is never below the distance over Tgt_sig.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CALLTARGETS_H
#define KLEE_CALLTARGETS_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"

#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace klee {
namespace calls {

// The function a call names, through casts and aliases, or null.
inline const llvm::Function *callee(const llvm::CallBase &cb) {
  return llvm::dyn_cast<llvm::Function>(
      cb.getCalledOperand()->stripPointerCastsAndAliases());
}

inline bool indirect(const llvm::CallBase &cb) {
  return !cb.isInlineAsm() && !callee(cb);
}

inline uint64_t idOf(const llvm::MDOperand &op) {
  auto *c = llvm::mdconst::dyn_extract<llvm::ConstantInt>(op);
  return c ? c->getZExtValue() : UINT64_MAX;
}

class Targets {
public:
  // A program may be given as several modules of one context (D and U before
  // they are linked): a function is address-taken when any of them takes the
  // address of its name, and a name stands for its definition when one of
  // them has it, else for a declaration. A local name is one module's own.
  void index(llvm::Module &m) {
    for (llvm::Function &f : m) {
      if (f.isIntrinsic())
        continue;
      std::string name = f.getName().str();
      if (f.hasLocalLinkage())
        name = m.getModuleIdentifier() + '\0' + name;
      if (f.hasAddressTaken())
        taken.insert(name);
      llvm::Function *&slot = named[name];
      if (!slot || (slot->isDeclaration() && !f.isDeclaration()))
        slot = &f;
      if (llvm::MDNode *n = f.getMetadata("sp.fn"))
        byId[idOf(n->getOperand(0))] = &f;
    }
    ready = false;
  }

  const std::vector<llvm::Function *> &signature(const llvm::CallBase &cb) const {
    build();
    static const std::vector<llvm::Function *> none;
    auto it = sig.find(cb.getFunctionType());
    return it == sig.end() ? none : it->second;
  }

  const std::vector<llvm::Function *> &of(const llvm::CallBase &cb) const {
    llvm::MDNode *n = cb.getMetadata("sp.tgt");
    if (!n)
      return signature(cb);
    auto hit = cache.find(&cb);
    if (hit != cache.end())
      return hit->second;
    std::set<const llvm::Function *> in;
    for (const llvm::MDOperand &op : n->operands())
      if (auto it = byId.find(idOf(op)); it != byId.end())
        in.insert(it->second);
    std::vector<llvm::Function *> r;
    for (llvm::Function *f : signature(cb))
      if (in.count(f) || !f->getMetadata("sp.fn"))
        r.push_back(f);
    empty += r.empty();
    return cache[&cb] = r;
  }

  // Sites read with sp.tgt that no function reaches.
  mutable unsigned empty = 0;

private:
  void build() const {
    if (ready)
      return;
    sig.clear();
    for (const auto &[name, f] : named)
      if (taken.count(name))
        sig[f->getFunctionType()].push_back(f);
    ready = true;
  }
  std::map<std::string, llvm::Function *> named;
  std::set<std::string> taken;
  std::map<uint64_t, llvm::Function *> byId;
  mutable std::map<llvm::FunctionType *, std::vector<llvm::Function *>> sig;
  mutable std::unordered_map<const llvm::CallBase *, std::vector<llvm::Function *>> cache;
  mutable bool ready = false;
};

} // namespace calls
} // namespace klee

#endif
