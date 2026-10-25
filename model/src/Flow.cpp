#include "Model.h"

// Dependence of the values a callee computes on two of its formals, a pointer
// p and an integer n. Two forward closures are taken: the pointers into the
// object p points into (P), and the values that depend on n (N). The closures
// are context sensitive. Inside a function they follow SSA edges and the
// reload of a local that a value was stored into. Across a call they enter
// the callee at the formal the dependent actual binds; the callee's return
// re-enters the caller only when that return depends on the entered formal,
// which the callee's own summary decides. Each (function, formal, kind)
// summary and each (value, kind) node is computed once, so both are finite.
//
// The closures are not joined through heap fields: a store of a dependent
// value to a field does not make every load of that field dependent. That
// merge is flow- and instance-insensitive and spreads a count across the
// whole program. A relation that holds only through such a field is left
// unproven rather than asserted.
//
// n bounds the bytes read through p when some access to p's object is bounded
// by a value in N: a copy whose pointer is in P and whose length is in N; an
// address in P indexed by a value in N; an address in P indexed by a variable
// that a comparison with a value in N bounds; or a read-only declaration
// passed the count beside the pointer.

namespace {

enum Kind { P = 0, N = 1 };

bool isCopyIntrinsic(const Function *F) {
  return F && (F->getName().starts_with("llvm.memcpy") || F->getName().starts_with("llvm.memmove"));
}

// An intrinsic other than a copy or fill computes its integer result from its
// operands, so a dependent operand makes the result dependent.
bool passesValue(const Function *F) {
  return F && F->isIntrinsic() && !isCopyIntrinsic(F) && !F->getName().starts_with("llvm.memset") &&
         !F->getName().starts_with("llvm.dbg.") && !F->getName().starts_with("llvm.lifetime.");
}

// The storage an index or bound names, across -O0 reloads and constant
// adjustments: the local it is loaded from, else the value itself.
std::string storageOf(Value *V) {
  std::unordered_set<const Value *> seen;
  while (V && seen.insert(V).second) {
    if (auto *C = dyn_cast<CastInst>(V)) {
      V = C->getOperand(0);
      continue;
    }
    if (auto *B = dyn_cast<BinaryOperator>(V)) {
      bool c0 = isa<Constant>(B->getOperand(0)), c1 = isa<Constant>(B->getOperand(1));
      if (c0 != c1) {
        V = c0 ? B->getOperand(1) : B->getOperand(0);
        continue;
      }
    }
    break;
  }
  if (auto *L = dyn_cast_or_null<LoadInst>(V))
    if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
      return "a" + std::to_string(reinterpret_cast<uintptr_t>(A));
  return "v" + std::to_string(reinterpret_cast<uintptr_t>(V));
}

} // namespace

struct Model::FlowIndex {
  std::map<std::tuple<const Function *, unsigned, int>, std::optional<bool>> retDep;
};

bool Model::pairRead(Function *D, unsigned p, unsigned n) const {
  if (!D || D->isDeclaration() || p >= D->arg_size() || n >= D->arg_size())
    return false;
  if (!D->getArg(p)->getType()->isPointerTy() || !D->getArg(n)->getType()->isIntegerTy())
    return false;
  auto key = std::make_tuple((const Function *)D, p, n);
  if (auto it = pairMemo.find(key); it != pairMemo.end())
    return it->second;
  if (!flowIdx)
    flowIdx = std::make_shared<FlowIndex>();
  FlowIndex &ix = *flowIdx;

  // Successors of a dependent value inside its own function.
  auto local = [&](Value *V, int kind, const std::function<void(Value *)> &to) {
    for (User *U : V->users()) {
      if (isa<CastInst>(U) || isa<PHINode>(U) || isa<FreezeInst>(U)) {
        to(U);
      } else if (auto *S = dyn_cast<SelectInst>(U)) {
        if (S->getCondition() != V)
          to(U);
      } else if (auto *G = dyn_cast<GetElementPtrInst>(U)) {
        if (kind == P && G->getPointerOperand() == V)
          to(U);
      } else if (isa<BinaryOperator>(U) || isa<TruncInst>(U) || isa<ZExtInst>(U) || isa<SExtInst>(U)) {
        if (kind == N)
          to(U);
      } else if (auto *St = dyn_cast<StoreInst>(U)) {
        // A value stored to a local reaches the reloads of that local.
        if (St->getValueOperand() != V)
          continue;
        if (auto *A = dyn_cast<AllocaInst>(St->getPointerOperand()->stripPointerCasts()))
          for (User *W : A->users())
            if (auto *L = dyn_cast<LoadInst>(W))
              if (L->getPointerOperand()->stripPointerCasts() == A)
                to(L);
      } else if (auto *CB = dyn_cast<CallBase>(U)) {
        if (kind == N && CB->getType()->isIntegerTy() && passesValue(CB->getCalledFunction()))
          to(CB);
      }
    }
  };

  // The return of F depends on formal k.
  std::function<bool(Function *, unsigned, int)> retDep = [&](Function *F, unsigned k, int kind) -> bool {
    if (!F || F->isDeclaration() || k >= F->arg_size() || F->getReturnType()->isVoidTy())
      return false;
    auto rk = std::make_tuple((const Function *)F, k, kind);
    if (auto it = ix.retDep.find(rk); it != ix.retDep.end())
      return it->second && *it->second;
    ix.retDep[rk] = std::nullopt; // A cycle returns nothing of its own.
    std::unordered_set<const Value *> seen{F->getArg(k)};
    std::vector<Value *> work{F->getArg(k)};
    auto push = [&](Value *W) {
      if (seen.insert(W).second)
        work.push_back(W);
    };
    bool yes = false;
    while (!work.empty() && !yes) {
      Value *V = work.back();
      work.pop_back();
      local(V, kind, push);
      for (User *U : V->users()) {
        if (isa<ReturnInst>(U)) {
          yes = true;
          break;
        }
        auto *CB = dyn_cast<CallBase>(U);
        if (!CB)
          continue;
        for (unsigned a = 0; a < CB->arg_size(); ++a)
          if (CB->getArgOperand(a) == V)
            for (Function *T : targetsOf(CB))
              if (retDep(T, a, kind))
                push(CB);
      }
    }
    ix.retDep[rk] = yes;
    return yes;
  };

  std::set<std::pair<const Value *, int>> visited;
  std::unordered_set<const Value *> inP, inN;
  std::unordered_set<const Function *> touched;
  std::vector<std::pair<Value *, int>> work;
  auto note = [&](Value *V) {
    if (auto *I = dyn_cast<Instruction>(V))
      touched.insert(I->getFunction());
    else if (auto *A = dyn_cast<Argument>(V))
      touched.insert(A->getParent());
  };
  auto push = [&](Value *V, int kind) {
    if (!visited.insert({V, kind}).second)
      return;
    (kind == P ? inP : inN).insert(V);
    note(V);
    work.push_back({V, kind});
  };
  push(D->getArg(p), P);
  push(D->getArg(n), N);
  while (!work.empty()) {
    auto [V, kind] = work.back();
    work.pop_back();
    local(V, kind, [&, kind = kind](Value *W) { push(W, kind); });
    for (User *U : V->users()) {
      auto *CB = dyn_cast<CallBase>(U);
      if (!CB)
        continue;
      Function *C = CB->getCalledFunction();
      if (C && C->isIntrinsic())
        continue;
      for (unsigned a = 0; a < CB->arg_size(); ++a) {
        if (CB->getArgOperand(a) != V)
          continue;
        bool returns = false;
        for (Function *T : targetsOf(CB)) {
          if (!T || T->isDeclaration() || a >= T->arg_size())
            continue;
          push(T->getArg(a), kind);
          returns = returns || retDep(T, a, kind);
        }
        if (returns)
          push(CB, kind);
      }
    }
  }

  bool yes = false;
  std::unordered_set<std::string> indexed, bounded;
  std::vector<const Function *> order(touched.begin(), touched.end());
  std::sort(order.begin(), order.end(), [](const Function *a, const Function *b) { return a->getName() < b->getName(); });
  for (const Function *CF : order) {
    for (const Instruction &I : instructions(*CF)) {
      if (auto *G = dyn_cast<GetElementPtrInst>(&I)) {
        if (!inP.count(G->getPointerOperand()))
          continue;
        for (Value *Ix : G->indices()) {
          if (isa<Constant>(Ix))
            continue;
          if (inN.count(Ix))
            yes = true;
          indexed.insert(storageOf(Ix));
        }
      } else if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
        for (unsigned s = 0; s < 2; ++s)
          if (inN.count(Cmp->getOperand(s)))
            bounded.insert(storageOf(Cmp->getOperand(1 - s)));
      } else if (auto *CB = dyn_cast<CallBase>(&I)) {
        Function *C = CB->getCalledFunction();
        if (isCopyIntrinsic(C) && CB->arg_size() >= 3 &&
            (inP.count(CB->getArgOperand(0)) || inP.count(CB->getArgOperand(1))) && inN.count(CB->getArgOperand(2)))
          yes = true;
        if (C && C->isDeclaration() && !C->isIntrinsic())
          for (unsigned k = 0; k + 1 < CB->arg_size(); ++k)
            if (inP.count(CB->getArgOperand(k)) && inN.count(CB->getArgOperand(k + 1)) &&
                CB->getArgOperand(k + 1)->getType()->isIntegerTy() && CB->onlyReadsMemory(k))
              yes = true;
      }
      if (yes)
        break;
    }
    if (yes)
      break;
  }
  if (!yes)
    for (const std::string &s : indexed)
      if (bounded.count(s)) {
        yes = true;
        break;
      }
  pairMemo[key] = yes;
  return yes;
}
