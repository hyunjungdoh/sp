#include "Model.h"

#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/IR/InstIterator.h>

// Dependence of the values a callee computes on two of its formals, a pointer
// p and an integer n. Two forward closures are taken: the pointers into the
// object p points into (P), and the values that depend on n (N).
//
// Through SSA the closures are context sensitive. Inside a function they
// follow SSA edges and the reload of a local that a value was stored into.
// Across a call they enter the callee at the formal the dependent actual
// binds; the callee's return re-enters the caller only when that return
// depends on the entered formal, which the callee's own summary decides.
//
// Through memory they move only as a pair. A field pair (T, f, g) is
// established when one function stores a value of P to field f and a value
// of N to field g of one base of struct type T. A function that loads field
// f and field g of one base of type T then reads a pair of that kind: the
// two loads join P and N. One base is one SSA value, or the reloads of a
// local stored once. A single field is never merged on its own, so a count
// does not spread to every load of a field; it reaches a reader only with
// the pointer it bounds, read from the same object.
//
// n bounds the bytes read through p when some access to p's object is bounded
// by a value in N: a copy whose pointer is in P and whose length is in N; an
// address in P indexed by a value in N; an address in P indexed by a variable
// that a comparison with a value in N bounds; or a read-only declaration
// passed the count beside the pointer.
//
// The relation is a may-relation. Reported for a pair that is not one, it
// asks the harness for a buffer of n bytes where the program would take
// fewer, which only removes inputs that break the callee's size contract;
// missed, it leaves p's extent free.

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

// Casts only: stripPointerCasts would also drop a GEP to field zero.
const Value *noCasts(const Value *V) {
  while (auto *O = dyn_cast<Operator>(V)) {
    if (O->getOpcode() != Instruction::BitCast && O->getOpcode() != Instruction::AddrSpaceCast)
      break;
    V = O->getOperand(0);
  }
  return V;
}

// The value a base pointer stands for. Reloads of a local with one store
// are that store's value; any other value is itself.
const Value *baseOf(const Value *V) {
  V = noCasts(V);
  if (auto *L = dyn_cast<LoadInst>(V))
    if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
      const StoreInst *one = nullptr;
      for (const User *U : A->users())
        if (auto *S = dyn_cast<StoreInst>(U)) {
          if (S->getPointerOperand()->stripPointerCasts() != A || one)
            return V;
          one = S;
        }
      if (one)
        return A;
    }
  return V;
}

// A struct type named without the suffix module linking adds.
std::string typeName(StructType *ST) {
  if (!ST->hasName())
    return "";
  StringRef s = ST->getName();
  size_t dot = s.rfind('.');
  if (dot != StringRef::npos && dot + 1 < s.size() &&
      s.drop_front(dot + 1).find_first_not_of("0123456789") == StringRef::npos)
    s = s.take_front(dot);
  return s.str();
}

// A field address: a GEP that steps from a base into a named struct through
// constant field indices. The field is the byte offset in the outer struct.
struct Field {
  const Value *base = nullptr;
  std::string type;
  int64_t off = 0;
};
bool fieldOf(const Value *Ptr, const DataLayout &dl, Field &out) {
  auto *G = dyn_cast<GEPOperator>(noCasts(Ptr));
  if (!G)
    return false;
  auto *ST = dyn_cast<StructType>(G->getSourceElementType());
  if (!ST || typeName(ST).empty())
    return false;
  int64_t off = 0;
  auto it = gep_type_begin(G);
  for (auto I = G->idx_begin(); I != G->idx_end(); ++I, ++it) {
    auto *C = dyn_cast<ConstantInt>(*I);
    if (!C)
      return false;
    if (StructType *S = it.getStructTypeOrNull())
      off += (int64_t)dl.getStructLayout(S)->getElementOffset((unsigned)C->getZExtValue());
    else if (!C->isZero())
      return false;
  }
  out.base = baseOf(G->getPointerOperand());
  out.type = typeName(ST);
  out.off = off;
  return true;
}

} // namespace

struct Model::FlowIndex {
  std::map<std::tuple<const Function *, unsigned, int>, std::optional<bool>> retDep;
  std::unordered_map<const CallBase *, std::vector<Function *>> tg;
  // The call tree of a root: its functions in discovery order, the call
  // sites of each, and its field loads by (type, offset).
  struct Tree {
    std::vector<Function *> fns;
    std::unordered_map<const Function *, std::vector<CallBase *>> sites;
    std::map<std::pair<std::string, int64_t>, std::vector<std::pair<LoadInst *, const Value *>>> loads;
  };
  std::map<const Function *, std::shared_ptr<Tree>> trees;
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
  const DataLayout &dl = D->getParent()->getDataLayout();
  auto targets = [&](CallBase *CB) -> const std::vector<Function *> & {
    auto it = ix.tg.find(CB);
    if (it == ix.tg.end())
      it = ix.tg.emplace(CB, targetsOf(CB)).first;
    return it->second;
  };

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
            for (Function *T : targets(CB))
              if (retDep(T, a, kind))
                push(CB);
      }
    }
    ix.retDep[rk] = yes;
    return yes;
  };

  auto treeOf = [&](Function *R) -> const FlowIndex::Tree & {
    auto &slot = ix.trees[R];
    if (slot)
      return *slot;
    slot = std::make_shared<FlowIndex::Tree>();
    FlowIndex::Tree &t = *slot;
    std::unordered_set<const Function *> in{R};
    t.fns.push_back(R);
    for (size_t i = 0; i < t.fns.size(); ++i)
      for (Instruction &I : instructions(*t.fns[i])) {
        if (auto *L = dyn_cast<LoadInst>(&I)) {
          Field f;
          if (fieldOf(L->getPointerOperand(), dl, f))
            t.loads[{f.type, f.off}].push_back({L, f.base});
          continue;
        }
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        if (Function *C = CB->getCalledFunction(); C && C->isIntrinsic())
          continue;
        for (Function *T : targets(CB))
          if (T && !T->isDeclaration()) {
            t.sites[T].push_back(CB);
            if (in.insert(T).second)
              t.fns.push_back(T);
          }
      }
    return t;
  };

  // pairs: also carry field pairs through memory. A node is (value, kind,
  // global), global when the value was read from a field and so belongs to
  // no calling context; its return reaches every call site in the tree.
  auto decide = [&](bool pairs) {
    const FlowIndex::Tree *tree = pairs ? &treeOf(D) : nullptr;
    std::set<std::tuple<const Value *, int, bool>> visited;
    std::unordered_set<const Value *> inP, inN;
    std::unordered_set<const Function *> touched;
    std::vector<std::tuple<Value *, int, bool>> work;
    // Fields a value of each kind is stored to, by (function, base, type).
    std::map<std::tuple<const Function *, const Value *, std::string>, std::set<int64_t>> storedTo[2];
    std::set<std::tuple<std::string, int64_t, int64_t>> established;
    auto push = [&](Value *V, int kind, bool global) {
      if (!visited.insert({V, kind, global}).second)
        return;
      (kind == P ? inP : inN).insert(V);
      if (auto *I = dyn_cast<Instruction>(V))
        touched.insert(I->getFunction());
      else if (auto *A = dyn_cast<Argument>(V))
        touched.insert(A->getParent());
      work.push_back({V, kind, global});
    };
    // Every function of the tree that loads both fields of one base reads
    // the pair.
    auto establish = [&](const std::string &type, int64_t fp, int64_t fn) {
      if (!established.insert({type, fp, fn}).second)
        return;
      auto ip = tree->loads.find({type, fp});
      auto in = tree->loads.find({type, fn});
      if (ip == tree->loads.end() || in == tree->loads.end())
        return;
      std::map<std::pair<const Function *, const Value *>, std::vector<LoadInst *>> lenAt;
      for (auto [L, b] : in->second)
        lenAt[{L->getFunction(), b}].push_back(L);
      for (auto [L, b] : ip->second) {
        auto it = lenAt.find({L->getFunction(), b});
        if (it == lenAt.end())
          continue;
        push(L, P, true);
        for (LoadInst *Ln : it->second)
          push(Ln, N, true);
      }
    };
    push(D->getArg(p), P, false);
    push(D->getArg(n), N, false);
    while (!work.empty()) {
      auto [V, kind, global] = work.back();
      work.pop_back();
      local(V, kind, [&, kind = kind, global = global](Value *W) { push(W, kind, global); });
      for (User *U : V->users()) {
        if (pairs) {
          if (auto *St = dyn_cast<StoreInst>(U); St && St->getValueOperand() == V) {
            Field f;
            if (!fieldOf(St->getPointerOperand(), dl, f))
              continue;
            auto k = std::make_tuple((const Function *)St->getFunction(), f.base, f.type);
            if (!storedTo[kind][k].insert(f.off).second)
              continue;
            auto other = storedTo[1 - kind].find(k);
            if (other != storedTo[1 - kind].end())
              for (int64_t o : std::set<int64_t>(other->second))
                establish(f.type, kind == P ? f.off : o, kind == P ? o : f.off);
            continue;
          }
          if (global && isa<ReturnInst>(U)) {
            if (auto it = tree->sites.find(cast<ReturnInst>(U)->getFunction()); it != tree->sites.end())
              for (CallBase *CB : it->second)
                push(CB, kind, true);
            continue;
          }
        }
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
          for (Function *T : targets(CB)) {
            if (!T || T->isDeclaration() || a >= T->arg_size())
              continue;
            push(T->getArg(a), kind, global);
            returns = returns || retDep(T, a, kind);
          }
          if (returns)
            push(CB, kind, global);
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
    return yes;
  };

  // The pair closure contains the SSA one, so the SSA answer is tried first
  // and the call tree is indexed only when it is needed.
  bool yes = decide(false) || decide(true);
  pairMemo[key] = yes;
  return yes;
}
