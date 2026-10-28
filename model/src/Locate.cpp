#include "Model.h"
#include "llvm/IR/CFG.h"

namespace {

std::string bareStruct(const StructType *ST) {
  if (!ST->hasName())
    return "";
  StringRef s = ST->getName();
  size_t dot = s.rfind('.');
  if (dot != StringRef::npos && dot + 1 < s.size() &&
      s.drop_front(dot + 1).find_first_not_of("0123456789") == StringRef::npos)
    s = s.take_front(dot);
  return s.str();
}

// The field a pointer addresses: the innermost struct its constant field
// indices select and the byte offset there. A variable array index names the
// array's one element cell, as cells do.
std::optional<std::pair<std::string, int64_t>> fieldKey(const Value *P, const DataLayout &dl) {
  P = P->stripPointerCasts();
  while (auto *G = dyn_cast<GEPOperator>(P)) {
    if (isa<StructType>(G->getSourceElementType()))
      break;
    P = G->getPointerOperand()->stripPointerCasts();
  }
  auto *G = dyn_cast<GEPOperator>(P);
  if (!G)
    return std::nullopt;
  auto *ST = dyn_cast<StructType>(G->getSourceElementType());
  if (!ST || ST->isOpaque())
    return std::nullopt;
  Type *cur = ST;
  StructType *inner = nullptr;
  int64_t off = 0;
  auto I = G->idx_begin();
  if (I == G->idx_end())
    return std::nullopt;
  for (++I; I != G->idx_end(); ++I) {
    if (auto *S = dyn_cast<StructType>(cur)) {
      auto *C = dyn_cast<ConstantInt>(*I);
      if (!C)
        return std::nullopt;
      unsigned idx = (unsigned)C->getZExtValue();
      inner = S;
      off = (int64_t)dl.getStructLayout(S)->getElementOffset(idx);
      cur = S->getElementType(idx);
    } else if (auto *AT = dyn_cast<ArrayType>(cur)) {
      cur = AT->getElementType();
    } else
      return std::nullopt;
  }
  if (!inner)
    return std::nullopt;
  return std::make_pair(bareStruct(inner), off);
}

bool containsStruct(Type *T, const std::string &name, std::set<Type *> &seen) {
  if (!T || !seen.insert(T).second)
    return false;
  if (auto *S = dyn_cast<StructType>(T)) {
    if (bareStruct(S) == name)
      return true;
    for (Type *E : S->elements())
      if (containsStruct(E, name, seen))
        return true;
    return false;
  }
  if (auto *A = dyn_cast<ArrayType>(T))
    return containsStruct(A->getElementType(), name, seen);
  return false;
}

} // namespace

// §3.8 정의 3.8.2: 값 V를 필드 key에 쓰면 비트 m이 오를 수 있는가(↑_b). 상수는 그
// 비트로, key 자신의 적재는 항등 갱신으로, or는 한쪽, and는 양쪽, 캐스트·phi·select는
// 들어오는 값의 합으로 정한다. -O0의 지역 슬롯 적재는 그 슬롯에 저장된 값들의 합이다.
// 그 밖의 값은 오를 수 있다(보수적).
static bool raisesBit(const Value *V, uint64_t m, const std::pair<std::string, int64_t> &key, const DataLayout &dl,
                      std::set<const Value *> &seen) {
  if (!seen.insert(V).second)
    return false;
  if (auto *C = dyn_cast<CastInst>(V))
    return raisesBit(C->getOperand(0), m, key, dl, seen);
  if (auto *K = dyn_cast<ConstantInt>(V))
    return K->getBitWidth() <= 64 && (K->getZExtValue() & m) != 0;
  if (isa<ConstantPointerNull>(V))
    return false;
  if (auto *L = dyn_cast<LoadInst>(V)) {
    const Value *P = L->getPointerOperand()->stripPointerCasts();
    if (auto fk = fieldKey(P, dl); fk && *fk == key)
      return false;
    if (auto *A = dyn_cast<AllocaInst>(P)) {
      for (const User *U : A->users())
        if (auto *S = dyn_cast<StoreInst>(U))
          if (S->getPointerOperand()->stripPointerCasts() == A && raisesBit(S->getValueOperand(), m, key, dl, seen))
            return true;
      return false;
    }
    return true;
  }
  if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    if (BO->getOpcode() == Instruction::Or)
      return raisesBit(BO->getOperand(0), m, key, dl, seen) || raisesBit(BO->getOperand(1), m, key, dl, seen);
    if (BO->getOpcode() == Instruction::And)
      return raisesBit(BO->getOperand(0), m, key, dl, seen) && raisesBit(BO->getOperand(1), m, key, dl, seen);
    return true;
  }
  if (auto *P = dyn_cast<PHINode>(V)) {
    for (const Value *In : P->incoming_values())
      if (raisesBit(In, m, key, dl, seen))
        return true;
    return false;
  }
  if (auto *S = dyn_cast<SelectInst>(V))
    return raisesBit(S->getTrueValue(), m, key, dl, seen) || raisesBit(S->getFalseValue(), m, key, dl, seen);
  return true;
}

Function *Model::memoEstablisher(Value *Cond, bool onTrue) const {
  while (auto *C = dyn_cast<CastInst>(Cond))
    Cond = C->getOperand(0);
  auto *Cmp = dyn_cast<ICmpInst>(Cond);
  if (!Cmp)
    return nullptr;
  auto pred = onTrue ? Cmp->getPredicate() : Cmp->getInversePredicate();
  if (pred != ICmpInst::ICMP_EQ && pred != ICmpInst::ICMP_NE)
    return nullptr;
  for (unsigned s = 0; s < 2; ++s) {
    Value *A = Cmp->getOperand(s);
    while (auto *C = dyn_cast<CastInst>(A))
      A = C->getOperand(0);
    auto *BO = dyn_cast<BinaryOperator>(A);
    if (!BO || BO->getOpcode() != Instruction::And)
      continue;
    Value *O = Cmp->getOperand(1 - s);
    while (auto *C = dyn_cast<CastInst>(O))
      O = C->getOperand(0);
    auto *k = dyn_cast<ConstantInt>(O);
    if (!k || k->getBitWidth() > 64)
      return nullptr;
    for (unsigned t = 0; t < 2; ++t) {
      auto *K = dyn_cast<ConstantInt>(BO->getOperand(1 - t));
      if (!K || K->getBitWidth() > 64)
        continue;
      uint64_t m = K->getZExtValue();
      if (!m || (m & (m - 1)))
        return nullptr;
      bool set = (pred == ICmpInst::ICMP_NE && k->isZero()) || (pred == ICmpInst::ICMP_EQ && k->getZExtValue() == m);
      if (!set)
        return nullptr;
      Value *X = BO->getOperand(t);
      while (auto *C = dyn_cast<CastInst>(X))
        X = C->getOperand(0);
      auto *L = dyn_cast<LoadInst>(X);
      if (!L)
        return nullptr;
      auto key = fieldKey(L->getPointerOperand(), dl);
      if (!key)
        return nullptr;
      auto ck = std::make_tuple(key->first, key->second, m);
      if (auto it = estCache.find(ck); it != estCache.end())
        return it->second;
      std::set<Function *> est;
      for (Module *M : {&down, &up})
        for (Function &F : *M) {
          if (F.isDeclaration())
            continue;
          for (Instruction &I : instructions(F)) {
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              auto fk = fieldKey(S->getPointerOperand(), dl);
              std::set<const Value *> seen;
              if (fk && *fk == *key && raisesBit(S->getValueOperand(), m, *key, dl, seen))
                est.insert(&F);
            } else if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
              if (auto *MS = dyn_cast<MemSetInst>(MI))
                if (auto *B = dyn_cast<ConstantInt>(MS->getValue()); B && B->isZero())
                  continue;
              Value *D = MI->getRawDest()->stripPointerCasts();
              std::set<Type *> tseen;
              if (auto *G = dyn_cast<GEPOperator>(D)) {
                if (containsStruct(G->getResultElementType(), key->first, tseen) ||
                    (fieldKey(D, dl) && *fieldKey(D, dl) == *key))
                  est.insert(&F);
              } else if (auto *Al = dyn_cast<AllocaInst>(D)) {
                if (containsStruct(Al->getAllocatedType(), key->first, tseen))
                  est.insert(&F);
              }
            }
          }
        }
      Function *g = est.size() == 1 ? *est.begin() : nullptr;
      estCache[ck] = g;
      return g;
    }
  }
  return nullptr;
}

Value *Model::rootOf(Value *V) {
    std::unordered_set<const Value *> seen;
    while (V && seen.insert(V).second) {
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        V = G->getPointerOperand();
        continue;
      }
      if (auto *CE = dyn_cast<ConstantExpr>(V)) {
        if (CE->isCast()) {
          V = CE->getOperand(0);
          continue;
        }
      }
      break;
    }
    return V;
  }

std::optional<int> Model::carryArg(Function *F) const {
    if (!F || F->isDeclaration())
      return std::nullopt;
    auto it = carryCache.find(F);
    if (it != carryCache.end())
      return it->second < 0 ? std::nullopt : std::optional<int>(it->second);
    carryCache[F] = -2;
    Value *retRoot = nullptr;
    bool badRet = false;
    for (BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
        continue;
      Value *r = rootOf(V);
      if (!retRoot)
        retRoot = r;
      else if (retRoot != r)
        badRet = true;
    }
    int found = -1;
    if (!badRet && retRoot) {
      if (auto *A = dyn_cast<Argument>(retRoot)) {
        found = (int)A->getArgNo();
      } else {
        std::unordered_map<Function *, bool> pc;
        std::unordered_set<Function *> st;
        auto see = [&](Value *src) {
          int arg = -1;
          Suffix suf;
          if (!fromFormal(F, src, pc, st, arg, suf))
            return;
          if (found == -1)
            found = arg;
          else if (found != arg)
            found = -2;
        };
        for (Instruction &I : instructions(*F)) {
          if (auto *S = dyn_cast<StoreInst>(&I)) {
            if (rootOf(S->getPointerOperand()) != retRoot)
              continue;
            if (auto *L = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts()))
              see(L->getPointerOperand());
            continue;
          }
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          Copy cp = fixedCopy(*CB);
          if (!cp.ok || rootOf(CB->getArgOperand(cp.dst)) != retRoot)
            continue;
          see(CB->getArgOperand(cp.src));
        }
        if (found < -1)
          found = -1;
      }
    }
    carryCache[F] = found;
    return found < 0 ? std::nullopt : std::optional<int>(found);
  }

bool Model::objectLoc(Model::Mem &m, Value *V, Loc &out) const {
    std::unordered_set<const Value *> seen;
    std::function<bool(Value *)> go = [&](Value *V) -> bool {
      if (!V || !seen.insert(V).second)
        return false;
      if (auto it = m.loc.find(V); it != m.loc.end()) {
        out = it->second;
        return true;
      }
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        Step st;
        if (!constStep(dl, G, st) || !go(G->getPointerOperand()))
          return false;
        st.deref = out.pointee;
        if (movesAddress(st)) {
          out.suf.push_back(st);
          out.pointee = false;
        }
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (!isa<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          return false;
        return reloadLoc(m, L, out);
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return false;
          one = in;
        }
        return one && go(one);
      }
      return false;
    };
    return go(V);
  }

uint64_t Model::pointedExtent(Function *F, Value *Root, std::unordered_set<const Function *> &stack, int depth) const {
    (void)depth;
    if (!F || !Root || F->isDeclaration() || !stack.insert(F).second)
      return 0;
    struct Pop {
      std::unordered_set<const Function *> &s;
      const Function *f;
      ~Pop() { s.erase(f); }
    } pop{stack, F};
    std::unordered_map<const Value *, int64_t> at;
    std::vector<const Value *> q{Root};
    at[Root] = 0;
    for (size_t i = 0; i < q.size(); ++i) {
      const Value *V = q[i];
      int64_t o = at[V];
      for (const User *U : V->users()) {
        if (auto *C = dyn_cast<CastInst>(U)) {
          if (!at.count(C)) {
            at[C] = o;
            q.push_back(C);
          }
          continue;
        }
        auto *G = dyn_cast<GetElementPtrInst>(U);
        if (!G || G->getPointerOperand() != V)
          continue;
        APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta)) {
          if (!isa<StructType>(G->getSourceElementType()) && G->getResultElementType()->isSized()) {
            uint64_t n = dl.getTypeStoreSize(G->getResultElementType()).getFixedValue();
            at.emplace(G, o);
            if (n && o >= 0)
              at[G] = o;
          }
          continue;
        }
        int64_t n = o + delta.getSExtValue();
        if (!at.count(G)) {
          at[G] = n;
          q.push_back(G);
        }
      }
    }
    uint64_t end = 0;
    auto cover = [&](int64_t o, uint64_t n) {
      if (n == 0)
        return;
      if (o < 0)
        o = 0;
      end = std::max(end, (uint64_t)o + n);
    };
    for (const auto &kv : at) {
      auto *G = dyn_cast<GetElementPtrInst>(kv.first);
      if (!G || G->hasAllConstantIndices() || isa<StructType>(G->getSourceElementType()))
        continue;
      if (G->getResultElementType()->isSized())
        cover(kv.second, dl.getTypeStoreSize(G->getResultElementType()).getFixedValue());
    }
    for (Instruction &I : instructions(*F)) {
      if (auto *L = dyn_cast<LoadInst>(&I)) {
        auto it = at.find(L->getPointerOperand());
        if (it != at.end())
          cover(it->second, dl.getTypeStoreSize(L->getType()).getFixedValue());
      } else if (auto *S = dyn_cast<StoreInst>(&I)) {
        auto it = at.find(S->getPointerOperand());
        if (it != at.end())
          cover(it->second, dl.getTypeStoreSize(S->getValueOperand()->getType()).getFixedValue());
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Function *Cal = CB->getCalledFunction();
      if (Cal && (Cal->getName().starts_with("llvm.memcpy") || Cal->getName().starts_with("llvm.memmove") ||
                  Cal->getName().starts_with("llvm.memset"))) {
        if (CB->arg_size() >= 3)
          if (auto *N = dyn_cast<ConstantInt>(CB->getArgOperand(2))) {
            uint64_t len = N->getZExtValue();
            for (unsigned a = 0; a < 2 && a < CB->arg_size(); ++a) {
              if (Cal->getName().starts_with("llvm.memset") && a == 1)
                break;
              auto it = at.find(CB->getArgOperand(a));
              if (it != at.end())
                cover(it->second, len);
            }
          }
      }
      if (!Cal || Cal->isDeclaration() || ignorable(Cal))
        continue;
      Function *D = define(Cal->getName());
      if (!D || D->isDeclaration())
        continue;
      for (unsigned a = 0; a < CB->arg_size() && a < D->arg_size(); ++a) {
        Value *Op = CB->getArgOperand(a);
        while (auto *C = dyn_cast<CastInst>(Op))
          Op = C->getOperand(0);
        auto it = at.find(Op);
        if (it == at.end())
          continue;
        cover(it->second, pointedExtent(D, D->getArg(a), stack, depth + 1));
      }
    }
    return end;
  }

const std::vector<const StoreInst *> *Model::reaching(const LoadInst *L) const {
    if (auto it = reachMemo.find(L); it != reachMemo.end())
      return it->second ? &*it->second : nullptr;
    auto &memo = reachMemo[L];
    auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
    if (!A)
      return nullptr;
    std::unordered_set<const Instruction *> writes;
    std::vector<const Value *> names{A};
    std::unordered_set<const Value *> named;
    while (!names.empty()) {
      const Value *V = names.back();
      names.pop_back();
      if (!named.insert(V).second)
        continue;
      for (const User *U : V->users()) {
        if (isa<BitCastInst>(U) || isa<AddrSpaceCastInst>(U)) {
          names.push_back(U);
          continue;
        }
        if (auto *G = dyn_cast<GEPOperator>(U); G && G->getPointerOperand() == V && G->hasAllZeroIndices()) {
          names.push_back(U);
          continue;
        }
        if (isa<LoadInst>(U))
          continue;
        if (auto *S = dyn_cast<StoreInst>(U)) {
          if (S->getValueOperand() == V)
            return nullptr;
          writes.insert(S);
          continue;
        }
        if (auto *II = dyn_cast<IntrinsicInst>(U))
          if (II->isLifetimeStartOrEnd() || isa<DbgInfoIntrinsic>(II))
            continue;
        if (auto *CB = dyn_cast<CallBase>(U)) {
          bool writes_ = !CB->onlyReadsMemory();
          for (unsigned i = 0; writes_ && i < CB->arg_size(); ++i)
            if (CB->getArgOperand(i) == V && CB->onlyReadsMemory(i))
              writes_ = false;
          if (writes_)
            writes.insert(CB);
          continue;
        }
        return nullptr;
      }
    }
    std::vector<const StoreInst *> got;
    std::unordered_set<const StoreInst *> have;
    bool unknown = false;
    auto scan = [&](BasicBlock::const_reverse_iterator it, BasicBlock::const_reverse_iterator end) {
      for (; it != end; ++it) {
        if (!writes.count(&*it))
          continue;
        if (auto *S = dyn_cast<StoreInst>(&*it)) {
          if (have.insert(S).second)
            got.push_back(S);
        } else
          unknown = true;
        return true;
      }
      return false;
    };
    const BasicBlock *LB = L->getParent();
    std::vector<const BasicBlock *> work;
    if (!scan(++L->getReverseIterator(), LB->rend()))
      for (const BasicBlock *P : predecessors(LB))
        work.push_back(P);
    std::unordered_set<const BasicBlock *> seen;
    while (!work.empty() && !unknown) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!seen.insert(B).second)
        continue;
      if (!scan(B->rbegin(), B->rend()))
        for (const BasicBlock *P : predecessors(B))
          work.push_back(P);
    }
    if (unknown)
      return nullptr;
    memo = std::move(got);
    return &*memo;
  }

bool Model::reloadLoc(const Model::Mem &m, const LoadInst *L, Loc &out) const {
    const auto *R = reaching(L);
    if (!R)
      return false;
    std::optional<Loc> one;
    for (const StoreInst *S : *R) {
      const Value *sv = S->getValueOperand()->stripPointerCasts();
      if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
        continue;
      auto it = m.stored.find(S);
      if (it == m.stored.end() || (one && !(*one == it->second)))
        return false;
      one = it->second;
    }
    if (!one)
      return false;
    out = *one;
    return true;
  }

bool Model::cellAt(Loc v, Loc &cell) {
    if (v.pointee)
      v.suf.push_back(Step{"", 0, true});
    cell = Loc{v.arg, std::move(v.suf), false};
    return !cell.suf.empty();
  }

// Extend a location's address path by a constant-offset suffix. The first
// step enters the pointee when the base already denotes a held pointer, as in
// a field access of a loaded object. A moved address is no held pointer; an
// empty suffix leaves the value as it was.
static void appendAddr(Loc &b, const Suffix &extra) {
  if (extra.empty())
    return;
  for (size_t i = 0; i < extra.size(); ++i) {
    Step st = extra[i];
    if (i == 0)
      st.deref = st.deref || b.pointee;
    b.suf.push_back(st);
  }
  b.pointee = false;
}

// The local a pointer addresses and its constant byte offset into it.
static const AllocaInst *localBase(const DataLayout &dl, Value *V, int64_t &off) {
  APInt d(64, 0);
  Value *B = V->stripAndAccumulateConstantOffsets(dl, d, true);
  auto *A = dyn_cast<AllocaInst>(B);
  if (!A)
    return nullptr;
  off = d.getSExtValue();
  return A;
}

static std::string pinKey(const Loc &o) {
    std::string k = std::to_string(o.arg);
    for (const Step &s : o.suf)
      k += "|" + s.type + "@" + std::to_string(s.off) + (s.deref ? "*" : "");
    return k;
  }

void Model::pinVptr(const Loc &obj, const DynWitness &w) const {
    if (obj.arg < 0 || w.vtable.empty())
      return;
    Loc pin = obj;
    pin.suf.push_back(Step{"", 0, true});
    pin.suf.push_back(Step{w.type, 0, false});
    pin.pointee = false;
    std::string k = pinKey(pin);
    lastPins.push_back(k);
    VptrPin p{pin.arg, pin.suf, w.vtable, w.vptr};
    if (auto it = vptrPins.find(k); it != vptrPins.end()) {
      if (it->second.g != p.g || it->second.byte != p.byte)
        vptrBad.insert(k);
      return;
    }
    vptrPins.emplace(k, std::move(p));
  }

// A class typeinfo constant: its first word addresses one of the ABI
// typeinfo vtables the compiler emitted, which selects the record variant.
static bool classTypeInfo(const GlobalVariable *G) {
    if (!G || !G->hasInitializer())
      return false;
    const Value *first = nullptr;
    if (auto *CS = dyn_cast<ConstantStruct>(G->getInitializer())) {
      if (CS->getNumOperands())
        first = CS->getOperand(0);
    } else if (auto *CA = dyn_cast<ConstantArray>(G->getInitializer())) {
      if (CA->getNumOperands())
        first = CA->getOperand(0);
    }
    if (!first)
      return false;
    if (auto *GE = dyn_cast<GEPOperator>(first))
      first = GE->getPointerOperand();
    first = first->stripPointerCasts();
    auto *V = dyn_cast<GlobalVariable>(first);
    return V && V->getName().contains("class_type_info");
  }

std::optional<Model::DynWitness> Model::dynWitness(const CallBase *CB) const {
    if (!CB || CB->arg_size() != 4 || !CB->getArgOperand(0)->getType()->isPointerTy())
      return std::nullopt;
    auto *dst = dyn_cast<GlobalVariable>(CB->getArgOperand(2)->stripPointerCasts());
    auto *hint = dyn_cast<ConstantInt>(CB->getArgOperand(3));
    auto *src = dyn_cast<GlobalVariable>(CB->getArgOperand(1)->stripPointerCasts());
    if (!dst || !src || !hint || !classTypeInfo(src) || !classTypeInfo(dst))
      return std::nullopt;
    // A negative hint is the slow search. It names no constant offset, so
    // the cast constrains nothing.
    if (hint->getSExtValue() < 0)
      return std::nullopt;
    int64_t need = -hint->getSExtValue();
    if (!vtForReady) {
      vtForReady = true;
      uint64_t ps = dl.getPointerSize(0);
      std::function<void(Constant *, uint64_t, std::vector<std::pair<uint64_t, Constant *>> &)> slots =
          [&](Constant *C, uint64_t base, std::vector<std::pair<uint64_t, Constant *>> &out) {
            if (auto *CS = dyn_cast<ConstantStruct>(C)) {
              if (!CS->getType()->isSized())
                return;
              const StructLayout *SL = dl.getStructLayout(CS->getType());
              for (unsigned i = 0; i < CS->getNumOperands(); ++i)
                slots(CS->getOperand(i), base + SL->getElementOffset(i), out);
              return;
            }
            if (auto *CA = dyn_cast<ConstantArray>(C)) {
              Type *E = CA->getType()->getElementType();
              if (!E->isSized())
                return;
              uint64_t es = dl.getTypeAllocSize(E).getFixedValue();
              for (unsigned i = 0; i < CA->getNumOperands(); ++i)
                slots(CA->getOperand(i), base + (uint64_t)i * es, out);
              return;
            }
            if (C->getType()->isPointerTy())
              out.push_back({base, C});
          };
      auto topOf = [](Constant *C) -> std::optional<int64_t> {
        if (isa<ConstantPointerNull>(C))
          return 0;
        if (auto *CE = dyn_cast<ConstantExpr>(C))
          if (CE->getOpcode() == Instruction::IntToPtr)
            if (auto *N = dyn_cast<ConstantInt>(CE->getOperand(0)))
              return N->getSExtValue();
        return std::nullopt;
      };
      for (Module *M : {&down, &up})
        for (GlobalVariable &G : M->globals()) {
          if (!G.hasInitializer())
            continue;
          std::vector<std::pair<uint64_t, Constant *>> s;
          slots(G.getInitializer(), 0, s);
          for (size_t i = 0; i + 1 < s.size(); ++i) {
            if (s[i].first + ps != s[i + 1].first)
              continue;
            auto *T = dyn_cast<GlobalVariable>(s[i + 1].second->stripPointerCasts());
            if (!T || !classTypeInfo(T))
              continue;
            // [offset to top, typeinfo, first virtual function]. The vptr
            // addresses the function.
            if (i + 2 >= s.size() || s[i + 1].first + ps != s[i + 2].first)
              continue;
            auto top = topOf(s[i].second);
            if (!top)
              continue;
            DynWitness w;
            w.delta = *top;
            w.vtable = G.getName().str();
            w.vptr = s[i + 2].first;
            vtFor[T].push_back(w);
          }
        }
      indexVtables();
      for (auto &kv : vtFor)
        for (DynWitness &w : kv.second) {
          uint64_t best = 0;
          for (const auto &ty : vtOf)
            for (const VTab &vt : ty.second) {
              if (!vt.g || vt.g->getName() != w.vtable || vt.base != w.vptr)
                continue;
              StructType *ST = structNamed(ty.first);
              uint64_t n = ST && !ST->isOpaque() && ST->isSized() ? dl.getTypeAllocSize(ST).getFixedValue() : 0;
              if (n >= best) {
                best = n;
                w.type = ty.first;
              }
            }
        }
    }
    const DynWitness *wit = nullptr;
    if (auto it = vtFor.find(dst); it != vtFor.end())
      for (const DynWitness &w : it->second)
        if (w.delta == need && (!wit || w.vptr < wit->vptr || (w.vptr == wit->vptr && w.vtable < wit->vtable)))
          wit = &w;
    if (!wit)
      return std::nullopt;
    DynWitness out = *wit;
    out.delta = need;
    return out;
  }

std::optional<std::pair<int, Suffix>> Model::loadRet(Function *F) const {
    if (!F || F->isDeclaration())
      return std::nullopt;
    if (auto it = loadRetCache.find(F); it != loadRetCache.end())
      return it->second;
    if (!loadRetStack.insert(F).second)
      return std::nullopt;
    // The returned value is load(formal[arg] + suf): either a load of such an
    // address, or a getter call whose own path composes onto the argument.
    std::unordered_set<const Value *> seen;
    std::function<std::optional<std::pair<int, Suffix>>(Value *)> path =
        [&](Value *V) -> std::optional<std::pair<int, Suffix>> {
      if (!V || !seen.insert(V).second)
        return std::nullopt;
      if (auto *C = dyn_cast<CastInst>(V))
        return path(C->getOperand(0));
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (!L->getType()->isPointerTy())
          return std::nullopt;
        ArgRef a = addrIn(F, L->getPointerOperand());
        if (!a.ok || a.arg < 0)
          return std::nullopt;
        return std::make_pair(a.arg, a.suf);
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        Function *C = CB->getCalledFunction();
        Function *D = C ? define(C->getName()) : nullptr;
        if (!D)
          return std::nullopt;
        auto lr = loadRet(D);
        if (!lr || lr->first < 0 || (unsigned)lr->first >= CB->arg_size())
          return std::nullopt;
        ArgRef a = addrIn(F, CB->getArgOperand((unsigned)lr->first));
        if (!a.ok || a.arg < 0)
          return std::nullopt;
        Suffix s = a.suf;
        s.insert(s.end(), lr->second.begin(), lr->second.end());
        return std::make_pair(a.arg, std::move(s));
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return std::nullopt;
          one = in;
        }
        return one ? path(one) : std::nullopt;
      }
      return std::nullopt;
    };
    std::optional<std::pair<int, Suffix>> ans;
    bool any = false, bad = false;
    for (BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      if (isa<UndefValue>(V) || isa<ConstantPointerNull>(V))
        continue;
      if (!V->getType()->isPointerTy()) {
        bad = true;
        break;
      }
      auto one = path(V);
      if (!one) {
        bad = true;
        break;
      }
      if (!any) {
        ans = one;
        any = true;
      } else if (ans->first != one->first || !sameSteps(ans->second, one->second)) {
        bad = true;
        break;
      }
    }
    loadRetStack.erase(F);
    if (bad || !any)
      ans = std::nullopt;
    loadRetCache[F] = ans;
    return ans;
  }

Model::May Model::writesAt(Function *D, int k, int64_t off, uint64_t w) const {
    if (!D || D->isDeclaration() || k < 0 || (unsigned)k >= D->arg_size())
      return May::Unknown;
    auto key = std::make_tuple((const Function *)D, k, off, w);
    if (auto it = writesMemo.find(key); it != writesMemo.end())
      return it->second;
    // A cycle cannot prove absence of a write.
    if (!writesStack.insert(key).second)
      return May::Unknown;
    // Whether a pointer may address formal k's object: through casts and
    // offsets of any kind, every value a spill slot receives, every incoming
    // value of a merge, and calls that may hand back an argument.
    std::unordered_map<const Value *, bool> memoK;
    std::function<bool(Value *)> mayBeK = [&](Value *V) -> bool {
      if (!V)
        return false;
      if (auto it = memoK.find(V); it != memoK.end())
        return it->second;
      memoK[V] = false;
      bool r = false;
      if (auto *Ar = dyn_cast<Argument>(V))
        r = Ar->getParent() == D && (int)Ar->getArgNo() == k;
      else if (auto *C = dyn_cast<CastInst>(V))
        r = mayBeK(C->getOperand(0));
      else if (auto *G = dyn_cast<GEPOperator>(V))
        r = mayBeK(G->getPointerOperand());
      else if (auto *P = dyn_cast<PHINode>(V)) {
        for (Value *in : P->incoming_values())
          r = r || mayBeK(in);
      } else if (auto *Se = dyn_cast<SelectInst>(V))
        r = mayBeK(Se->getTrueValue()) || mayBeK(Se->getFalseValue());
      else if (auto *L = dyn_cast<LoadInst>(V)) {
        if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          for (User *U : Al->users())
            if (auto *S = dyn_cast<StoreInst>(U))
              if (S->getPointerOperand()->stripPointerCasts() == Al)
                r = r || mayBeK(S->getValueOperand());
      } else if (auto *CB = dyn_cast<CallBase>(V)) {
        for (Value *Op : CB->args())
          if (Op->getType()->isPointerTy())
            r = r || mayBeK(Op);
      }
      memoK[V] = r;
      return r;
    };
    auto overlaps = [&](int64_t o, uint64_t ww) {
      return o < off + (int64_t)w && off < o + (int64_t)ww;
    };
    May res = May::No;
    auto bump = [&](May m) {
      if (m == May::Yes)
        res = May::Yes;
      else if (m == May::Unknown && res == May::No)
        res = May::Unknown;
    };
    for (Instruction &I : instructions(*D)) {
      if (res == May::Yes)
        break;
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        Value *P = S->getPointerOperand();
        ArgRef a = addrIn(D, P);
        uint64_t sz = dl.getTypeStoreSize(S->getValueOperand()->getType()).getFixedValue();
        if (a.ok && a.arg == k) {
          if (overlaps(a.bytes, sz))
            res = May::Yes;
        } else if (!a.ok && mayBeK(P)) {
          // A write into formal k's object at an offset we cannot pin down.
          bump(May::Unknown);
        }
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || ignorable(CB->getCalledFunction()))
        continue;
      if (CB->onlyReadsMemory())
        continue;
      Function *C = CB->getCalledFunction();
      Function *E = C ? define(C->getName()) : nullptr;
      for (unsigned a = 0; a < CB->arg_size(); ++a) {
        Value *Op = CB->getArgOperand(a);
        if (!Op->getType()->isPointerTy() || CB->onlyReadsMemory(a))
          continue;
        ArgRef ar = addrIn(D, Op);
        bool toK = (ar.ok && ar.arg == k) || (!ar.ok && mayBeK(Op));
        if (!toK)
          continue;
        if (!E || !ar.ok) {
          bump(May::Unknown);
          continue;
        }
        bump(writesAt(E, (int)a, off - ar.bytes, w));
      }
    }
    writesStack.erase(key);
    writesMemo[key] = res;
    return res;
  }

bool Model::slotHeld(Model::Mem &m, const AllocaInst *A, int64_t off, const Instruction *at, Loc &out) const {
    if (!A)
      return false;
    if (at && at->getFunction() != A->getFunction())
      at = nullptr;
    auto memoKey = std::make_tuple(A, off, at);
    auto pin = [&](const Mem::Held &h) {
      if (h.vtable.empty())
        return;
      pinVptr(out, DynWitness{0, h.vtable, h.vbyte, h.vtype});
    };
    if (auto it = m.held.find(memoKey); it != m.held.end()) {
      if (it->second.loc) {
        out = *it->second.loc;
        pin(it->second);
        return true;
      }
      if (it->second.facts == m.facts())
        return false;
    }
    if (!slotStack.insert({A, off}).second)
      return false;
    DynWitness cast;
    bool ok = slotHeldOnce(m, A, off, at, out, cast);
    slotStack.erase({A, off});
    Mem::Held h;
    if (ok) {
      h.loc = out;
      h.vtable = cast.vtable;
      h.vbyte = cast.vptr;
      h.vtype = cast.type;
      pin(h);
    } else
      h.facts = m.facts();
    m.held[memoKey] = std::move(h);
    return ok;
  }

bool Model::slotHeldOnce(Model::Mem &m, const AllocaInst *A, int64_t off, const Instruction *at, Loc &out, DynWitness &cast) const {
    Function *F = const_cast<AllocaInst *>(A)->getFunction();
    // Names of the local and their byte offset from its base.
    std::unordered_map<const Value *, int64_t> nameOff;
    std::vector<const Value *> names{A};
    nameOff[A] = 0;
    // A definition of the field. No value means the definition cannot be named,
    // so a read it reaches is not an entry pointer.
    Mem::SlotDefs &slot = m.defs[std::make_pair(A, off)];
    bool fresh = !slot.done || slot.facts != m.facts();
    std::vector<Mem::SlotDef> eff;
    bool lost = false;
    if (!fresh) {
      eff = slot.defs;
      lost = slot.lost;
    }
    auto kill = [&](const Instruction *I) {
      if (I)
        eff.push_back({I, std::nullopt});
      else
        lost = true;
    };
    for (size_t i = 0; fresh && i < names.size(); ++i) {
      const Value *V = names[i];
      int64_t base = nameOff[V];
      for (const User *U : V->users()) {
        if (isa<LoadInst>(U))
          continue;
        if (isa<BitCastInst>(U) || isa<AddrSpaceCastInst>(U)) {
          if (!nameOff.count(U)) {
            nameOff[U] = base;
            names.push_back(U);
          }
          continue;
        }
        if (auto *G = dyn_cast<GEPOperator>(U)) {
          if (G->getPointerOperand() != V)
            continue;
          APInt d(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, d)) {
            kill(dyn_cast<Instruction>(U)); // an unknown offset of the local
            continue;
          }
          int64_t n = base + d.getSExtValue();
          if (!nameOff.count(G)) {
            nameOff[G] = n;
            names.push_back(G);
          }
          continue;
        }
        if (auto *II = dyn_cast<IntrinsicInst>(U)) {
          if (II->isLifetimeStartOrEnd() || isa<DbgInfoIntrinsic>(II))
            continue;
        }
        if (auto *S = dyn_cast<StoreInst>(const_cast<User *>(U))) {
          if (S->getValueOperand() == V) {
            kill(S); // the address escapes
            continue;
          }
          if (base != off)
            continue;
          Value *sv = S->getValueOperand()->stripPointerCasts();
          if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv)) {
            kill(S); // the field becomes null, which is not an entry pointer
            continue;
          }
          Loc v;
          if (!cellLoc(m, S->getValueOperand(), v))
            kill(S);
          else
            eff.push_back({S, v});
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(const_cast<User *>(U))) {
          Function *C = CB->getCalledFunction();
          Function *D = C ? define(C->getName()) : nullptr;
          for (unsigned a = 0; a < CB->arg_size(); ++a) {
            if (CB->getArgOperand(a) != V)
              continue;
            if (CB->onlyReadsMemory() || CB->onlyReadsMemory(a))
              continue;
            int64_t rel = off - base;
            if (!D) {
              kill(CB);
              continue;
            }
            std::vector<PtrPut> puts = putsAt(D, nullptr, (int)a, rel);
            std::optional<Loc> cand;
            DynWitness pin;
            bool conflict = false, found = false, unresolved = false;
            for (const PtrPut &p : puts) {
              if (p.dstArg != (int)a || p.dstBytes != rel)
                continue;
              bool through = false;
              for (const Step &s : p.dstSuf)
                through = through || s.deref;
              if (through)
                continue; // writes a pointee, not this field
              found = true;
              if (p.srcArg < 0 || (unsigned)p.srcArg >= CB->arg_size()) {
                unresolved = true;
                break;
              }
              Loc b;
              Value *act = CB->getArgOperand((unsigned)p.srcArg);
              if (cellLoc(m, act, b)) {
                appendAddr(b, p.srcSuf);
                if (p.srcLoad) {
                  if (b.pointee)
                    b.suf.push_back(Step{"", 0, true});
                  b.pointee = true;
                }
              } else if (p.srcLoad) {
                // The loaded pointer is the one a local holds at this field.
                int64_t lo = 0;
                const AllocaInst *Al = localBase(dl, act, lo);
                int64_t fld = lo + p.srcBytes;
                for (const Step &s : p.srcSuf) {
                  if (s.deref)
                    Al = nullptr;
                  else
                    fld += s.off;
                }
                if (!Al || !slotHeld(m, Al, fld, CB, b))
                  unresolved = true;
              } else
                unresolved = true;
              if (unresolved)
                break;
              if (cand && !(*cand == b))
                conflict = true;
              else
                cand = b;
              if (!p.vtable.empty())
                pin = DynWitness{0, p.vtable, p.vbyte, p.vtype};
            }
            if (found && cand && !conflict && !unresolved)
              eff.push_back({CB, cand, pin.vtable, pin.vptr, pin.type});
            else if (found)
              kill(CB); // a put we could not resolve, or disagreeing puts
            else if (writesAt(D, (int)a, rel, 8) != May::No)
              kill(CB); // written where the body reaches it, with no named put
          }
          continue;
        }
        kill(dyn_cast<Instruction>(U)); // an unmodelled use of the local's address
      }
    }
    if (fresh) {
      slot.done = true;
      slot.facts = m.facts();
      slot.lost = lost;
      slot.defs = eff;
    }
    if (lost)
      return false;
    // A definition reaches the read when a path from it to the read crosses no
    // other definition of the field.
    std::unordered_set<const Instruction *> defs;
    for (const Mem::SlotDef &e : eff)
      defs.insert(e.at);
    auto reaches = [&](const Instruction *D) {
      if (!at)
        return true;
      if (!D || D == at)
        return false;
      auto crossed = [&](BasicBlock::const_iterator from, BasicBlock::const_iterator to) {
        for (auto it = from; it != to; ++it)
          if (defs.count(&*it))
            return true;
        return false;
      };
      if (D->getParent() == at->getParent())
        return D->comesBefore(at) && !crossed(std::next(D->getIterator()), at->getIterator());
      if (crossed(std::next(D->getIterator()), D->getParent()->end()))
        return false;
      std::unordered_set<const BasicBlock *> seen;
      std::vector<const BasicBlock *> q;
      for (const BasicBlock *S : successors(D->getParent()))
        q.push_back(S);
      for (size_t n = 0; n < q.size(); ++n) {
        const BasicBlock *B = q[n];
        if (!seen.insert(B).second)
          continue;
        if (B == at->getParent())
          return !crossed(B->begin(), at->getIterator());
        if (crossed(B->begin(), B->end()))
          continue;
        for (const BasicBlock *S : successors(B))
          q.push_back(S);
      }
      return false;
    };
    std::optional<Loc> val;
    const Mem::SlotDef *wit = nullptr;
    bool mixed = false;
    for (const Mem::SlotDef &e : eff) {
      if (!reaches(e.at))
        continue;
      if (!e.val)
        return false;
      if (val && !(*val == *e.val))
        return false;
      val = e.val;
      // Definitions that agree on the pointer but not on the cast leave the
      // dynamic type open.
      if (wit && (wit->vtable != e.vtable || wit->vbyte != e.vbyte))
        mixed = true;
      if (!wit)
        wit = &e;
    }
    if (!val)
      return false;
    out = *val;
    if (wit && !mixed && !wit->vtable.empty())
      cast = DynWitness{0, wit->vtable, wit->vbyte, wit->vtype};
    return true;
  }

bool Model::cellLoc(Model::Mem &m, Value *V, Loc &out) const {
    std::unordered_set<const Value *> seen;
    bool cross = false;
    std::function<bool(Value *)> go = [&](Value *V) -> bool {
      if (!V || !seen.insert(V).second)
        return false;
      if (auto it = m.loc.find(V); it != m.loc.end()) {
        out = it->second;
        return true;
      }
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        if (!go(G->getPointerOperand()))
          return false;
        if (!G->hasAllConstantIndices()) {
          if (isa<StructType>(G->getSourceElementType()))
            return false;
          cross = false;
          return true;
        }
        Step st;
        if (!constStep(dl, G, st))
          return false;
        st.deref = cross || out.pointee;
        if (movesAddress(st)) {
          out.suf.push_back(st);
          out.pointee = false;
        }
        cross = false;
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        int64_t lo = 0;
        const AllocaInst *Al = localBase(dl, L->getPointerOperand(), lo);
        if (isa<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) && reloadLoc(m, L, out))
          return true;
        if (Al)
          return resolveHeld && L->getType()->isPointerTy() && slotHeld(m, Al, lo, L, out);
        if (L->getType()->isPointerTy() && go(L->getPointerOperand())) {
          if (out.pointee)
            out.suf.push_back(Step{"", 0, true});
          out.pointee = true;
          return true;
        }
        return false;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return false;
          one = in;
        }
        return one && go(one);
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        if (auto dc = dynWitness(CB)) {
          if (!go(CB->getArgOperand(0)))
            return false;
          if (dc->delta) {
            if (out.pointee)
              out.suf.push_back(Step{"", 0, true});
            out.pointee = false;
            out.suf.push_back(Step{"", dc->delta, false});
          }
          pinVptr(out, *dc);
          return true;
        }
        Function *C = CB->getCalledFunction();
        Function *D = C ? define(C->getName()) : nullptr;
        if (!D)
          return false;
        if (auto lr = loadRet(D); lr && lr->first >= 0 && lr->first < (int)CB->arg_size()) {
          // The getter returns load(actual + suf).
          Value *act = CB->getArgOperand((unsigned)lr->first);
          int64_t lo = 0;
          if (const AllocaInst *Al = localBase(dl, act, lo)) {
            for (const Step &st : lr->second) {
              if (st.deref)
                return false;
              lo += st.off;
            }
            if (resolveHeld)
              return slotHeld(m, Al, lo, CB, out);
          }
          if (!go(act))
            return false;
          appendAddr(out, lr->second);
          if (out.pointee)
            out.suf.push_back(Step{"", 0, true});
          out.pointee = true;
          return true;
        }
        // The callee returns the address formal[arg] + suf.
        if (const FnMove &mv = fnMove(D); mv.retOk && mv.ret.arg >= 0 && mv.ret.arg < (int)CB->arg_size()) {
          if (!go(CB->getArgOperand((unsigned)mv.ret.arg)))
            return false;
          appendAddr(out, mv.ret.suf);
          return true;
        }
        return false;
      }
      return false;
    };
    return go(V);
  }

bool Model::locOf(Model::Mem &m, Value *V, Loc &out) const {
    std::unordered_set<const Value *> seen;
    bool cross = false;
    std::function<bool(Value *)> go = [&](Value *V) -> bool {
      if (!V || !seen.insert(V).second)
        return false;
      if (auto it = m.loc.find(V); it != m.loc.end()) {
        out = it->second;
        return true;
      }
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        if (!G->hasAllConstantIndices())
          return false;
        if (!go(G->getPointerOperand()))
          return false;
        Step st;
        if (!constStep(dl, G, st))
          return false;
        st.deref = cross || out.pointee;
        if (movesAddress(st)) {
          out.suf.push_back(st);
          out.pointee = false;
        }
        cross = false;
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        int64_t lo = 0;
        const AllocaInst *Al = localBase(dl, L->getPointerOperand(), lo);
        if (isa<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) && reloadLoc(m, L, out))
          return true;
        if (Al)
          return resolveHeld && L->getType()->isPointerTy() && slotHeld(m, Al, lo, L, out);
        if (L->getType()->isPointerTy() && go(L->getPointerOperand())) {
          if (out.pointee)
            out.suf.push_back(Step{"", 0, true});
          out.pointee = true;
          return true;
        }
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return false;
          one = in;
        }
        return one && go(one);
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        if (auto dc = dynWitness(CB)) {
          if (!go(CB->getArgOperand(0)))
            return false;
          if (dc->delta) {
            if (out.pointee)
              out.suf.push_back(Step{"", 0, true});
            out.pointee = false;
            out.suf.push_back(Step{"", dc->delta, false});
          }
          pinVptr(out, *dc);
          return true;
        }
        Function *C = CB->getCalledFunction();
        Function *D = C ? define(C->getName()) : nullptr;
        if (!D)
          return false;
        if (auto lr = loadRet(D); lr && lr->first >= 0 && lr->first < (int)CB->arg_size()) {
          // The getter returns load(actual + suf).
          Value *act = CB->getArgOperand((unsigned)lr->first);
          int64_t lo = 0;
          if (const AllocaInst *Al = localBase(dl, act, lo)) {
            for (const Step &st : lr->second) {
              if (st.deref)
                return false;
              lo += st.off;
            }
            if (resolveHeld)
              return slotHeld(m, Al, lo, CB, out);
          }
          if (!go(act))
            return false;
          appendAddr(out, lr->second);
          if (out.pointee)
            out.suf.push_back(Step{"", 0, true});
          out.pointee = true;
          return true;
        }
        // The callee returns the address formal[arg] + suf.
        if (const FnMove &mv = fnMove(D); mv.retOk && mv.ret.arg >= 0 && mv.ret.arg < (int)CB->arg_size()) {
          if (!go(CB->getArgOperand((unsigned)mv.ret.arg)))
            return false;
          appendAddr(out, mv.ret.suf);
          return true;
        }
        if (auto a = carryArg(D); a && *a < (int)CB->arg_size())
          return go(CB->getArgOperand((unsigned)*a));
        return false;
      }
      return false;
    };
    return go(V);
  }

bool Model::sameSteps(const Suffix &a, const Suffix &b) {
    if (a.size() != b.size())
      return false;
    for (size_t i = 0; i < a.size(); ++i)
      if (a[i].type != b[i].type || a[i].off != b[i].off)
        return false;
    return true;
  }

Value *Model::storedOnce(const AllocaInst *A) const {
    Value *st = nullptr;
    for (User *U : const_cast<AllocaInst *>(A)->users()) {
      auto *S = dyn_cast<StoreInst>(U);
      if (!S || S->getPointerOperand()->stripPointerCasts() != A)
        continue;
      Value *sv = S->getValueOperand();
      if (isa<UndefValue>(sv) || isa<ConstantPointerNull>(sv))
        continue;
      if (st && st != sv)
        return nullptr;
      st = sv;
    }
    return st;
  }

Model::ArgRef Model::addrIn(Function *F, Value *V) const {
    std::unordered_set<const Value *> seen;
    std::function<ArgRef(Value *)> go = [&](Value *V) -> ArgRef {
      ArgRef bad;
      if (!V || !seen.insert(V).second)
        return bad;
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *CE = dyn_cast<ConstantExpr>(V))
        if (CE->isCast())
          return go(CE->getOperand(0));
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        Step st;
        if (!constStep(dl, G, st))
          return bad;
        ArgRef base = go(G->getPointerOperand());
        if (!base.ok)
          return bad;
        base.bytes += st.off;
        if (movesAddress(st))
          base.suf.push_back(st);
        return base;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (!A)
          return bad;
        Value *st = storedOnce(A);
        return st ? go(st) : bad;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        Function *C = CB->getCalledFunction();
        if (!C)
          return bad;
        Function *D = define(C->getName());
        if (!D)
          return bad;
        const FnMove &mv = fnMove(D);
        if (!mv.retOk || mv.ret.arg < 0 || (unsigned)mv.ret.arg >= CB->arg_size())
          return bad;
        ArgRef base = go(CB->getArgOperand((unsigned)mv.ret.arg));
        if (!base.ok)
          return bad;
        base.bytes += mv.ret.bytes;
        base.suf.insert(base.suf.end(), mv.ret.suf.begin(), mv.ret.suf.end());
        return base;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return bad;
          one = in;
        }
        return one ? go(one) : bad;
      }
      if (auto *A = dyn_cast<Argument>(V)) {
        if (A->getParent() != F)
          return bad;
        ArgRef r;
        r.root = A;
        r.arg = (int)A->getArgNo();
        r.ok = true;
        return r;
      }
      if (auto *A = dyn_cast<AllocaInst>(V)) {
        if (A->getParent()->getParent() != F)
          return bad;
        ArgRef r;
        r.root = A;
        r.ok = true;
        return r;
      }
      return bad;
    };
    return go(V);
  }

bool Model::castAddr(Function *F, Value *V, ArgRef &addr, DynWitness *wit) const {
    std::unordered_set<const Value *> seen;
    std::function<bool(Value *)> go = [&](Value *V) -> bool {
      if (!V || !seen.insert(V).second)
        return false;
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return false;
          one = in;
        }
        return one && go(one);
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          if (Value *st = storedOnce(A))
            return go(st);
        return false;
      }
      auto *CB = dyn_cast<CallBase>(V);
      if (!CB)
        return false;
      if (auto dc = dynWitness(CB)) {
        if (dc->delta)
          return false;
        if (wit && wit->vtable.empty())
          *wit = *dc;
        return go(CB->getArgOperand(0));
      }
      Function *C = CB->getCalledFunction();
      Function *D = C ? define(C->getName()) : nullptr;
      if (!D)
        return false;
      auto lr = loadRet(D);
      if (!lr || lr->first < 0 || (unsigned)lr->first >= CB->arg_size())
        return false;
      ArgRef a = addrIn(F, CB->getArgOperand((unsigned)lr->first));
      if (!a.ok || a.arg < 0)
        return false;
      a.suf.insert(a.suf.end(), lr->second.begin(), lr->second.end());
      addr = std::move(a);
      return true;
    };
    return go(V);
  }

static bool sufDeref(const Suffix &s) {
  for (const Step &st : s)
    if (st.deref)
      return true;
  return false;
}

const std::vector<Model::PtrPut> &Model::putsAt(Function *F, const Value *root, int arg, int64_t bytes) const {
  static const std::vector<PtrPut> none;
  if (!F || F->isDeclaration())
    return none;
  auto key = std::make_tuple(F, root, root ? 0 : arg, bytes);
  if (auto it = putMemo.find(key); it != putMemo.end())
    return it->second;
  if (!putStack.insert(key).second)
    return none;
  std::vector<PtrPut> got;
  {
    const FnMove &mv = fnMove(F);
    for (const PtrPut &p : mv.puts) {
      if (p.srcArg < 0)
        continue;
      if (root) {
        if (p.dstRoot == root && p.dstBytes == bytes)
          got.push_back(p);
      } else if (!sufDeref(p.dstSuf) && p.dstArg == arg && p.dstBytes == bytes)
        got.push_back(p);
    }
  }
  for (const FnMove::Edge &e : fnMove(F).edges) {
    if (!e.callee)
      continue;
    for (unsigned i = 0; i < e.actual.size(); ++i) {
      const ArgRef &at = e.actual[i];
      if (!at.ok || sufDeref(at.suf))
        continue;
      int64_t rel = 0;
      if (root) {
        if (at.root != root || at.bytes > bytes)
          continue;
        rel = bytes - at.bytes;
      } else {
        if (at.arg != arg || at.bytes > bytes)
          continue;
        rel = bytes - at.bytes;
      }
      std::vector<PtrPut> inner = putsAt(e.callee, nullptr, (int)i, rel);
      for (PtrPut &p : inner) {
        if (p.srcArg < 0 || (unsigned)p.srcArg >= e.actual.size())
          continue;
        ArgRef src = e.actual[(unsigned)p.srcArg];
        bool load = p.srcLoad;
        DynWitness wit;
        bool fromCast = false;
        if (!src.ok && !p.srcLoad && e.op[(unsigned)p.srcArg] &&
            castAddr(F, const_cast<Value *>(e.op[(unsigned)p.srcArg]), src, &wit)) {
          load = true;
          fromCast = true;
        }
        if (!src.ok)
          continue;
        if (load && src.arg < 0) {
          auto *A = dyn_cast<AllocaInst>(src.root);
          if (!A)
            continue;
          Value *st = storedOnce(A);
          if (!st)
            continue;
          ArgRef v = addrIn(F, st);
          if (v.ok && v.arg >= 0) {
            src = std::move(v);
            load = false;
          } else {
            Value *sv = st;
            while (auto *Cast = dyn_cast<CastInst>(sv))
              sv = Cast->getOperand(0);
            auto *L = dyn_cast<LoadInst>(sv);
            if (!L)
              continue;
            ArgRef a = addrIn(F, L->getPointerOperand());
            if (!a.ok || a.arg < 0)
              continue;
            src = std::move(a);
          }
        }
        if (src.arg < 0)
          continue;
        src.bytes += p.srcBytes;
        src.suf.insert(src.suf.end(), p.srcSuf.begin(), p.srcSuf.end());
        PtrPut q;
        q.dstRoot = root ? root : at.root;
        q.dstArg = root ? at.arg : arg;
        q.dstBytes = bytes;
        q.srcArg = src.arg;
        q.srcSuf = std::move(src.suf);
        q.srcBytes = src.bytes;
        q.srcLoad = load;
        if (fromCast) {
          q.vtable = std::move(wit.vtable);
          q.vbyte = wit.vptr;
          q.vtype = std::move(wit.type);
        } else {
          q.vtable = std::move(p.vtable);
          q.vbyte = p.vbyte;
          q.vtype = std::move(p.vtype);
        }
        got.push_back(std::move(q));
      }
    }
  }
  putStack.erase(key);
  return putMemo.emplace(key, std::move(got)).first->second;
}

const Model::FnMove &Model::fnMove(Function *F) const {
    static const FnMove empty;
    if (!F || F->isDeclaration())
      return empty;
    if (auto it = moveCache.find(F); it != moveCache.end())
      return it->second;
    if (!moveStack.insert(F).second)
      return empty;
    FnMove out;
    auto add = [&](ArgRef dst, ArgRef src, bool srcLoad) {
      if (!dst.ok || !src.ok || src.arg < 0)
        return;
      if (dst.arg < 0 && !isa<AllocaInst>(dst.root))
        return;
      PtrPut p;
      p.dstRoot = dst.root;
      p.dstArg = dst.arg;
      p.dstSuf = std::move(dst.suf);
      p.dstBytes = dst.bytes;
      p.srcArg = src.arg;
      p.srcSuf = std::move(src.suf);
      p.srcBytes = src.bytes;
      p.srcLoad = srcLoad;
      out.puts.push_back(std::move(p));
    };
    auto stamp = [&](const DynWitness &w) {
      if (w.vtable.empty() || out.puts.empty())
        return;
      PtrPut &q = out.puts.back();
      q.vtable = w.vtable;
      q.vbyte = w.vptr;
      q.vtype = w.type;
    };
    ArgRef ret;
    bool anyRet = false;
    bool badRet = false;
    for (BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      if (isa<UndefValue>(V) || isa<ConstantPointerNull>(V))
        continue;
      if (!V->getType()->isPointerTy()) {
        badRet = true;
        continue;
      }
      ArgRef a = addrIn(F, V);
      if (!a.ok || a.arg < 0) {
        badRet = true;
        continue;
      }
      if (!anyRet) {
        ret = a;
        anyRet = true;
      } else if (a.arg != ret.arg || a.bytes != ret.bytes || !sameSteps(a.suf, ret.suf))
        badRet = true;
    }
    if (anyRet && !badRet) {
      out.retOk = true;
      out.ret = ret;
    }
    for (Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        if (!S->getValueOperand()->getType()->isPointerTy())
          continue;
        ArgRef dst = addrIn(F, S->getPointerOperand());
        Value *sv = S->getValueOperand();
        while (auto *C = dyn_cast<CastInst>(sv))
          sv = C->getOperand(0);
        ArgRef src = addrIn(F, sv);
        if (src.ok) {
          add(dst, src, false);
          continue;
        }
        DynWitness wit;
        if (castAddr(F, sv, src, &wit)) {
          size_t n = out.puts.size();
          add(dst, src, true);
          if (out.puts.size() != n)
            stamp(wit);
          continue;
        }
        if (auto *L = dyn_cast<LoadInst>(sv))
          add(dst, addrIn(F, L->getPointerOperand()), true);
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Copy cp = fixedCopy(*CB);
      if (cp.ok && cp.len == dl.getPointerSize(0))
        add(addrIn(F, CB->getArgOperand(cp.dst)), addrIn(F, CB->getArgOperand(cp.src)), true);
      Function *C = CB->getCalledFunction();
      if (!C)
        continue;
      Function *D = define(C->getName());
      if (!D)
        continue;
      FnMove::Edge e;
      e.callee = D;
      e.op.resize(CB->arg_size());
      e.actual.resize(CB->arg_size());
      bool any = false;
      for (unsigned i = 0; i < CB->arg_size(); ++i) {
        e.op[i] = CB->getArgOperand(i);
        e.actual[i] = addrIn(F, CB->getArgOperand(i));
        any = any || e.actual[i].ok;
      }
      if (any)
        out.edges.push_back(std::move(e));
    }
    moveStack.erase(F);
    return moveCache.emplace(F, std::move(out)).first->second;
  }

std::optional<Loc> Model::valueAt(Function *F, Value *V, const Model::Mem &m) const {
    if (!F || !V)
      return std::nullopt;
    std::string key;
    key.reserve(64);
    key += std::to_string(reinterpret_cast<uintptr_t>(F));
    key.push_back(':');
    key += std::to_string(reinterpret_cast<uintptr_t>(V));
    for (Argument &A : F->args()) {
      key.push_back('|');
      auto it = m.loc.find(&A);
      if (it == m.loc.end())
        continue;
      key += std::to_string(it->second.arg);
      for (const Step &s : it->second.suf)
        key += ":" + s.type + "@" + std::to_string(s.off);
    }
    if (!valueStack.insert(key).second)
      return std::nullopt;
    if (auto it = valueCache.find(key); it != valueCache.end()) {
      valueStack.erase(key);
      return it->second;
    }
    std::unordered_set<const Value *> seen;
    std::function<std::optional<Loc>(Value *)> go = [&](Value *V) -> std::optional<Loc> {
      if (!V || !seen.insert(V).second)
        return std::nullopt;
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *CE = dyn_cast<ConstantExpr>(V))
        if (CE->isCast())
          return go(CE->getOperand(0));
      if (auto *A = dyn_cast<Argument>(V)) {
        if (A->getParent() != F)
          return std::nullopt;
        auto it = m.loc.find(A);
        if (it == m.loc.end())
          return std::nullopt;
        return it->second;
      }
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        ArgRef a = addrIn(F, V);
        if (!a.ok || a.arg < 0 || (unsigned)a.arg >= F->arg_size())
          return std::nullopt;
        auto it = m.loc.find(F->getArg((unsigned)a.arg));
        if (it == m.loc.end())
          return std::nullopt;
        Loc L = it->second;
        L.suf.insert(L.suf.end(), a.suf.begin(), a.suf.end());
        L.pointee = false;
        return L;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (A) {
          Value *st = storedOnce(A);
          return st ? go(st) : std::nullopt;
        }
        if (!L->getType()->isPointerTy())
          return std::nullopt;
        ArgRef slot = addrIn(F, L->getPointerOperand());
        if (!slot.ok || !slot.root)
          return std::nullopt;
        std::vector<PtrPut> puts = putsAt(F, slot.root, -1, slot.bytes);
        std::optional<Loc> found;
        bool conflict = false;
        for (const PtrPut &p : puts) {
          if (p.dstRoot != slot.root || p.dstBytes != slot.bytes || p.srcArg < 0)
            continue;
          if ((unsigned)p.srcArg >= F->arg_size())
            continue;
          auto it = m.loc.find(F->getArg((unsigned)p.srcArg));
          if (it == m.loc.end())
            continue;
          Loc got = it->second;
          got.suf.insert(got.suf.end(), p.srcSuf.begin(), p.srcSuf.end());
          got.pointee = p.srcLoad;
          if (!found)
            found = got;
          else if (found->arg != got.arg || found->pointee != got.pointee || !sameSteps(found->suf, got.suf))
            conflict = true;
        }
        if (conflict || !found)
          return std::nullopt;
        return found;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        Function *C = CB->getCalledFunction();
        if (!C)
          return std::nullopt;
        Function *D = define(C->getName());
        if (!D)
          return std::nullopt;
        const FnMove &mv = fnMove(D);
        if (!mv.retOk || mv.ret.arg < 0 || (unsigned)mv.ret.arg >= CB->arg_size())
          return std::nullopt;
        auto base = go(CB->getArgOperand((unsigned)mv.ret.arg));
        if (!base)
          return std::nullopt;
        base->suf.insert(base->suf.end(), mv.ret.suf.begin(), mv.ret.suf.end());
        base->pointee = false;
        return base;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in)
            return std::nullopt;
          one = in;
        }
        return one ? go(one) : std::nullopt;
      }
      return std::nullopt;
    };
    std::optional<Loc> ans = go(V);
    valueStack.erase(key);
    valueCache[key] = ans;
    return ans;
  }

void Model::bindFormals(Model::Mem &m, Function *F, const std::vector<std::optional<Loc>> &args) const {
    unsigned i = 0;
    for (Argument &A : F->args()) {
      if (i < args.size() && args[i])
        m.loc[&A] = *args[i];
      ++i;
    }
  }

void Model::notePins(Model::Mem &m, const Value *V) const {
    if (!lastPins.empty())
      m.pins[V].insert(lastPins.begin(), lastPins.end());
  }

void Model::propagateObject(Model::Mem &m, Function *F) const {
    bool grew = true;
    while (grew) {
      grew = false;
      for (Instruction &I : instructions(*F)) {
        if (isa<CallBase>(&I))
          continue;
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          auto *A = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts());
          Loc v;
          if (A && !m.stored.count(S) && cellLoc(m, S->getValueOperand(), v)) {
            m.stored[S] = v;
            grew = true;
          }
          continue;
        }
        Loc v;
        if (m.loc.count(&I))
          continue;
        lastPins.clear();
        if (cellLoc(m, &I, v)) {
          m.loc[&I] = v;
          notePins(m, &I);
          grew = true;
        }
      }
    }
  }

void Model::propagate(Model::Mem &m, Function *F) const {
    bool grew = true;
    while (grew) {
      grew = false;
      for (Instruction &I : instructions(*F)) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          auto *A = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts());
          Loc v;
          if (A && !m.stored.count(S) && locOf(m, S->getValueOperand(), v)) {
            m.stored[S] = v;
            grew = true;
          }
          continue;
        }
        Loc v;
        if (m.loc.count(&I))
          continue;
        lastPins.clear();
        if (locOf(m, &I, v)) {
          m.loc[&I] = v;
          notePins(m, &I);
          grew = true;
        }
      }
    }
  }

bool Model::fromFormal(Function *F, Value *V, std::unordered_map<Function *, bool> &pureCache, std::unordered_set<Function *> &stack, int &arg, Suffix &suf) const {
    Mem m;
    std::vector<std::optional<Loc>> roots(F->arg_size());
    for (unsigned i = 0; i < F->arg_size(); ++i)
      roots[i] = Loc{(int)i, {}};
    bindFormals(m, F, roots);
    propagate(m, F);
    Loc L;
    if (!locOf(m, V, L))
      return false;
    arg = L.arg;
    suf = L.suf;
    (void)pureCache;
    (void)stack;
    return true;
  }

bool Model::summarizes(Function *F, const std::vector<std::optional<Loc>> &args, std::unordered_map<std::string, bool> &cache,
                  std::unordered_set<std::string> &stack, Function *edgeNext) {
    if (!F || F->isDeclaration())
      return false;
    std::string key;
    key += F->getName();
    key.push_back('#');
    if (edgeNext)
      key += edgeNext->getName();
    for (const auto &a : args) {
      key.push_back('|');
      if (!a) {
        key.push_back('-');
        continue;
      }
      key += std::to_string(a->arg);
      for (const Step &s : a->suf)
        key += ":" + s.type + "+" + std::to_string(s.off);
    }
    if (auto it = cache.find(key); it != cache.end())
      return it->second;
    // A cycle has no store of its own. The frame already on the stack
    // reports a real failure if it has one.
    if (!stack.insert(key).second)
      return true;
    Mem m;
    bindFormals(m, F, args);
    // propagateObject does not treat a pointer loaded from a field as this cell.
    propagateObject(m, F);
    auto onObject = [&](Value *V) {
      auto *A = dyn_cast<Argument>(rootOf(V));
      return A && m.loc.count(A);
    };
    bool ok = true;
    for (Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        Loc L;
        if (!objectLoc(m, S->getPointerOperand(), L) && onObject(S->getPointerOperand())) {
          ok = false;
          break;
        }
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Function *C = CB->getCalledFunction();
      if (ignorable(C))
        continue;
      Copy copied = fixedCopy(*CB);
      if (copied.ok) {
        bool touches = false;
        bool known = true;
        for (unsigned a : {copied.dst, copied.src}) {
          Loc L;
          if (objectLoc(m, CB->getArgOperand(a), L)) {
            touches = true;
            continue;
          }
          if (onObject(CB->getArgOperand(a))) {
            touches = true;
            known = false;
          }
        }
        if (touches && !known) {
          ok = false;
          break;
        }
        continue;
      }
      if (edgeNext) {
        auto ts = targetsOf(CB);
        if (std::find(ts.begin(), ts.end(), edgeNext) != ts.end())
          continue;
      }
      std::vector<std::optional<Loc>> down;
      bool touch = false;
      bool unknown = false;
      bool mayWrite = false;
      unsigned argi = 0;
      for (Value *Op : CB->args()) {
        Loc L;
        // A pointer loaded from the object is a different object.
        bool located = objectLoc(m, Op, L);
        bool into = located || (Op->getType()->isPointerTy() && onObject(Op));
        // memory(argmem: read) is on the function. readonly is on one argument.
        // Both come from the header that produced this declaration.
        if (into && !CB->onlyReadsMemory() && !CB->onlyReadsMemory(argi))
          mayWrite = true;
        if (located) {
          down.push_back(L);
          touch = true;
        } else {
          down.push_back(std::nullopt);
          if (into)
            unknown = true;
        }
        ++argi;
      }
      if (!mayWrite)
        continue;
      if (unknown || (touch && (!C || C->isDeclaration() || !summarizes(C, down, cache, stack, nullptr)))) {
        ok = false;
        break;
      }
    }
    stack.erase(key);
    cache[key] = ok;
    return ok;
  }

std::unordered_set<const BasicBlock *> Model::chosenPath(Function *F, const std::unordered_set<Instruction *> &goals) const {
    std::unordered_set<const BasicBlock *> reach;
    if (!F || F->isDeclaration() || goals.empty())
      return reach;
    std::vector<const BasicBlock *> stack;
    std::unordered_set<const BasicBlock *> goalB;
    for (Instruction *g : goals)
      if (g && g->getFunction() == F) {
        stack.push_back(g->getParent());
        goalB.insert(g->getParent());
      }
    while (!stack.empty()) {
      const BasicBlock *BB = stack.back();
      stack.pop_back();
      if (!BB || !reach.insert(BB).second)
        continue;
      for (const BasicBlock *P : predecessors(BB))
        stack.push_back(P);
    }
    const BasicBlock *entry = &F->getEntryBlock();
    if (!reach.count(entry) || goalB.empty())
      return reach;
    std::unordered_map<const BasicBlock *, const BasicBlock *> prev;
    std::unordered_set<const BasicBlock *> seen;
    std::queue<const BasicBlock *> q;
    q.push(entry);
    seen.insert(entry);
    const BasicBlock *hit = nullptr;
    while (!q.empty()) {
      const BasicBlock *BB = q.front();
      q.pop();
      if (goalB.count(BB)) {
        hit = BB;
        break;
      }
      std::vector<const BasicBlock *> succs;
      for (const BasicBlock *S : successors(BB))
        if (reach.count(S))
          succs.push_back(S);
      std::sort(succs.begin(), succs.end(), [](const BasicBlock *A, const BasicBlock *B) { return A->getName() < B->getName(); });
      for (const BasicBlock *S : succs) {
        if (!seen.insert(S).second)
          continue;
        prev[S] = BB;
        q.push(S);
      }
    }
    if (!hit)
      return reach;
    std::unordered_set<const BasicBlock *> path;
    for (const BasicBlock *BB = hit;;) {
      path.insert(BB);
      auto it = prev.find(BB);
      if (it == prev.end())
        break;
      BB = it->second;
    }
    return path;
  }

std::unordered_set<const BasicBlock *> Model::sliceReach(Function *F, const std::vector<Function *> &seq) const {
    std::unordered_set<const BasicBlock *> reach;
    if (!F || F->isDeclaration())
      return reach;
    std::unordered_set<Instruction *> goals;
    bool onSeq = false;
    for (size_t si = 0; si < seq.size(); ++si) {
      if (seq[si] != F)
        continue;
      onSeq = true;
      if (si + 1 < seq.size())
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          auto ts = targetsOf(CB);
          if (std::find(ts.begin(), ts.end(), seq[si + 1]) != ts.end())
            goals.insert(&I);
        }
      for (Instruction &I : instructions(*F))
        if (sinkHere(I, sinkFile, sinkLine))
          goals.insert(&I);
    }
    if (!onSeq)
      for (BasicBlock &BB : *F)
        if (isa<ReturnInst>(BB.getTerminator()))
          goals.insert(BB.getTerminator());
    std::vector<const BasicBlock *> st;
    for (Instruction *g : goals)
      if (g)
        st.push_back(g->getParent());
    while (!st.empty()) {
      const BasicBlock *BB = st.back();
      st.pop_back();
      if (!BB || !reach.insert(BB).second)
        continue;
      for (const BasicBlock *P : predecessors(BB))
        st.push_back(P);
    }
    return reach;
  }
