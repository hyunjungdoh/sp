#include "Model.h"

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
        if (!G->hasAllConstantIndices() || !go(G->getPointerOperand()))
          return false;
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return false;
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName())
            out.suf.push_back(Step{ST->getName().str(), off.getSExtValue()});
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (!A)
          return false;
        auto it = m.slot.find(A);
        if (it == m.slot.end())
          return false;
        out = it->second;
        return true;
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

bool Model::heldPointer(const LoadInst *L) const {
    auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
    if (!A)
      return true;
    for (const User *U : A->users()) {
      auto *S = dyn_cast<StoreInst>(U);
      if (!S || S->getPointerOperand()->stripPointerCasts() != A)
        continue;
      if (isa<LoadInst>(S->getValueOperand()->stripPointerCasts()))
        return true;
    }
    return false;
  }

bool Model::cellLoc(Model::Mem &m, Value *V, Loc &out) const {
    std::unordered_set<const Value *> seen;
    bool cross = false;
    std::function<bool(Value *)> go = [&](Value *V) -> bool {
      if (!V || !seen.insert(V).second)
        return false;
      if (auto it = m.loc.find(V); it != m.loc.end()) {
        out = it->second;
        if (auto *L = dyn_cast<LoadInst>(V))
          if (L->getType()->isPointerTy() && !out.suf.empty() && heldPointer(L))
            out.pointee = true;
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
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return false;
        bool into = cross || out.pointee;
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName()) {
            out.suf.push_back(Step{ST->getName().str(), off.getSExtValue(), into});
            out.pointee = false;
          }
        cross = false;
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (A) {
          auto it = m.slot.find(A);
          if (it == m.slot.end())
            return false;
          out = it->second;
          if (L->getType()->isPointerTy() && !out.suf.empty() && heldPointer(L))
            out.pointee = true;
          return true;
        }
        if (L->getType()->isPointerTy() && go(L->getPointerOperand())) {
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
        if (auto *L = dyn_cast<LoadInst>(V))
          if (L->getType()->isPointerTy() && !out.suf.empty() && heldPointer(L))
            out.pointee = true;
        return true;
      }
      if (auto *C = dyn_cast<CastInst>(V))
        return go(C->getOperand(0));
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        if (!G->hasAllConstantIndices())
          return false;
        if (!go(G->getPointerOperand()))
          return false;
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return false;
        bool into = cross || out.pointee;
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName()) {
            out.suf.push_back(Step{ST->getName().str(), off.getSExtValue(), into});
            out.pointee = false;
          }
        cross = false;
        return true;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          auto it = m.slot.find(A);
          if (it == m.slot.end())
            return false;
          out = it->second;
          if (L->getType()->isPointerTy() && !out.suf.empty() && heldPointer(L))
            out.pointee = true;
          return true;
        }
        if (L->getType()->isPointerTy() && go(L->getPointerOperand())) {
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
        Function *C = CB->getCalledFunction();
        if (!C)
          return false;
        Function *D = define(C->getName());
        if (!D)
          return false;
        auto a = carryArg(D);
        if (!a || *a >= (int)CB->arg_size())
          return false;
        return go(CB->getArgOperand((unsigned)*a));
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
        if (!G->hasAllConstantIndices())
          return bad;
        ArgRef base = go(G->getPointerOperand());
        if (!base.ok)
          return bad;
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return bad;
        base.bytes += off.getSExtValue();
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName())
            base.suf.push_back(Step{ST->getName().str(), off.getSExtValue(), false});
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
        FnMove mv = fnMove(D);
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

Model::FnMove Model::fnMove(Function *F) const {
    FnMove empty;
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
      FnMove inner = fnMove(D);
      for (const PtrPut &p : inner.puts) {
        if (p.dstArg < 0 || p.srcArg < 0)
          continue;
        if ((unsigned)p.dstArg >= CB->arg_size() || (unsigned)p.srcArg >= CB->arg_size())
          continue;
        ArgRef dst = addrIn(F, CB->getArgOperand((unsigned)p.dstArg));
        ArgRef src = addrIn(F, CB->getArgOperand((unsigned)p.srcArg));
        if (!dst.ok || !src.ok)
          continue;
        dst.bytes += p.dstBytes;
        dst.suf.insert(dst.suf.end(), p.dstSuf.begin(), p.dstSuf.end());
        bool load = p.srcLoad;
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
            while (auto *C = dyn_cast<CastInst>(sv))
              sv = C->getOperand(0);
            auto *L = dyn_cast<LoadInst>(sv);
            if (!L)
              continue;
            ArgRef a = addrIn(F, L->getPointerOperand());
            if (!a.ok || a.arg < 0)
              continue;
            src = std::move(a);
          }
        }
        src.bytes += p.srcBytes;
        src.suf.insert(src.suf.end(), p.srcSuf.begin(), p.srcSuf.end());
        add(dst, src, load);
      }
    }
    moveStack.erase(F);
    moveCache[F] = out;
    return out;
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
        FnMove mv = fnMove(F);
        std::optional<Loc> found;
        bool conflict = false;
        for (const PtrPut &p : mv.puts) {
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
        FnMove mv = fnMove(D);
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
          if (A && objectLoc(m, S->getValueOperand(), v) && !m.slot.count(A)) {
            m.slot[A] = v;
            grew = true;
          }
          continue;
        }
        Loc v;
        if (objectLoc(m, &I, v) && !m.loc.count(&I)) {
          m.loc[&I] = v;
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
          if (A && locOf(m, S->getValueOperand(), v) && !m.slot.count(A)) {
            m.slot[A] = v;
            grew = true;
          }
          continue;
        }
        Loc v;
        if (locOf(m, &I, v) && !m.loc.count(&I)) {
          m.loc[&I] = v;
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
