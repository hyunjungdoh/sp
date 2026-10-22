#include "Model.h"

#include "llvm/IR/CFG.h"

#include <map>
#include <optional>

// A load reads the last store on every path that reaches it. Those stores
// cover the load when each path has one; they need not dominate it. A store
// or a load in a callee that receives the object is a store or a load of
// that object. A stored pointer is that value, so the slot is not the cell.
// A call's value is the return it computes. A pointer returned by a
// declaration that receives no runtime pointer is an object created on this
// path; bytes written into it are followed. An entry cell that still has no
// store is an input. The sink address, its length, and every comparison
// that reaches the sink use the same equation.

namespace {

struct Place {
  enum Base { Entry, Obj, Local, Global, No } base = No;
  int arg = -1;
  const Instruction *obj = nullptr;
  const AllocaInst *slot = nullptr;
  const GlobalValue *gv = nullptr;
  Suffix suf;
  bool operator==(const Place &o) const {
    return base == o.base && arg == o.arg && obj == o.obj && slot == o.slot && gv == o.gv && suf == o.suf;
  }
  bool operator<(const Place &o) const {
    if (base != o.base)
      return base < o.base;
    if (arg != o.arg)
      return arg < o.arg;
    if (obj != o.obj)
      return obj < o.obj;
    if (slot != o.slot)
      return slot < o.slot;
    if (gv != o.gv)
      return gv < o.gv;
    return suf < o.suf;
  }
};

struct Ov {
  enum K { Open, Addr, Cont, From } k = Open;
  Place p;
  const CallBase *call = nullptr;
};

bool sameOv(const Ov &a, const Ov &b) {
  return a.k == b.k && a.p == b.p && a.call == b.call;
}

bool ovLess(const Ov &a, const Ov &b) {
  if (a.k != b.k)
    return a.k < b.k;
  if (a.call != b.call)
    return a.call < b.call;
  return a.p < b.p;
}

// Destination pointer, source pointer, integer length, then only integers.
bool isCopy(const CallBase &CB) {
  if (CB.arg_size() < 3)
    return false;
  if (!CB.getArgOperand(0)->getType()->isPointerTy() || !CB.getArgOperand(1)->getType()->isPointerTy())
    return false;
  if (!CB.getArgOperand(2)->getType()->isIntegerTy())
    return false;
  for (unsigned i = 3; i < CB.arg_size(); ++i)
    if (!CB.getArgOperand(i)->getType()->isIntegerTy())
      return false;
  return true;
}

// A fresh object: the declaration returns a pointer and every pointer
// argument is a constant. A runtime pointer is the object the caller already
// had, or a buffer the call fills.
bool isAlloc(const CallBase &CB) {
  Function *D = CB.getCalledFunction();
  if (!D || !D->isDeclaration() || D->isIntrinsic() || D->getName().starts_with("llvm."))
    return false;
  if (!CB.getType()->isPointerTy())
    return false;
  bool anyInt = false;
  for (Value *A : CB.args()) {
    if (A->getType()->isIntegerTy())
      anyInt = true;
    if (A->getType()->isPointerTy() && !isa<Constant>(A))
      return false;
  }
  return anyInt;
}

// Consecutive field offsets are one cell. A variable index and a pointer
// load are boundaries. The struct type name is not part of the cell.
Place normPlace(Place p) {
  Suffix o;
  for (const Step &st : p.suf) {
    if (st.deref) {
      o.push_back(Step{"", 0, true});
      continue;
    }
    if (st.type == "v") {
      o.push_back(Step{"v", 0, false});
      continue;
    }
    if (!o.empty() && !o.back().deref && o.back().type != "v")
      o.back().off += st.off;
    else if (st.off != 0)
      o.push_back(Step{"", st.off, false});
  }
  p.suf = std::move(o);
  return p;
}

bool prefixPlace(const Place &q, const Place &p) {
  if (q.base != p.base || q.arg != p.arg || q.obj != p.obj || q.slot != p.slot || q.gv != p.gv)
    return false;
  if (q.suf.size() > p.suf.size())
    return false;
  for (size_t i = 0; i < q.suf.size(); ++i)
    if (!(q.suf[i] == p.suf[i]))
      return false;
  return true;
}

struct Fact {
  bool incoming = true;
  bool span = false;
  std::vector<Ov> vals;
  bool operator==(const Fact &o) const {
    return incoming == o.incoming && span == o.span && vals.size() == o.vals.size() &&
           std::equal(vals.begin(), vals.end(), o.vals.begin(), sameOv);
  }
  bool operator<(const Fact &o) const {
    if (incoming != o.incoming)
      return incoming < o.incoming;
    if (span != o.span)
      return span < o.span;
    if (vals.size() != o.vals.size())
      return vals.size() < o.vals.size();
    for (size_t i = 0; i < vals.size(); ++i)
      if (!sameOv(vals[i], o.vals[i]))
        return ovLess(vals[i], o.vals[i]);
    return false;
  }
};

using CellMem = std::map<Place, Fact>;

void addVal(Fact &f, const Ov &v) {
  if (v.k == Ov::Open)
    return;
  auto it = std::lower_bound(f.vals.begin(), f.vals.end(), v, ovLess);
  if (it == f.vals.end() || !sameOv(*it, v))
    f.vals.insert(it, v);
}

Fact kill(Ov v, bool span) {
  Fact f;
  f.incoming = false;
  f.span = span;
  addVal(f, v);
  return f;
}

Fact mergeFact(const Fact &a, const Fact &b) {
  Fact f;
  f.incoming = a.incoming || b.incoming;
  f.span = a.span && b.span;
  for (const Ov &v : a.vals)
    addVal(f, v);
  for (const Ov &v : b.vals)
    addVal(f, v);
  return f;
}

CellMem mergeCellMem(const CellMem &a, const CellMem &b) {
  CellMem r;
  std::set<Place> keys;
  for (const auto &kv : a)
    keys.insert(kv.first);
  for (const auto &kv : b)
    keys.insert(kv.first);
  for (const Place &p : keys) {
    Fact fa = a.count(p) ? a.at(p) : Fact{};
    Fact fb = b.count(p) ? b.at(p) : Fact{};
    r.emplace(p, mergeFact(fa, fb));
  }
  return r;
}

Fact lookup(const CellMem &mem, const Place &p) {
  const Fact *best = nullptr;
  size_t bestLen = 0;
  for (const auto &kv : mem) {
    if (!prefixPlace(kv.first, p))
      continue;
    bool exact = kv.first.suf.size() == p.suf.size();
    if (!exact && !kv.second.span)
      continue;
    // A span covers the bytes of that object. It does not cover a pointee.
    if (!exact) {
      bool cross = false;
      for (size_t i = kv.first.suf.size(); i < p.suf.size(); ++i)
        if (p.suf[i].deref)
          cross = true;
      if (cross)
        continue;
    }
    if (!best || kv.first.suf.size() > bestLen) {
      best = &kv.second;
      bestLen = kv.first.suf.size();
    }
  }
  if (!best)
    return Fact{};
  if (bestLen == p.suf.size())
    return *best;
  Fact f = *best;
  Suffix extra(p.suf.begin() + (long)bestLen, p.suf.end());
  for (Ov &v : f.vals) {
    if (v.k == Ov::Cont || v.k == Ov::Addr) {
      v.p.suf.insert(v.p.suf.end(), extra.begin(), extra.end());
      v.p = normPlace(v.p);
    }
  }
  std::sort(f.vals.begin(), f.vals.end(), ovLess);
  f.vals.erase(std::unique(f.vals.begin(), f.vals.end(), sameOv), f.vals.end());
  return f;
}

uint64_t mix(uint64_t h, uint64_t v) {
  return h ^ (v + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2));
}

uint64_t hashPlace(const Place &p) {
  uint64_t h = mix(0, (uint64_t)p.base);
  h = mix(h, (uint64_t)(p.arg + 3));
  h = mix(h, (uint64_t)(uintptr_t)p.obj);
  h = mix(h, (uint64_t)(uintptr_t)p.slot);
  h = mix(h, (uint64_t)(uintptr_t)p.gv);
  for (const Step &s : p.suf) {
    h = mix(h, (uint64_t)s.off);
    h = mix(h, s.deref ? 1 : 0);
    for (unsigned char c : s.type)
      h = mix(h, c);
  }
  return h;
}

uint64_t hashOv(const Ov &v) {
  return mix(mix(hashPlace(v.p), (uint64_t)v.k), (uint64_t)(uintptr_t)v.call);
}

uint64_t hashCellMem(const CellMem &m) {
  uint64_t h = mix(0, m.size());
  for (const auto &kv : m) {
    h = mix(h, hashPlace(kv.first));
    h = mix(h, kv.second.incoming ? 1 : 0);
    h = mix(h, kv.second.span ? 1 : 0);
    for (const Ov &v : kv.second.vals)
      h = mix(h, hashOv(v));
  }
  return h;
}

} // namespace

void Model::inputs(const std::vector<Function *> &seq, raw_ostream &out) {
  if (seq.empty() || !seq[0])
    return;
  out << "t " << pretty(seq[0]->getName()) << "\n";

  std::vector<Instruction *> sinkAt;
  for (Function *F : seq) {
    if (!F || F->isDeclaration())
      continue;
    for (Instruction &I : instructions(*F))
      if (sinkHere(I, sinkFile, sinkLine))
        sinkAt.push_back(&I);
  }
  // The sink line may compute an address that a later access dereferences.
  // That access, and the length it uses, are the same read.
  std::unordered_set<Instruction *> access(sinkAt.begin(), sinkAt.end());
  std::unordered_set<const AllocaInst *> spills;
  bool grew = true;
  while (grew) {
    grew = false;
    std::vector<Instruction *> cur(access.begin(), access.end());
    for (Instruction *I : cur) {
      for (User *U : I->users()) {
        auto *UI = dyn_cast<Instruction>(U);
        if (!UI || UI->getFunction() != I->getFunction())
          continue;
        if (isa<CastInst>(UI) || isa<GetElementPtrInst>(UI)) {
          if (access.insert(UI).second)
            grew = true;
          continue;
        }
        if (auto *S = dyn_cast<StoreInst>(UI)) {
          if (S->getValueOperand() == I) {
            if (access.insert(S).second)
              grew = true;
            if (auto *A = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
              spills.insert(A);
          }
        } else if (isa<CallBase>(UI) || isa<LoadInst>(UI)) {
          if (access.insert(UI).second)
            grew = true;
        }
      }
    }
    for (const AllocaInst *A : spills) {
      for (const User *U : A->users()) {
        if (auto *L = dyn_cast<LoadInst>(U))
          if (access.insert(const_cast<LoadInst *>(L)).second)
            grew = true;
      }
    }
  }

  auto goalCall = [&](Function *F) -> CallBase * {
    for (size_t i = 0; i + 1 < seq.size(); ++i) {
      if (seq[i] != F)
        continue;
      std::vector<CallBase *> hits;
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto ts = targetsOf(CB);
        if (std::find(ts.begin(), ts.end(), seq[i + 1]) == ts.end())
          continue;
        hits.push_back(CB);
      }
      if (hits.empty())
        return nullptr;
      CallBase *best = hits[0];
      for (CallBase *C : hits)
        if (C->comesBefore(best))
          best = C;
      return best;
    }
    return nullptr;
  };

  auto sinkIn = [&](Function *F) -> Instruction * {
    Instruction *last = nullptr;
    for (Instruction *S : sinkAt)
      if (S->getFunction() == F)
        last = S;
    return last;
  };

  std::set<Place> recorded;
  std::map<const CallBase *, std::vector<Ov>> argSaved;
  std::map<const CallBase *, Ov> retOf;
  std::unordered_set<const Function *> stack;
  std::unordered_set<const Function *> explainStack;
  std::map<BasicBlock *, std::unordered_set<BasicBlock *>> reachCache;

  struct Result {
    CellMem at;
    Ov ret;
    std::map<BasicBlock *, CellMem> out;
    CellMem entry;
    Instruction *goal = nullptr;
    std::vector<Ov> args;
    Function *fn = nullptr;
  };
  std::map<const CallBase *, Result> callDone;
  struct Cached {
    std::vector<Ov> args;
    CellMem entry;
    Result result;
  };
  std::unordered_map<uint64_t, std::vector<Cached>> cache;

  auto reaches = [&](BasicBlock *B, BasicBlock *Goal) {
    if (!Goal)
      return true;
    auto &set = reachCache[Goal];
    if (set.empty()) {
      std::deque<BasicBlock *> q;
      q.push_back(Goal);
      set.insert(Goal);
      while (!q.empty()) {
        BasicBlock *x = q.front();
        q.pop_front();
        for (BasicBlock *p : predecessors(x))
          if (set.insert(p).second)
            q.push_back(p);
      }
    }
    return set.count(B) != 0;
  };

  auto incoming = [&](BasicBlock *BB, BasicBlock *goalBB, const std::map<BasicBlock *, CellMem> &outs, const CellMem &entry) {
    CellMem in;
    bool any = false;
    if (BB == &BB->getParent()->getEntryBlock()) {
      in = entry;
      any = true;
    }
    for (BasicBlock *P : predecessors(BB)) {
      if (goalBB && !reaches(P, goalBB))
        continue;
      auto it = outs.find(P);
      if (it == outs.end())
        continue;
      if (!any) {
        in = it->second;
        any = true;
      } else
        in = mergeCellMem(in, it->second);
    }
    if (!any)
      in = entry;
    return in;
  };

  std::function<Ov(Value *, const Function *, const std::vector<Ov> &, const CellMem &)> eval;
  // A phi or select is the only value that can take an operand defined later,
  // so every cycle in the value graph passes through one. Evaluating such a
  // value while it is already being evaluated means a loop carries it back to
  // itself; that value has no single reaching base and reads as unresolved.
  std::unordered_set<const Value *> evalActive;
  std::function<Result(Function *, const std::vector<Ov> &, Instruction *, const CellMem &)> analyze;
  std::function<void(const Ov &, const CellMem &)> explainOv;
  std::function<void(Value *, const Function *, const std::vector<Ov> &, const CellMem &)> explainValue;
  std::set<std::tuple<int, Place, const CallBase *>> explained;

  // A cell whose bits are a pointer is that cell. A pointee is introduced only
  // by a store of an address, which eval already returns as Addr.
  auto materialize = [](Ov got, Type *) { return got; };

  eval = [&](Value *V, const Function *F, const std::vector<Ov> &args, const CellMem &mem) -> Ov {
    Ov open;
    if (!V)
      return open;
    bool track = isa<PHINode>(V) || isa<SelectInst>(V);
    if (track && !evalActive.insert(V).second)
      return open;
    struct Pop {
      std::unordered_set<const Value *> *s;
      const Value *v;
      bool on;
      ~Pop() {
        if (on)
          s->erase(v);
      }
    } pop{&evalActive, V, track};
    if (auto *C = dyn_cast<CastInst>(V))
      return eval(C->getOperand(0), F, args, mem);
    if (auto *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->isCast())
        return eval(CE->getOperand(0), F, args, mem);
    }
    if (isa<ConstantInt>(V) || isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
      return open;
    if (auto *A = dyn_cast<Argument>(V)) {
      if (A->getParent() != F || A->getArgNo() >= args.size())
        return open;
      return args[A->getArgNo()];
    }
    if (auto *G = dyn_cast<GEPOperator>(V)) {
      Ov base = eval(G->getPointerOperand(), F, args, mem);
      if (base.k != Ov::Addr)
        return open;
      if (!G->hasAllConstantIndices()) {
        if (isa<StructType>(G->getSourceElementType()))
          return open;
        base.p.suf.push_back(Step{"v", 0, false});
        base.p = normPlace(base.p);
        return base;
      }
      APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
      if (!G->accumulateConstantOffset(dl, off))
        return open;
      base.p.suf.push_back(Step{"", off.getSExtValue(), false});
      base.p = normPlace(base.p);
      return base;
    }
    if (auto *L = dyn_cast<LoadInst>(V)) {
      Ov ptr = eval(L->getPointerOperand(), F, args, mem);
      if (ptr.k != Ov::Addr)
        return open;
      Fact f = lookup(mem, ptr.p);
      if (!f.incoming && f.vals.size() == 1)
        return materialize(f.vals[0], L->getType());
      if (!f.incoming)
        return open;
      if (!f.vals.empty())
        return open;
      if (ptr.p.base != Place::Entry)
        return open;
      // No covering store. The cell is unresolved, so it is not the pointee.
      Ov got;
      got.k = Ov::Cont;
      got.p = normPlace(ptr.p);
      return got;
    }
    if (auto *CB = dyn_cast<CallBase>(V)) {
      auto it = retOf.find(CB);
      if (it == retOf.end())
        return open;
      return it->second;
    }
    if (auto *P = dyn_cast<PHINode>(V)) {
      Ov acc;
      bool any = false;
      bool bad = false;
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
        Value *in = P->getIncomingValue(i);
        if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
          continue;
        Ov o = eval(in, F, args, mem);
        if (o.k == Ov::Open)
          continue;
        if (!any) {
          acc = o;
          any = true;
        } else if (!sameOv(acc, o))
          bad = true;
      }
      if (!any || bad)
        return open;
      return acc;
    }
    if (auto *S = dyn_cast<SelectInst>(V)) {
      Ov t = eval(S->getTrueValue(), F, args, mem);
      Ov f = eval(S->getFalseValue(), F, args, mem);
      if (sameOv(t, f) && t.k != Ov::Open)
        return t;
      if (t.k == Ov::Open)
        return f;
      if (f.k == Ov::Open)
        return t;
      return open;
    }
    if (auto *Al = dyn_cast<AllocaInst>(V)) {
      Ov o;
      o.k = Ov::Addr;
      o.p.base = Place::Local;
      o.p.slot = Al;
      return o;
    }
    if (auto *GV = dyn_cast<GlobalValue>(V)) {
      Ov o;
      o.k = Ov::Addr;
      o.p.base = Place::Global;
      o.p.gv = GV;
      return o;
    }
    return open;
  };

  explainOv = [&](const Ov &v, const CellMem &mem) {
    if (v.k == Ov::Open)
      return;
    if (!explained.insert({(int)v.k, v.p, v.call}).second)
      return;
    if (v.k == Ov::Cont) {
      if (v.p.base == Place::Entry)
        recorded.insert(v.p);
      return;
    }
    if (v.k == Ov::From) {
      auto it = argSaved.find(v.call);
      if (it == argSaved.end())
        return;
      for (const Ov &a : it->second)
        explainOv(a, mem);
      return;
    }
    if (v.k != Ov::Addr)
      return;
    Fact f = lookup(mem, v.p);
    for (const Ov &s : f.vals)
      explainOv(s, mem);
    if ((f.vals.empty() || f.incoming) && v.p.base == Place::Entry)
      recorded.insert(normPlace(v.p));
    // Entry pointers stored in this object are sources of the bytes it holds.
    for (const auto &kv : mem) {
      if (kv.first.base != v.p.base || kv.first.arg != v.p.arg || kv.first.obj != v.p.obj ||
          kv.first.slot != v.p.slot || kv.first.gv != v.p.gv)
        continue;
      if (!prefixPlace(v.p, kv.first))
        continue;
      bool cross = false;
      for (size_t i = v.p.suf.size(); i < kv.first.suf.size(); ++i)
        if (kv.first.suf[i].deref)
          cross = true;
      if (cross)
        continue;
      for (const Ov &s : kv.second.vals)
        explainOv(s, mem);
    }
    if (v.p.base == Place::Obj && f.vals.empty()) {
      for (const auto &kv : mem) {
        if (kv.first.obj != v.p.obj || kv.first.base != Place::Obj)
          continue;
        if (!prefixPlace(v.p, kv.first) && !prefixPlace(kv.first, v.p))
          continue;
        for (const Ov &s : kv.second.vals)
          explainOv(s, mem);
      }
    }
  };

  explainValue = [&](Value *V, const Function *F, const std::vector<Ov> &args, const CellMem &mem) {
    std::unordered_set<const Value *> seen;
    std::function<void(Value *)> go = [&](Value *U) {
      if (!U || !seen.insert(U).second)
        return;
      if (auto *C = dyn_cast<CastInst>(U)) {
        go(C->getOperand(0));
        return;
      }
      if (auto *G = dyn_cast<GEPOperator>(U)) {
        go(G->getPointerOperand());
        if (!G->hasAllConstantIndices()) {
          for (unsigned i = 1; i < G->getNumOperands(); ++i)
            if (!isa<Constant>(G->getOperand(i)))
              go(G->getOperand(i));
        }
      }
      if (auto *L = dyn_cast<LoadInst>(U)) {
        Ov ptr = eval(L->getPointerOperand(), F, args, mem);
        if (ptr.k != Ov::Addr)
          return;
        Fact fact = lookup(mem, ptr.p);
        if (fact.vals.empty() && fact.incoming) {
          if (ptr.p.base != Place::Entry)
            return;
          // The unresolved cell is not the input when this object already
          // holds an entry pointer. That pointer is the source.
          Place parent = normPlace(ptr.p);
          bool held = false;
          if (!parent.suf.empty()) {
            parent.suf.pop_back();
            for (const auto &kv : mem) {
              if (kv.first.base != parent.base || kv.first.arg != parent.arg || kv.first.obj != parent.obj ||
                  kv.first.slot != parent.slot || kv.first.gv != parent.gv)
                continue;
              if (!prefixPlace(parent, kv.first) || kv.first.suf.size() == parent.suf.size())
                continue;
              bool cross = false;
              for (size_t i = parent.suf.size(); i < kv.first.suf.size(); ++i)
                if (kv.first.suf[i].deref)
                  cross = true;
              if (cross)
                continue;
              for (const Ov &s : kv.second.vals) {
                if (s.p.base == Place::Entry && (s.k == Ov::Addr || s.k == Ov::Cont)) {
                  explainOv(s, mem);
                  held = true;
                }
              }
            }
          }
          if (!held)
            recorded.insert(normPlace(ptr.p));
          return;
        }
        for (const Ov &s : fact.vals)
          explainOv(materialize(s, L->getType()), mem);
        if (fact.incoming && ptr.p.base == Place::Entry)
          recorded.insert(ptr.p);
        return;
      }
      explainOv(eval(U, F, args, mem), mem);
    };
    go(V);
  };

  auto resolveBody = [&](CallBase *CB, Function *Caller) -> Function * {
    if (Function *Cal = CB->getCalledFunction()) {
      if (Cal->isIntrinsic() || Cal->getName().starts_with("llvm."))
        return nullptr;
      return define(Cal->getName());
    }
    for (size_t i = 0; i + 1 < seq.size(); ++i) {
      if (seq[i] != Caller)
        continue;
      auto all = targetsOf(CB);
      if (std::find(all.begin(), all.end(), seq[i + 1]) != all.end())
        return seq[i + 1];
    }
    auto all = targetsOf(CB);
    if (all.size() == 1)
      return all[0];
    return nullptr;
  };

  // A store or a load in a callee that receives an object is a store or a
  // load of that object. The script names which argument and which offset,
  // and each callsite applies it to its own actuals.
  struct Base {
    int arg = -1;
    int64_t off = 0;
    bool ok = false;
    bool cont = false;
    bool var = false;
    const Instruction *alloc = nullptr;
  };
  struct Eff {
    int dstArg = -1;
    int64_t dstOff = 0;
    bool dstVar = false;
    int srcArg = -1;
    int64_t srcOff = 0;
    bool srcCont = false;
    bool srcVar = false;
    const Instruction *srcAlloc = nullptr;
    const Instruction *allocI = nullptr;
    const CallBase *from = nullptr;
    std::vector<Base> fromArgs;
  };
  struct Op {
    bool store = false;
    bool read = false;
    bool call = false;
    Eff e;
    Base rd;
    std::vector<Function *> bodies;
    std::vector<Base> args;
  };
  std::unordered_map<const Function *, std::vector<Op>> scriptOf;
  std::vector<Place> pendingReads;
  std::unordered_set<const Function *> applyStack;
  // A callee's effect depends only on the function and the abstract values of
  // its arguments. The call graph joins and splits, so the same function with
  // the same arguments is reached along many paths of one traversal; threading
  // its effect once per distinct pair makes the traversal finite instead of
  // growing with the number of paths. The set spans one top-level thread and
  // is cleared when that thread returns, so a later caller state still applies.
  std::unordered_set<std::string> applyMemo;

  std::unordered_map<const Function *, Base> retArgOf;
  std::unordered_set<const Function *> retStack;
  std::function<Base(Function *)> retArg;
  retArg = [&](Function *G) -> Base {
    auto it = retArgOf.find(G);
    if (it != retArgOf.end())
      return it->second;
    Base none;
    if (!G || G->isDeclaration() || !retStack.insert(G).second) {
      retArgOf.emplace(G, none);
      return none;
    }
    std::map<const AllocaInst *, int> spill;
    for (Instruction &I : instructions(*G)) {
      auto *S = dyn_cast<StoreInst>(&I);
      if (!S)
        continue;
      auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts());
      auto *A = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
      if (Al && A && A->getParent() == G && !spill.count(Al))
        spill[Al] = (int)A->getArgNo();
    }
    std::function<Base(Value *)> bof = [&](Value *V) -> Base {
      Base no;
      if (!V)
        return no;
      if (auto *C = dyn_cast<CastInst>(V))
        return bof(C->getOperand(0));
      if (auto *A = dyn_cast<Argument>(V)) {
        if (A->getParent() != G)
          return no;
        Base b;
        b.ok = true;
        b.arg = (int)A->getArgNo();
        return b;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          auto s = spill.find(Al);
          if (s != spill.end()) {
            Base b;
            b.ok = true;
            b.arg = s->second;
            return b;
          }
        }
        return no;
      }
      if (auto *Gp = dyn_cast<GEPOperator>(V)) {
        Base b = bof(Gp->getPointerOperand());
        if (!b.ok)
          return no;
        if (!Gp->hasAllConstantIndices()) {
          b.var = true;
          return b;
        }
        APInt off(dl.getIndexSizeInBits(Gp->getPointerAddressSpace()), 0);
        if (!Gp->accumulateConstantOffset(dl, off))
          return no;
        b.off += off.getSExtValue();
        return b;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        Function *D = nullptr;
        if (Function *C = CB->getCalledFunction())
          D = define(C->getName());
        if (!D || D->isDeclaration())
          return no;
        Base rb = retArg(D);
        if (!rb.ok || rb.arg < 0 || rb.arg >= (int)CB->arg_size())
          return no;
        Base act = bof(CB->getArgOperand(rb.arg));
        if (!act.ok)
          return no;
        act.off += rb.off;
        act.var = act.var || rb.var;
        return act;
      }
      return no;
    };
    Base acc;
    bool any = false;
    bool bad = false;
    for (Instruction &I : instructions(*G)) {
      auto *R = dyn_cast<ReturnInst>(&I);
      if (!R || !R->getReturnValue())
        continue;
      Base b = bof(R->getReturnValue());
      if (!b.ok) {
        bad = true;
        continue;
      }
      if (!any) {
        acc = b;
        any = true;
      } else if (acc.arg != b.arg || acc.off != b.off || acc.var != b.var)
        bad = true;
    }
    if (!any || bad)
      acc = none;
    retStack.erase(G);
    retArgOf.emplace(G, acc);
    return retArgOf.find(G)->second;
  };

  std::function<const std::vector<Op> &(Function *)> script;
  script = [&](Function *F) -> const std::vector<Op> & {
    static const std::vector<Op> kEmpty;
    auto it = scriptOf.find(F);
    if (it != scriptOf.end())
      return it->second;
    if (!F || F->isDeclaration())
      return kEmpty;
    std::map<const AllocaInst *, int> spillArg;
    for (Instruction &I : instructions(*F)) {
      auto *S = dyn_cast<StoreInst>(&I);
      if (!S)
        continue;
      auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts());
      auto *A = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
      if (!Al || !A || A->getParent() != F || spillArg.count(Al))
        continue;
      spillArg[Al] = (int)A->getArgNo();
    }
    // Unwrap casts and a call that returns one of its arguments unchanged.
    // Following such passthrough calls is how a pointer threaded through
    // std::move, std::get, and the unique_ptr accessors keeps its base.
    std::function<Value *(Value *)> thru = [&](Value *V) -> Value * {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(V)) {
          Function *D = nullptr;
          if (Function *Cal = CB->getCalledFunction())
            D = define(Cal->getName());
          if (!D || D->isDeclaration())
            break;
          Base rb = retArg(D);
          if (!rb.ok || rb.off != 0 || rb.var || rb.arg < 0 || rb.arg >= (int)CB->arg_size())
            break;
          V = CB->getArgOperand(rb.arg);
          continue;
        }
        break;
      }
      return V;
    };
    std::function<Base(Value *)> asBase = [&](Value *V) -> Base {
      Base no;
      if (!V)
        return no;
      V = thru(V);
      if (auto *A = dyn_cast<Argument>(V)) {
        if (A->getParent() != F)
          return no;
        Base b;
        b.ok = true;
        b.arg = (int)A->getArgNo();
        return b;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        if (isAlloc(*CB)) {
          Base b;
          b.ok = true;
          b.alloc = CB;
          return b;
        }
        Function *D = nullptr;
        if (Function *Cal = CB->getCalledFunction())
          D = define(Cal->getName());
        if (!D || D->isDeclaration())
          return no;
        Base rb = retArg(D);
        if (!rb.ok || rb.arg < 0 || rb.arg >= (int)CB->arg_size())
          return no;
        Base b = asBase(CB->getArgOperand(rb.arg));
        if (!b.ok)
          return no;
        b.off += rb.off;
        b.var = b.var || rb.var;
        return b;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        Value *P = thru(L->getPointerOperand());
        if (auto *Al = dyn_cast<AllocaInst>(P->stripPointerCasts())) {
          auto s = spillArg.find(Al);
          if (s != spillArg.end()) {
            Base b;
            b.ok = true;
            b.arg = s->second;
            return b;
          }
          return no;
        }
        Base b = asBase(P);
        if (!b.ok)
          return no;
        b.cont = true;
        return b;
      }
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        Base b = asBase(G->getPointerOperand());
        if (!b.ok)
          return no;
        if (!G->hasAllConstantIndices()) {
          b.var = true;
          return b;
        }
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return no;
        b.off += off.getSExtValue();
        return b;
      }
      return no;
    };
    std::map<const AllocaInst *, Value *> held;
    for (Instruction &I : instructions(*F)) {
      auto *S = dyn_cast<StoreInst>(&I);
      if (!S)
        continue;
      if (auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
        held[Al] = S->getValueOperand();
    }
    auto peel = [&](Value *V) -> Value * {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
            auto h = held.find(Al);
            if (h == held.end())
              break;
            V = h->second;
            continue;
          }
        }
        break;
      }
      return V;
    };
    auto fromCall = [&](Value *V) -> Base {
      Base no;
      auto *CB = dyn_cast<CallBase>(V);
      if (!CB)
        return no;
      Function *D = nullptr;
      if (Function *Cal = CB->getCalledFunction())
        D = define(Cal->getName());
      if (!D || D->isDeclaration())
        return no;
      Base rb = retArg(D);
      if (!rb.ok || rb.arg < 0 || rb.arg >= (int)CB->arg_size())
        return no;
      Base act = asBase(CB->getArgOperand(rb.arg));
      if (!act.ok)
        return no;
      act.off += rb.off;
      act.var = act.var || rb.var;
      return act;
    };
    std::vector<Op> out;
    for (Instruction &I : instructions(*F)) {
      if (auto *L = dyn_cast<LoadInst>(&I)) {
        Base b = asBase(L->getPointerOperand());
        if (b.ok) {
          Op op;
          op.read = true;
          op.rd = b;
          out.push_back(op);
        }
      }
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        if (isa<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
          continue;
        Value *Ptr = peel(S->getPointerOperand());
        Base dst = asBase(Ptr);
        if (!dst.ok)
          dst = fromCall(Ptr);
        if (!dst.ok || dst.cont)
          continue;
        Op op;
        op.store = true;
        op.e.dstArg = dst.arg;
        op.e.dstOff = dst.off;
        op.e.dstVar = dst.var;
        Value *Val = peel(S->getValueOperand());
        Base src = asBase(Val);
        if (src.ok) {
          op.e.srcArg = src.arg;
          op.e.srcOff = src.off;
          op.e.srcCont = src.cont;
          op.e.srcVar = src.var;
          op.e.srcAlloc = src.alloc;
        } else if (auto *CB = dyn_cast<CallBase>(Val)) {
          op.e.from = CB;
          for (Value *A : CB->args())
            op.e.fromArgs.push_back(asBase(A));
        } else
          continue;
        out.push_back(op);
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || CB->isInlineAsm())
        continue;
      if (Function *Cal = CB->getCalledFunction())
        if (Cal->isIntrinsic() || Cal->getName().starts_with("llvm."))
          continue;
      Op op;
      op.call = true;
      if (Function *Cal = CB->getCalledFunction()) {
        if (Function *D = define(Cal->getName()))
          if (!D->isDeclaration())
            op.bodies.push_back(D);
      } else {
        for (Function *T : targetsOf(CB))
          if (T && !T->isDeclaration())
            op.bodies.push_back(T);
      }
      for (Value *A : CB->args())
        op.args.push_back(asBase(A));
      bool touched = !op.bodies.empty();
      if (!touched)
        for (const Base &a : op.args)
          if (a.ok)
            touched = true;
      if (touched)
        out.push_back(op);
    }
    return scriptOf.emplace(F, std::move(out)).first->second;
  };

  std::function<void(Function *, const std::vector<Ov> &, CellMem &)> applyEff;
  auto placeOf = [&](const Base &b, const std::vector<Ov> &formals, const CellMem &cur) -> Ov {
    Ov none;
    if (!b.ok)
      return none;
    if (b.alloc) {
      Ov a;
      a.k = Ov::Addr;
      a.p.base = Place::Obj;
      a.p.obj = b.alloc;
      return a;
    }
    if (b.arg < 0 || b.arg >= (int)formals.size())
      return none;
    Ov o = formals[b.arg];
    if (o.k != Ov::Addr)
      return none;
    if (b.off != 0)
      o.p.suf.push_back(Step{"", b.off, false});
    if (b.var)
      o.p.suf.push_back(Step{"v", 0, false});
    o.p = normPlace(o.p);
    if (b.cont) {
      Fact f = lookup(cur, o.p);
      if (f.vals.size() == 1 && !f.incoming)
        return f.vals[0];
      if (o.p.base == Place::Entry || o.p.base == Place::Obj) {
        Ov c;
        c.k = Ov::Cont;
        c.p = o.p;
        return c;
      }
      return none;
    }
    return o;
  };
  auto ctxKey = [](const Function *F, const std::vector<Ov> &fs) {
    std::string s;
    raw_string_ostream os(s);
    os << (const void *)F;
    for (const Ov &o : fs) {
      os << '|' << (int)o.k << ',' << (int)o.p.base << ',' << o.p.arg << ','
         << (const void *)o.p.obj << ',' << (const void *)o.p.slot << ','
         << (const void *)o.p.gv << ',' << (const void *)o.call;
      for (const Step &st : o.p.suf)
        os << ';' << st.type << ':' << st.off << ':' << (int)st.deref;
    }
    os.flush();
    return s;
  };
  applyEff = [&](Function *F, const std::vector<Ov> &formals, CellMem &cur) {
    if (!F || F->isDeclaration())
      return;
    bool root = applyStack.empty();
    auto done = [&] {
      applyStack.erase(F);
      if (root)
        applyMemo.clear();
    };
    if (!applyStack.insert(F).second)
      return;
    bool track = false;
    for (const Ov &o : formals)
      if (o.k == Ov::Addr && (o.p.base == Place::Entry || o.p.base == Place::Obj))
        track = true;
    if (!track) {
      done();
      return;
    }
    if (!applyMemo.insert(ctxKey(F, formals)).second) {
      done();
      return;
    }
    const std::vector<Op> &ops = script(F);
    for (const Op &op : ops) {
      if (op.read) {
        Ov p = placeOf(op.rd, formals, cur);
        if ((p.k == Ov::Addr || p.k == Ov::Cont) && p.p.base == Place::Entry)
          pendingReads.push_back(p.p);
      }
      if (op.store) {
        const Eff &e = op.e;
        Ov dest = placeOf(Base{e.dstArg, e.dstOff, true, false, e.dstVar}, formals, cur);
        if (dest.k != Ov::Addr)
          continue;
        if (dest.p.base != Place::Entry && dest.p.base != Place::Obj)
          continue;
        Ov val;
        if (e.allocI || e.srcAlloc) {
          val.k = Ov::Addr;
          val.p.base = Place::Obj;
          val.p.obj = e.allocI ? e.allocI : e.srcAlloc;
        } else if (e.from) {
          val.k = Ov::From;
          val.call = e.from;
          std::vector<Ov> fa;
          fa.reserve(e.fromArgs.size());
          for (const Base &a : e.fromArgs)
            fa.push_back(placeOf(a, formals, cur));
          argSaved[e.from] = std::move(fa);
        } else if (e.srcArg >= 0) {
          val = placeOf(Base{e.srcArg, e.srcOff, true, e.srcCont, e.srcVar}, formals, cur);
          if (e.srcCont && val.k == Ov::Addr)
            val.k = Ov::Cont;
        }
        if (val.k == Ov::Open)
          continue;
        cur[dest.p] = kill(val, false);
      }
      if (op.call && op.bodies.empty()) {
        for (const Base &a : op.args) {
          Ov p = placeOf(a, formals, cur);
          if ((p.k == Ov::Addr || p.k == Ov::Cont) && p.p.base == Place::Entry)
            pendingReads.push_back(p.p);
        }
      }
      if (op.call && !op.bodies.empty()) {
        std::vector<Ov> inner(op.args.size());
        bool pass = false;
        for (size_t i = 0; i < op.args.size(); ++i) {
          inner[i] = placeOf(op.args[i], formals, cur);
          if (inner[i].k == Ov::Addr && (inner[i].p.base == Place::Entry || inner[i].p.base == Place::Obj))
            pass = true;
          if (inner[i].k == Ov::Cont && (inner[i].p.base == Place::Entry || inner[i].p.base == Place::Obj))
            pass = true;
        }
        if (!pass)
          continue;
        for (Function *B : op.bodies)
          applyEff(B, inner, cur);
      }
    }
    done();
  };

  std::function<void(Function *, const Result &)> explainResult;

  auto applyCall = [&](CallBase *CB, Function *Fn, const std::vector<Ov> &args, CellMem &cur, Instruction *goal, bool replay) {
    std::vector<Ov> actual;
    actual.reserve(CB->arg_size());
    for (Value *A : CB->args())
      actual.push_back(eval(A, Fn, args, cur));
    argSaved[CB] = actual;
    Function *Body = resolveBody(CB, Fn);
    bool defined = Body && !Body->isDeclaration();
    bool edge = defined && goal && CB == goal;
    // Only the call that reaches the sink is entered. Any other call writes
    // the objects it receives; its arguments are the sources of those bytes.
    if (edge) {
      if (replay) {
        auto it = callDone.find(CB);
        if (it != callDone.end()) {
          retOf[CB] = it->second.ret;
          explainResult(Body, it->second);
        }
        return;
      }
      Instruction *ng = sinkIn(Body);
      if (!ng)
        ng = goalCall(Body);
      std::vector<Ov> formals(Body->arg_size());
      for (unsigned i = 0; i < formals.size() && i < actual.size(); ++i)
        formals[i] = actual[i];
      Result r = analyze(Body, formals, ng, cur);
      retOf[CB] = r.ret;
      callDone[CB] = std::move(r);
      return;
    }
    if (defined || !CB->getCalledFunction()) {
      std::vector<Function *> bodies;
      if (defined)
        bodies.push_back(Body);
      else {
        for (Function *T : targetsOf(CB))
          if (T && !T->isDeclaration())
            bodies.push_back(T);
      }
      std::vector<Ov> formals(CB->arg_size());
      for (unsigned i = 0; i < formals.size() && i < actual.size(); ++i)
        formals[i] = actual[i];
      for (Function *B : bodies)
        applyEff(B, formals, cur);
      for (const Place &p : pendingReads) {
        Fact f = lookup(cur, p);
        if (f.vals.size() == 1 && !f.incoming) {
          const Ov &s = f.vals[0];
          if ((s.k == Ov::Addr || s.k == Ov::Cont) && s.p.base == Place::Entry)
            recorded.insert(normPlace(s.p));
          continue;
        }
        if (!f.vals.empty() && !f.incoming)
          continue;
        if (p.base == Place::Entry)
          recorded.insert(normPlace(p));
      }
      pendingReads.clear();
    }
    if (!defined) {
      for (const Ov &a : actual) {
        if (a.k != Ov::Addr && a.k != Ov::Cont)
          continue;
        if (a.p.base != Place::Entry)
          continue;
        Fact f = lookup(cur, a.p);
        if (f.vals.size() == 1 && !f.incoming) {
          const Ov &s = f.vals[0];
          if ((s.k == Ov::Addr || s.k == Ov::Cont) && s.p.base == Place::Entry)
            recorded.insert(normPlace(s.p));
          continue;
        }
        if (!f.vals.empty() && !f.incoming)
          continue;
        recorded.insert(normPlace(a.p));
      }
      if (isAlloc(*CB)) {
        Ov produced;
        produced.k = Ov::Addr;
        produced.p.base = Place::Obj;
        produced.p.obj = CB;
        retOf[CB] = produced;
        return;
      }
      auto writeDest = [&](unsigned dst, unsigned src, bool span) {
        if (dst >= actual.size() || src >= actual.size())
          return;
        const Ov &d = actual[dst];
        const Ov &s = actual[src];
        if (d.k != Ov::Addr)
          return;
        if (s.k == Ov::Addr) {
          Ov c;
          c.k = Ov::Cont;
          c.p = s.p;
          cur[d.p] = kill(c, span);
        } else
          cur[d.p] = kill(s, span);
      };
      if (isCopy(*CB)) {
        writeDest(0, 1, true);
        return;
      }
      Read rd = asRead(*CB);
      if (rd.ok) {
        if (rd.buf < actual.size() && actual[rd.buf].k == Ov::Addr) {
          Ov produced;
          produced.k = Ov::From;
          produced.call = CB;
          cur[actual[rd.buf].p] = kill(produced, true);
        }
        Ov produced;
        produced.k = Ov::From;
        produced.call = CB;
        retOf[CB] = produced;
        return;
      }
    }
    Ov produced;
    produced.k = Ov::From;
    produced.call = CB;
    retOf[CB] = produced;
  };

  analyze = [&](Function *Fn, const std::vector<Ov> &args, Instruction *goal, const CellMem &entry) -> Result {
    Result none;
    none.entry = entry;
    none.goal = goal;
    none.args = args;
    none.fn = Fn;
    none.at = entry;
    if (!Fn || Fn->isDeclaration())
      return none;
    uint64_t key = mix(hashCellMem(entry), (uint64_t)(uintptr_t)Fn);
    key = mix(key, (uint64_t)(uintptr_t)goal);
    for (const Ov &a : args)
      key = mix(key, hashOv(a));
    if (auto it = cache.find(key); it != cache.end()) {
      for (const Cached &c : it->second) {
        if (c.args.size() == args.size() && c.entry == entry &&
            std::equal(c.args.begin(), c.args.end(), args.begin(), sameOv))
          return c.result;
      }
    }
    if (!stack.insert(Fn).second)
      return none;
    auto held = std::make_unique<std::map<BasicBlock *, CellMem>>();
    auto &outs = *held;
    std::map<BasicBlock *, std::unordered_set<uint64_t>> seenOut;
    BasicBlock *goalBB = goal ? goal->getParent() : nullptr;
    std::deque<BasicBlock *> wl;
    std::unordered_set<BasicBlock *> queued;
    auto enqueue = [&](BasicBlock *B) {
      if (goalBB && !reaches(B, goalBB))
        return;
      if (queued.insert(B).second)
        wl.push_back(B);
    };
    enqueue(&Fn->getEntryBlock());
    while (!wl.empty()) {
      BasicBlock *BB = wl.front();
      wl.pop_front();
      queued.erase(BB);
      CellMem cur = incoming(BB, goalBB, outs, entry);
      for (Instruction &I : *BB) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          Ov ptr = eval(S->getPointerOperand(), Fn, args, cur);
          if (ptr.k == Ov::Addr)
            cur[ptr.p] = kill(eval(S->getValueOperand(), Fn, args, cur), false);
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(&I))
          applyCall(CB, Fn, args, cur, goal, false);
      }
      if (outs.count(BB) && outs[BB] == cur)
        continue;
      uint64_t h = hashCellMem(cur);
      auto &seen = seenOut[BB];
      if (!seen.insert(h).second)
        continue;
      outs[BB] = std::move(cur);
      for (BasicBlock *S : successors(BB))
        enqueue(S);
    }
    Result r;
    r.entry = entry;
    r.goal = goal;
    r.args = args;
    r.fn = Fn;
    r.out = outs;
    r.at = entry;
    if (!goal) {
      bool any = false;
      bool bad = false;
      for (BasicBlock &BB : *Fn) {
        auto *Ret = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!Ret)
          continue;
        auto it = outs.find(&BB);
        if (it == outs.end())
          continue;
        if (!any) {
          r.at = it->second;
          any = true;
        } else
          r.at = mergeCellMem(r.at, it->second);
        if (!Ret->getReturnValue())
          continue;
        Ov o = eval(Ret->getReturnValue(), Fn, args, it->second);
        if (o.k == Ov::Open)
          continue;
        if (r.ret.k == Ov::Open)
          r.ret = o;
        else if (!sameOv(r.ret, o))
          bad = true;
      }
      if (bad)
        r.ret = Ov{};
    }
    stack.erase(Fn);
    cache[key].push_back(Cached{args, entry, r});
    return r;
  };

  explainResult = [&](Function *Fn, const Result &r) {
    if (!Fn || !explainStack.insert(Fn).second)
      return;
    BasicBlock *goalBB = r.goal ? r.goal->getParent() : nullptr;
    for (BasicBlock &BB : *Fn) {
      if (goalBB && !reaches(&BB, goalBB))
        continue;
      if (!r.out.count(&BB) && &BB != &Fn->getEntryBlock())
        continue;
      CellMem cur = incoming(&BB, goalBB, r.out, r.entry);
      for (Instruction &I : BB) {
        if (!I.isDebugOrPseudoInst()) {
          if (access.count(&I) && (isa<LoadInst>(I) || isa<StoreInst>(I) || isa<CallBase>(I))) {
            for (Value *Op : I.operands())
              explainValue(Op, Fn, r.args, cur);
          } else if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
            explainValue(Cmp->getOperand(0), Fn, r.args, cur);
            explainValue(Cmp->getOperand(1), Fn, r.args, cur);
          }
        }
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          Ov ptr = eval(S->getPointerOperand(), Fn, r.args, cur);
          if (ptr.k == Ov::Addr)
            cur[ptr.p] = kill(eval(S->getValueOperand(), Fn, r.args, cur), false);
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(&I))
          applyCall(CB, Fn, r.args, cur, r.goal, true);
      }
    }
    explainStack.erase(Fn);
  };

  std::vector<Ov> entryArgs(seq[0]->arg_size());
  for (unsigned i = 0; i < seq[0]->arg_size(); ++i) {
    Ov o;
    o.p.base = Place::Entry;
    o.p.arg = (int)i;
    o.k = seq[0]->getArg(i)->getType()->isPointerTy() ? Ov::Addr : Ov::Cont;
    entryArgs[i] = o;
  }
  Instruction *top = sinkIn(seq[0]);
  if (!top)
    top = goalCall(seq[0]);
  Result root = analyze(seq[0], entryArgs, top, CellMem{});
  explainResult(seq[0], root);

  if (recorded.empty())
    out << "input none\n";
  for (const Place &p : recorded) {
    out << "input arg " << p.arg;
    for (const Step &s : p.suf)
      out << " " << s.type << "+" << s.off << (s.deref ? "*" : "");
    out << "\n";
  }
}
