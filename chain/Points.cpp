#include "Points.hpp"

#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"

#include <algorithm>

namespace chain {

Points::Points(const llvm::Module &M0, const llvm::Module &U0, Hooks h)
    : M(M0), U(U0), hooks(std::move(h)), DL(M0.getDataLayout()) {
  ctxs.push_back(Ctx{});
  outsideObj = newObj(Kind::Outside, nullptr);
  harnessObj = newObj(Kind::Harness, nullptr);
  const llvm::Module *mods[2] = {&M, &U};
  for (const llvm::Module *Mod : mods) {
    for (const llvm::Function &F : *Mod) {
      if (F.isDeclaration())
        continue;
      for (const llvm::Instruction &I : llvm::instructions(F)) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
        if (R) {
          returnsOf[&F].push_back(R);
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        if (const llvm::Function *D = C->getCalledFunction()) {
          const llvm::Function *B = bodyOf(D);
          if (B && !B->isDeclaration())
            directCallers[B].push_back(C);
        } else {
          indirectCalls.push_back(C);
        }
      }
    }
  }
}

void Points::saturate() {}

const llvm::Function *Points::bodyOf(const llvm::Function *F) const {
  if (!F)
    return nullptr;
  if (!F->isDeclaration())
    return F;
  if (hooks.body)
    if (const llvm::Function *B = hooks.body(F))
      return B;
  return F;
}

const llvm::DataLayout &Points::dlOf(const llvm::Value *v) const {
  if (const auto *I = llvm::dyn_cast<llvm::Instruction>(v))
    return I->getModule()->getDataLayout();
  if (const auto *A = llvm::dyn_cast<llvm::Argument>(v))
    return A->getParent()->getParent()->getDataLayout();
  if (const auto *G = llvm::dyn_cast<llvm::GlobalValue>(v))
    return G->getParent()->getDataLayout();
  return DL;
}

void Points::ensureObjSlots(unsigned o) {
  while (writesOf.size() <= o) {
    writesOf.emplace_back();
    ptrLoadsOf.emplace_back();
    escapesOf.emplace_back();
  }
}

unsigned Points::newObj(Kind k, const llvm::Value *site) {
  Obj o;
  o.kind = k;
  o.site = site;
  objs.push_back(o);
  ensureObjSlots(static_cast<unsigned>(objs.size() - 1));
  return static_cast<unsigned>(objs.size() - 1);
}

unsigned Points::objectFor(Kind k, const llvm::Value *site) {
  auto key = std::make_pair(static_cast<const void *>(site), static_cast<unsigned>(k));
  auto it = objOf.find(key);
  if (it != objOf.end())
    return it->second;
  unsigned o = newObj(k, site);
  objOf.emplace(key, o);
  return o;
}

unsigned Points::location(unsigned o, int64_t off) {
  auto key = std::make_pair(o, off);
  auto it = locOf.find(key);
  if (it != locOf.end())
    return it->second;
  unsigned id = static_cast<unsigned>(locs.size());
  locs.push_back(Loc{o, off});
  locOf.emplace(key, id);
  return id;
}

int64_t Points::addOff(int64_t k, int64_t d) {
  if (k == Any || d == Any)
    return Any;
  const __int128 s = static_cast<__int128>(k) + d;
  if (s > INT64_MAX || s < INT64_MIN)
    return Any;
  return static_cast<int64_t>(s);
}

int64_t Points::gepOff(const llvm::GEPOperator *G) const {
  if (!G)
    return Any;
  llvm::APInt off(dlOf(G).getIndexSizeInBits(G->getPointerAddressSpace()), 0);
  if (!G->accumulateConstantOffset(dlOf(G), off))
    return Any;
  if (off.getSignificantBits() > 63 && !off.isNegative())
    return Any;
  return off.getSExtValue();
}

std::vector<unsigned> Points::snapshot(const llvm::Value *v) const {
  std::vector<unsigned> out;
  auto it = pt.find(v);
  if (it == pt.end())
    return out;
  for (unsigned id : it->second)
    out.push_back(id);
  return out;
}

void Points::insertPt(const llvm::Value *v, unsigned loc) {
  if (!v)
    return;
  const Loc L = locs[loc];
  OffState &st = offState[v][L.obj];
  if (L.off == Any) {
    st.any = true;
  } else if (st.any) {
    return;
  } else if (!st.have) {
    st.have = true;
    st.one = L.off;
  } else if (st.one != L.off) {
    st.any = true;
    const unsigned any = location(L.obj, Any);
    insertPt(v, any);
    return;
  }
  auto &s = pt[v];
  if (s.test(loc))
    return;
  s.set(loc);
  changed = true;
  propQ.push_back(Prop{v, loc});
  if (L.obj == harnessObj)
    fillHarness(L.off);
  std::vector<int64_t> cells;
  if (auto hs = harnessStore.find(v); hs != harnessStore.end())
    cells = hs->second;
  for (int64_t cell : cells)
    memAdd(harnessObj, cell, loc);
}

void Points::demand(const llvm::Value *v) {
  if (!v || llvm::isa<llvm::ConstantData>(v))
    return;
  if (!demanded.insert(v).second)
    return;
  demandQ.push_back(v);
}

void Points::drain() {
  if (draining)
    return;
  draining = true;
  while (!demandQ.empty() || !propQ.empty()) {
    if (!demandQ.empty()) {
      const llvm::Value *v = demandQ.back();
      demandQ.pop_back();
      install(v);
      continue;
    }
    Prop p = propQ.back();
    propQ.pop_back();
    propagate(p.v, p.loc);
  }
  draining = false;
  if (changed) {
    ++epoch;
    changed = false;
  }
}

void Points::recordWrite(unsigned obj, int64_t off, int64_t len, const llvm::Instruction *I) {
  if (!I)
    return;
  ensureObjSlots(obj);
  if (!writeSeen.insert(WKey{obj, off, len, I}).second)
    return;
  writesOf[obj].push_back(Write{I, off, len, 0});
  changed = true;
}

void Points::noteEscape(unsigned obj, const llvm::CallBase *C) {
  if (!C)
    return;
  ensureObjSlots(obj);
  if (!escapeSeen.insert({C, reinterpret_cast<const void *>(static_cast<uintptr_t>(obj))}).second)
    return;
  escapesOf[obj].push_back(C);
  changed = true;
}

void Points::notePtrLoad(unsigned obj, int64_t off, const llvm::LoadInst *L) {
  if (!L)
    return;
  ensureObjSlots(obj);
  if (!ptrLoadSeen.insert({L, reinterpret_cast<const void *>(static_cast<uintptr_t>(obj) ^ static_cast<uintptr_t>(off))}).second)
    return;
  ptrLoadsOf[obj].push_back(PtrLoad{L, off});
  changed = true;
}

void Points::memAdd(unsigned obj, int64_t off, unsigned loc) {
  auto &cell = mem[obj][off];
  if (cell.test(loc))
    return;
  cell.set(loc);
  changed = true;
  auto rit = readers.find({obj, off});
  if (rit != readers.end())
    for (const llvm::LoadInst *L : rit->second)
      insertPt(L, loc);
  auto ait = anyReaders.find(obj);
  if (ait != anyReaders.end())
    for (const llvm::LoadInst *L : ait->second)
      insertPt(L, loc);
}

void Points::readMem(const llvm::LoadInst *L, Loc addr) {
  if (addr.obj == harnessObj)
    fillHarness(addr.off);
  auto take = [&](int64_t off) {
    auto oit = mem.find(addr.obj);
    if (oit == mem.end())
      return;
    auto cit = oit->second.find(off);
    if (cit == oit->second.end())
      return;
    const std::vector<unsigned> ids = [&] {
      std::vector<unsigned> v;
      for (unsigned id : cit->second)
        v.push_back(id);
      return v;
    }();
    for (unsigned id : ids)
      insertPt(L, id);
  };
  if (addr.off == Any) {
    if (readerAnySeen.insert({L, addr.obj}).second)
      anyReaders[addr.obj].push_back(L);
    auto oit = mem.find(addr.obj);
    if (oit != mem.end()) {
      std::vector<int64_t> keys;
      for (const auto &kv : oit->second)
        keys.push_back(kv.first);
      for (int64_t k : keys)
        take(k);
    }
    return;
  }
  if (readerSeen.insert({L, addr.obj, addr.off}).second)
    readers[{addr.obj, addr.off}].push_back(L);
  take(addr.off);
}

void Points::fillHarness(int64_t target) {
  if (!hooks.harness)
    return;
  if (!filledHarness.insert(target).second)
    return;
  std::vector<const llvm::Argument *> args;
  const llvm::Module *mods[2] = {&M, &U};
  for (const llvm::Module *Mod : mods)
    for (const llvm::Function &F : *Mod) {
      if (F.isDeclaration() || !hooks.harness(&F))
        continue;
      for (const llvm::Argument &A : F.args())
        if (pointerLike(A.getType()))
          args.push_back(&A);
    }
  // One value reached at two concrete offsets does not name both cells.
  // The value is Any, matching the points-to join. A loop that adds a
  // constant each iteration is finite for that reason.
  struct WOff {
    bool any = false;
    bool have = false;
    int64_t one = 0;
  };
  std::unordered_map<const llvm::Value *, WOff> walk;
  std::vector<std::pair<const llvm::Value *, int64_t>> work;
  auto enqueue = [&](const llvm::Value *v, int64_t off) {
    if (!v)
      return;
    WOff &st = walk[v];
    if (st.any)
      return;
    if (off == Any) {
      st.any = true;
      work.emplace_back(v, Any);
      return;
    }
    if (!st.have) {
      st.have = true;
      st.one = off;
      work.emplace_back(v, off);
      return;
    }
    if (st.one == off)
      return;
    st.any = true;
    work.emplace_back(v, Any);
  };
  for (const llvm::Argument *A : args)
    enqueue(A, 0);
  while (!work.empty()) {
    const llvm::Value *v = work.back().first;
    const int64_t off = work.back().second;
    work.pop_back();
    const bool hit = target == Any || off == Any || off == target;
    if (hit) {
      const int64_t cell = off;
      for (const llvm::User *U : v->users()) {
        const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
        if (St && St->getPointerOperand() == v) {
          const int64_t len =
              static_cast<int64_t>(dlOf(St).getTypeStoreSize(St->getValueOperand()->getType()));
          recordWrite(harnessObj, cell, len, St);
          if (pointerLike(St->getValueOperand()->getType())) {
            harnessStore[St->getValueOperand()].push_back(cell);
            demand(St->getValueOperand());
            for (unsigned sl : snapshot(St->getValueOperand()))
              memAdd(harnessObj, cell, sl);
          }
          continue;
        }
        const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
        if (Ld && Ld->getPointerOperand() == v && pointerLike(Ld->getType()))
          readMem(Ld, Loc{harnessObj, cell});
      }
    }
    for (const llvm::User *U : v->users()) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
        if (pointerLike(C->getType()))
          enqueue(C, off);
        continue;
      }
      if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
        if (pointerLike(Fz->getType()))
          enqueue(Fz, off);
        continue;
      }
      if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
        if (pointerLike(PN->getType()))
          enqueue(PN, off);
        continue;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
        if (pointerLike(Sel->getType()))
          enqueue(Sel, off);
        continue;
      }
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(U)) {
        if (CE->isCast() && pointerLike(CE->getType()))
          enqueue(CE, off);
        else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(CE))
          if (G->getPointerOperand() == v)
            enqueue(G, addOff(off, gepOff(G)));
        continue;
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
        if (G->getPointerOperand() == v)
          enqueue(G, addOff(off, gepOff(G)));
        continue;
      }
      const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
      if (!St || St->getValueOperand() != v)
        continue;
      const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(St->getPointerOperand());
      if (!AI)
        continue;
      for (const llvm::User *LU : AI->users()) {
        const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(LU);
        if (Ld && Ld->getPointerOperand() == AI)
          enqueue(Ld, off);
      }
    }
  }
}

void Points::seedFunc(const llvm::Function *F) {
  const llvm::Function *B = bodyOf(F);
  if (!B)
    B = F;
  if (!seededFunc.insert(B).second)
    return;
  insertPt(B, location(objectFor(Kind::Func, B), 0));
}

void Points::seedGlobal(const llvm::GlobalVariable *G) {
  if (!G || !seededGlobal.insert(G).second)
    return;
  unsigned o = objectFor(Kind::Global, G);
  insertPt(G, location(o, 0));
  if (G->hasInitializer())
    fillConst(o, 0, G->getInitializer());
}

void Points::fillConst(unsigned obj, int64_t base, const llvm::Constant *C) {
  if (!C || llvm::isa<llvm::ConstantAggregateZero>(C) || llvm::isa<llvm::ConstantPointerNull>(C) ||
      llvm::isa<llvm::UndefValue>(C))
    return;
  if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(C)) {
    seedGlobal(G);
    memAdd(obj, base, location(objectFor(Kind::Global, G), 0));
    return;
  }
  if (const auto *F = llvm::dyn_cast<llvm::Function>(C)) {
    seedFunc(F);
    const llvm::Function *B = bodyOf(F);
    memAdd(obj, base, location(objectFor(Kind::Func, B ? B : F), 0));
    return;
  }
  if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(C)) {
    if (CE->isCast()) {
      if (const auto *K = llvm::dyn_cast<llvm::Constant>(CE->getOperand(0)))
        fillConst(obj, base, K);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(CE)) {
      const int64_t d = gepOff(G);
      if (const auto *K = llvm::dyn_cast<llvm::Constant>(G->getPointerOperand())) {
        if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(K->stripPointerCasts())) {
          seedGlobal(GV);
          memAdd(obj, base, location(objectFor(Kind::Global, GV), d == Any ? Any : addOff(0, d)));
        } else if (const auto *F = llvm::dyn_cast<llvm::Function>(K->stripPointerCasts())) {
          seedFunc(F);
          const llvm::Function *B = bodyOf(F);
          memAdd(obj, base, location(objectFor(Kind::Func, B ? B : F), 0));
        } else {
          fillConst(obj, addOff(base, d), K);
        }
      }
      return;
    }
  }
  if (const auto *S = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
    const llvm::StructLayout *SL = dlOf(S).getStructLayout(S->getType());
    for (unsigned i = 0; i < S->getNumOperands(); ++i)
      if (const auto *K = llvm::dyn_cast<llvm::Constant>(S->getOperand(i)))
        fillConst(obj, addOff(base, static_cast<int64_t>(SL->getElementOffset(i))), K);
    return;
  }
  if (const auto *A = llvm::dyn_cast<llvm::ConstantArray>(C)) {
    llvm::Type *E = A->getType()->getElementType();
    const uint64_t es = E->isSized() ? dlOf(A).getTypeAllocSize(E).getFixedValue() : 0;
    for (unsigned i = 0; i < A->getNumOperands(); ++i)
      if (const auto *K = llvm::dyn_cast<llvm::Constant>(A->getOperand(i)))
        fillConst(obj, addOff(base, static_cast<int64_t>(es * i)), K);
  }
}

void Points::bind(const llvm::CallBase *C, const llvm::Function *F0) {
  const llvm::Function *F = bodyOf(F0);
  if (!C || !F)
    return;
  if (!bound.insert({C, F}).second)
    return;
  if (F->isDeclaration()) {
    for (const llvm::Value *a : C->args())
      if (pointerLike(a->getType()))
        for (unsigned loc : snapshot(a))
          noteEscape(locs[loc].obj, C);
    if (pointerLike(C->getType()) && demanded.count(C))
      insertPt(C, location(objectFor(Kind::Outside, C), 0));
    return;
  }
  indirectBound[F].push_back(C);
  unsigned i = 0;
  for (const llvm::Argument &A : F->args()) {
    if (i >= C->arg_size())
      break;
    const llvm::Value *act = C->getArgOperand(i);
    if (pointerLike(A.getType()) && pointerLike(act->getType())) {
      copyTo[act].push_back(&A);
      demand(act);
      for (unsigned loc : snapshot(act))
        insertPt(&A, loc);
    }
    ++i;
  }
  if (pointerLike(C->getType())) {
    auto rit = returnsOf.find(F);
    if (rit != returnsOf.end()) {
      for (const llvm::ReturnInst *R : rit->second) {
        const llvm::Value *rv = R->getReturnValue();
        if (!rv || !pointerLike(rv->getType()))
          continue;
        copyTo[rv].push_back(C);
        for (unsigned loc : snapshot(rv))
          insertPt(C, loc);
        if (demanded.count(C))
          demand(rv);
      }
    }
  }
}

void Points::scanIndirect(const llvm::Function *F) {
  const llvm::Function *B = bodyOf(F);
  if (!B || B->isDeclaration())
    return;
  if (!scannedIndirect.insert(B).second)
    return;
  if (!B->hasAddressTaken())
    return;
  seedFunc(B);
}

int64_t Points::copyLen(const llvm::CallBase *C) const {
  if (C->arg_size() < 3)
    return -1;
  if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(C->getArgOperand(2))) {
    if (CI->getValue().getActiveBits() > 62)
      return -1;
    return static_cast<int64_t>(CI->getZExtValue());
  }
  return -1;
}

void Points::propagateUser(const llvm::Value *v, unsigned loc, const llvm::User *U) {
  const Loc L = locs[loc];
  if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(U)) {
    if (CE->isCast() && pointerLike(CE->getType())) {
      insertPt(CE, loc);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(CE)) {
      if (G->getPointerOperand() == v)
        insertPt(CE, location(L.obj, addOff(L.off, gepOff(G))));
    }
    return;
  }
  if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
    if (pointerLike(C->getType()))
      insertPt(C, loc);
    return;
  }
  if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
    if (pointerLike(Fz->getType()))
      insertPt(Fz, loc);
    return;
  }
  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
    if (G->getPointerOperand() == v)
      insertPt(G, location(L.obj, addOff(L.off, gepOff(G))));
    return;
  }
  if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
    if (pointerLike(PN->getType()))
      insertPt(PN, loc);
    return;
  }
  if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
    if (pointerLike(Sel->getType()))
      insertPt(Sel, loc);
    return;
  }
  if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
    if (R->getReturnValue() != v)
      return;
    const llvm::Function *F = R->getFunction();
    auto dit = directCallers.find(F);
    if (dit != directCallers.end())
      for (const llvm::CallBase *C : dit->second)
        if (pointerLike(C->getType()) && demanded.count(C))
          insertPt(C, loc);
    auto iit = indirectBound.find(F);
    if (iit != indirectBound.end())
      for (const llvm::CallBase *C : iit->second)
        if (pointerLike(C->getType()) && demanded.count(C))
          insertPt(C, loc);
    return;
  }
  if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(U)) {
    if (St->getPointerOperand() == v) {
      const int64_t len = static_cast<int64_t>(dlOf(St).getTypeStoreSize(St->getValueOperand()->getType()));
      recordWrite(L.obj, L.off, len, St);
      if (pointerLike(St->getValueOperand()->getType())) {
        // The stored pointer's cells are the contents of this address.
        // Demand it so a later growth of its points-to set is written
        // into mem; the value-side arm below does that write.
        demand(St->getValueOperand());
        for (unsigned sl : snapshot(St->getValueOperand()))
          memAdd(L.obj, L.off, sl);
      }
    } else if (St->getValueOperand() == v && pointerLike(v->getType())) {
      // pt(v) arrived. The address's cells are part of the same inclusion,
      // so solve the address and write v into every cell it points at.
      demand(St->getPointerOperand());
      for (unsigned pl : snapshot(St->getPointerOperand())) {
        const Loc a = locs[pl];
        memAdd(a.obj, a.off, loc);
      }
    }
    return;
  }
  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
    if (Ld->getPointerOperand() != v)
      return;
    if (pointerLike(Ld->getType())) {
      notePtrLoad(L.obj, L.off, Ld);
      readMem(Ld, L);
    }
    return;
  }
  const auto *C = llvm::dyn_cast<llvm::CallBase>(U);
  if (!C || C->isInlineAsm())
    return;
  const llvm::Value *dst = nullptr;
  const llvm::Value *src = nullptr;
  if (hooks.byteCopy && hooks.byteCopy(C, dst, src) && dst == v) {
    recordWrite(L.obj, L.off, copyLen(C), C);
    // Forward mem cells from the source to the destination so that a
    // memcpy of a pointer-bearing struct copies the pointer too.
    if (src && pointerLike(src->getType())) {
      demand(src);
      for (unsigned sl : snapshot(src)) {
        const Loc sL = locs[sl];
        auto oit = mem.find(sL.obj);
        if (oit == mem.end())
          continue;
        std::vector<std::pair<int64_t, std::vector<unsigned>>> snap;
        for (const auto &kv : oit->second) {
          std::vector<unsigned> ids;
          for (unsigned id : kv.second)
            ids.push_back(id);
          snap.emplace_back(kv.first, std::move(ids));
        }
        for (const auto &[off, ids] : snap)
          for (unsigned id : ids) {
            int64_t dstOff = (sL.off == Any || L.off == Any || off == Any)
                                 ? Any
                                 : L.off + (off - sL.off);
            memAdd(L.obj, dstOff, id);
          }
      }
    }
  }
  if (const auto *MS = llvm::dyn_cast<llvm::MemSetInst>(C)) {
    if (MS->getDest() == v) {
      int64_t len = -1;
      if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(MS->getLength()))
        if (CI->getValue().getActiveBits() <= 62)
          len = static_cast<int64_t>(CI->getZExtValue());
      recordWrite(L.obj, L.off, len, MS);
    }
  }
  if (C->getCalledOperand() == v) {
    if (objs[L.obj].kind == Kind::Func)
      if (const auto *F = llvm::dyn_cast<llvm::Function>(objs[L.obj].site))
        if (!C->getCalledFunction())
          bind(C, F);
  }
  unsigned i = 0;
  for (const llvm::Value *a : C->args()) {
    if (a == v) {
      if (const llvm::Function *D = C->getCalledFunction()) {
        const llvm::Function *B = bodyOf(D);
        if (B && !B->isDeclaration() && i < B->arg_size()) {
          const llvm::Argument *A = B->getArg(i);
          // The formal is solved when a query demands it. Pushing every
          // actual into every callee is the whole module.
          if (pointerLike(A->getType()) && demanded.count(A))
            insertPt(A, loc);
        } else {
          noteEscape(L.obj, C);
        }
      } else {
        bool hit = false;
        auto iit = indirectBound.end();
        for (const auto &kv : indirectBound) {
          if (std::find(kv.second.begin(), kv.second.end(), C) == kv.second.end())
            continue;
          hit = true;
          if (i < kv.first->arg_size()) {
            const llvm::Argument *A = kv.first->getArg(i);
            if (pointerLike(A->getType()) && demanded.count(A))
              insertPt(A, loc);
          }
        }
        (void)iit;
        if (!hit)
          noteEscape(L.obj, C);
      }
    }
    ++i;
  }
}

void Points::propagate(const llvm::Value *v, unsigned loc) {
  if (!v)
    return;
  if (!seenProp.insert({v, static_cast<unsigned>(loc)}).second)
    return;
  const bool harness = locs[loc].obj == harnessObj;
  const bool func = objs[locs[loc].obj].kind == Kind::Func;
  for (const llvm::User *U : v->users()) {
    // A demanded user is inside the query. Stores write cells. Loads of a
    // demanded address, or of the harness object, read the cell. A field
    // address is followed only when that gep itself was demanded. A call
    // receives the value only when its formal was demanded.
    if (demanded.count(U)) {
      propagateUser(v, loc, U);
      continue;
    }
    if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
      if (Ld->getPointerOperand() == v && (harness || demanded.count(v)))
        propagateUser(v, loc, U);
      continue;
    }
    if (llvm::isa<llvm::StoreInst>(U)) {
      propagateUser(v, loc, U);
      continue;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
      if (!C->isInlineAsm()) {
        const llvm::Value *dst = nullptr;
        const llvm::Value *src = nullptr;
        if (hooks.byteCopy && hooks.byteCopy(C, dst, src) && (dst == v || src == v)) {
          propagateUser(v, loc, U);
          continue;
        }
      }
    }
    if (!func)
      continue;
    if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::ConstantExpr>(U))
      propagateUser(v, loc, U);
    else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U))
      if (!C->isInlineAsm() && C->getCalledOperand() == v)
        propagateUser(v, loc, U);
  }
  auto cit = copyTo.find(v);
  if (cit != copyTo.end())
    for (const llvm::Value *dst : cit->second)
      insertPt(dst, loc);
}

void Points::install(const llvm::Value *v) {
  if (const auto *A = llvm::dyn_cast<llvm::Argument>(v)) {
    const llvm::Function *B = bodyOf(A->getParent());
    bool any = false;
    if (B) {
      auto dit = directCallers.find(B);
      if (dit != directCallers.end()) {
        for (const llvm::CallBase *C : dit->second) {
          if (A->getArgNo() >= C->arg_size())
            continue;
          const llvm::Value *act = C->getArgOperand(A->getArgNo());
          if (!pointerLike(act->getType()))
            continue;
          any = true;
          copyTo[act].push_back(A);
          demand(act);
          for (unsigned loc : snapshot(act))
            insertPt(A, loc);
        }
      }
      if (B->hasAddressTaken())
        scanIndirect(B);
      if (pointerLike(A->getType()) && hooks.harness && hooks.harness(B))
        insertPt(A, location(harnessObj, 0));
      else if (!any && !B->hasAddressTaken())
        insertPt(A, location(outsideObj, 0));
    }
    return;
  }
  if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(v)) {
    insertPt(AI, location(objectFor(Kind::Alloca, AI), 0));
    return;
  }
  if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(v)) {
    seedGlobal(G);
    return;
  }
  if (const auto *F = llvm::dyn_cast<llvm::Function>(v)) {
    seedFunc(F);
    return;
  }
  if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(v)) {
    if (CE->isCast()) {
      demand(CE->getOperand(0));
      for (unsigned loc : snapshot(CE->getOperand(0)))
        if (pointerLike(CE->getType()))
          insertPt(CE, loc);
    } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(CE)) {
      demand(G->getPointerOperand());
      for (unsigned loc : snapshot(G->getPointerOperand())) {
        const Loc L = locs[loc];
        insertPt(CE, location(L.obj, addOff(L.off, gepOff(G))));
      }
    } else if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      insertPt(CE, location(outsideObj, 0));
    }
    return;
  }
  const auto *I = llvm::dyn_cast<llvm::Instruction>(v);
  if (!I) {
    if (pointerLike(v->getType()))
      insertPt(v, location(outsideObj, 0));
    return;
  }
  if (const auto *C = llvm::dyn_cast<llvm::CastInst>(I)) {
    demand(C->getOperand(0));
    for (unsigned loc : snapshot(C->getOperand(0)))
      if (pointerLike(C->getType()))
        insertPt(C, loc);
    return;
  }
  if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(I)) {
    demand(Fz->getOperand(0));
    for (unsigned loc : snapshot(Fz->getOperand(0)))
      if (pointerLike(Fz->getType()))
        insertPt(Fz, loc);
    return;
  }
  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(I)) {
    demand(G->getPointerOperand());
    // The base may already have been propagated, before this gep was
    // demanded. Copy the cells that exist now. Cells that arrive later
    // still flow, because this gep is demanded.
    for (unsigned loc : snapshot(G->getPointerOperand())) {
      const Loc L = locs[loc];
      insertPt(G, location(L.obj, addOff(L.off, gepOff(G))));
    }
    return;
  }
  if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(I)) {
    for (const llvm::Value *inc : PN->incoming_values()) {
      if (!pointerLike(inc->getType()))
        continue;
      demand(inc);
      for (unsigned loc : snapshot(inc))
        insertPt(PN, loc);
    }
    return;
  }
  if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(I)) {
    for (const llvm::Value *arm : {Sel->getTrueValue(), Sel->getFalseValue()}) {
      if (!pointerLike(arm->getType()))
        continue;
      demand(arm);
      for (unsigned loc : snapshot(arm))
        if (pointerLike(Sel->getType()))
          insertPt(Sel, loc);
    }
    return;
  }
  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(I)) {
    demand(Ld->getPointerOperand());
    for (unsigned loc : snapshot(Ld->getPointerOperand()))
      if (pointerLike(Ld->getType()))
        readMem(Ld, locs[loc]);
    return;
  }
  if (const auto *C = llvm::dyn_cast<llvm::CallBase>(I)) {
    if (C->isInlineAsm()) {
      if (pointerLike(C->getType()))
        insertPt(C, location(outsideObj, 0));
      return;
    }
    if (hooks.allocates && hooks.allocates(C)) {
      if (!seededCall.insert(C).second)
        return;
      unsigned o = objectFor(Kind::Alloc, C);
      insertPt(C, location(o, 0));
      if (hooks.allocSource)
        if (const llvm::Value *src = hooks.allocSource(C)) {
          recordWrite(o, 0, -1, C);
          demand(src);
        }
      return;
    }
    const llvm::Value *dst = nullptr;
    const llvm::Value *src = nullptr;
    if (hooks.byteCopy && hooks.byteCopy(C, dst, src) && dst)
      demand(dst);
    if (const llvm::Function *D = C->getCalledFunction()) {
      const llvm::Function *B = bodyOf(D);
      if (B && !B->isDeclaration()) {
        auto rit = returnsOf.find(B);
        if (rit != returnsOf.end()) {
          for (const llvm::ReturnInst *R : rit->second) {
            const llvm::Value *rv = R->getReturnValue();
            if (!rv || !pointerLike(rv->getType()) || !pointerLike(C->getType()))
              continue;
            copyTo[rv].push_back(C);
            demand(rv);
            for (unsigned loc : snapshot(rv))
              insertPt(C, loc);
          }
        }
      } else if (pointerLike(C->getType())) {
        insertPt(C, location(objectFor(Kind::Outside, C), 0));
      }
    } else {
      demand(C->getCalledOperand());
    }
    return;
  }
  if (pointerLike(I->getType()))
    insertPt(I, location(outsideObj, 0));
}

const llvm::SparseBitVector<> &Points::of(const llvm::Value *v) {
  static const llvm::SparseBitVector<> empty;
  if (!v)
    return empty;
  demand(v);
  drain();
  OfSlot &slot = ofCache[v];
  if (slot.ep != epoch) {
    slot.bits.clear();
    auto it = pt.find(v);
    if (it != pt.end())
      slot.bits = it->second;
    slot.ep = epoch;
  }
  return slot.bits;
}

const llvm::SparseBitVector<> &Points::of(const llvm::Value *v, const llvm::CallBase *) {
  return of(v);
}

const std::vector<Points::Write> &Points::writes(unsigned o) {
  static const std::vector<Write> none;
  if (o >= objs.size())
    return none;
  ensureObjSlots(o);
  const Obj &ob = objs[o];
  if (ob.site && demanded.insert(ob.site).second)
    demandQ.push_back(ob.site);
  else if (ob.site)
    demand(ob.site);
  drain();
  return writesOf[o];
}

const std::vector<Points::PtrLoad> &Points::ptrLoads(unsigned o) {
  static const std::vector<PtrLoad> none;
  if (o >= objs.size())
    return none;
  writes(o);
  return ptrLoadsOf[o];
}

const std::vector<const llvm::CallBase *> &Points::escapes(unsigned o) {
  static const std::vector<const llvm::CallBase *> none;
  if (o >= objs.size())
    return none;
  writes(o);
  return escapesOf[o];
}

std::vector<const llvm::Function *> Points::callees(const llvm::CallBase *C) {
  std::vector<const llvm::Function *> out;
  if (!C || C->isInlineAsm())
    return out;
  if (const llvm::Function *D = C->getCalledFunction())
    out.push_back(bodyOf(D) ? bodyOf(D) : D);
  else {
    demand(C->getCalledOperand());
    drain();
    for (unsigned loc : snapshot(C->getCalledOperand())) {
      if (objs[locs[loc].obj].kind != Kind::Func)
        continue;
      if (const auto *F = llvm::dyn_cast<llvm::Function>(objs[locs[loc].obj].site))
        out.push_back(bodyOf(F) ? bodyOf(F) : F);
    }
  }
  if (hooks.callees)
    for (const llvm::Function *D : hooks.callees(C))
      if (D)
        out.push_back(D);
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

bool Points::unresolved(const llvm::CallBase *C) {
  if (!C || C->isInlineAsm())
    return true;
  if (!C->getCalledFunction()) {
    demand(C->getCalledOperand());
    drain();
    bool anyFunc = false;
    for (unsigned loc : snapshot(C->getCalledOperand())) {
      if (objs[locs[loc].obj].kind == Kind::Func)
        anyFunc = true;
      else
        return true;
    }
    if (!anyFunc)
      return true;
  }
  for (const llvm::Function *F : callees(C)) {
    const llvm::Function *B = bodyOf(F);
    if (!B || B->isDeclaration())
      return true;
  }
  return false;
}

const std::vector<const llvm::CallBase *> &Points::callers(const llvm::Function *F) {
  static const std::vector<const llvm::CallBase *> none;
  const llvm::Function *B = bodyOf(F);
  if (!B)
    return none;
  scanIndirect(B);
  drain();
  auto eit = callerEpoch.find(B);
  if (eit != callerEpoch.end() && eit->second == epoch && callerCache.count(B))
    return callerCache[B];
  std::vector<const llvm::CallBase *> out;
  auto dit = directCallers.find(B);
  if (dit != directCallers.end())
    out = dit->second;
  auto iit = indirectBound.find(B);
  if (iit != indirectBound.end())
    out.insert(out.end(), iit->second.begin(), iit->second.end());
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  callerCache[B] = std::move(out);
  callerEpoch[B] = epoch;
  return callerCache[B];
}

int Points::regionIndex(const Regions &r, int64_t off) {
  auto it = std::upper_bound(r.bounds.begin(), r.bounds.end(), off);
  return static_cast<int>(it - r.bounds.begin()) - 1;
}

void Points::nodeLeaves(const Regions &r, size_t k, size_t &lo, size_t &hi) {
  lo = hi = k;
  while (lo < r.leaves) {
    lo = 2 * lo;
    hi = 2 * hi + 1;
  }
  lo -= r.leaves;
  hi -= r.leaves;
}

void Points::leafBytes(const Regions &r, size_t a, size_t b, int64_t &lo, bool &loInf, int64_t &hi,
                       bool &hiInf) {
  loInf = a == 0;
  lo = loInf ? 0 : r.bounds[a - 1];
  hiInf = b >= r.bounds.size();
  hi = hiInf ? 0 : r.bounds[b];
}

const Points::Regions &Points::regions(unsigned o) {
  writes(o);
  while (regionsOf.size() <= o)
    regionsOf.emplace_back();
  Regions &r = regionsOf[o];
  if (r.epoch == epoch)
    return r;
  r = Regions();
  r.epoch = epoch;
  const std::vector<Write> &ws = writesOf[o];
  auto endOf = [](const Write &w, int64_t &e) {
    if (w.len < 0)
      return false;
    e = w.off <= INT64_MAX - w.len ? w.off + w.len : INT64_MAX;
    return true;
  };
  for (const Write &w : ws) {
    if (w.off == Any || w.len == 0)
      continue;
    r.bounds.push_back(w.off);
    int64_t e;
    if (endOf(w, e))
      r.bounds.push_back(e);
  }
  std::sort(r.bounds.begin(), r.bounds.end());
  r.bounds.erase(std::unique(r.bounds.begin(), r.bounds.end()), r.bounds.end());
  const size_t n = r.bounds.size() + 1;
  while (r.leaves < n)
    r.leaves <<= 1;
  r.tree.assign(2 * r.leaves, {});
  auto toDef = [](const Write &w) { return Def{w.inst, w.ctx, w.off, w.len}; };
  for (const Write &w : ws) {
    if (w.len == 0)
      continue;
    const Def d = toDef(w);
    if (w.off == Any) {
      r.any.push_back(d);
      continue;
    }
    size_t lo = static_cast<size_t>(regionIndex(r, w.off) + 1);
    int64_t e;
    size_t hi = endOf(w, e) ? static_cast<size_t>(regionIndex(r, e - 1) + 1) : n - 1;
    for (lo += r.leaves, hi += r.leaves + 1; lo < hi; lo >>= 1, hi >>= 1) {
      if (lo & 1)
        r.tree[lo++].push_back(d);
      if (hi & 1)
        r.tree[--hi].push_back(d);
    }
  }
  return r;
}

} // namespace chain
