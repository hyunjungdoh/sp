#include "Points.hpp"

#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"

#include <algorithm>
#include <functional>
#include <tuple>

namespace chain {
Points::Points(const llvm::Module &M0, const llvm::Module &U0, Hooks h)
    : M(M0), U(U0), hooks(std::move(h)), DL(M0.getDataLayout()) {
  ctxs.push_back(Ctx{});
  outsideObj = newObj(Kind::Outside, nullptr, 0, std::nullopt);
  const llvm::Module *mods[2] = {&M, &U};
  for (const llvm::Module *Mod : mods) {
    for (const llvm::Function &F : *Mod) {
      if (F.isDeclaration())
        continue;
      for (const llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
          returnsOf[&F].push_back(R);
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        std::set<const llvm::Function *> ds;
        for (const llvm::Function *D0 : calleesOf(C)) {
          const llvm::Function *D = bodyOf(D0);
          if (D && !D->isDeclaration() && ds.insert(D).second)
            staticCallers[D].push_back(C);
        }
      }
    }
  }
  findCloned();
}

const llvm::Function *Points::bodyOf(const llvm::Function *F) {
  if (!F)
    return nullptr;
  if (!F->isDeclaration())
    return F;
  if (hooks.body)
    if (const llvm::Function *B = hooks.body(F))
      return B;
  return F;
}

std::vector<const llvm::Function *> Points::calleesOf(const llvm::CallBase *C) {
  std::vector<const llvm::Function *> cs;
  if (const llvm::Function *D = C->getCalledFunction())
    cs.push_back(D);
  if (hooks.callees)
    for (const llvm::Function *D : hooks.callees(C))
      cs.push_back(D);
  return cs;
}

bool Points::pointerLike(const llvm::Type *T) const { return T && T->isPointerTy(); }

const llvm::Function *Points::fnOf(const llvm::Value *v) const {
  if (const auto *I = llvm::dyn_cast<llvm::Instruction>(v))
    return I->getFunction();
  if (const auto *A = llvm::dyn_cast<llvm::Argument>(v))
    return A->getParent();
  return nullptr;
}

unsigned Points::ctxOf(const llvm::Value *v, unsigned ctx) const {
  const llvm::Function *F = fnOf(v);
  return F && cloned.count(F) ? ctx : 0;
}

// The functions analysed once per call site. A local is an alloca whose
// address is only loaded from and stored to; what a load of it yields is
// what the stores to it store. The values a return value is made of are
// found through casts, offsets, phis, selects and locals.
// A local: an alloca whose address is only loaded from, stored to, or
// read by a byte copy, so that what a load of it yields is what the stores
// to it store.
bool Points::localAlloca(const llvm::AllocaInst *AI) {
  std::vector<const llvm::Value *> stack{AI};
  std::unordered_set<const llvm::Value *> seenV{AI};
  while (!stack.empty()) {
    const llvm::Value *v = stack.back();
    stack.pop_back();
    for (const llvm::User *Us : v->users()) {
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(Us)) {
        if (L->getPointerOperand() != v)
          return false;
      } else if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(Us)) {
        if (St->getPointerOperand() != v || seenV.count(St->getValueOperand()))
          return false;
      } else if (llvm::isa<llvm::BitCastInst>(Us) || llvm::isa<llvm::AddrSpaceCastInst>(Us)) {
        if (seenV.insert(Us).second)
          stack.push_back(Us);
      } else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(Us)) {
        if (G->getPointerOperand() != v || !G->hasAllZeroIndices())
          return false;
        if (seenV.insert(Us).second)
          stack.push_back(Us);
      } else if (const auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(Us)) {
        if (II->isAssumeLikeIntrinsic() || llvm::isa<llvm::DbgInfoIntrinsic>(II))
          continue;
        const llvm::Value *d = nullptr;
        const llvm::Value *s = nullptr;
        if (!(hooks.byteCopy && hooks.byteCopy(II, d, s) && s == v && d != v))
          return false;
      } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(Us)) {
        const llvm::Value *d = nullptr;
        const llvm::Value *s = nullptr;
        if (!(hooks.byteCopy && hooks.byteCopy(C, d, s) && s == v && d != v))
          return false;
      } else {
        return false;
      }
    }
  }
  return true;
}

// The constant an integer operand has in a context, when it has one: a
// constant; a formal, through the call the context was entered by; a
// local's load, when every store to it stores the same constant; casts
// and arithmetic of such.
std::optional<int64_t> Points::evalConst(const llvm::Value *v, unsigned ctx, unsigned depth) {
  if (depth > 32)
    return std::nullopt;
  if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    if (CI->getValue().getSignificantBits() > 62)
      return std::nullopt;
    return CI->getSExtValue();
  }
  if (const auto *A = llvm::dyn_cast<llvm::Argument>(v)) {
    ctx = ctxOf(A, ctx);
    if (ctx == 0)
      return std::nullopt;
    const Ctx &c = ctxs[ctx];
    if (A->getArgNo() >= c.site->arg_size())
      return std::nullopt;
    return evalConst(c.site->getArgOperand(A->getArgNo()), c.parent, depth + 1);
  }
  if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v)) {
    if (!C->isIntegerCast())
      return std::nullopt;
    auto x = evalConst(C->getOperand(0), ctx, depth + 1);
    if (!x)
      return std::nullopt;
    const unsigned bits = C->getType()->getIntegerBitWidth();
    llvm::APInt ap(64, static_cast<uint64_t>(*x), true);
    if (llvm::isa<llvm::TruncInst>(C))
      ap = ap.trunc(bits).sext(64);
    else if (llvm::isa<llvm::ZExtInst>(C))
      ap = ap.trunc(C->getOperand(0)->getType()->getIntegerBitWidth()).zext(64);
    if (ap.getSignificantBits() > 62)
      return std::nullopt;
    return ap.getSExtValue();
  }
  if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(v)) {
    const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts());
    if (!AI || !localAlloca(AI))
      return std::nullopt;
    std::optional<int64_t> out;
    for (const llvm::User *Us : AI->users())
      if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(Us)) {
        auto x = evalConst(St->getValueOperand(), ctx, depth + 1);
        if (!x || (out && *out != *x))
          return std::nullopt;
        out = x;
      }
    return out;
  }
  if (const auto *B = llvm::dyn_cast<llvm::BinaryOperator>(v)) {
    auto x = evalConst(B->getOperand(0), ctx, depth + 1);
    auto y = evalConst(B->getOperand(1), ctx, depth + 1);
    if (!x || !y)
      return std::nullopt;
    llvm::APInt a(128, static_cast<uint64_t>(*x), true), b(128, static_cast<uint64_t>(*y), true);
    llvm::APInt r;
    switch (B->getOpcode()) {
    case llvm::Instruction::Add:
      r = a + b;
      break;
    case llvm::Instruction::Sub:
      r = a - b;
      break;
    case llvm::Instruction::Mul:
      r = a * b;
      break;
    default:
      return std::nullopt;
    }
    if (r.getSignificantBits() > 62)
      return std::nullopt;
    return r.getSExtValue();
  }
  return std::nullopt;
}

void Points::findCloned() {
  auto isLocal = [&](const llvm::AllocaInst *AI) { return localAlloca(AI); };
  auto localOf = [&](const llvm::Value *p) -> const llvm::AllocaInst * {
    const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(p->stripPointerCasts());
    return AI && isLocal(AI) ? AI : nullptr;
  };
  auto roots = [&](const llvm::Value *v0) {
    std::vector<const llvm::Value *> out, stack{v0};
    std::unordered_set<const llvm::Value *> seenV{v0};
    auto visit = [&](const llvm::Value *x) {
      if (seenV.insert(x).second)
        stack.push_back(x);
    };
    while (!stack.empty()) {
      const llvm::Value *v = stack.back();
      stack.pop_back();
      if (llvm::isa<llvm::CastInst>(v) || llvm::isa<llvm::FreezeInst>(v)) {
        visit(llvm::cast<llvm::User>(v)->getOperand(0));
      } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(v)) {
        visit(G->getPointerOperand());
      } else if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(v)) {
        for (const llvm::Value *in : PN->incoming_values())
          visit(in);
      } else if (const auto *SI = llvm::dyn_cast<llvm::SelectInst>(v)) {
        visit(SI->getTrueValue());
        visit(SI->getFalseValue());
      } else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(v)) {
        if (CE->isCast())
          visit(CE->getOperand(0));
        else
          out.push_back(v);
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(v)) {
        const llvm::AllocaInst *AI = localOf(L->getPointerOperand());
        if (!AI) {
          out.push_back(v);
          continue;
        }
        for (const llvm::User *Us : AI->users())
          if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(Us))
            visit(St->getValueOperand());
      } else {
        out.push_back(v);
      }
    }
    return out;
  };
  // A function whose whole effect is a library byte copy or fill: besides
  // those calls, only locals, their loads and stores, casts, offsets,
  // comparisons, control flow and the return.
  auto forwarder = [&](const llvm::Function &F) {
    unsigned copies = 0;
    for (const llvm::Instruction &I : llvm::instructions(F)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
        if (!isLocal(AI))
          return false;
      } else if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (!localOf(St->getPointerOperand()))
          return false;
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        if (!localOf(L->getPointerOperand()))
          return false;
      } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
        const llvm::Value *d = nullptr;
        const llvm::Value *s = nullptr;
        if (const auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(C)) {
          if (llvm::isa<llvm::MemSetInst>(II) || (hooks.byteCopy && hooks.byteCopy(C, d, s)))
            ++copies;
          else if (!II->isAssumeLikeIntrinsic() && !llvm::isa<llvm::DbgInfoIntrinsic>(II))
            return false;
        } else if (!C->isInlineAsm() && hooks.byteCopy && hooks.byteCopy(C, d, s)) {
          ++copies;
        } else {
          return false;
        }
      } else if (!(llvm::isa<llvm::CastInst>(&I) || llvm::isa<llvm::GetElementPtrInst>(&I) ||
                   llvm::isa<llvm::CmpInst>(&I) || llvm::isa<llvm::BranchInst>(&I) ||
                   llvm::isa<llvm::SwitchInst>(&I) || llvm::isa<llvm::ReturnInst>(&I) ||
                   llvm::isa<llvm::PHINode>(&I) || llvm::isa<llvm::SelectInst>(&I) ||
                   llvm::isa<llvm::FreezeInst>(&I) || llvm::isa<llvm::UnreachableInst>(&I))) {
        return false;
      }
    }
    return copies > 0;
  };
  std::vector<const llvm::Function *> fns;
  const llvm::Module *mods[2] = {&M, &U};
  for (const llvm::Module *Mod : mods)
    for (const llvm::Function &F : *Mod)
      if (!F.isDeclaration())
        fns.push_back(&F);
  std::unordered_map<const llvm::Function *, std::vector<const llvm::Value *>> retRoots;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> callsIn;
  for (const llvm::Function *F : fns) {
    for (const llvm::Instruction &I : llvm::instructions(*F))
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I))
        if (!C->isInlineAsm())
          callsIn[F].push_back(C);
    if (!pointerLike(F->getReturnType()))
      continue;
    auto ri = returnsOf.find(F);
    if (ri == returnsOf.end())
      continue;
    for (const llvm::ReturnInst *R : ri->second)
      if (R->getReturnValue())
        for (const llvm::Value *r : roots(R->getReturnValue()))
          retRoots[F].push_back(r);
  }
  std::unordered_set<const llvm::Function *> forwarders;
  for (const llvm::Function *F : fns)
    if (forwarder(*F))
      forwarders.insert(F);
  std::unordered_set<const llvm::Function *> banned;
  for (;;) {
    cloned.clear();
    for (const llvm::Function *F : forwarders)
      if (!banned.count(F))
        cloned.insert(F);
    // Functions returning fresh memory: a least fixpoint, since fresh
    // memory may come through another such function.
    bool changed = true;
    while (changed) {
      changed = false;
      for (const llvm::Function *F : fns) {
        if (banned.count(F) || cloned.count(F))
          continue;
        auto rr = retRoots.find(F);
        if (rr == retRoots.end())
          continue;
        bool fresh = false;
        for (const llvm::Value *r : rr->second) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(r);
          if (!C || C->isInlineAsm())
            continue;
          if (hooks.allocates && hooks.allocates(C)) {
            fresh = true;
            break;
          }
          for (const llvm::Function *D0 : calleesOf(C))
            if (cloned.count(bodyOf(D0))) {
              fresh = true;
              break;
            }
          if (fresh)
            break;
        }
        if (fresh) {
          cloned.insert(F);
          changed = true;
        }
      }
    }
    // Recursion among them would make the contexts unbounded: such
    // functions are analysed once.
    std::unordered_map<const llvm::Function *, std::vector<const llvm::Function *>> succ;
    for (const llvm::Function *F : cloned)
      for (const llvm::CallBase *C : callsIn[F])
        for (const llvm::Function *D0 : calleesOf(C)) {
          const llvm::Function *D = bodyOf(D0);
          if (cloned.count(D))
            succ[F].push_back(D);
        }
    std::unordered_map<const llvm::Function *, unsigned> index, low;
    std::unordered_set<const llvm::Function *> onStack;
    std::vector<const llvm::Function *> stack;
    unsigned next = 1;
    std::vector<const llvm::Function *> recursive;
    struct Frame {
      const llvm::Function *f;
      size_t i;
    };
    for (const llvm::Function *root : cloned) {
      if (index.count(root))
        continue;
      std::vector<Frame> frames;
      auto enterF = [&](const llvm::Function *f) {
        index[f] = low[f] = next++;
        stack.push_back(f);
        onStack.insert(f);
        frames.push_back(Frame{f, 0});
      };
      enterF(root);
      while (!frames.empty()) {
        Frame &fr = frames.back();
        const llvm::Function *f = fr.f;
        auto &ss = succ[f];
        if (fr.i < ss.size()) {
          const llvm::Function *g = ss[fr.i++];
          if (!index.count(g))
            enterF(g);
          else if (onStack.count(g))
            low[f] = std::min(low[f], index[g]);
          continue;
        }
        if (low[f] == index[f]) {
          std::vector<const llvm::Function *> comp;
          const llvm::Function *m;
          do {
            m = stack.back();
            stack.pop_back();
            onStack.erase(m);
            comp.push_back(m);
          } while (m != f);
          bool self = false;
          for (const llvm::Function *g : ss)
            if (g == f)
              self = true;
          if (comp.size() > 1 || self)
            for (const llvm::Function *g : comp)
              recursive.push_back(g);
        }
        frames.pop_back();
        if (!frames.empty())
          low[frames.back().f] = std::min(low[frames.back().f], low[f]);
      }
    }
    if (recursive.empty())
      break;
    for (const llvm::Function *g : recursive)
      banned.insert(g);
  }
}

unsigned Points::context(unsigned parent, const llvm::CallBase *site, const llvm::Function *F) {
  // The chain of call sites identifies the context; the callee is part of
  // the key since a call through a pointer may reach several.
  auto key = std::make_tuple(parent, site, F);
  auto it = ctxId.find(key);
  if (it != ctxId.end())
    return it->second;
  Ctx c;
  c.parent = parent;
  c.site = site;
  c.fn = F;
  ctxs.push_back(c);
  unsigned x = static_cast<unsigned>(ctxs.size() - 1);
  ctxId.emplace(key, x);
  return x;
}

// A context of a function analysed per call site: the whole body is
// registered in it, so that every store, call and pointer of the body is
// seen in that context.
void Points::enter(const llvm::Function *F, unsigned ctx) {
  if (!entered.insert({F, ctx}).second)
    return;
  ctxsOf[F].push_back(ctx);
  for (const llvm::Argument &A : F->args())
    if (pointerLike(A.getType()))
      node(&A, ctx);
  for (const llvm::Instruction &I : llvm::instructions(*F)) {
    if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I))
      registerStore(St, ctx);
    else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I))
      registerCall(C, ctx);
    else if (pointerLike(I.getType()))
      node(&I, ctx);
  }
}

// Asking about a value of a function analysed per call site asks for every
// context it is entered in: each call known statically binds, and a
// function the harness calls or nothing calls is entered without a call.
void Points::demandFn(const llvm::Function *F) {
  if (!demandedFn.insert(F).second)
    return;
  const std::vector<const llvm::CallBase *> sc = staticCallers[F];
  if (sc.empty() || (hooks.harness && hooks.harness(F)))
    enter(F, 0);
  for (const llvm::CallBase *C : sc) {
    const llvm::Function *G = fnOf(C);
    if (G && cloned.count(G)) {
      demandFn(G);
      const std::vector<unsigned> xs = ctxsOf[G];
      for (unsigned x : xs)
        bindCall(C, x, F);
    } else {
      bindCall(C, 0, F);
    }
  }
}

unsigned Points::newObj(Kind k, const llvm::Value *site, unsigned ctx, std::optional<int64_t> size) {
  Obj o;
  o.kind = k;
  o.site = site;
  o.ctx = ctx;
  objs.push_back(o);
  objLocs.emplace_back();
  // The offsets kept apart inside the object: the byte offsets below its
  // static size. An object without a static size -- memory allocated with
  // a size computed at run time -- has no layout to keep apart: it is one
  // cell, which every pointer into it addresses. Every object thus has
  // finitely many locations, so the solution is finite.
  int64_t ext = 0;
  if (k == Kind::Alloca) {
    if (auto sz = llvm::cast<llvm::AllocaInst>(site)->getAllocationSize(DL))
      if (!sz->isScalable())
        ext = static_cast<int64_t>(sz->getFixedValue());
  } else if (k == Kind::Alloc) {
    if (size)
      ext = *size;
    else if (hooks.allocSize)
      if (auto sz = hooks.allocSize(llvm::cast<llvm::CallBase>(site)))
        ext = static_cast<int64_t>(*sz);
  } else if (k == Kind::Global) {
    llvm::Type *T = llvm::cast<llvm::GlobalVariable>(site)->getValueType();
    if (T->isSized())
      ext = static_cast<int64_t>(DL.getTypeAllocSize(T));
  }
  objExt.push_back(ext);
  unionOf.push_back(0);
  return static_cast<unsigned>(objs.size() - 1);
}

unsigned Points::siteObj(Kind k, const llvm::Value *site, unsigned ctx, std::optional<int64_t> size) {
  auto key = std::make_pair(site, ctx);
  auto it = objOf.find(key);
  if (it != objOf.end())
    return it->second;
  unsigned o = newObj(k, site, ctx, size);
  objOf.emplace(key, o);
  return o;
}

// A pointer into o reaches code with no body here that may write memory:
// a pointer to memory outside both modules may then be stored anywhere in
// o, and the call is recorded as a writer of o.
void Points::escape(unsigned o, const llvm::CallBase *C) {
  if (!escapeSeen.insert({o, C}).second)
    return;
  escapesOf[o].push_back(C);
  ++nEscapes;
  unsigned any = location(o, Any);
  unsigned u = location(outsideObj, 0);
  if (P(any).set(u)) {
    delta[find(any)].set(u);
    push(any);
  }
}

unsigned Points::newNode(const llvm::Value *v, unsigned ctx) {
  unsigned id = static_cast<unsigned>(pts.size());
  pts.emplace_back();
  seen.emplace_back();
  delta.emplace_back();
  copyTo.emplace_back();
  gepTo.emplace_back();
  isLoc.push_back(false);
  isSlice.push_back(0);
  locs.emplace_back();
  nodeVal.push_back(v);
  nodeCtx.push_back(ctx);
  usersDone.push_back(v == nullptr);
  inWork.push_back(false);
  gained.emplace_back();
  rep.push_back(id);
  members.emplace_back();
  symAt.emplace_back();
  symUser.emplace_back();
  copyFrom.emplace_back();
  storeSink.push_back(0);
  concreteOnly.push_back(0);
  imgDirty.push_back(0);
  hookedSym.emplace_back();
  return id;
}

unsigned Points::find(unsigned n) {
  unsigned r = n;
  while (rep[r] != r)
    r = rep[r];
  while (rep[n] != r) {
    unsigned next = rep[n];
    rep[n] = r;
    n = next;
  }
  return r;
}

// Two classes become one. What either had carried along its own edges
// has not been carried along the other's, so only what both had carried
// stays carried; the rest is carried again. Every member's hooks see the
// whole set again: a member of one class has not seen the other's
// elements, and the hooks add each fact once.
void Points::unify(unsigned a, unsigned b) {
  unsigned r = find(a), s = find(b);
  if (r == s)
    return;
  if (s < r)
    std::swap(r, s);
  rep[s] = r;
  if (members[r].empty())
    members[r].push_back(r);
  if (members[s].empty())
    members[r].push_back(s);
  else
    members[r].insert(members[r].end(), members[s].begin(), members[s].end());
  members[s].clear();
  members[s].shrink_to_fit();
  pts[r] |= pts[s];
  PtsSet both;
  for (unsigned x : seen[r])
    if (seen[s].test(x))
      both.set(x);
  seen[r] = std::move(both);
  delta[r] = pts[r];
  delta[r].intersectWithComplement(seen[r]);
  gained[r] = pts[r];
  copyTo[r] |= copyTo[s];
  copyTo[r].reset(r);
  copyTo[r].reset(s);
  gepTo[r].insert(gepTo[r].end(), gepTo[s].begin(), gepTo[s].end());
  symAt[r].insert(symAt[r].end(), symAt[s].begin(), symAt[s].end());
  symUser[r].insert(symUser[r].end(), symUser[s].begin(), symUser[s].end());
  copyFrom[r].insert(copyFrom[r].end(), copyFrom[s].begin(), copyFrom[s].end());
  if (storeSink[s])
    storeSink[r] = 1;
  if (concreteOnly[s])
    concreteOnly[r] = 1;
  hookedSym[r] |= hookedSym[s];
  ++imgEpoch;
  pts[s].clear();
  seen[s].clear();
  delta[s].clear();
  gained[s].clear();
  copyTo[s].clear();
  gepTo[s].clear();
  gepTo[s].shrink_to_fit();
  symAt[s].clear();
  symAt[s].shrink_to_fit();
  symUser[s].clear();
  symUser[s].shrink_to_fit();
  copyFrom[s].clear();
  copyFrom[s].shrink_to_fit();
  hookedSym[s].clear();
  merged.push_back(r);
  retargetSlices(s, r);
  atFix = false;
  if (!inWork[r]) {
    inWork[r] = true;
    work.push_back(r);
  }
}

void Points::push(unsigned n) {
  // A node is queued only when it holds a location the propagation has not
  // carried yet. A new edge can drop a location the target already carried;
  // queueing it again would open another round that moves nothing.
  n = find(n);
  if (!pending(n))
    return;
  atFix = false;
  if (inWork[n])
    return;
  inWork[n] = true;
  work.push_back(n);
}

bool Points::pending(unsigned n) const { return !delta[n].empty(); }

void Points::edge(unsigned from, unsigned to, bool gep, int64_t off) {
  from = find(from);
  to = find(to);
  if (from == to && (!gep || off == 0))
    return;
  Edge e;
  e.to = to;
  e.gep = gep;
  e.off = off;
  if (!gep || off == 0) {
    e.gep = false;
    if (!copyTo[from].set(to))
      return;
    ++nEdges;
    if (!pts[from].empty()) {
      const PtsSet cur = pts[from];
      apply(e, cur, from);
    }
    return;
  }
  for (const Edge &x : gepTo[from])
    if (find(x.to) == to && x.off == off)
      return;
  gepTo[from].push_back(e);
  ++nEdges;
  if (!pts[from].empty()) {
    const PtsSet cur = pts[from];
    apply(e, cur, from);
  }
}

unsigned Points::unionNode(unsigned o) {
  if (unionOf[o])
    return unionOf[o];
  unsigned id = newNode(nullptr, 0);
  concreteOnly[id] = 1;
  unionOf[o] = id;
  for (unsigned l : objLocs[o])
    edge(l, id);
  return id;
}

unsigned Points::loadSummary(unsigned addr) {
  auto it = loadSum.find(addr);
  if (it != loadSum.end())
    return it->second;
  const unsigned s = newNode(nullptr, 0);
  concreteOnly[s] = 1;
  loadSum.emplace(addr, s);
  return s;
}

unsigned Points::storeSummary(unsigned addr) {
  auto it = storeSum.find(addr);
  unsigned s;
  if (it == storeSum.end()) {
    s = newNode(nullptr, 0);
    storeSink[s] = 1;
    concreteOnly[s] = 1;
    storeSum.emplace(addr, s);
  } else {
    s = it->second;
  }
  // Copy the values first. Connecting one can register another store of
  // this same pointer, which calls back here.
  std::vector<unsigned> vals;
  auto si = storesAt.find(addr);
  if (si != storesAt.end())
    for (const StoreAt &st : si->second)
      if (st.value != UINT32_MAX)
        vals.push_back(st.value);
  for (unsigned v : vals)
    edge(v, s);
  return s;
}

void Points::pourLoad(unsigned summary, unsigned id) {
  const Loc lc = locs[id];
  if (objs[lc.obj].kind == Kind::Func)
    return;
  if (lc.off != Any) {
    edge(id, summary);
    edge(location(lc.obj, Any), summary);
  } else {
    edge(unionNode(lc.obj), summary);
  }
  if (lc.obj < sliceAt.size()) {
    const std::vector<SliceHit> hits = sliceAt[lc.obj];
    for (const SliceHit &h : hits)
      if (h.off == Any || lc.off == Any || h.off == lc.off)
        edge(sliceMem(h.slice), summary);
  }
}

void Points::noteLoad(unsigned L, unsigned id) {
  const Loc lc = locs[id];
  if (objs[lc.obj].kind == Kind::Func)
    return;
  if (!ptrLoadSeen.insert({L, id}).second)
    return;
  ptrLoadsOf[lc.obj].push_back(PtrLoad{llvm::cast<llvm::LoadInst>(nodeVal[L]), lc.off});
  ++nPtrLoads;
}

void Points::linkLoad(unsigned addr, unsigned L, unsigned id) {
  if (isSliceId(id))
    return;
  const Loc lc = locs[id];
  // Code is not data memory: a load from a function reads no pointer.
  if (objs[lc.obj].kind == Kind::Func)
    return;
  // The cell feeds the pointer's load summary. Every load of the pointer
  // copies the summary, so a second load does not repeat the cell edges.
  const unsigned s = loadSummary(addr);
  pourLoad(s, id);
  edge(s, L);
  noteLoad(L, id);
}

bool Points::isSliceId(unsigned id) const { return id < isSlice.size() && isSlice[id]; }

unsigned Points::makeSlice(PtsSet roots, int64_t off, bool cyclic) {
  if (off == Any)
    cyclic = true;
  roots.flush();
  roots.internLarge();
  const ShiftKey key{roots.bodyPtr(), cyclic ? Any : off, cyclic};
  auto it = sliceId.find(key);
  if (it != sliceId.end())
    return it->second;
  const unsigned id = newNode(nullptr, 0);
  isSlice[id] = 1;
  Slice &s = sliceOf[id];
  s.roots = std::move(roots);
  s.off = cyclic ? Any : off;
  s.cyclic = cyclic;
  sliceId.emplace(key, id);
  return id;
}

unsigned Points::stableSlice(unsigned src, int64_t off, bool cyclic) {
  src = find(src);
  if (off == Any)
    cyclic = true;
  if (cyclic)
    off = Any;
  const SliceKey key{src, off, cyclic};
  auto it = sliceBySrc.find(key);
  if (it != sliceBySrc.end())
    return it->second;
  const unsigned id = newNode(nullptr, 0);
  isSlice[id] = 1;
  sliceOf[id].src = src;
  sliceOf[id].off = off;
  sliceOf[id].cyclic = cyclic;
  sliceBySrc.emplace(key, id);
  if (slicesFrom.size() <= src)
    slicesFrom.resize(static_cast<size_t>(src) + 1);
  slicesFrom[src].push_back(id);
  return id;
}

void Points::connectSlice(unsigned sid, unsigned obj, int64_t off) {
  // Cells stay out of the constraint graph. An edge from each cell into the
  // slice memory joins every large points-to set to a fresh node and the
  // fixpoint rebuilds those sets. A store through the slice and a concrete
  // store of an alias still meet in the slice memory.
  (void)sid;
  (void)obj;
  (void)off;
}

void Points::addSliceCell(unsigned sid, unsigned obj, int64_t off) {
  {
    auto it = sliceOf[sid].cellOf.find(obj);
    if (it != sliceOf[sid].cellOf.end()) {
      const int64_t have = sliceOf[sid].cells[it->second].second;
      if (have == off || have == Any)
        return;
      sliceOf[sid].cells[it->second].second = Any;
      if (obj < sliceAt.size())
        for (SliceHit &h : sliceAt[obj])
          if (h.slice == sid)
            h.off = Any;
      connectSlice(sid, obj, Any);
      return;
    }
    const size_t ix = sliceOf[sid].cells.size();
    sliceOf[sid].cellOf.emplace(obj, ix);
    sliceOf[sid].cells.push_back({obj, off});
  }
  if (sliceAt.size() <= obj)
    sliceAt.resize(static_cast<size_t>(obj) + 1);
  sliceAt[obj].push_back(SliceHit{off, sid});
  connectSlice(sid, obj, off);
}

void Points::addSliceFunc(unsigned sid, unsigned obj) {
  std::vector<unsigned> &funcs = sliceOf[sid].funcs;
  if (std::find(funcs.begin(), funcs.end(), obj) != funcs.end())
    return;
  funcs.push_back(obj);
  const std::vector<unsigned> users = sliceOf[sid].users;
  for (unsigned n : users) {
    auto ci = callsAt.find(n);
    if (ci == callsAt.end())
      continue;
    const std::vector<CallAt> calls = ci->second;
    for (const CallAt &ca : calls)
      if (const llvm::Function *F = target(ca.call, obj))
        bindCall(ca.call, ca.ctx, F);
  }
}

void Points::growSlice(unsigned sid, const PtsSet &ids) {
  if (ids.empty() || sliceOf[sid].growing)
    return;
  // Roots stay on the source node. Copying each location into the slice
  // duplicates the set once per displacement.
  if (ids.sideEmpty() && ids.bodyPtr() != nullptr && ids.bodyPtr() == sliceOf[sid].folded)
    return;
  sliceOf[sid].growing = true;
  sliceOf[sid].seeded = true;
  for (unsigned id : ids) {
    if (isSliceId(id) || id >= isLoc.size() || !isLoc[id])
      continue;
    if (objs[locs[id].obj].kind == Kind::Func)
      addSliceFunc(sid, locs[id].obj);
  }
  if (ids.sideEmpty() && ids.count() >= sliceOf[sid].foldN) {
    sliceOf[sid].folded = ids.bodyPtr();
    sliceOf[sid].foldN = ids.count();
  }
  sliceOf[sid].indexed = false;
  sliceOf[sid].growing = false;
}

void Points::pour(unsigned sid, const PtsSet &roots, int64_t base, bool cyclic,
                  std::unordered_set<unsigned> &seen) {
  for (unsigned id : roots) {
    if (isSliceId(id)) {
      if (!seen.insert(id).second)
        continue;
      const unsigned isrc = sliceOf[id].src;
      const int64_t ioff = sliceOf[id].off;
      const bool icyc = sliceOf[id].cyclic;
      bool nc = cyclic || icyc || base == Any || ioff == Any;
      int64_t noff = Any;
      if (!nc) {
        const __int128 sum = static_cast<__int128>(base) + ioff;
        if (sum > INT64_MAX || sum < INT64_MIN)
          nc = true;
        else
          noff = static_cast<int64_t>(sum);
      }
      if (isrc == UINT32_MAX) {
        const PtsSet legacy = sliceOf[id].roots;
        pour(sid, legacy, nc ? Any : noff, nc, seen);
      } else {
        const PtsSet inner = pts[find(isrc)];
        pour(sid, inner, nc ? Any : noff, nc, seen);
      }
      continue;
    }
    if (id >= isLoc.size() || !isLoc[id])
      continue;
    const Loc lc = locs[id];
    if (objs[lc.obj].kind == Kind::Func)
      continue;
    int64_t off;
    if (cyclic || base == Any || lc.off == Any) {
      off = Any;
    } else {
      const __int128 sum = static_cast<__int128>(lc.off) + base;
      if (sum > INT64_MAX || sum < INT64_MIN)
        off = Any;
      else
        off = static_cast<int64_t>(sum);
    }
    addSliceCell(sid, lc.obj, off);
  }
}

void Points::materializeSlice(unsigned sid) {
  if (sliceOf[sid].indexed)
    return;
  sliceOf[sid].indexed = true;
  std::unordered_set<unsigned> seen;
  seen.insert(sid);
  const int64_t base = sliceOf[sid].off;
  const bool cyclic = sliceOf[sid].cyclic;
  // The source node's set is the roots. A slice does not keep a second copy.
  // A root that is itself a slice is the same set, shifted again.
  if (sliceOf[sid].src == UINT32_MAX) {
    const PtsSet roots = sliceOf[sid].roots;
    pour(sid, roots, base, cyclic, seen);
  } else {
    const PtsSet roots = pts[find(sliceOf[sid].src)];
    pour(sid, roots, base, cyclic, seen);
  }
}

void Points::retargetSlices(unsigned from, unsigned to) {
  if (from >= slicesFrom.size())
    return;
  const std::vector<unsigned> sids = std::move(slicesFrom[from]);
  slicesFrom[from].clear();
  for (unsigned sid : sids) {
    const int64_t off = sliceOf[sid].off;
    const bool cyclic = sliceOf[sid].cyclic;
    sliceBySrc.erase(SliceKey{from, off, cyclic});
    const SliceKey nk{to, off, cyclic};
    auto it = sliceBySrc.find(nk);
    if (it == sliceBySrc.end()) {
      sliceOf[sid].src = to;
      sliceBySrc.emplace(nk, sid);
      if (slicesFrom.size() <= to)
        slicesFrom.resize(static_cast<size_t>(to) + 1);
      slicesFrom[to].push_back(sid);
    } else {
      const unsigned canon = it->second;
      sliceOf[canon].same.push_back(sid);
      sliceOf[sid].src = to;
      const PtsSet roots = sliceOf[sid].roots;
      if (!roots.empty())
        growSlice(canon, roots);
    }
  }
}

unsigned Points::composeSlice(unsigned id, int64_t off, bool cyclic) {
  const unsigned src = sliceOf[id].src;
  const int64_t base = sliceOf[id].off;
  const bool baseCyc = sliceOf[id].cyclic;
  if (src == UINT32_MAX) {
    const Slice s = sliceOf[id];
    if (cyclic || off == Any || s.cyclic || s.off == Any)
      return makeSlice(s.roots, Any, true);
    if (off == 0)
      return id;
    const __int128 sum = static_cast<__int128>(s.off) + off;
    if (sum > INT64_MAX || sum < INT64_MIN)
      return makeSlice(s.roots, Any, true);
    return makeSlice(s.roots, static_cast<int64_t>(sum), false);
  }
  if (off == 0 && !cyclic)
    return id;
  bool nc = cyclic || off == Any || baseCyc || base == Any;
  int64_t noff = Any;
  if (!nc) {
    const __int128 sum = static_cast<__int128>(base) + off;
    if (sum > INT64_MAX || sum < INT64_MIN)
      nc = true;
    else
      noff = static_cast<int64_t>(sum);
  }
  const unsigned nid = stableSlice(src, noff, nc);
  if (nid == id)
    return id;
  std::vector<unsigned> &derived = sliceOf[id].derived;
  if (std::find(derived.begin(), derived.end(), nid) == derived.end())
    derived.push_back(nid);
  if (!sliceOf[nid].seeded)
    growSlice(nid, pts[find(src)]);
  return nid;
}

Points::PtsSet Points::sliceImage(unsigned id) {
  if (sliceOf[id].ready)
    return sliceOf[id].image;
  // Copy first. shiftElems creates locations and can reallocate sliceOf.
  const PtsSet roots = sliceOf[id].roots;
  const int64_t off = sliceOf[id].off;
  const bool cyclic = sliceOf[id].cyclic;
  PtsSet img = shiftElems(roots, off, cyclic);
  img.internLarge();
  sliceOf[id].image = std::move(img);
  sliceOf[id].ready = true;
  return sliceOf[id].image;
}

Points::PtsSet Points::expandAddrs(const PtsSet &set) {
  bool any = false;
  for (unsigned id : set)
    if (isSliceId(id)) {
      any = true;
      break;
    }
  if (!any)
    return set;
  PtsSet out;
  for (unsigned id : set) {
    if (isSliceId(id))
      out |= sliceImage(id);
    else
      out.set(id);
  }
  return out;
}

unsigned Points::sliceMem(unsigned sid) {
  if (sliceOf[sid].haveMem)
    return sliceOf[sid].mem;
  const unsigned m = newNode(nullptr, 0);
  sliceOf[sid].haveMem = true;
  sliceOf[sid].mem = m;
  return m;
}

void Points::ensureSlice(unsigned sid) {
  if (sliceOf[sid].seeded)
    return;
  sliceOf[sid].seeded = true;
  if (sliceOf[sid].src == UINT32_MAX)
    return;
  const PtsSet roots = pts[find(sliceOf[sid].src)];
  if (!roots.empty())
    growSlice(sid, roots);
}

void Points::bridgeCell(unsigned locId) {
  const Loc lc = locs[locId];
  if (lc.obj >= sliceAt.size())
    return;
  const std::vector<SliceHit> hits = sliceAt[lc.obj];
  for (const SliceHit &h : hits)
    if (h.off == Any || lc.off == Any || h.off == lc.off)
      edge(locId, sliceMem(h.slice));
}

void Points::replayCopy(unsigned sid, unsigned first) {
  if (!isSliceId(sid) || sliceOf[sid].replaying)
    return;
  sliceOf[sid].replaying = true;
  const unsigned src = find(sliceOf[sid].src);
  const PtsSet roots = pts[src];
  std::vector<unsigned> todo;
  unsigned loader = UINT32_MAX;
  todo.push_back(first);
  std::vector<char> have(static_cast<size_t>(first) + 1);
  have[first] = 1;
  for (size_t i = 0; i < todo.size(); ++i) {
    const unsigned u = todo[i];
    if (loader == UINT32_MAX && loadsAt.count(u))
      loader = u;
    hookCells(u, roots, u == loader);
    for (unsigned id : roots) {
      if (!isSliceId(id) || id == sid)
        continue;
      onPtsSlice(u, id);
    }
    if (!isSliceId(sid))
      break;
    const std::vector<unsigned> now = sliceOf[sid].users;
    for (unsigned u2 : now) {
      if (have.size() <= u2)
        have.resize(static_cast<size_t>(u2) + 1);
      if (have[u2])
        continue;
      have[u2] = 1;
      todo.push_back(u2);
    }
  }
  if (loader != UINT32_MAX && isSliceId(sid)) {
    const std::vector<unsigned> now = sliceOf[sid].users;
    for (unsigned u : now)
      if (u != loader)
        shareLoads(sid, loader, u);
  }
  if (isSliceId(sid))
    sliceOf[sid].replaying = false;
}

void Points::syncCopyUsers(unsigned n, const PtsSet &fresh) {
  if (n >= slicesFrom.size() || fresh.empty())
    return;
  const std::vector<unsigned> sids = slicesFrom[n];
  for (unsigned sid : sids) {
    if (!isSliceId(sid) || sliceOf[sid].src == UINT32_MAX)
      continue;
    if (sliceOf[sid].users.empty())
      continue;
    const PtsSet neu = linkSliceCells(sid, fresh);
    const std::vector<unsigned> users = sliceOf[sid].users;
    for (unsigned u : users)
      applySliceUses(sid, u, neu);
  }
}

Points::PtsSet Points::linkSliceCells(unsigned sid, const PtsSet &ids) {
  PtsSet neu;
  if (!isSliceId(sid) || ids.empty() || sliceOf[sid].linking)
    return neu;
  if (sliceOf[sid].src == UINT32_MAX && sliceOf[sid].roots.empty())
    return neu;
  // Heap stack. Slice chains are far deeper than the C stack.
  struct Job {
    unsigned sid = 0;
    PtsSet ids;
    bool expanded = false;
    std::vector<unsigned> kids;
  };
  std::vector<Job> st;
  st.push_back(Job{sid, ids, false, {}});
  std::unordered_set<unsigned> seen;
  std::unordered_map<unsigned, std::vector<unsigned>> born;
  const unsigned root = sid;
  auto noteHit = [&](unsigned cur, unsigned id) {
    if (id >= isLoc.size() || !isLoc[id])
      return;
    const Loc lc = locs[id];
    if (objs[lc.obj].kind == Kind::Func)
      return;
    if (sliceAt.size() <= lc.obj)
      sliceAt.resize(static_cast<size_t>(lc.obj) + 1);
    for (const SliceHit &h : sliceAt[lc.obj])
      if (h.slice == cur && h.off == lc.off)
        return;
    sliceAt[lc.obj].push_back(SliceHit{lc.off, cur});
  };
  auto noteOff = [&](unsigned cur, unsigned obj, int64_t off) {
    if (objs[obj].kind == Kind::Func)
      return;
    if (sliceAt.size() <= obj)
      sliceAt.resize(static_cast<size_t>(obj) + 1);
    for (const SliceHit &h : sliceAt[obj])
      if (h.slice == cur && h.off == off)
        return;
    sliceAt[obj].push_back(SliceHit{off, cur});
  };
  auto linkDirect = [&](unsigned cur, unsigned id) {
    if (isSliceId(id) || id >= isLoc.size() || !isLoc[id])
      return;
    const Loc lc = locs[id];
    if (objs[lc.obj].kind == Kind::Func) {
      addSliceFunc(cur, lc.obj);
      return;
    }
    if (!sliceOf[cur].linked.insert(id).second)
      return;
    born[cur].push_back(id);
    // The cell's contents and the stored value meet at this cell. The
    // whole-object node is not pulled in: that would mix every field.
    edge(id, sliceOf[cur].out);
    edge(sliceOf[cur].in, id);
    noteHit(cur, id);
  };
  while (!st.empty()) {
    if (!st.back().expanded) {
      const unsigned cur = st.back().sid;
      if (!isSliceId(cur) || sliceOf[cur].linking || !seen.insert(cur).second) {
        st.pop_back();
        continue;
      }
      PtsSet use = std::move(st.back().ids);
      if (use.empty() || (sliceOf[cur].src == UINT32_MAX && sliceOf[cur].roots.empty())) {
        st.pop_back();
        continue;
      }
      const int64_t off = sliceOf[cur].off;
      const bool cyc = sliceOf[cur].cyclic;
      if (!sliceOf[cur].haveOut) {
        const unsigned o = newNode(nullptr, 0);
        concreteOnly[o] = 1;
        sliceOf[cur].out = o;
        sliceOf[cur].haveOut = true;
      }
      if (!sliceOf[cur].haveIn) {
        const unsigned i = newNode(nullptr, 0);
        concreteOnly[i] = 1;
        sliceOf[cur].in = i;
        sliceOf[cur].haveIn = true;
      }
      sliceOf[cur].linking = true;
      std::vector<unsigned> kids;
      for (unsigned id : use) {
        if (isSliceId(id)) {
          const unsigned k = (off == 0 && !cyc) ? id : composeSlice(id, off, cyc);
          kids.push_back(k);
          continue;
        }
        if (id >= isLoc.size() || !isLoc[id])
          continue;
        const Loc lc = locs[id];
        if (objs[lc.obj].kind == Kind::Func) {
          addSliceFunc(cur, lc.obj);
          continue;
        }
        int64_t noff = Any;
        if (!cyc && off != Any && lc.off != Any) {
          const __int128 sum = static_cast<__int128>(lc.off) + off;
          if (sum <= INT64_MAX && sum >= INT64_MIN)
            noff = static_cast<int64_t>(sum);
        }
        if (noff == Any) {
          const std::vector<unsigned> ls = objLocs[lc.obj];
          for (unsigned l : ls)
            linkDirect(cur, l);
          cellWait[lc.obj].insert({cur, Any});
          continue;
        }
        if (off == 0 && !cyc) {
          linkDirect(cur, id);
          continue;
        }
        const auto found = locId.find(std::make_pair(lc.obj, noff));
        if (found != locId.end())
          linkDirect(cur, found->second);
        else {
          cellWait[lc.obj].insert({cur, noff});
          noteOff(cur, lc.obj, noff);
        }
        const auto any = locId.find(std::make_pair(lc.obj, Any));
        if (any != locId.end())
          linkDirect(cur, any->second);
      }
      for (unsigned k : kids) {
        std::vector<unsigned> &nest = sliceOf[cur].nested;
        if (std::find(nest.begin(), nest.end(), k) == nest.end())
          nest.push_back(k);
      }
      st.back().kids = std::move(kids);
      st.back().expanded = true;
      sliceOf[cur].expanded = true;
      continue;
    }
    const unsigned cur = st.back().sid;
    const std::vector<unsigned> kids = st.back().kids;
    st.pop_back();
    if (isSliceId(cur)) {
      for (unsigned k : kids) {
        if (!isSliceId(k))
          continue;
        if (!sliceOf[k].haveOut) {
          const unsigned o = newNode(nullptr, 0);
          concreteOnly[o] = 1;
          sliceOf[k].out = o;
          sliceOf[k].haveOut = true;
        }
        if (!sliceOf[k].haveIn) {
          const unsigned i = newNode(nullptr, 0);
          concreteOnly[i] = 1;
          sliceOf[k].in = i;
          sliceOf[k].haveIn = true;
        }
        edge(sliceOf[k].in, sliceOf[k].out);
        std::vector<unsigned> &up = sliceOf[k].parents;
        if (std::find(up.begin(), up.end(), cur) != up.end())
          continue;
        up.push_back(cur);
        edge(sliceOf[k].out, sliceOf[cur].out);
        edge(sliceOf[cur].in, sliceOf[k].in);
        const std::vector<unsigned> funcs = sliceOf[k].funcs;
        for (unsigned fo : funcs)
          addSliceFunc(cur, fo);
      }
      sliceOf[cur].linking = false;
    }
  }
  std::vector<unsigned> walk{root};
  std::unordered_set<unsigned> vis;
  for (size_t i = 0; i < walk.size(); ++i) {
    const unsigned s = walk[i];
    if (!isSliceId(s) || !vis.insert(s).second)
      continue;
    auto it = born.find(s);
    if (it != born.end())
      for (unsigned c : it->second)
        neu.set(c);
    const std::vector<unsigned> nest = sliceOf[s].nested;
    for (unsigned k : nest)
      walk.push_back(k);
  }
  return neu;
}

void Points::applySliceUses(unsigned sid, unsigned n, const PtsSet &cells) {
  if (!isSliceId(sid) || cells.empty() || !hasHooks(n))
    return;
  auto ci = callsAt.find(n);
  if (ci != callsAt.end()) {
    const std::vector<CallAt> calls = ci->second;
    const std::vector<unsigned> funcs = sliceOf[sid].funcs;
    for (const CallAt &ca : calls)
      for (unsigned o : funcs)
        if (const llvm::Function *F = target(ca.call, o))
          bindCall(ca.call, ca.ctx, F);
  }
  auto ei = escapesAt.find(n);
  if (ei != escapesAt.end()) {
    const std::vector<const llvm::CallBase *> calls = ei->second;
    for (unsigned id : cells) {
      if (id >= isLoc.size() || !isLoc[id])
        continue;
      if (objs[locs[id].obj].kind == Kind::Func)
        continue;
      for (const llvm::CallBase *C : calls) {
        escape(locs[id].obj, C);
        if (!sliceOf[sid].factSeen.insert(Slice::FactKey{C, 0, 'E'}).second)
          continue;
        sliceOf[sid].facts.push_back(Slice::Fact{C, 0, 0, 'E'});
      }
    }
  }
  auto di = copyDstAt.find(n);
  if (di != copyDstAt.end())
    for (unsigned c : di->second)
      for (unsigned d : cells) {
        if (d >= isLoc.size() || !isLoc[d])
          continue;
        copyDst(c, d);
      }
  auto sri = copySrcAt.find(n);
  if (sri != copySrcAt.end())
    for (unsigned c : sri->second)
      for (unsigned x : cells) {
        if (x >= isLoc.size() || !isLoc[x])
          continue;
        copySrc(c, x);
      }
  auto mi = memsetAt.find(n);
  if (mi != memsetAt.end()) {
    const std::vector<CallAt> calls = mi->second;
    for (unsigned d : cells) {
      if (d >= isLoc.size() || !isLoc[d])
        continue;
      if (objs[locs[d].obj].kind == Kind::Func)
        continue;
      for (const CallAt &ca : calls) {
        const int64_t len = memsetLen(ca.call, ca.ctx);
        if (!sliceOf[sid].factSeen.insert(Slice::FactKey{ca.call, ca.ctx, 'M'}).second)
          continue;
        sliceOf[sid].facts.push_back(Slice::Fact{ca.call, ca.ctx, len, 'M'});
      }
    }
  }
}

void Points::attachSlice(unsigned sid, unsigned n) {
  if (!isSliceId(sid) || sliceOf[sid].src == UINT32_MAX || !hasHooks(n))
    return;
  bool known = false;
  for (unsigned u : sliceOf[sid].users)
    if (u == n) {
      known = true;
      break;
    }
  if (known)
    return;
  sliceOf[sid].users.push_back(n);
  const unsigned src = find(sliceOf[sid].src);
  const PtsSet neu = linkSliceCells(sid, pts[src]);
  if (sliceOf[sid].haveIn && sliceOf[sid].haveOut)
    edge(sliceOf[sid].in, sliceOf[sid].out);
  if (sliceOf[sid].haveOut) {
    auto li = loadsAt.find(n);
    if (li != loadsAt.end()) {
      const unsigned s = loadSummary(n);
      edge(sliceOf[sid].out, s);
      const std::vector<unsigned> loads = li->second;
      for (unsigned L : loads) {
        edge(s, L);
        const auto *I = llvm::cast<llvm::Instruction>(nodeVal[L]);
        if (!sliceOf[sid].factSeen.insert(Slice::FactKey{I, 0, 'L'}).second)
          continue;
        sliceOf[sid].facts.push_back(Slice::Fact{I, 0, 0, 'L'});
      }
    }
  }
  auto si = storesAt.find(n);
  if (si != storesAt.end() && sliceOf[sid].haveIn) {
    const std::vector<StoreAt> stores = si->second;
    bool ptrStore = false;
    for (const StoreAt &st : stores)
      if (st.value != UINT32_MAX)
        ptrStore = true;
    if (ptrStore)
      edge(storeSummary(n), sliceOf[sid].in);
    for (const StoreAt &st : stores) {
      const int64_t len = static_cast<int64_t>(DL.getTypeStoreSize(st.inst->getValueOperand()->getType()));
      if (!sliceOf[sid].factSeen.insert(Slice::FactKey{st.inst, st.ctx, 'S'}).second)
        continue;
      sliceOf[sid].facts.push_back(Slice::Fact{st.inst, st.ctx, len, 'S'});
    }
  }
  applySliceUses(sid, n, neu);
}

void Points::onPtsSlice(unsigned n, unsigned sid) {
  if (!isSliceId(sid) || sliceOf[sid].src == UINT32_MAX)
    return;
  attachSlice(sid, n);
}

void Points::realize(unsigned o) {
  if (o < objRealized.size() && objRealized[o])
    return;
  if (objRealized.size() <= o)
    objRealized.resize(static_cast<size_t>(o) + 1);
  objRealized[o] = 1;
  if (o >= sliceAt.size())
    return;
  const std::vector<SliceHit> hits = sliceAt[o];
  for (const SliceHit &h : hits) {
    // Facts of the slice that names this cell, and of every slice that
    // contains that slice: a load or store through an outer pointer reaches
    // this field.
    std::vector<unsigned> q{h.slice};
    std::unordered_set<unsigned> seen;
    for (size_t i = 0; i < q.size(); ++i) {
      const unsigned sid = q[i];
      if (!isSliceId(sid) || !seen.insert(sid).second)
        continue;
      const std::vector<Slice::Fact> facts = sliceOf[sid].facts;
      for (const Slice::Fact &f : facts) {
        if (f.kind == 'L') {
          ptrLoadsOf[o].push_back(PtrLoad{llvm::cast<llvm::LoadInst>(f.inst), h.off});
          continue;
        }
        if (f.kind == 'E') {
          escapesOf[o].push_back(llvm::cast<llvm::CallBase>(f.inst));
          continue;
        }
        if (!writable(o))
          continue;
        writesOf[o].push_back(Write{f.inst, h.off, f.len, f.ctx});
      }
      const std::vector<unsigned> up = sliceOf[sid].parents;
      for (unsigned p : up)
        q.push_back(p);
    }
  }
}

Points::PtsSet Points::shift(const PtsSet &set, int64_t off, bool cyclic, unsigned src) {
  PtsSet out;
  if (set.empty())
    return out;
  if (off == 0 && !cyclic)
    return set;
  // A slice id with source and offset. Its meaning is the current and
  // future pts(src) shifted by off, element by element. Downstream nodes
  // hold one id instead of a bitmap of displaced cells; a hook that reads
  // the id expands to cells via materializeSlice.
  if (src != UINT32_MAX) {
    const unsigned sc = find(src);
    const unsigned sid = stableSlice(sc, off, cyclic || off == Any);
    if (!sliceOf[sid].seeded)
      growSlice(sid, pts[sc]);
    out.set(sid);
    return out;
  }
  // src unknown: element-wise.
  return shiftElems(set, off, cyclic);
}

Points::PtsSet Points::shiftElems(const PtsSet &set, int64_t off, bool cyclic) {
  PtsSet out;
  if (set.empty())
    return out;
  const bool batch = set.count() > 32;
  std::vector<unsigned> image;
  if (batch)
    image.reserve(set.count());
  for (unsigned id : set) {
    if (isSliceId(id)) {
      const unsigned c = composeSlice(id, off, cyclic);
      if (batch)
        image.push_back(c);
      else
        out.set(c);
      continue;
    }
    const Loc lc = locs[id];
    unsigned to;
    if (objs[lc.obj].kind == Kind::Func) {
      // Code cells do not displace.
      to = id;
    } else if (off == Any || lc.off == Any || cyclic) {
      to = location(lc.obj, Any);
    } else if (off == 0) {
      to = id;
    } else {
      // Precise: every offset of every object moves by off. Each (o, k) and
      // (o, k') produce (o, k + off) and (o, k' + off) separately.
      to = location(lc.obj, lc.off + off);
    }
    if (batch)
      image.push_back(to);
    else
      out.set(to);
  }
  if (batch && !image.empty()) {
    std::sort(image.begin(), image.end());
    image.erase(std::unique(image.begin(), image.end()), image.end());
    out.assignSorted(image);
  }
  return out;
}

void Points::apply(const Edge &e0, const PtsSet &set, unsigned src) {
  Edge e = e0;
  e.to = find(e.to);
  bool changed = false;
  if (!e.gep) {
    // pts[dst] includes pts[src], now and as src grows. The cells stay on
    // src; dst holds one reference, so the same field offsets are not stored
    // again at every destination.
    const unsigned from = src == UINT32_MAX ? src : find(src);
    if (from != UINT32_MAX && from < pts.size()) {
      const unsigned sid = stableSlice(from, 0, false);
      if (!sliceOf[sid].seeded) {
        const PtsSet roots = pts[from];
        growSlice(sid, roots);
      } else {
        growSlice(sid, set);
      }
      PtsSet one;
      one.set(sid);
      changed = pts[e.to].absorb(one, delta[e.to]);
    } else {
      changed = pts[e.to].absorb(set, delta[e.to]);
    }
  } else {
    PtsSet img = shift(set, e.off, e.cyclic, src);
    if (pts[e.to].absorb(img, delta[e.to]))
      changed = true;
  }
  if (changed) {
    pts[e.to].internLarge();
    push(e.to);
    ++imgEpoch;
  }
}

void Points::touchImage(unsigned n) {
  n = find(n);
  if (n < imgDirty.size() && imgDirty[n])
    return;
  if (n >= imgDirty.size())
    imgDirty.resize(n + 1);
  imgDirty[n] = 1;
  imgQ.push_back(n);
}

bool Points::hasHooks(unsigned n) const {
  return loadsAt.count(n) || storesAt.count(n) || callsAt.count(n) || escapesAt.count(n) ||
         copyDstAt.count(n) || copySrcAt.count(n) || memsetAt.count(n);
}

void Points::hookMembers(unsigned n, const PtsSet &fresh) {
  if (fresh.empty())
    return;
  if (members[n].empty()) {
    if (!hasHooks(n))
      return;
    materializeUsers(n);
    onPts(n, fresh);
    return;
  }
  const std::vector<unsigned> ms = members[n];
  for (unsigned m : ms) {
    if (!hasHooks(m))
      continue;
    materializeUsers(m);
    onPts(m, fresh);
  }
}

Points::PtsSet Points::pointees(unsigned n) {
  n = find(n);
  if (n < imgSeen.size() && imgSeen[n] == imgEpoch && n < imgCache.size())
    return imgCache[n];
  // A cycle returns the concrete locations already known.
  std::vector<char> visiting(pts.size());
  std::function<PtsSet(unsigned)> rec = [&](unsigned x) -> PtsSet {
    x = find(x);
    if (x < imgSeen.size() && imgSeen[x] == imgEpoch && x < imgCache.size())
      return imgCache[x];
    if (x < visiting.size() && visiting[x])
      return pts[x];
    if (x >= visiting.size())
      visiting.resize(x + 1);
    visiting[x] = 1;
    const std::vector<Sym> syms = x < symAt.size() ? symAt[x] : std::vector<Sym>{};
    const std::vector<unsigned> preds = x < copyFrom.size() ? copyFrom[x] : std::vector<unsigned>{};
    PtsSet r = pts[x];
    for (const Sym &s : syms) {
      const unsigned src = find(s.src);
      const bool looping = src < visiting.size() && visiting[src];
      PtsSet base = looping ? pts[src] : rec(src);
      r |= shift(base, s.off, s.cyclic || looping);
    }
    for (unsigned p : preds) {
      p = find(p);
      if (p == x || (p < visiting.size() && visiting[p]))
        continue;
      r |= rec(p);
    }
    visiting[x] = 0;
    r.internLarge();
    if (imgCache.size() <= x) {
      imgCache.resize(x + 1);
      imgSeen.resize(x + 1);
    }
    imgCache[x] = r;
    imgSeen[x] = imgEpoch;
    return r;
  };
  return rec(n);
}

void Points::symbolicHooks() {
  if (imgQ.empty())
    return;
  ++imgEpoch;
  std::vector<unsigned> q;
  q.swap(imgQ);
  for (size_t i = 0; i < q.size(); ++i) {
    const unsigned n = find(q[i]);
    if (n < imgDirty.size())
      imgDirty[n] = 0;
    const std::vector<unsigned> outs = copyTo[n].seq;
    for (unsigned t : outs) {
      t = find(t);
      if (t < imgDirty.size() && imgDirty[t])
        continue;
      if (t >= imgDirty.size())
        imgDirty.resize(static_cast<size_t>(t) + 1);
      imgDirty[t] = 1;
      q.push_back(t);
    }
    if (n < symUser.size()) {
      const std::vector<unsigned> users = symUser[n];
      for (unsigned u : users) {
        u = find(u);
        if (u < imgDirty.size() && imgDirty[u])
          continue;
        if (u >= imgDirty.size())
          imgDirty.resize(static_cast<size_t>(u) + 1);
        imgDirty[u] = 1;
        q.push_back(u);
      }
    }
  }
  struct Job {
    unsigned n;
    PtsSet neu;
  };
  std::vector<Job> jobs;
  for (unsigned raw : q) {
    const unsigned n = find(raw);
    bool hooks = hasHooks(n);
    if (!hooks && n < members.size())
      for (unsigned m : members[n])
        if (hasHooks(m)) {
          hooks = true;
          break;
        }
    bool sink = false;
    if (n < copyTo.size())
      for (unsigned t : copyTo[n].seq) {
        t = find(t);
        if (isLoc[t] || (t < storeSink.size() && storeSink[t])) {
          sink = true;
          break;
        }
      }
    if (!hooks && !sink)
      continue;
    const PtsSet all = pointees(n);
    PtsSet neu;
    for (unsigned id : all) {
      if (pts[n].test(id))
        continue;
      if (n < hookedSym.size() && hookedSym[n].test(id))
        continue;
      neu.set(id);
    }
    if (neu.empty())
      continue;
    if (n >= hookedSym.size())
      hookedSym.resize(n + 1);
    hookedSym[n] |= neu;
    // A cell or a store summary already received the concrete locations
    // along its copy edge. The offset image is not stored on the pointer,
    // so the new locations are written here, once.
    if (sink) {
      const std::vector<unsigned> targets = copyTo[n].seq;
      for (unsigned t : targets) {
        t = find(t);
        if (!isLoc[t] && (t >= storeSink.size() || !storeSink[t]))
          continue;
        if (pts[t].absorb(neu, delta[t])) {
          pts[t].internLarge();
          push(t);
        }
      }
    }
    if (hooks)
      jobs.push_back(Job{n, neu});
  }
  ++imgEpoch;
  for (const Job &job : jobs)
    hookMembers(job.n, job.neu);
}

void Points::attachWait(unsigned o, int64_t off, unsigned id) {
  const auto it = cellWait.find(o);
  if (it == cellWait.end())
    return;
  const std::vector<std::pair<unsigned, int64_t>> waits(it->second.begin(), it->second.end());
  for (const auto &w : waits) {
    const unsigned sid = w.first;
    const int64_t woff = w.second;
    if (off != Any && woff != Any && woff != off)
      continue;
    if (!isSliceId(sid) || !sliceOf[sid].haveOut || !sliceOf[sid].haveIn)
      continue;
    if (!sliceOf[sid].linked.insert(id).second)
      continue;
    edge(id, sliceOf[sid].out);
    edge(sliceOf[sid].in, id);
    if (id >= isLoc.size() || !isLoc[id])
      continue;
    const Loc lc = locs[id];
    if (objs[lc.obj].kind == Kind::Func)
      continue;
    if (sliceAt.size() <= lc.obj)
      sliceAt.resize(static_cast<size_t>(lc.obj) + 1);
    bool have = false;
    for (const SliceHit &h : sliceAt[lc.obj])
      if (h.slice == sid && h.off == lc.off) {
        have = true;
        break;
      }
    if (!have)
      sliceAt[lc.obj].push_back(SliceHit{lc.off, sid});
  }
}

unsigned Points::location(unsigned o, int64_t off) {
  if (objs[o].kind == Kind::Func)
    off = 0;  // code has no cells
  else if (off != Any && (off < 0 || off >= objExt[o]))
    off = Any;
  auto key = std::make_pair(o, off);
  auto it = locId.find(key);
  if (it != locId.end())
    return it->second;
  unsigned id = newNode(nullptr, 0);
  isLoc[id] = true;
  locs[id].obj = o;
  locs[id].off = off;
  locId.emplace(key, id);
  objLocs[o].push_back(id);
  attachWait(o, off, id);
  if (unionOf[o])
    edge(id, unionOf[o]);
  if (objs[o].kind == Kind::Outside) {
    // Memory outside both modules holds pointers to itself.
    unsigned self = off == 0 ? id : location(o, 0);
    if (P(id).set(self)) {
      delta[find(id)].set(self);
      push(id);
    }
  }
  auto cr = copyRel.find(o);
  if (cr != copyRel.end()) {
    const std::vector<std::pair<unsigned, int64_t>> rels = cr->second;
    for (const auto &r : rels) {
      const int64_t len = copies[r.first].len;
      if (off == Any)
        edge(id, copyMid(r.first, Any));
      else if (off >= r.second && off < r.second + len)
        edge(id, copyMid(r.first, off - r.second));
    }
  }
  return id;
}

// A query names the cells of a slice without adding them to the constraint
// graph. Joining them would copy the slice's set onto every cell.
unsigned Points::locateQuiet(unsigned o, int64_t off) {
  if (objs[o].kind == Kind::Func)
    off = 0;
  else if (off != Any && (off < 0 || off >= objExt[o]))
    off = Any;
  auto key = std::make_pair(o, off);
  auto it = locId.find(key);
  if (it != locId.end())
    return it->second;
  const unsigned id = newNode(nullptr, 0);
  isLoc[id] = true;
  locs[id].obj = o;
  locs[id].off = off;
  locId.emplace(key, id);
  objLocs[o].push_back(id);
  return id;
}

unsigned Points::quietId(unsigned o, int64_t off) {
  if (objs[o].kind == Kind::Func)
    off = 0;
  else if (off != Any && (off < 0 || off >= objExt[o]))
    off = Any;
  auto key = std::make_pair(o, off);
  auto it = locId.find(key);
  if (it != locId.end())
    return it->second;
  auto q = quietLoc.find(key);
  if (q != quietLoc.end())
    return q->second;
  const unsigned id = kQuiet + static_cast<unsigned>(quiets.size());
  quiets.push_back(key);
  quietLoc.emplace(key, id);
  return id;
}

void Points::seed(unsigned n, unsigned o) {
  unsigned id = location(o, 0);
  if (!P(n).set(id))
    return;
  delta[find(n)].set(id);
  push(n);
}

int64_t Points::gepOffset(const llvm::GEPOperator *G) {
  if (!G->hasAllConstantIndices())
    return Any;
  llvm::APInt off(DL.getIndexTypeSizeInBits(G->getType()), 0);
  if (!G->accumulateConstantOffset(DL, off))
    return Any;
  return off.getSExtValue();
}

unsigned Points::node(const llvm::Value *v, unsigned ctx) {
  ctx = ctxOf(v, ctx);
  auto key = std::make_pair(v, ctx);
  auto it = valNode.find(key);
  if (it != valNode.end())
    return it->second;
  const llvm::Function *F = fnOf(v);
  if (F && cloned.count(F) && !entered.count({F, ctx})) {
    enter(F, ctx);
    it = valNode.find(key);
    if (it != valNode.end())
      return it->second;
  }
  unsigned n = newNode(v, ctx);
  valNode.emplace(key, n);
  valNodes[v].push_back(n);
  // Incoming edges from the value's definition.
  if (const auto *I = llvm::dyn_cast<llvm::Instruction>(v)) {
    if (llvm::isa<llvm::AllocaInst>(I)) {
      seed(n, siteObj(Kind::Alloca, v, ctx));
    } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(I)) {
      edge(node(G->getPointerOperand(), ctx), n, true, gepOffset(G));
    } else if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I)) {
      if (llvm::isa<llvm::IntToPtrInst>(I))
        seed(n, outsideObj);
      else if (pointerLike(I->getOperand(0)->getType()))
        edge(node(I->getOperand(0), ctx), n);
      else
        seed(n, outsideObj);
    } else if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(I)) {
      for (const llvm::Value *in : PN->incoming_values())
        edge(node(in, ctx), n);
    } else if (const auto *SI = llvm::dyn_cast<llvm::SelectInst>(I)) {
      edge(node(SI->getTrueValue(), ctx), n);
      edge(node(SI->getFalseValue(), ctx), n);
    } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(I)) {
      unsigned a = node(L->getPointerOperand(), ctx);
      loadsAt[a].push_back(n);
      const PtsSet cur = P(a);
      for (unsigned id : cur) {
        if (isSliceId(id))
          onPtsSlice(a, id);
        else
          linkLoad(a, n, id);
      }
    } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(I)) {
      registerCall(C, ctx);
    } else {
      // A pointer made from an integer, an exception value, a va_arg, an
      // aggregate element: memory not described here.
      seed(n, outsideObj);
    }
  } else if (const auto *A = llvm::dyn_cast<llvm::Argument>(v)) {
    const bool harness = hooks.harness && hooks.harness(F);
    const std::vector<const llvm::CallBase *> sc = staticCallers[F];
    if (cloned.count(F)) {
      // In a context entered through a call, the call bound the formal.
      // Without one, the formal is the harness's memory, or memory from
      // outside both modules when nothing here calls the function.
      if (ctx == 0 && (harness || sc.empty()))
        seed(n, outsideObj);
    } else {
      // A formal of an export receives the harness's memory; a formal
      // nothing here calls receives memory from outside both modules.
      if (harness || sc.empty())
        seed(n, outsideObj);
      for (const llvm::CallBase *C : sc) {
        const llvm::Function *G = fnOf(C);
        if (G && cloned.count(G)) {
          const std::vector<unsigned> xs = ctxsOf[G];
          for (unsigned x : xs)
            bindCall(C, x, F);
        } else {
          bindCall(C, 0, F);
        }
      }
    }
  } else if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(v)) {
    seed(n, siteObj(Kind::Global, v, 0));
    fillGlobal(G);
  } else if (const auto *Fn = llvm::dyn_cast<llvm::Function>(v)) {
    seed(n, siteObj(Kind::Func, Fn, 0));
  } else if (const auto *GA = llvm::dyn_cast<llvm::GlobalAlias>(v)) {
    edge(node(GA->getAliasee(), 0), n);
  } else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(v)) {
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(CE)) {
      edge(node(G->getPointerOperand(), 0), n, true, gepOffset(G));
    } else if (CE->isCast() && pointerLike(CE->getOperand(0)->getType())) {
      edge(node(CE->getOperand(0), 0), n);
    } else {
      seed(n, outsideObj);
    }
  } else if (llvm::isa<llvm::ConstantPointerNull>(v) || llvm::isa<llvm::UndefValue>(v)) {
    // Points nowhere.
  } else {
    seed(n, outsideObj);
  }
  return n;
}

void Points::fillGlobal(const llvm::GlobalVariable *G) {
  if (!G->hasInitializer())
    return;
  fillConstant(objOf[{G, 0}], 0, G->getInitializer());
}

void Points::fillConstant(unsigned o, int64_t off, const llvm::Constant *C) {
  if (llvm::isa<llvm::ConstantAggregateZero>(C) || llvm::isa<llvm::UndefValue>(C) ||
      llvm::isa<llvm::ConstantPointerNull>(C) || llvm::isa<llvm::ConstantDataSequential>(C))
    return;
  if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
    const llvm::StructLayout *SL = DL.getStructLayout(CS->getType());
    for (unsigned i = 0; i < CS->getNumOperands(); ++i)
      fillConstant(o, off + static_cast<int64_t>(SL->getElementOffset(i)), CS->getOperand(i));
    return;
  }
  if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
    const int64_t sz = static_cast<int64_t>(DL.getTypeAllocSize(CA->getType()->getElementType()));
    for (unsigned i = 0; i < CA->getNumOperands(); ++i)
      fillConstant(o, off + sz * static_cast<int64_t>(i), CA->getOperand(i));
    return;
  }
  if (const auto *CV = llvm::dyn_cast<llvm::ConstantVector>(C)) {
    const int64_t sz = static_cast<int64_t>(DL.getTypeAllocSize(CV->getType()->getElementType()));
    for (unsigned i = 0; i < CV->getNumOperands(); ++i)
      fillConstant(o, off + sz * static_cast<int64_t>(i), CV->getOperand(i));
    return;
  }
  if (pointerLike(C->getType()))
    edge(node(C, 0), location(o, off));
}

bool Points::external(const llvm::CallBase *C, std::vector<const llvm::Function *> &cs) {
  if (const auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(C))
    if (II->isAssumeLikeIntrinsic())
      return false;
  if (C->doesNotAccessMemory())
    return false;
  bool ext = false;
  for (const llvm::Function *D0 : cs) {
    const llvm::Function *D = bodyOf(D0);
    if (!D || D->isDeclaration())
      ext = true;
  }
  return ext;
}

int64_t Points::memsetLen(const llvm::CallBase *C, unsigned ctx) {
  if (C->arg_size() < 3)
    return -1;
  if (auto n = evalConst(C->getArgOperand(2), ctx))
    if (*n >= 0)
      return *n;
  return -1;
}

void Points::registerCopy(const llvm::CallBase *C, unsigned ctx, unsigned dn, unsigned sn, int64_t len) {
  unsigned ci = static_cast<unsigned>(copies.size());
  copies.emplace_back();
  copies[ci].call = C;
  copies[ci].ctx = ctx;
  copies[ci].len = len;
  copyDstAt[dn].push_back(ci);
  copySrcAt[sn].push_back(ci);
  const PtsSet ds = P(dn);
  const PtsSet ss = P(sn);
  for (unsigned d : ds) {
    if (isSliceId(d))
      onPtsSlice(dn, d);
    else
      copyDst(ci, d);
  }
  for (unsigned x : ss) {
    if (isSliceId(x))
      onPtsSlice(sn, x);
    else
      copySrc(ci, x);
  }
}

void Points::registerCall(const llvm::CallBase *C, unsigned ctx) {
  if (C->isInlineAsm())
    return;
  ctx = ctxOf(C, ctx);
  if (!callSeen.insert({C, ctx}).second)
    return;
  const bool ptrResult = pointerLike(C->getType());
  unsigned n = ptrResult ? node(C, ctx) : 0;
  const llvm::Value *dst = nullptr;
  const llvm::Value *src = nullptr;
  if (hooks.byteCopy && hooks.byteCopy(C, dst, src)) {
    int64_t len = -1;
    if (C->arg_size() >= 3)
      if (auto n = evalConst(C->getArgOperand(2), ctx))
        if (*n >= 0)
          len = *n;
    registerCopy(C, ctx, node(dst, ctx), node(src, ctx), len);
    return;
  }
  if (const auto *MS = llvm::dyn_cast<llvm::MemSetInst>(C)) {
    unsigned dn = node(MS->getRawDest(), ctx);
    memsetAt[dn].push_back(CallAt{C, ctx});
    const PtsSet ds = P(dn);
    for (unsigned d : ds) {
      if (isSliceId(d))
        onPtsSlice(dn, d);
      else
        addWrite(locs[d].obj, locs[d].off, memsetLen(C, ctx), C, ctx);
    }
    return;
  }
  std::vector<const llvm::Function *> cs = calleesOf(C);
  bool ext = external(C, cs);
  for (const llvm::Function *D : cs)
    bindCall(C, ctx, D);
  if (!C->getCalledFunction()) {
    // The functions a call through a pointer reaches are the functions
    // the pointer may hold. Memory outside both modules holds data, not
    // code: a pointer that may point there is not thereby a call into
    // unknown code. A call whose pointer holds no function at all, once
    // the solution is complete, is one.
    unsigned cn = node(C->getCalledOperand(), ctx);
    callsAt[cn].push_back(CallAt{C, ctx});
    indirectCalls.push_back(CallAt{C, ctx});
    const PtsSet cur = P(cn);
    for (unsigned id : cur) {
      if (isSliceId(id))
        onPtsSlice(cn, id);
      else if (const llvm::Function *F = target(C, locs[id].obj))
        bindCall(C, ctx, F);
    }
  }
  if (ptrResult && hooks.allocates && hooks.allocates(C)) {
    // The size requested, through the context when it is a formal.
    std::optional<int64_t> size;
    if (hooks.allocSizeArgs)
      if (auto sa = hooks.allocSizeArgs(C))
        if (sa->first < C->arg_size())
          if (auto a = evalConst(C->getArgOperand(sa->first), ctx)) {
            if (!sa->second) {
              size = a;
            } else if (*sa->second < C->arg_size()) {
              if (auto b = evalConst(C->getArgOperand(*sa->second), ctx)) {
                llvm::APInt p = llvm::APInt(128, static_cast<uint64_t>(*a), true) *
                                llvm::APInt(128, static_cast<uint64_t>(*b), true);
                if (p.getSignificantBits() <= 62)
                  size = p.getSExtValue();
              }
            }
            if (size && *size < 0)
              size.reset();
          }
    seed(n, siteObj(Kind::Alloc, C, ctx, size));
    // Fresh memory that holds the contents of memory it replaces: a copy
    // of that memory into it, from its start, of unknown length.
    if (hooks.allocSource)
      if (const llvm::Value *from = hooks.allocSource(C))
        if (pointerLike(from->getType()))
          registerCopy(C, ctx, n, node(from, ctx), -1);
  } else if (ext) {
    treatExternal(C, ctx);
  }
}

// The function a call through a pointer reaches when the pointer holds
// object o: the function, when its type is the type the call expects.
// A call through a pointer of another type is not a call of the
// function (the determinacy engine resolves calls the same way).
const llvm::Function *Points::target(const llvm::CallBase *C, unsigned o) const {
  const Obj &ob = objs[o];
  if (ob.kind != Kind::Func)
    return nullptr;
  const auto *F = llvm::cast<llvm::Function>(ob.site);
  if (F->getFunctionType() != C->getFunctionType())
    return nullptr;
  return F;
}

// A call into code with no body here: what it returns is memory outside
// both modules, and what it is handed a pointer to may be written by it.
void Points::treatExternal(const llvm::CallBase *C, unsigned ctx) {
  if (!externalCalls.insert({C, ctx}).second)
    return;
  if (pointerLike(C->getType()))
    seed(node(C, ctx), outsideObj);
  if (C->onlyReadsMemory())
    return;
  for (unsigned i = 0; i < C->arg_size(); ++i) {
    const llvm::Value *a = C->getArgOperand(i);
    if (!pointerLike(a->getType()))
      continue;
    unsigned an = node(a, ctx);
    escapesAt[an].push_back(C);
    const PtsSet cur = P(an);
    for (unsigned id : cur) {
      if (isSliceId(id))
        onPtsSlice(an, id);
      else
        escape(locs[id].obj, C);
    }
  }
}

void Points::bindCall(const llvm::CallBase *C, unsigned ctx, const llvm::Function *F0) {
  const llvm::Function *F = bodyOf(F0);
  if (!F || F->isDeclaration())
    return;
  ctx = ctxOf(C, ctx);
  if (!bound.insert({C, ctx, F}).second)
    return;
  auto &cl = callersOf[F];
  if (std::find(cl.begin(), cl.end(), C) == cl.end())
    cl.push_back(C);
  const unsigned x = cloned.count(F) ? context(ctx, C, F) : 0;
  unsigned i = 0;
  for (const llvm::Argument &A : F->args()) {
    if (i >= C->arg_size())
      break;
    if (pointerLike(A.getType()) && pointerLike(C->getArgOperand(i)->getType()))
      edge(node(C->getArgOperand(i), ctx), node(&A, x));
    ++i;
  }
  if (pointerLike(C->getType())) {
    unsigned cn = node(C, ctx);
    auto ri = returnsOf.find(F);
    if (ri != returnsOf.end())
      for (const llvm::ReturnInst *R : ri->second)
        if (R->getReturnValue() && pointerLike(R->getReturnValue()->getType()))
          edge(node(R->getReturnValue(), x), cn);
  }
  // The body is a constraint of this call. A callee reached only through a
  // pointer is not in the caller-closure that rooted the solve, so its
  // stores and calls are entered here or the bytes that pass through it
  // are dropped.
  enter(F, x);
}

void Points::registerStore(const llvm::StoreInst *St, unsigned ctx) {
  ctx = ctxOf(St, ctx);
  if (!storeSeen.insert({St, ctx}).second)
    return;
  unsigned an = node(St->getPointerOperand(), ctx);
  const llvm::Value *val = St->getValueOperand();
  unsigned vn = pointerLike(val->getType()) ? node(val, ctx) : UINT32_MAX;
  storesAt[an].push_back(StoreAt{vn, St, ctx});
  const int64_t sz = static_cast<int64_t>(DL.getTypeStoreSize(val->getType()));
  const PtsSet cur = P(an);
  bool wrote = false;
  for (unsigned id : cur) {
    if (isSliceId(id)) {
      onPtsSlice(an, id);
      continue;
    }
    if (!writable(locs[id].obj))
      continue;
    addWrite(locs[id].obj, locs[id].off, sz, St, ctx);
    wrote = true;
  }
  // The value joins the pointer's store summary, and every cell already
  // named copies that summary. Cells found later do the same.
  if (vn != UINT32_MAX && wrote) {
    const unsigned s = storeSummary(an);
    for (unsigned id : cur) {
      if (isSliceId(id))
        continue;
      if (!writable(locs[id].obj))
        continue;
      edge(s, id);
    }
  }
}

// Memory the program can write: not code, and not a global the IR marks
// constant. A write there is no execution of the program, so it defines
// no byte and stores no pointer.
bool Points::writable(unsigned o) const {
  const Obj &ob = objs[o];
  if (ob.kind == Kind::Func)
    return false;
  if (ob.kind == Kind::Global)
    if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(ob.site))
      return !G->isConstant();
  return true;
}

void Points::addWrite(unsigned o, int64_t off, int64_t len, const llvm::Instruction *I, unsigned ctx) {
  if (!writable(o))
    return;
  if (!writeSeen.insert(std::make_tuple(o, off, len, I, ctx)).second)
    return;
  writesOf[o].push_back(Write{I, off, len, ctx});
  ++nWrites;
}

void Points::copyEnsure(unsigned n) {
  if (copyRep.size() > n)
    return;
  const size_t old = copyRep.size();
  copyRep.resize(static_cast<size_t>(n) + 1);
  copySucc.resize(copyRep.size());
  copyPred.resize(copyRep.size());
  copyHit.resize(copyRep.size());
  copyHave.resize(copyRep.size());
  copyMark.resize(copyRep.size());
  for (size_t i = old; i < copyRep.size(); ++i)
    copyRep[i] = static_cast<unsigned>(i);
}

unsigned Points::copyFind(unsigned x) {
  copyEnsure(x);
  unsigned r = x;
  while (copyRep[r] != r)
    r = copyRep[r];
  while (copyRep[x] != r) {
    const unsigned p = copyRep[x];
    copyRep[x] = r;
    x = p;
  }
  return r;
}

unsigned Points::copyFresh() {
  if (copyMark.size() < copyRep.size())
    copyMark.resize(copyRep.size());
  if (++copyStamp == 0) {
    std::fill(copyMark.begin(), copyMark.end(), 0u);
    copyStamp = 1;
  }
  return copyStamp;
}

// Remember everything `from` reaches. A successor whose answer is still
// current contributes its set, so a later question does not walk it again.
void Points::copyFill(unsigned from) {
  copyEnsure(from);
  const unsigned stamp = copyFresh();
  PtsSet hit;
  std::vector<unsigned> st{from};
  copyMark[from] = stamp;
  while (!st.empty()) {
    const unsigned x = st.back();
    st.pop_back();
    for (unsigned y0 : copySucc[x]) {
      const unsigned y = copyFind(y0);
      if (y >= copyMark.size())
        copyMark.resize(y + 1);
      if (copyMark[y] == stamp)
        continue;
      copyMark[y] = stamp;
      hit.set(y);
      if (y < copyHave.size() && copyHave[y]) {
        if (y < copyHit.size())
          hit |= copyHit[y];
      } else {
        st.push_back(y);
      }
    }
  }
  if (copyHit.size() <= from)
    copyHit.resize(static_cast<size_t>(from) + 1);
  if (copyHave.size() <= from)
    copyHave.resize(static_cast<size_t>(from) + 1);
  copyHit[from] = std::move(hit);
  copyHave[from] = 1;
}

void Points::copyDrop() {
  for (size_t i = 0; i < copyHave.size(); ++i) {
    if (!copyHave[i])
      continue;
    copyHave[i] = 0;
    copyHit[i].clear();
  }
}

// An edge out of `from` was added. `from` itself was updated. Anything
// that already reaches `from` now reaches the new target, so a remembered
// answer there is no longer current.
void Points::copyInvalidateAbove(unsigned from) {
  const unsigned stamp = copyFresh();
  std::vector<unsigned> st;
  for (unsigned p : copyPred[from]) {
    p = copyFind(p);
    if (p >= copyMark.size())
      copyMark.resize(p + 1);
    if (copyMark[p] == stamp)
      continue;
    copyMark[p] = stamp;
    st.push_back(p);
  }
  while (!st.empty()) {
    const unsigned x = st.back();
    st.pop_back();
    if (x < copyHave.size() && copyHave[x]) {
      copyHave[x] = 0;
      copyHit[x].clear();
    }
    for (unsigned p : copyPred[x]) {
      p = copyFind(p);
      if (p >= copyMark.size())
        copyMark.resize(p + 1);
      if (copyMark[p] == stamp)
        continue;
      copyMark[p] = stamp;
      st.push_back(p);
    }
  }
}

// Adding the edge `from` -> `to` closes a cycle: `to` already reaches `from`.
// The new component is every object that is both a descendant of `to` and an
// ancestor of `from`. Each of those reaches the others once the edge exists.
void Points::mergeCopyCycle(unsigned from, unsigned to) {
  const unsigned markD = copyFresh();
  std::vector<unsigned> desc;
  std::vector<unsigned> st{to};
  if (to >= copyMark.size())
    copyMark.resize(to + 1);
  copyMark[to] = markD;
  while (!st.empty()) {
    const unsigned x = st.back();
    st.pop_back();
    desc.push_back(x);
    for (unsigned y : copySucc[x]) {
      y = copyFind(y);
      if (y >= copyMark.size())
        copyMark.resize(y + 1);
      if (copyMark[y] != markD) {
        copyMark[y] = markD;
        st.push_back(y);
      }
    }
  }
  std::vector<char> isDesc(copyRep.size());
  for (unsigned x : desc) {
    if (x >= isDesc.size())
      isDesc.resize(x + 1);
    isDesc[x] = 1;
  }
  const unsigned markA = copyFresh();
  st.clear();
  st.push_back(from);
  if (from >= copyMark.size())
    copyMark.resize(from + 1);
  copyMark[from] = markA;
  std::vector<unsigned> S;
  if (from < isDesc.size() && isDesc[from])
    S.push_back(from);
  while (!st.empty()) {
    const unsigned x = st.back();
    st.pop_back();
    for (unsigned y : copyPred[x]) {
      y = copyFind(y);
      if (y >= copyMark.size())
        copyMark.resize(y + 1);
      if (copyMark[y] == markA)
        continue;
      copyMark[y] = markA;
      if (y < isDesc.size() && isDesc[y])
        S.push_back(y);
      st.push_back(y);
    }
  }
  if (S.empty())
    return;
  unsigned r = S[0];
  for (unsigned n : S)
    if (n < r)
      r = n;
  std::vector<char> inS(copyRep.size());
  std::vector<unsigned> outE, inE;
  for (unsigned n : S) {
    if (n >= inS.size())
      inS.resize(n + 1);
    inS[n] = 1;
  }
  for (unsigned n : S) {
    for (unsigned m : copySucc[n]) {
      m = copyFind(m);
      if (m >= inS.size())
        inS.resize(m + 1);
      if (!inS[m])
        outE.push_back(m);
    }
    for (unsigned m : copyPred[n]) {
      m = copyFind(m);
      if (m >= inS.size())
        inS.resize(m + 1);
      if (!inS[m])
        inE.push_back(m);
    }
    copySucc[n].clear();
    copyPred[n].clear();
  }
  for (unsigned n : S)
    copyRep[n] = r;
  copyRep[r] = r;
  auto rewriteSucc = [&](unsigned m) {
    std::vector<unsigned> keep;
    bool has = false;
    for (unsigned s : copySucc[m]) {
      s = copyFind(s);
      if (s == r) {
        has = true;
        continue;
      }
      if (s < inS.size() && inS[s])
        continue;
      keep.push_back(s);
    }
    if (!has)
      keep.push_back(r);
    copySucc[m].swap(keep);
  };
  auto rewritePred = [&](unsigned m) {
    std::vector<unsigned> keep;
    bool has = false;
    for (unsigned p : copyPred[m]) {
      p = copyFind(p);
      if (p == r) {
        has = true;
        continue;
      }
      if (p < inS.size() && inS[p])
        continue;
      keep.push_back(p);
    }
    if (!has)
      keep.push_back(r);
    copyPred[m].swap(keep);
  };
  std::unordered_set<unsigned> seen;
  for (unsigned m : outE) {
    m = copyFind(m);
    if (m == r || !seen.insert(m).second)
      continue;
    copySucc[r].push_back(m);
    rewritePred(m);
  }
  seen.clear();
  for (unsigned m : inE) {
    m = copyFind(m);
    if (m == r || !seen.insert(m).second)
      continue;
    rewriteSucc(m);
    copyPred[r].push_back(m);
  }
  // Component identities moved. Remembered reachability names the old roots.
  copyDrop();
}

// Whether copies already carry cells of `from` into `to`, directly or
// through other objects.
bool Points::copiesInto(unsigned from, unsigned to) {
  if (from == to)
    return true;
  from = copyFind(from);
  to = copyFind(to);
  if (from == to)
    return true;
  if (from >= copyHave.size() || !copyHave[from])
    copyFill(from);
  return copyHit[from].test(to);
}

void Points::addCopyEdge(unsigned from, unsigned to) {
  if (from == to)
    return;
  from = copyFind(from);
  to = copyFind(to);
  if (from == to)
    return;
  // The same object pair is asked once per pointed-to offset. The answer
  // does not change after the first time, and reachability only grows.
  const uint64_t key = (static_cast<uint64_t>(from) << 32) | to;
  if (!copyAsked.insert(key).second)
    return;
  if (from >= copyHave.size() || !copyHave[from])
    copyFill(from);
  if (copyHit[from].test(to))
    return;
  if (to >= copyHave.size() || !copyHave[to])
    copyFill(to);
  if (copyHit[to].test(from)) {
    mergeCopyCycle(from, to);
    from = copyFind(from);
    to = copyFind(to);
    if (from == to)
      return;
  }
  copySucc[from].push_back(to);
  copyPred[to].push_back(from);
  if (from < copyHave.size() && copyHave[from]) {
    copyHit[from].set(to);
    if (to < copyHave.size() && copyHave[to])
      copyHit[from] |= copyHit[to];
    else {
      copyHave[from] = 0;
      copyHit[from].clear();
    }
  }
  copyInvalidateAbove(from);
}

// A byte copy of known length carries the cell at distance k from the
// source pointer to the cell at distance k from the destination pointer,
// for every k below the length. One node per copy and distance stands
// between them, so a copy whose pointers may each point to many places
// costs the sum, not the product, of those places.
unsigned Points::copyMid(unsigned ci, int64_t k) {
  Copy &cp = copies[ci];
  auto it = cp.mid.find(k);
  if (it != cp.mid.end())
    return it->second;
  unsigned m = newNode(nullptr, 0);
  cp.mid.emplace(k, m);
  const std::vector<std::pair<Loc, bool>> dsts = cp.dsts;
  for (const auto &d : dsts) {
    if (d.second || d.first.off == Any || k == Any)
      edge(m, location(d.first.obj, Any));
    else
      edge(m, location(d.first.obj, d.first.off + k));
  }
  return m;
}

// A byte copy of unknown length may carry any cell of a source object to
// any offset of a destination object: it carries the source objects as
// wholes to the destination objects as wholes. Tracking its alignment
// would make every destination hold every source's cells at the
// alignment's shift, and through chains of such copies at every
// composition of shifts; the witness walk, which has the copy's pointer
// offsets, still follows the copy cell by cell.
unsigned Points::copyWhole(unsigned ci) {
  Copy &cp = copies[ci];
  if (cp.whole)
    return cp.whole;
  cp.whole = newNode(nullptr, 0);
  return cp.whole;
}

void Points::copySrc(unsigned ci, unsigned srcLoc) {
  Copy &cp = copies[ci];
  if (!cp.srcSeen.insert(srcLoc).second)
    return;
  const Loc s = locs[srcLoc];
  cp.srcs.push_back(s);
  if (cp.len < 0) {
    edge(unionNode(s.obj), copyWhole(ci));
    return;
  }
  // A destination this source already feeds, directly or through other
  // copies, closes a cycle of copies: repeated, it would carry cells to
  // every offset. Such a destination takes the source as a whole.
  for (auto &d : cp.dsts) {
    if (!d.second && copiesInto(d.first.obj, s.obj)) {
      d.second = true;
      addWrite(d.first.obj, Any, -1, cp.call, cp.ctx);
      const std::map<int64_t, unsigned> mids = cp.mid;
      for (const auto &km : mids)
        edge(km.second, location(d.first.obj, Any));
    }
    addCopyEdge(s.obj, d.first.obj);
  }
  if (s.off == Any) {
    edge(unionNode(s.obj), copyMid(ci, Any));
    return;
  }
  copyRel[s.obj].push_back({ci, s.off});
  const std::vector<unsigned> ls = objLocs[s.obj];
  for (unsigned l : ls) {
    const int64_t x = locs[l].off;
    if (x == Any)
      edge(l, copyMid(ci, Any));
    else if (x >= s.off && x < s.off + cp.len)
      edge(l, copyMid(ci, x - s.off));
  }
}

void Points::copyDst(unsigned ci, unsigned dstLoc) {
  Copy &cp = copies[ci];
  if (!cp.dstSeen.insert(dstLoc).second)
    return;
  const Loc d = locs[dstLoc];
  if (!writable(d.obj))
    return;
  if (cp.len < 0) {
    addWrite(d.obj, d.off, -1, cp.call, cp.ctx);
    cp.dsts.push_back({d, true});
    edge(copyWhole(ci), location(d.obj, Any));
    return;
  }
  bool whole = d.off == Any;
  for (const Loc &s : cp.srcs) {
    if (!whole && copiesInto(d.obj, s.obj))
      whole = true;
    addCopyEdge(s.obj, d.obj);
  }
  addWrite(d.obj, whole ? Any : d.off, whole ? -1 : cp.len, cp.call, cp.ctx);
  cp.dsts.push_back({d, whole});
  const std::map<int64_t, unsigned> mids = cp.mid;
  for (const auto &km : mids) {
    if (whole || km.first == Any)
      edge(km.second, location(d.obj, Any));
    else
      edge(km.second, location(d.obj, d.off + km.first));
  }
}

void Points::materializeUsers(unsigned n) {
  if (usersDone[n])
    return;
  usersDone[n] = true;
  const llvm::Value *v = nodeVal[n];
  if (!v)
    return;
  std::vector<const llvm::User *> users(v->user_begin(), v->user_end());
  for (const llvm::User *Us : users) {
    if (const auto *I = llvm::dyn_cast<llvm::Instruction>(Us)) {
      // The body of a function analysed per call site is registered as a
      // whole when a context is entered.
      if (cloned.count(I->getFunction()))
        continue;
      if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(I)) {
        registerStore(St, 0);
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(I)) {
        if (pointerLike(L->getType()))
          node(L, 0);
      } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(I)) {
        registerCall(C, 0);
      } else if (pointerLike(I->getType()) &&
                 (llvm::isa<llvm::GEPOperator>(I) || llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::PHINode>(I) ||
                  llvm::isa<llvm::SelectInst>(I) || llvm::isa<llvm::FreezeInst>(I))) {
        node(I, 0);
      }
    } else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(Us)) {
      if (pointerLike(CE->getType())) {
        unsigned cn = node(CE, 0);
        materializeUsers(cn);
      }
    }
  }
}

unsigned Points::sliceFeed(unsigned sid) {
  if (sliceOf[sid].haveFeed)
    return sliceOf[sid].feed;
  const unsigned f = newNode(nullptr, 0);
  sliceOf[sid].haveFeed = true;
  sliceOf[sid].feed = f;
  return f;
}

void Points::feedCopy(unsigned sid, const PtsSet &ids) {
  if (!isSliceId(sid) || ids.empty())
    return;
  const unsigned feed = sliceFeed(sid);
  for (unsigned id : ids) {
    if (isSliceId(id) || id >= isLoc.size() || !isLoc[id])
      continue;
    const Loc lc = locs[id];
    if (objs[lc.obj].kind == Kind::Func)
      continue;
    if (lc.off != Any) {
      edge(id, feed);
      edge(location(lc.obj, Any), feed);
    } else {
      edge(unionNode(lc.obj), feed);
    }
  }
}

void Points::shareLoads(unsigned sid, unsigned loader, unsigned n) {
  if (n == loader)
    return;
  auto it = loadSum.find(loader);
  if (it == loadSum.end())
    return;
  auto li = loadsAt.find(n);
  if (li == loadsAt.end())
    return;
  const unsigned summary = it->second;
  const std::vector<unsigned> loads = li->second;
  for (unsigned L : loads) {
    edge(summary, L);
    if (!isSliceId(sid))
      continue;
    const auto *I = llvm::cast<llvm::Instruction>(nodeVal[L]);
    if (!sliceOf[sid].factSeen.insert(Slice::FactKey{I, 0, 'L'}).second)
      continue;
    sliceOf[sid].facts.push_back(Slice::Fact{I, 0, 0, 'L'});
  }
}

void Points::attachLoads(unsigned sid, unsigned n) {
  auto li = loadsAt.find(n);
  if (li == loadsAt.end())
    return;
  const unsigned feed = sliceFeed(sid);
  const std::vector<unsigned> loads = li->second;
  for (unsigned L : loads) {
    edge(feed, L);
    if (!sliceOf[sid].factSeen.insert(Slice::FactKey{llvm::cast<llvm::Instruction>(nodeVal[L]), 0, 'L'}).second)
      continue;
    sliceOf[sid].facts.push_back(Slice::Fact{llvm::cast<llvm::Instruction>(nodeVal[L]), 0, 0, 'L'});
  }
}

void Points::hookCells(unsigned n, const PtsSet &got, bool doLoads) {
  if (got.empty() || !hasHooks(n))
    return;
  auto li = loadsAt.find(n);
  if (doLoads && li != loadsAt.end()) {
    std::vector<unsigned> loads = li->second;
    for (unsigned id : got) {
      if (id >= isLoc.size() || !isLoc[id])
        continue;
      for (unsigned L : loads)
        linkLoad(n, L, id);
    }
  }
  auto si = storesAt.find(n);
  if (si != storesAt.end()) {
    const std::vector<StoreAt> stores = si->second;
    bool ptrStore = false;
    for (const StoreAt &st : stores)
      if (st.value != UINT32_MAX)
        ptrStore = true;
    // One edge from the summary carries every stored pointer into the cell.
    const unsigned s = ptrStore ? storeSummary(n) : 0;
    for (unsigned id : got) {
      if (id >= isLoc.size() || !isLoc[id])
        continue;
      if (!writable(locs[id].obj))
        continue;
      for (const StoreAt &st : stores)
        addWrite(locs[id].obj, locs[id].off,
                 static_cast<int64_t>(DL.getTypeStoreSize(st.inst->getValueOperand()->getType())), st.inst, st.ctx);
      if (ptrStore) {
        edge(s, id);
        bridgeCell(id);
      }
    }
  }
  auto ci = callsAt.find(n);
  if (ci != callsAt.end()) {
    const std::vector<CallAt> calls = ci->second;
    for (unsigned id : got) {
      if (id >= isLoc.size() || !isLoc[id])
        continue;
      for (const CallAt &ca : calls)
        if (const llvm::Function *F = target(ca.call, locs[id].obj))
          bindCall(ca.call, ca.ctx, F);
    }
  }
  auto ei = escapesAt.find(n);
  if (ei != escapesAt.end()) {
    const std::vector<const llvm::CallBase *> calls = ei->second;
    for (unsigned id : got) {
      if (id >= isLoc.size() || !isLoc[id])
        continue;
      for (const llvm::CallBase *C : calls)
        escape(locs[id].obj, C);
    }
  }
  auto di = copyDstAt.find(n);
  if (di != copyDstAt.end()) {
    const std::vector<unsigned> cis = di->second;
    for (unsigned c : cis)
      for (unsigned d : got) {
        if (d >= isLoc.size() || !isLoc[d])
          continue;
        copyDst(c, d);
      }
  }
  auto sri = copySrcAt.find(n);
  if (sri != copySrcAt.end()) {
    const std::vector<unsigned> cis = sri->second;
    for (unsigned c : cis)
      for (unsigned x : got) {
        if (x >= isLoc.size() || !isLoc[x])
          continue;
        copySrc(c, x);
      }
  }
  auto mi = memsetAt.find(n);
  if (mi != memsetAt.end()) {
    const std::vector<CallAt> calls = mi->second;
    for (unsigned d : got) {
      if (d >= isLoc.size() || !isLoc[d])
        continue;
      for (const CallAt &ca : calls)
        addWrite(locs[d].obj, locs[d].off, memsetLen(ca.call, ca.ctx), ca.call, ca.ctx);
    }
  }
}

void Points::onPts(unsigned n, const PtsSet &fresh) {
  if (fresh.empty())
    return;
  // A slice is one memory. Its cells are not built here. A concrete location
  // that names the same object and offset is bridged to that memory.
  bool anySlice = false;
  for (unsigned id : fresh)
    if (isSliceId(id)) {
      anySlice = true;
      break;
    }
  if (!anySlice) {
    hookCells(n, fresh);
    return;
  }
  PtsSet concrete;
  for (unsigned id : fresh) {
    if (isSliceId(id))
      onPtsSlice(n, id);
    else
      concrete.set(id);
  }
  hookCells(n, concrete);
}

// Strongly connected components of the edges between classes, by
// Tarjan's search, iterative. With copies only, a component is a set of
// classes that hold the same set at the fixpoint; with offsets too, an
// offset edge inside a component is pointer arithmetic on a cycle.
std::vector<unsigned> Points::components(bool withOffsets) {
  const unsigned N = static_cast<unsigned>(pts.size());
  std::vector<unsigned> index(N, 0), low(N, 0), comp(N, 0);
  std::vector<bool> onStack(N, false);
  std::vector<unsigned> stack;
  unsigned next = 1, ncomp = 0;
  struct Frame {
    unsigned n;
    size_t ci;
    size_t gi;
    bool copies;
  };
  for (unsigned root = 0; root < N; ++root) {
    if (index[root] || find(root) != root)
      continue;
    std::vector<Frame> frames;
    auto enterN = [&](unsigned n) {
      index[n] = low[n] = next++;
      stack.push_back(n);
      onStack[n] = true;
      frames.push_back(Frame{n, 0, 0, true});
    };
    enterN(root);
    while (!frames.empty()) {
      Frame &f = frames.back();
      unsigned n = f.n;
      unsigned child = N;
      if (f.copies) {
        const std::vector<unsigned> &seq = copyTo[n].seq;
        if (f.ci < seq.size()) {
          child = find(seq[f.ci]);
          ++f.ci;
        } else {
          f.copies = false;
        }
      }
      if (child == N && !f.copies && withOffsets) {
        if (f.gi < gepTo[n].size()) {
          child = find(gepTo[n][f.gi].to);
          ++f.gi;
        }
      }
      if (child != N) {
        if (!index[child]) {
          enterN(child);
        } else if (onStack[child]) {
          low[n] = std::min(low[n], index[child]);
        }
        continue;
      }
      // All successors done.
      if (low[n] == index[n]) {
        ++ncomp;
        unsigned m;
        do {
          m = stack.back();
          stack.pop_back();
          onStack[m] = false;
          comp[m] = ncomp;
        } while (m != n);
      }
      frames.pop_back();
      if (!frames.empty())
        low[frames.back().n] = std::min(low[frames.back().n], low[n]);
    }
  }
  return comp;
}

// Classes on a cycle of copy edges become one class.
void Points::collapse() {
  const std::vector<unsigned> comp = components(false);
  const unsigned N = static_cast<unsigned>(comp.size());
  std::vector<unsigned> first(N + 1, N);
  for (unsigned n = 0; n < N; ++n) {
    if (find(n) != n || comp[n] == 0)
      continue;
    unsigned &f = first[comp[n]];
    if (f == N)
      f = n;
    else
      unify(f, n);
  }
}

// An offset edge inside a component of the copy and offset edges is
// pointer arithmetic on a cycle: a pointer stepped along it addresses
// every offset of its objects, so from then on that edge yields the
// object as a whole. Edges added later may close new cycles; the search
// is repeated as the graph grows.
void Points::findCycles() {
  collapse();
  const std::vector<unsigned> comp = components(true);
  const unsigned N = static_cast<unsigned>(comp.size());
  // Mark, then apply. Applying walks offsets and can append edges; a
  // reference into gepTo would not survive that, and an unmarked copy of
  // the edge would be applied again every round.
  for (unsigned n = 0; n < N; ++n) {
    if (find(n) != n)
      continue;
    std::vector<Edge> again;
    const size_t cnt = gepTo[n].size();
    for (size_t i = 0; i < cnt; ++i) {
      Edge &e = gepTo[n][i];
      const unsigned t = find(e.to);
      if (e.cyclic || t >= N || comp[t] != comp[n])
        continue;
      e.cyclic = true;
      const unsigned tgt = find(e.to);
      if (tgt < symAt.size())
        for (Sym &s : symAt[tgt])
          if (find(s.src) == n && s.off == e.off)
            s.cyclic = true;
      again.push_back(e);
    }
    for (const Edge &e : again) {
      if (!pts[n].empty()) {
        const PtsSet cur = pts[n];
        apply(e, cur, n);
      }
    }
  }
}

void Points::solve() {
  // The witness asks the same solution many times. Nothing is recomputed
  // while the worklist is empty and every indirect call has been judged.
  if (atFix && work.empty() && drainedCalls == indirectCalls.size())
    return;
  // What a query can observe, before: a solve that moves none of it
  // leaves the solution -- and every cache keyed by epoch -- standing.
  const size_t nodes0 = pts.size(), locs0 = locs.size(), ctxs0 = ctxs.size(), writes0 = nWrites,
               ptrLoads0 = nPtrLoads, escapes0 = nEscapes, ext0 = externalCalls.size(),
               res0 = resolvedCalls.size();
  bool moved = false;
  solving = true;
  // Rounds. Each round first finds the cycles of the graph as it stands,
  // so that an offset edge on a cycle yields whole objects before it is
  // ever applied in that round; then carries what every node gained along
  // its edges to a fixpoint; then runs the hooks of the nodes that gained
  // something, which add the edges and nodes the gain implies. Those are
  // carried in the next round, after the cycles they close are found.
  for (;;) {
    if (work.empty()) {
      if (!imgQ.empty()) {
        symbolicHooks();
        if (!work.empty() || !imgQ.empty())
          continue;
      }
      // Calls through pointers that hold no function in the solution so
      // far reach code with no body here.
      bool more = false;
      const std::vector<CallAt> calls = indirectCalls;
      for (const CallAt &ca : calls) {
        if (externalCalls.count({ca.call, ca.ctx}) || resolvedCalls.count({ca.call, ca.ctx}))
          continue;
        bool any = false;
        const PtsSet held = P(node(ca.call->getCalledOperand(), ca.ctx));
        for (unsigned id : held) {
          if (isSliceId(id)) {
            ensureSlice(id);
            const std::vector<unsigned> funcs = sliceOf[id].funcs;
            for (unsigned o : funcs)
              if (target(ca.call, o)) {
                any = true;
                break;
              }
          } else if (target(ca.call, locs[id].obj)) {
            any = true;
          }
          if (any)
            break;
        }
        if (any) {
          // Points-to sets only grow, so a call that holds a function keeps it.
          resolvedCalls.insert({ca.call, ca.ctx});
          continue;
        }
        treatExternal(ca.call, ca.ctx);
        more = true;
      }
      // A call registered while this drain ran was not in the snapshot.
      if (!more && indirectCalls.size() == calls.size())
        break;
      if (work.empty())
        continue;
    }
    if (nEdges != cycSeen) {
      cycSeen = nEdges;
      findCycles();
    }
    std::vector<unsigned> touched;
    while (!work.empty()) {
      const unsigned raw = work.back();
      work.pop_back();
      inWork[raw] = false;
      // A class joined since it was queued is processed as its class.
      const unsigned n = find(raw);
      if (n != raw) {
        if (inWork[n])
          continue;
        inWork[n] = false;
      }
      PtsSet fresh = std::move(delta[n]);
      delta[n].clear();
      if (fresh.empty())
        continue;
      moved = true;
      seen[n] |= fresh;
      if (gained[n].empty())
        touched.push_back(n);
      gained[n] |= fresh;
      const std::vector<unsigned> targets = copyTo[n].seq;
      Edge e;
      for (unsigned t : targets) {
        e.to = t;
        apply(e, fresh, n);
      }
      if (n < gepTo.size() && !gepTo[n].empty()) {
        const std::vector<Edge> geps = gepTo[n];
        for (const Edge &ge : geps)
          apply(ge, fresh, n);
      }
      syncCopyUsers(n, fresh);
    }
    // A class joined this round has its whole set in gained (unify);
    // its members' hooks see the elements the other class brought.
    for (unsigned r : merged)
      if (find(r) == r && !gained[r].empty())
        touched.push_back(r);
    merged.clear();
    std::sort(touched.begin(), touched.end());
    touched.erase(std::unique(touched.begin(), touched.end()), touched.end());
    for (unsigned n : touched) {
      if (find(n) != n)
        continue;
      PtsSet fresh = gained[n];
      gained[n].clear();
      if (members[n].empty()) {
        materializeUsers(n);
        onPts(n, fresh);
        continue;
      }
      const std::vector<unsigned> ms = members[n];
      for (unsigned m : ms) {
        materializeUsers(m);
        onPts(m, fresh);
      }
    }
    symbolicHooks();
  }
  solving = false;
  drainedCalls = indirectCalls.size();
  atFix = true;
  if (moved || pts.size() != nodes0 || locs.size() != locs0 || ctxs.size() != ctxs0 || nWrites != writes0 ||
      nPtrLoads != ptrLoads0 || nEscapes != escapes0 || externalCalls.size() != ext0 ||
      resolvedCalls.size() != res0)
    ++epoch;
}

void Points::saturate() {
  // A global is named when a reached function or another reached global
  // mentions it. A global nothing reached mentions is not read or written.
  // A function runs only when a harness export reaches it, or a global
  // constructor does, or a call the solution resolves does. A function
  // with no such path does not run, so its stores are not constraints.
  std::vector<const llvm::Function *> q;
  std::unordered_set<const llvm::Function *> known;
  auto add = [&](const llvm::Function *F) {
    F = bodyOf(F);
    if (!F || F->isDeclaration())
      return;
    if (!known.insert(F).second)
      return;
    q.push_back(F);
  };
  bool rooted = false;
  for (const llvm::Module *Mod : {&M, &U}) {
    if (hooks.harness)
      for (const llvm::Function &F : *Mod)
        if (hooks.harness(&F)) {
          add(&F);
          rooted = true;
        }
    for (const char *name : {"llvm.global_ctors", "llvm.global_dtors"}) {
      const llvm::GlobalVariable *GV = Mod->getNamedGlobal(name);
      if (!GV || !GV->hasInitializer())
        continue;
      const auto *A = llvm::dyn_cast<llvm::ConstantArray>(GV->getInitializer());
      if (!A)
        continue;
      for (const llvm::Use &U : A->operands()) {
        const auto *S = llvm::dyn_cast<llvm::ConstantStruct>(U.get());
        if (!S || S->getNumOperands() < 2)
          continue;
        if (const auto *F = llvm::dyn_cast<llvm::Function>(S->getOperand(1)->stripPointerCasts()))
          add(F);
      }
    }
  }
  // No harness was given: every function is a possible entry, as before.
  if (!rooted) {
    for (const llvm::Module *Mod : {&M, &U})
      for (const llvm::Function &F : *Mod)
        add(&F);
  }
  auto enlist = [&](const llvm::Function *F) {
    if (cloned.count(F)) {
      demandFn(F);
      if (ctxsOf[F].empty())
        enter(F, 0);
    } else if (!entered.count({F, 0})) {
      enter(F, 0);
    }
    for (const llvm::Instruction &I : llvm::instructions(*F)) {
      const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!C || C->isInlineAsm())
        continue;
      if (const llvm::Function *D = C->getCalledFunction())
        add(D);
    }
  };
  // Enter the reached set, solve, and enter whatever calls the solution
  // newly resolves. Then carry every node, so a later query adds nothing.
  for (;;) {
    const size_t knownBefore = known.size();
    while (!q.empty()) {
      const llvm::Function *F = q.back();
      q.pop_back();
      enlist(F);
    }
    const size_t ptsBefore = pts.size();
    const size_t nBefore = ptsBefore;
    for (unsigned n = 0; n < nBefore; ++n)
      if (demanded.insert(n).second)
        push(n);
    solve();
    std::vector<const llvm::Function *> bound;
    bound.reserve(callersOf.size());
    for (const auto &kv : callersOf)
      bound.push_back(kv.first);
    for (const llvm::Function *F : bound)
      add(F);
    if (q.empty() && known.size() == knownBefore && pts.size() == ptsBefore)
      break;
  }
}

void Points::expandHeld(unsigned id, llvm::SparseBitVector<> &one, std::unordered_set<unsigned> &seen) {
  if (!seen.insert(id).second)
    return;
  if (!isSliceId(id)) {
    one.set(id);
    return;
  }
  // A copy denotes the source set at the moment it is read, including every
  // element added after the copy edge carried the reference.
  if (!sliceOf[id].cyclic && sliceOf[id].off == 0 && sliceOf[id].src != UINT32_MAX) {
    if (!sliceOf[id].indexed)
      materializeSlice(id);
    const PtsSet roots = pts[find(sliceOf[id].src)];
    for (unsigned inner : roots)
      expandHeld(inner, one, seen);
    const std::vector<unsigned> funcs = sliceOf[id].funcs;
    for (unsigned fo : funcs) {
      const unsigned lid = location(fo, 0);
      if (!seen.insert(lid).second)
        continue;
      one.set(lid);
    }
    return;
  }
  ensureSlice(id);
  if (sliceOf[id].src == UINT32_MAX) {
    materializeSlice(id);
    const auto cells = sliceOf[id].cells;
    const auto funcs = sliceOf[id].funcs;
    for (const auto &cell : cells)
      one.set(quietId(cell.first, cell.second));
    for (unsigned fo : funcs)
      one.set(location(fo, 0));
    return;
  }
  const PtsSet roots = pts[find(sliceOf[id].src)];
  const int64_t off = sliceOf[id].off;
  const bool cyclic = sliceOf[id].cyclic;
  for (unsigned inner : roots) {
    if (isSliceId(inner)) {
      const unsigned c = (off == 0 && !cyclic) ? inner : composeSlice(inner, off, cyclic);
      expandHeld(c, one, seen);
      continue;
    }
    if (inner >= isLoc.size() || !isLoc[inner])
      continue;
    const Loc lc = locs[inner];
    if (objs[lc.obj].kind == Kind::Func) {
      const unsigned lid = location(lc.obj, 0);
      if (seen.insert(lid).second)
        one.set(lid);
      continue;
    }
    int64_t noff = Any;
    if (!cyclic && off != Any && lc.off != Any) {
      const __int128 sum = static_cast<__int128>(lc.off) + off;
      if (sum <= INT64_MAX && sum >= INT64_MIN)
        noff = static_cast<int64_t>(sum);
    }
    const unsigned q = (noff == lc.off) ? inner : quietId(lc.obj, noff);
    one.set(q);
  }
}

llvm::SparseBitVector<> Points::unionPts(const std::vector<unsigned> &nodes) {
  for (unsigned n : nodes)
    if (demanded.insert(n).second)
      push(n);
  solve();
  if (queryEpoch.size() < pts.size()) {
    queryEpoch.resize(pts.size());
    querySet.resize(pts.size());
  }
  llvm::SparseBitVector<> out;
  for (unsigned n : nodes) {
    if (queryEpoch[n] != epoch) {
      llvm::SparseBitVector<> one;
      const PtsSet held = P(n);
      bool sliced = false;
      for (unsigned id : held)
        if (isSliceId(id)) {
          sliced = true;
          break;
        }
      if (!sliced) {
        for (unsigned id : held)
          one.set(id);
      } else {
        std::unordered_set<unsigned> seen;
        for (unsigned id : held)
          expandHeld(id, one, seen);
      }
      querySet[n] = std::move(one);
      queryEpoch[n] = epoch;
    }
    out |= querySet[n];
  }
  return out;
}

const llvm::SparseBitVector<> &Points::storeOf(const llvm::Value *v, const llvm::CallBase *site,
                                               llvm::SparseBitVector<> out) {
  if (ofEpoch != epoch) {
    ofCache.clear();
    ofEpoch = epoch;
  }
  auto &slot = ofCache[{v, site}];
  slot = std::move(out);
  return slot;
}

const llvm::SparseBitVector<> &Points::of(const llvm::Value *v) {
  static const llvm::SparseBitVector<> empty;
  if (!v || !pointerLike(v->getType()))
    return empty;
  if (atFix && ofEpoch == epoch) {
    auto it = ofCache.find({v, nullptr});
    if (it != ofCache.end())
      return it->second;
  }
  const llvm::Function *F = fnOf(v);
  if (!F || !cloned.count(F))
    return storeOf(v, nullptr, unionPts({node(v, 0)}));
  demandFn(F);
  if (ctxsOf[F].empty())
    enter(F, 0);
  // Solving may enter further contexts; ask until none appear.
  llvm::SparseBitVector<> out;
  for (;;) {
    const std::vector<unsigned> xs = ctxsOf[F];
    std::vector<unsigned> ns;
    for (unsigned x : xs)
      ns.push_back(node(v, x));
    out = unionPts(ns);
    if (ctxsOf[F].size() == xs.size())
      break;
  }
  return storeOf(v, nullptr, std::move(out));
}

const llvm::SparseBitVector<> &Points::of(const llvm::Value *v, const llvm::CallBase *site) {
  static const llvm::SparseBitVector<> empty;
  if (!v || !pointerLike(v->getType()))
    return empty;
  const llvm::Function *F = fnOf(v);
  if (!F || !cloned.count(F) || !site)
    return of(v);
  if (atFix && ofEpoch == epoch) {
    auto it = ofCache.find({v, site});
    if (it != ofCache.end())
      return it->second;
  }
  demandFn(F);
  if (ctxsOf[F].empty())
    enter(F, 0);
  llvm::SparseBitVector<> out;
  for (;;) {
    const std::vector<unsigned> xs = ctxsOf[F];
    std::vector<unsigned> ns, all;
    for (unsigned x : xs) {
      unsigned n = node(v, x);
      all.push_back(n);
      if (ctxs[x].site == site)
        ns.push_back(n);
    }
    out = unionPts(ns.empty() ? all : ns);
    if (ctxsOf[F].size() == xs.size())
      break;
  }
  return storeOf(v, site, std::move(out));
}

// The bounds are the distinct ends of the writes; a write of known length
// covers the regions from its start to the one before its end, a write of
// unknown length every region from its start. A write of zero bytes
// covers none. Writes at offset Any cover every region.
const Points::Regions &Points::regions(unsigned o) {
  solve();
  realize(o);
  if (o >= regionsOf.size())
    regionsOf.resize(o + 1);
  Regions &r = regionsOf[o];
  if (r.epoch == epoch)
    return r;
  r = Regions();
  r.epoch = epoch;
  const std::vector<Write> &ws = writesOf[o];
  auto toDef = [](const Write &w) { return Def{w.inst, w.ctx, w.off, w.len}; };
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
  const size_t n = r.bounds.size() + 1;  // regions -1 .. bounds.size()-1
  while (r.leaves < n)
    r.leaves <<= 1;
  r.tree.assign(2 * r.leaves, {});
  for (const Write &w : ws) {
    if (w.len == 0)
      continue;
    const Def d = toDef(w);
    if (w.off == Any) {
      r.any.push_back(d);
      continue;
    }
    // Leaves [lo, hi] hold the regions the write covers.
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

const std::vector<Points::Write> &Points::writes(unsigned o) {
  solve();
  realize(o);
  return writesOf[o];
}

const std::vector<Points::PtrLoad> &Points::ptrLoads(unsigned o) {
  solve();
  realize(o);
  return ptrLoadsOf[o];
}

const std::vector<const llvm::CallBase *> &Points::escapes(unsigned o) {
  solve();
  realize(o);
  return escapesOf[o];
}

std::vector<const llvm::Function *> Points::callees(const llvm::CallBase *C) {
  std::vector<const llvm::Function *> out;
  if (C->isInlineAsm())
    return out;
  out = calleesOf(C);
  if (!C->getCalledFunction())
    for (unsigned id : of(C->getCalledOperand()))
      if (const llvm::Function *F = target(C, loc(id).obj))
        out.push_back(F);
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

bool Points::unresolved(const llvm::CallBase *C) {
  if (C->isInlineAsm())
    return true;
  if (const auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(C))
    if (II->isAssumeLikeIntrinsic())
      return false;
  if (C->doesNotAccessMemory())
    return false;
  if (const llvm::Function *D0 = C->getCalledFunction()) {
    const llvm::Function *D = bodyOf(D0);
    return !D || D->isDeclaration();
  }
  for (unsigned id : of(C->getCalledOperand()))
    if (target(C, loc(id).obj))
      return false;
  return true;
}

const std::vector<const llvm::CallBase *> &Points::callers(const llvm::Function *F) {
  static const std::vector<const llvm::CallBase *> none;
  const llvm::Function *B = bodyOf(F);
  if (!B)
    return none;
  solve();
  auto it = callersOf.find(B);
  return it == callersOf.end() ? none : it->second;
}

} // namespace chain
