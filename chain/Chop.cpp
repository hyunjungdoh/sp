#include "Chop.hpp"

#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"

#include <algorithm>
#include <cstdint>
#include <deque>
#include <functional>
#include <limits>
#include <queue>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {

std::string classSpec(const llvm::Function *F) {
  if (!F || !F->hasName())
    return {};
  static std::unordered_map<const llvm::Function *, std::string> memo;
  if (auto it = memo.find(F); it != memo.end())
    return it->second;
  std::string n = F->getName().str();
  std::string pretty = llvm::demangle(n);
  std::string key;
  if (!pretty.empty() && pretty != n) {
    std::vector<std::string> parts;
    std::string cur;
    int depth = 0;
    for (size_t i = 0; i < pretty.size(); ++i) {
      char c = pretty[i];
      if (c == '<') {
        ++depth;
        cur.push_back(c);
      } else if (c == '>') {
        if (depth > 0)
          --depth;
        cur.push_back(c);
      } else if (c == ':' && depth == 0 && i + 1 < pretty.size() && pretty[i + 1] == ':') {
        parts.push_back(cur);
        cur.clear();
        ++i;
      } else
        cur.push_back(c);
    }
    if (!cur.empty())
      parts.push_back(cur);
    if (parts.size() >= 2) {
      parts.pop_back();
      bool templ = false;
      for (const std::string &p : parts)
        if (p.find('<') != std::string::npos)
          templ = true;
      if (templ) {
        for (size_t i = 0; i < parts.size(); ++i) {
          if (i)
            key += "::";
          key += parts[i];
        }
      }
    }
  }
  memo.emplace(F, key);
  return key;
}

bool fieldSpecVisible(const std::string &storeSpec, bool init, const std::string &loadSpec) {
  if (init || storeSpec.empty() || loadSpec.empty())
    return true;
  auto bare = [](const std::string &spec) {
    std::string out;
    int depth = 0;
    for (char c : spec) {
      if (c == '<') {
        ++depth;
        continue;
      }
      if (c == '>') {
        if (depth > 0)
          --depth;
        continue;
      }
      if (depth == 0)
        out.push_back(c);
    }
    return out;
  };
  if (bare(storeSpec) != bare(loadSpec))
    return true;
  return storeSpec == loadSpec;
}

namespace {

std::string baseName(llvm::StringRef p) {
  auto s = p.find_last_of("/\\");
  return (s == llvm::StringRef::npos ? p : p.drop_front(s + 1)).str();
}

bool onLine(const llvm::Instruction &I, llvm::StringRef file, unsigned line) {
  const llvm::DebugLoc &DL = I.getDebugLoc();
  if (!DL)
    return false;
  const llvm::DILocation *S = DL.get();
  while (S) {
    if (S->getLine() == line && S->getFile() && baseName(S->getFile()->getFilename()) == file)
      return true;
    S = S->getInlinedAt();
  }
  return false;
}

const llvm::Value *strip(const llvm::Value *v) {
  std::unordered_set<const llvm::Value *> seen;
  while (v && seen.insert(v).second) {
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v)) {
      v = C->getOperand(0);
      continue;
    }
    const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(v);
    if (CE && CE->isCast()) {
      v = CE->getOperand(0);
      continue;
    }
    break;
  }
  return v;
}

const llvm::Function *asFunction(const llvm::Value *v) {
  v = strip(v);
  if (!v)
    return nullptr;
  return llvm::dyn_cast<llvm::Function>(v->stripPointerCasts());
}

const llvm::Function *defined(llvm::Module &M, llvm::StringRef name) {
  if (llvm::Function *F = M.getFunction(name))
    if (!F->isDeclaration())
      return F;
  if (llvm::GlobalAlias *A = M.getNamedAlias(name)) {
    if (!A->getAliasee())
      return nullptr;
    const auto *Fn =
        llvm::dyn_cast<llvm::Function>(A->getAliasee()->stripPointerCastsAndAliases());
    if (Fn && !Fn->isDeclaration())
      return Fn;
  }
  return nullptr;
}

const llvm::Function *calledDirect(const llvm::CallBase *C, llvm::Module &upstream) {
  if (!C || C->isInlineAsm())
    return nullptr;
  const llvm::Value *v = C->getCalledOperand();
  if (!v)
    return nullptr;
  const auto *F = llvm::dyn_cast<llvm::Function>(v->stripPointerCastsAndAliases());
  if (!F)
    return nullptr;
  if (!F->isDeclaration())
    return F;
  return defined(upstream, F->getName());
}

void promote(llvm::Module &M) {
  for (llvm::Function &F : M) {
    F.removeFnAttr(llvm::Attribute::OptimizeNone);
    F.removeFnAttr(llvm::Attribute::NoInline);
  }
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;
  llvm::PassBuilder PB;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
  llvm::ModulePassManager MPM;
  MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass()));
  MPM.run(M, MAM);
}

std::string show(const llvm::Function *F) {
  std::string n = F->getName().str();
  std::string d = llvm::demangle(n);
  if (d.empty() || d == n)
    return n;
  return d;
}

// Flow-insensitive, context-insensitive, field-sensitive Andersen.
// A pointer denotes an object at a constant byte offset. Constant field
// offsets along a GEP chain are added. A variable index into an array of
// pointers or aggregates denotes every element. A constant step through a
// pointer (`p + 1`) denotes the next element only while both addresses stay
// inside one array of pointers in the object's type; a step off that array
// is not a field. A procedure list is an access path (a parameter, or one
// constant field of it) whose elements are an array of function pointers.
// The integer at offset 0 empties it only when the walk compares a load of
// that integer. A walk loads its callee from an element of that array and
// calls only what was stored
// on a path that reaches the walk with no such store; the call is an edge
// of the caller that holds the path. The address is a variable element, or
// a pointer stepped by one and fed back through a phi. A constant index is
// a fixed slot. A load from a constant struct field is not that walk. A
// procedure parameter is replaced by the actual at the call; one that
// remains contributes the functions in its points-to set. If the summary
// equations do not settle, the path's callees are every procedure stored
// into a list. A parameter that no object reaches, used as a struct, denotes the
// external object of that struct; a field GEP is resolved from it before a
// GEP derived from it is given its own external object. An indirect call
// targets the functions in the callee's points-to set.
void fillCallers(
    llvm::Module &M,
    std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> &callers,
    const std::unordered_set<const llvm::Function *> &entries) {
  const llvm::DataLayout &DL = M.getDataLayout();
  struct Mem {
    uint64_t size = 0;
  };
  struct P {
    const void *obj = nullptr;
    int64_t off = 0;
    uint8_t k = 0; // 0 exact memory, 1 any offset, 2 function
    bool operator==(const P &o) const {
      return k == o.k && obj == o.obj && (k != 0 || off == o.off);
    }
  };
  struct PH {
    size_t operator()(const P &p) const {
      return std::hash<const void *>()(p.obj) ^ (std::hash<int64_t>()(p.off) << 1) ^ p.k;
    }
  };
  using PS = std::unordered_set<P, PH>;
  std::deque<Mem> arena;
  auto mem = [&](uint64_t sz) -> Mem * {
    arena.push_back(Mem{sz});
    return &arena.back();
  };
  auto sized = [&](llvm::Type *T) -> uint64_t {
    return T && T->isSized() ? DL.getTypeAllocSize(T) : 0;
  };
  std::unordered_map<const llvm::GlobalVariable *, Mem *> gmem;
  std::unordered_map<const llvm::AllocaInst *, Mem *> amem;
  std::unordered_map<const llvm::CallBase *, Mem *> hmem;
  std::unordered_set<const Mem *> heapMems;
  std::unordered_map<const Mem *, std::unordered_set<llvm::StructType *>> objTy;
  std::unordered_map<const Mem *, llvm::Type *> memTy;
  // One external object per struct type. A proved-different struct through a
  // merged pointer is this object, not an empty points-to and not a field of
  // the heap that already has another type.
  std::unordered_map<llvm::Type *, Mem *> extOf;
  auto ext = [&](llvm::Type *T) -> Mem * {
    auto it = extOf.find(T);
    if (it != extOf.end())
      return it->second;
    Mem *m = mem(sized(T));
    memTy[m] = T;
    return extOf[T] = m;
  };
  std::function<void(const llvm::CallBase *, Mem *)> localType;
  std::unordered_set<const llvm::Function *> thin;
  std::vector<const llvm::CallBase *> indirectRet;
  for (llvm::GlobalVariable &G : M.globals()) {
    Mem *m = mem(sized(G.getValueType()));
    gmem[&G] = m;
    memTy[m] = G.getValueType();
  }
  for (llvm::Function &F : M)
    if (!F.isDeclaration())
      for (llvm::Instruction &I : llvm::instructions(F))
        if (const auto *A = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
          uint64_t n = 1;
          if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(A->getArraySize()))
            n = CI->getZExtValue();
          else
            n = 0;
          uint64_t es = sized(A->getAllocatedType());
          amem[A] = mem(n == 0 || es == 0 ? 0 : es * n);
        }

  std::unordered_map<const llvm::Value *, PS> pts;
  std::unordered_map<const Mem *, std::unordered_map<int64_t, PS>> field;
  std::unordered_map<const Mem *, PS> wild;
  std::unordered_map<const llvm::Value *, std::vector<const llvm::Value *>> copies;
  struct GepC {
    const llvm::Value *dst;
    int64_t delta;
    bool any;
    llvm::Type *src;
    // Constant pointer-sized step. Not an unbounded offset: the solve keeps
    // it only while both ends stay inside one array of pointers.
    bool step = false;
    // Unknown index into an array of pointers. On a heap that has no struct
    // type this is that array's element set, kept at offset 0.
    bool elem = false;
  };
  std::unordered_map<const llvm::Value *, std::vector<GepC>> geps;
  std::unordered_map<const llvm::Value *, std::vector<const llvm::Value *>> loads;
  std::unordered_map<const llvm::Value *, std::vector<const llvm::Value *>> storeAt;
  std::unordered_map<const llvm::Value *, std::vector<const llvm::Value *>> storeOf;
  std::unordered_map<const llvm::Value *, std::vector<const llvm::CallBase *>> callsOf;
  std::unordered_map<const Mem *, std::unordered_map<int64_t, std::unordered_set<const llvm::Value *>>>
      exactLoad;
  std::unordered_map<const Mem *, std::unordered_set<const llvm::Value *>> anyLoad;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::Value *>> rets;
  struct CH {
    size_t operator()(const std::pair<const llvm::CallBase *, const llvm::Function *> &x) const {
      return std::hash<const void *>()(x.first) ^ (std::hash<const void *>()(x.second) << 1);
    }
  };
  std::unordered_set<std::pair<const llvm::CallBase *, const llvm::Function *>, CH> hit;

  auto exact = [](const Mem *m, int64_t off) { return P{m, off, 0}; };
  auto any = [](const Mem *m) { return P{m, 0, 1}; };
  auto code = [](const llvm::Function *f) { return P{f, 0, 2}; };

  struct Item {
    const llvm::Value *v = nullptr;
    P p;
    bool field = false;
    const Mem *m = nullptr;
    int64_t off = 0;
    bool wildN = false;
  };
  std::unordered_set<const llvm::Value *> loseOff;
  std::deque<Item> wl;
  auto addPts = [&](const llvm::Value *v, P p) {
    if (!v)
      return;
    if (p.k == 0) {
      const auto *m = static_cast<const Mem *>(p.obj);
      // A positive-offset cycle is not a field. Keep the first offset that
      // reached this value and drop the ones the cycle would keep producing.
      if (loseOff.count(v))
        if (auto it = pts.find(v); it != pts.end())
          for (const P &e : it->second)
            if (e.obj == m && e.k == 0)
              return;
    }
    if (p.k == 1)
      p.off = 0;
    if (!pts[v].insert(p).second)
      return;
    wl.push_back(Item{v, p, false, nullptr, 0, false});
  };

  auto constPtr = [&](const llvm::Constant *C, P &out) -> bool {
    std::unordered_set<const llvm::Constant *> seen;
    const llvm::Constant *cur = C;
    int64_t extra = 0;
    bool lost = false;
    while (cur && seen.insert(cur).second) {
      if (const auto *Fn = llvm::dyn_cast<llvm::Function>(cur)) {
        if (Fn->isDeclaration())
          return false;
        out = code(Fn);
        return true;
      }
      if (const auto *A = llvm::dyn_cast<llvm::GlobalAlias>(cur)) {
        cur = llvm::dyn_cast<llvm::Constant>(A->getAliasee());
        continue;
      }
      if (const auto *G = llvm::dyn_cast<llvm::GlobalVariable>(cur)) {
        Mem *m = gmem[G];
        if (!m)
          return false;
        if (lost || extra < 0 || (m->size && (uint64_t)extra >= m->size))
          out = any(m);
        else
          out = exact(m, extra);
        return true;
      }
      const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(cur);
      if (!CE)
        return false;
      if (CE->isCast()) {
        cur = llvm::dyn_cast<llvm::Constant>(CE->getOperand(0));
        continue;
      }
      if (const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(CE)) {
        llvm::APInt ap(DL.getIndexSizeInBits(GEP->getPointerAddressSpace()), 0);
        if (!GEP->accumulateConstantOffset(DL, ap))
          lost = true;
        else
          extra += ap.getSExtValue();
        cur = llvm::dyn_cast<llvm::Constant>(GEP->getPointerOperand());
        continue;
      }
      return false;
    }
    return false;
  };

  auto write = [&](const Mem *m, bool isAny, int64_t off, P p) {
    if (isAny) {
      if (wild[m].insert(p).second)
        wl.push_back(Item{nullptr, p, true, m, 0, true});
    } else if (field[m][off].insert(p).second)
      wl.push_back(Item{nullptr, p, true, m, off, false});
  };

  std::function<void(Mem *, uint64_t, const llvm::Constant *)> fill;
  fill = [&](Mem *m, uint64_t off, const llvm::Constant *C) {
    if (!C || C->isNullValue())
      return;
    if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      auto *ST = const_cast<llvm::StructType *>(llvm::cast<llvm::StructType>(CS->getType()));
      const llvm::StructLayout *SL = DL.getStructLayout(ST);
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        fill(m, off + SL->getElementOffset(i), llvm::cast<llvm::Constant>(CS->getOperand(i)));
      return;
    }
    if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
      llvm::Type *E = CA->getType()->getElementType();
      if (!E->isSized())
        return;
      uint64_t stride = DL.getTypeAllocSize(E);
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        fill(m, off + i * stride, llvm::cast<llvm::Constant>(CA->getOperand(i)));
      return;
    }
    if (C->getType()->isAggregateType())
      return;
    P p;
    if (constPtr(C, p))
      field[m][(int64_t)off].insert(p);
  };
  for (llvm::GlobalVariable &G : M.globals())
    if (G.hasInitializer())
      fill(gmem[&G], 0, G.getInitializer());

  for (llvm::Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (llvm::BasicBlock &BB : F)
      if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator()))
        if (R->getReturnValue() && R->getReturnValue()->getType()->isPointerTy())
          rets[&F].push_back(R->getReturnValue());
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(&I)) {
        if (C->getType()->isPointerTy() && C->getOperand(0)->getType()->isPointerTy())
          copies[C->getOperand(0)].push_back(C);
      } else if (const auto *PI = llvm::dyn_cast<llvm::PHINode>(&I)) {
        if (PI->getType()->isPointerTy())
          for (llvm::Value *inc : PI->incoming_values())
            if (inc->getType()->isPointerTy())
              copies[inc].push_back(PI);
      } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(&I)) {
        if (S->getType()->isPointerTy()) {
          copies[S->getTrueValue()].push_back(S);
          copies[S->getFalseValue()].push_back(S);
        }
      } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(&I)) {
        if (Fr->getType()->isPointerTy() && Fr->getOperand(0)->getType()->isPointerTy())
          copies[Fr->getOperand(0)].push_back(Fr);
      } else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
        // Constant struct fields stay exact. A variable index into an array of
        // pointers or aggregates is every element; a constant field path after
        // that index is applied to each element. A variable index into a scalar
        // array is not a field access.
        std::vector<llvm::Value *> ids;
        for (llvm::Value *idx : G->indices())
          ids.push_back(idx);
        std::vector<int64_t> deltas;
        llvm::Type *ty = G->getSourceElementType();
        int64_t delta = 0;
        bool ok = !ids.empty();
        bool sawField = false;
        for (unsigned i = 0; ok && i < ids.size(); ++i) {
          const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(ids[i]);
          if (i == 0) {
            if (!CI) {
              // An unknown index through a pointer, with no further field, is
              // an element of an array of pointers. A struct or a sized array
              // still uses its own index rule below; this is only the scalar form.
              if (ids.size() == 1 && ty->isPointerTy())
                geps[G->getPointerOperand()].push_back(
                    GepC{G, 0, false, nullptr, false, true});
              ok = false;
              break;
            }
            int64_t n = CI->getSExtValue();
            if (n != 0) {
              if (!ty->isSized()) {
                ok = false;
                break;
              }
              delta += n * (int64_t)DL.getTypeAllocSize(ty);
            }
            continue;
          }
          if (auto *ST = llvm::dyn_cast<llvm::StructType>(ty)) {
            if (!CI || CI->getZExtValue() >= ST->getNumElements()) {
              ok = false;
              break;
            }
            unsigned f = (unsigned)CI->getZExtValue();
            delta += (int64_t)DL.getStructLayout(ST)->getElementOffset(f);
            ty = ST->getElementType(f);
            sawField = true;
            continue;
          }
          auto *AT = llvm::dyn_cast<llvm::ArrayType>(ty);
          if (!AT || !AT->getElementType()->isSized()) {
            ok = false;
            break;
          }
          llvm::Type *elt = AT->getElementType();
          uint64_t es = DL.getTypeAllocSize(elt);
          if (CI) {
            delta += CI->getSExtValue() * (int64_t)es;
            ty = elt;
            sawField = true;
            continue;
          }
          int64_t suffix = 0;
          llvm::Type *cur = elt;
          for (unsigned j = i + 1; j < ids.size(); ++j) {
            const auto *LC = llvm::dyn_cast<llvm::ConstantInt>(ids[j]);
            if (!LC) {
              ok = false;
              break;
            }
            if (auto *SST = llvm::dyn_cast<llvm::StructType>(cur)) {
              if (LC->getZExtValue() >= SST->getNumElements()) {
                ok = false;
                break;
              }
              unsigned f = (unsigned)LC->getZExtValue();
              suffix += (int64_t)DL.getStructLayout(SST)->getElementOffset(f);
              cur = SST->getElementType(f);
            } else if (auto *A2 = llvm::dyn_cast<llvm::ArrayType>(cur)) {
              if (!A2->getElementType()->isSized()) {
                ok = false;
                break;
              }
              suffix += LC->getSExtValue() * (int64_t)DL.getTypeAllocSize(A2->getElementType());
              cur = A2->getElementType();
            } else {
              ok = false;
              break;
            }
          }
          bool fieldElem = elt->isPointerTy() || elt->isStructTy() || elt->isArrayTy();
          if (!ok || !fieldElem || es == 0 || AT->getNumElements() == 0)
            ok = false;
          else {
            for (uint64_t e = 0; e < AT->getNumElements(); ++e)
              deltas.push_back(delta + (int64_t)(e * es) + suffix);
            sawField = true;
          }
          ok = false;
          break;
        }
        if (ok && sawField)
          deltas.push_back(delta);
        else if (ok && delta == 0)
          // A zero index with no field is the same address.
          copies[G->getPointerOperand()].push_back(G);
        else if (ok && G->getSourceElementType()->isPointerTy())
          geps[G->getPointerOperand()].push_back(GepC{G, delta, false, nullptr, true});
        for (int64_t d : deltas)
          geps[G->getPointerOperand()].push_back(
              GepC{G, d, false, G->getSourceElementType()});
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        if (L->getType()->isPointerTy())
          loads[L->getPointerOperand()].push_back(L);
      } else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (S->getValueOperand()->getType()->isPointerTy()) {
          storeAt[S->getPointerOperand()].push_back(S->getValueOperand());
          storeOf[S->getValueOperand()].push_back(S->getPointerOperand());
        }
      } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (C->isInlineAsm() || (C->getCalledFunction() && C->getCalledFunction()->isIntrinsic()))
          continue;
        callsOf[C->getCalledOperand()].push_back(C);
        const llvm::Function *D = calledDirect(C, M);
        // A pointer returned by a declaration is an object. An indirect call
        // gets one only if no callee return supplies an object; that is
        // decided after the first fixpoint.
        if (!D && C->getType()->isPointerTy()) {
          if (C->isIndirectCall())
            indirectRet.push_back(C);
          else {
            hmem[C] = mem(0);
            heapMems.insert(hmem[C]);
          }
        }
      }
    }
  }

  auto apply = [&](P base, int64_t delta, bool lost, P &out) -> bool {
    if (base.k == 2)
      return false;
    const auto *m = static_cast<const Mem *>(base.obj);
    if (base.k == 1 || lost) {
      out = any(m);
      return true;
    }
    int64_t off = base.off + delta;
    // An offset before the object, past its end, or into an object that has
    // no size yet is not a known field. It is every offset of this object.
    if (off < 0 || (m->size == 0 && off != 0) || (m->size && (uint64_t)off >= m->size)) {
      out = any(m);
      return true;
    }
    out = exact(m, off);
    return true;
  };

  auto dumpPts = [&](const llvm::Value *v, auto fn) {
    if (const auto *C = llvm::dyn_cast<llvm::Constant>(v)) {
      P p;
      if (constPtr(C, p))
        fn(p);
      return;
    }
    for (const P &p : pts[v])
      fn(p);
  };

  std::function<void(const llvm::CallBase *, const llvm::Function *)> hitCode;
  hitCode = [&](const llvm::CallBase *C, const llvm::Function *F) {
    if (!C || !F || F->isDeclaration() || F->getParent() != &M)
      return;
    if (!hit.insert({C, F}).second)
      return;
    const llvm::Function *caller = C->getFunction();
    if (caller && caller->getParent() == &M)
      callers[F].insert(caller);
    unsigned n = std::min<unsigned>(C->arg_size(), F->arg_size());
    for (unsigned i = 0; i < n; ++i) {
      if (!C->getArgOperand(i)->getType()->isPointerTy())
        continue;
      if (!F->getArg(i)->getType()->isPointerTy())
        continue;
      copies[C->getArgOperand(i)].push_back(F->getArg(i));
      dumpPts(C->getArgOperand(i), [&](P p) { addPts(F->getArg(i), p); });
    }
    if (thin.count(F)) {
      if (!hmem.count(C)) {
        hmem[C] = mem(0);
        heapMems.insert(hmem[C]);
        localType(C, hmem[C]);
      }
      addPts(C, exact(hmem[C], 0));
      return;
    }
    for (const llvm::Value *rv : rets[F]) {
      copies[rv].push_back(C);
      dumpPts(rv, [&](P p) { addPts(C, p); });
    }
  };

  auto give = [&](const llvm::Value *dst, P p) {
    if (const auto *C = llvm::dyn_cast<llvm::Constant>(dst))
      if (!llvm::isa<llvm::GlobalVariable>(C) && !llvm::isa<llvm::Instruction>(dst))
        return;
    addPts(dst, p);
  };

  auto contents = [&](const Mem *m, bool isAny, int64_t off, auto fn) {
    if (auto fit = field.find(m); fit != field.end()) {
      if (isAny) {
        for (const auto &kv : fit->second)
          for (const P &p : kv.second)
            fn(p);
      } else if (auto it = fit->second.find(off); it != fit->second.end())
        for (const P &p : it->second)
          fn(p);
    }
    if (auto it = wild.find(m); it != wild.end())
      for (const P &p : it->second)
        fn(p);
  };

  {
    // Only an address that reaches a pointer load, a pointer store, or a
    // call is a field access. A GEP used only to address an integer does not
    // enter the points-to relation.
    std::unordered_set<const llvm::Value *> rel;
    std::deque<const llvm::Value *> rq;
    auto mark = [&](const llvm::Value *v) {
      if (v && rel.insert(v).second)
        rq.push_back(v);
    };
    for (const auto &kv : loads)
      mark(kv.first);
    for (const auto &kv : storeAt)
      mark(kv.first);
    for (const auto &kv : callsOf)
      mark(kv.first);
    while (!rq.empty()) {
      const llvm::Value *v = rq.front();
      rq.pop_front();
      if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(v))
        mark(G->getPointerOperand());
      else if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v))
        mark(C->getOperand(0));
      else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(v)) {
        for (llvm::Value *inc : P->incoming_values())
          mark(inc);
      } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(v)) {
        mark(S->getTrueValue());
        mark(S->getFalseValue());
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(v))
        mark(L->getPointerOperand());
    }
    for (auto it = geps.begin(); it != geps.end();) {
      auto &vec = it->second;
      vec.erase(std::remove_if(vec.begin(), vec.end(),
                               [&](const GepC &g) { return !rel.count(g.dst); }),
                vec.end());
      if (vec.empty())
        it = geps.erase(it);
      else
        ++it;
    }
  }
  {
    std::unordered_map<const llvm::Value *, unsigned> idx;
    std::vector<const llvm::Value *> nodes;
    auto idOf = [&](const llvm::Value *v) {
      auto it = idx.find(v);
      if (it != idx.end())
        return it->second;
      unsigned i = (unsigned)nodes.size();
      idx.emplace(v, i);
      nodes.push_back(v);
      return i;
    };
    struct E {
      unsigned to;
      int64_t d;
    };
    std::vector<std::pair<const llvm::Value *, std::pair<const llvm::Value *, int64_t>>> raw;
    for (const auto &kv : geps)
      for (const GepC &g : kv.second)
        raw.push_back({kv.first, {g.dst, g.step ? 0 : (g.any ? 1 : g.delta)}});
    for (const auto &kv : copies)
      for (const llvm::Value *d : kv.second)
        raw.push_back({kv.first, {d, 0}});
    for (const auto &e : raw) {
      idOf(e.first);
      idOf(e.second.first);
    }
    std::vector<std::vector<E>> adj(nodes.size());
    for (const auto &e : raw)
      adj[idOf(e.first)].push_back({idOf(e.second.first), e.second.second});
    std::vector<int> disc(nodes.size(), -1), low(nodes.size(), 0);
    std::vector<unsigned> st;
    std::vector<char> on(nodes.size(), 0);
    int timer = 0;
    std::vector<std::vector<unsigned>> sccs;
    std::function<void(unsigned)> dfs = [&](unsigned u) {
      disc[u] = low[u] = timer++;
      st.push_back(u);
      on[u] = 1;
      for (const E &e : adj[u]) {
        if (disc[e.to] < 0) {
          dfs(e.to);
          low[u] = std::min(low[u], low[e.to]);
        } else if (on[e.to])
          low[u] = std::min(low[u], disc[e.to]);
      }
      if (low[u] == disc[u]) {
        std::vector<unsigned> comp;
        while (true) {
          unsigned w = st.back();
          st.pop_back();
          on[w] = 0;
          comp.push_back(w);
          if (w == u)
            break;
        }
        sccs.push_back(std::move(comp));
      }
    };
    for (unsigned i = 0; i < nodes.size(); ++i)
      if (disc[i] < 0)
        dfs(i);
    std::vector<unsigned> sid(nodes.size());
    for (unsigned s = 0; s < sccs.size(); ++s)
      for (unsigned u : sccs[s])
        sid[u] = s;
    std::vector<char> bad(sccs.size(), 0);
    for (unsigned u = 0; u < adj.size(); ++u)
      for (const E &e : adj[u])
        if (sid[u] == sid[e.to] && e.d != 0)
          bad[sid[u]] = 1;
    for (unsigned s = 0; s < sccs.size(); ++s)
      if (bad[s])
        for (unsigned u : sccs[s])
          loseOff.insert(nodes[u]);
  }

  // A function that only returns a fresh allocation is an allocation site at
  // each of its calls. Callers do not share the object allocated inside it.
  for (llvm::Function &F : M) {
    if (!F.isDeclaration() || F.isIntrinsic())
      continue;
    if (F.getReturnType()->isPointerTy() && F.returnDoesNotAlias())
      thin.insert(&F);
  }
  auto fresh = [&](auto &self, const llvm::Value *v,
                   std::unordered_set<const llvm::Value *> &seen) -> bool {
    if (!v || !seen.insert(v).second)
      return true;
    if (const auto *C = llvm::dyn_cast<llvm::Constant>(v))
      return C->isNullValue();
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(v)) {
      // A call through an allocator function pointer is still a fresh object.
      // The wrapper that only returns it does not share one object across calls.
      if (C->isIndirectCall())
        return C->getType()->isPointerTy();
      const auto *D = llvm::dyn_cast<llvm::Function>(C->getCalledOperand()->stripPointerCastsAndAliases());
      return D && thin.count(D);
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v))
      return self(self, C->getOperand(0), seen);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(v))
      return self(self, Fr->getOperand(0), seen);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(v)) {
      for (llvm::Value *inc : P->incoming_values())
        if (inc->getType()->isPointerTy() && !self(self, inc, seen))
          return false;
      return true;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(v))
      return self(self, S->getTrueValue(), seen) && self(self, S->getFalseValue(), seen);
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(v)) {
      if (!llvm::isa<llvm::AllocaInst>(strip(L->getPointerOperand())))
        return false;
      auto it = storeAt.find(L->getPointerOperand());
      if (it == storeAt.end())
        return false;
      for (const llvm::Value *s : it->second)
        if (!self(self, s, seen))
          return false;
      seen.insert(L->getPointerOperand());
      return true;
    }
    return false;
  };
  bool grewThin = true;
  while (grewThin) {
    grewThin = false;
    for (llvm::Function &F : M) {
      if (F.isDeclaration() || thin.count(&F) || !F.getReturnType()->isPointerTy())
        continue;
      if (rets[&F].empty())
        continue;
      std::unordered_set<const llvm::Value *> carriers;
      bool ok = true;
      for (const llvm::Value *rv : rets[&F]) {
        std::unordered_set<const llvm::Value *> seen;
        if (!fresh(fresh, rv, seen)) {
          ok = false;
          break;
        }
        carriers.insert(seen.begin(), seen.end());
      }
      if (!ok)
        continue;
      auto strictUser = [&](const llvm::User *U, const llvm::Value *v) {
        if (llvm::isa<llvm::ReturnInst>(U) || llvm::isa<llvm::ICmpInst>(U) || carriers.count(U))
          return true;
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U))
          if (C->getCalledFunction() && C->getCalledFunction()->isIntrinsic())
            return true;
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U))
          if (S->getValueOperand() == v && carriers.count(S->getPointerOperand()))
            return true;
        return false;
      };
      bool strict = true;
      for (const llvm::Value *v : carriers) {
        if (llvm::isa<llvm::Constant>(v))
          continue;
        for (const llvm::User *U : v->users())
          if (!strictUser(U, v)) {
            strict = false;
            break;
          }
        if (!strict)
          break;
      }
      if (strict) {
        thin.insert(&F);
        grewThin = true;
      }
    }
  }

  localType = [&](const llvm::CallBase *C, Mem *h) {
    if (!C || !h)
      return;
    const llvm::Function *F = C->getFunction();
    if (!F)
      return;
    auto keyOf = [](const llvm::Value *addr) {
      std::string k;
      const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(addr);
      if (!G)
        return k;
      if (const auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType()))
        k = ST->hasName() ? ST->getName().str() : std::string("anon");
      k.push_back('#');
      k += std::to_string(reinterpret_cast<uintptr_t>(G->getPointerOperand()));
      for (llvm::Value *idx : G->indices()) {
        k.push_back(',');
        if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(idx))
          k += std::to_string(CI->getSExtValue());
        else
          k += std::to_string(reinterpret_cast<uintptr_t>(idx));
      }
      return k;
    };
    std::unordered_set<const llvm::Value *> hold;
    std::deque<const llvm::Value *> q;
    q.push_back(C);
    std::unordered_set<const llvm::Value *> addrs;
    std::unordered_set<std::string> keys;
    auto absorb = [&](const llvm::Value *v) {
      if (!hold.insert(v).second)
        return;
      q.push_back(v);
    };
    while (!q.empty()) {
      const llvm::Value *v = q.front();
      q.pop_front();
      for (const llvm::User *U : v->users()) {
        const auto *I = llvm::dyn_cast<llvm::Instruction>(U);
        if (!I || I->getFunction() != F)
          continue;
        if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(I)) {
          if (G->getPointerOperand() == v)
            if (auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType()))
              objTy[h].insert(ST);
        } else if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I) ||
                   llvm::isa<llvm::PHINode>(I) || llvm::isa<llvm::SelectInst>(I)) {
          absorb(I);
        } else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(I)) {
          if (S->getValueOperand() == v) {
            addrs.insert(S->getPointerOperand());
            if (std::string k = keyOf(S->getPointerOperand()); !k.empty())
              keys.insert(std::move(k));
          }
        }
      }
    }
    for (const llvm::Instruction &I : llvm::instructions(*F)) {
      const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!L || !L->getType()->isPointerTy() || hold.count(L))
        continue;
      const llvm::Value *a = L->getPointerOperand();
      std::string k = keyOf(a);
      if (!addrs.count(a) && (k.empty() || !keys.count(k)))
        continue;
      absorb(L);
    }
    while (!q.empty()) {
      const llvm::Value *v = q.front();
      q.pop_front();
      for (const llvm::User *U : v->users()) {
        const auto *I = llvm::dyn_cast<llvm::Instruction>(U);
        if (!I || I->getFunction() != F)
          continue;
        if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(I)) {
          if (G->getPointerOperand() == v)
            if (auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType()))
              objTy[h].insert(ST);
        } else if (llvm::isa<llvm::CastInst>(I) || llvm::isa<llvm::FreezeInst>(I) ||
                   llvm::isa<llvm::PHINode>(I) || llvm::isa<llvm::SelectInst>(I)) {
          absorb(I);
        }
      }
    }
  };
  for (const auto &kv : hmem)
    localType(kv.first, kv.second);

  for (llvm::GlobalVariable &G : M.globals())
    addPts(&G, exact(gmem[&G], 0));
  for (const auto &kv : amem)
    addPts(kv.first, exact(kv.second, 0));
  for (const auto &kv : hmem)
    addPts(kv.first, exact(kv.second, 0));
  for (llvm::Function &F : M)
    if (!F.isDeclaration())
      for (llvm::Instruction &I : llvm::instructions(F))
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I))
          if (const llvm::Function *D = calledDirect(C, M))
            hitCode(C, D);
  for (const auto &kv : copies)
    if (llvm::isa<llvm::Constant>(kv.first))
      dumpPts(kv.first, [&](P p) {
        for (const llvm::Value *dst : kv.second)
          give(dst, p);
      });

  // Both addresses lie in one array of pointers in the by-value layout.
  // A sized type cannot contain itself, so a type repeated on this path is
  // not that array.
  std::function<bool(llvm::Type *, int64_t, int64_t, int64_t, std::unordered_set<llvm::Type *> &)> inArray;
  inArray = [&](llvm::Type *T, int64_t base, int64_t a, int64_t b,
                std::unordered_set<llvm::Type *> &path) -> bool {
    if (!T || !T->isSized() || !path.insert(T).second)
      return false;
    struct Leave {
      std::unordered_set<llvm::Type *> &path;
      llvm::Type *T;
      ~Leave() { path.erase(T); }
    } leave{path, T};
    if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(T)) {
      llvm::Type *elt = AT->getElementType();
      if (!elt->isSized() || AT->getNumElements() == 0)
        return false;
      uint64_t es = DL.getTypeAllocSize(elt);
      if (es == 0 || AT->getNumElements() > std::numeric_limits<uint64_t>::max() / es)
        return false;
      int64_t end = base + (int64_t)(AT->getNumElements() * es);
      if (elt->isPointerTy())
        return a >= base && b < end && ((a - base) % (int64_t)es) == 0 &&
               ((b - base) % (int64_t)es) == 0;
      if (a < base || a >= end)
        return false;
      int64_t el = base + ((a - base) / (int64_t)es) * (int64_t)es;
      return inArray(elt, el, a, b, path);
    }
    auto *ST = llvm::dyn_cast<llvm::StructType>(T);
    if (!ST || ST->isOpaque() || ST->getNumElements() == 0)
      return false;
    const llvm::StructLayout *SL = DL.getStructLayout(ST);
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      llvm::Type *ft = ST->getElementType(i);
      if (!ft->isSized())
        continue;
      int64_t fo = base + (int64_t)SL->getElementOffset(i);
      int64_t fe = fo + (int64_t)DL.getTypeAllocSize(ft);
      if (a < fo || a >= fe)
        continue;
      return inArray(ft, fo, a, b, path);
    }
    return false;
  };
  auto stepOk = [&](const Mem *m, int64_t off, int64_t next) {
    int64_t a = off, b = next;
    if (a > b)
      std::swap(a, b);
    if (auto it = memTy.find(m); it != memTy.end()) {
      std::unordered_set<llvm::Type *> path;
      if (inArray(it->second, 0, a, b, path))
        return true;
    }
    if (auto it = objTy.find(m); it != objTy.end())
      for (llvm::StructType *ST : it->second) {
        std::unordered_set<llvm::Type *> path;
        if (inArray(ST, 0, a, b, path))
          return true;
      }
    return false;
  };

  auto drain = [&]() {
    while (!wl.empty()) {
      Item it0 = wl.front();
      wl.pop_front();
      const llvm::Value *v = it0.v;
      P p = it0.p;
      if (it0.field) {
        const Mem *m = it0.m;
        auto notify = [&](const llvm::Value *dst) { give(dst, p); };
        if (it0.wildN) {
          if (auto it = anyLoad.find(m); it != anyLoad.end())
            for (const llvm::Value *dst : it->second)
              notify(dst);
          if (auto it = exactLoad.find(m); it != exactLoad.end())
            for (const auto &kv : it->second)
              for (const llvm::Value *dst : kv.second)
                notify(dst);
        } else {
          if (auto it = exactLoad.find(m); it != exactLoad.end())
            if (auto e = it->second.find(it0.off); e != it->second.end())
              for (const llvm::Value *dst : e->second)
                notify(dst);
          if (auto it = anyLoad.find(m); it != anyLoad.end())
            for (const llvm::Value *dst : it->second)
              notify(dst);
        }
        continue;
      }
      if (auto it = copies.find(v); it != copies.end()) {
        auto &cs = it->second;
        for (size_t i = 0; i < cs.size(); ++i)
          give(cs[i], p);
      }
      if (p.k == 2) {
        if (auto it = callsOf.find(v); it != callsOf.end())
          for (const llvm::CallBase *C : it->second)
            hitCode(C, static_cast<const llvm::Function *>(p.obj));
      } else {
        if (auto it = geps.find(v); it != geps.end()) {
          const auto *m0 = static_cast<const Mem *>(p.obj);
          // A heap object is the struct it is accessed as while the pointer
          // still denotes that object alone. A later merged pointer does not
          // apply a different struct's fields to it.
          // 1 this heap's field. 0 a proved-different struct: the external
          // object of the struct being accessed. 2 the heap has no type yet,
          // so the access is that same external object. None is empty.
          auto accept = [&](const GepC &g) -> int {
            auto *ST = g.src ? llvm::dyn_cast<llvm::StructType>(g.src) : nullptr;
            if (!ST || p.k != 0 || p.off != 0 || !heapMems.count(m0))
              return 1;
            int nMem = 0;
            if (auto pit = pts.find(v); pit != pts.end())
              for (const P &q : pit->second)
                if (q.k != 2)
                  ++nMem;
            auto &tys = objTy[m0];
            if (tys.empty() && nMem == 1) {
              tys.insert(ST);
              return 1;
            }
            if (tys.empty())
              return 2;
            // The first member of a struct is that struct. A memory manager's
            // public header is stored and loaded at offset 0 of the private one.
            // A struct cannot contain itself by value, so the first-member
            // chain is finite. A repeated type is not a further prefix.
            auto prefix = [&](auto &self, llvm::StructType *inner, llvm::StructType *outer,
                              std::unordered_set<llvm::StructType *> &seen) -> int {
              if (!inner || !outer)
                return 0;
              if (inner == outer)
                return 1;
              if (!seen.insert(outer).second)
                return 0;
              if (outer->isOpaque() || outer->getNumElements() == 0)
                return 0;
              llvm::Type *f0 = outer->getElementType(0);
              if (f0 == inner)
                return 1;
              if (auto *S = llvm::dyn_cast<llvm::StructType>(f0))
                return self(self, inner, S, seen);
              return 0;
            };
            for (llvm::StructType *T : tys) {
              std::unordered_set<llvm::StructType *> seenA, seenB;
              if (prefix(prefix, ST, T, seenA) == 1 || prefix(prefix, T, ST, seenB) == 1)
                return 1;
            }
            return 0;
          };
          if (p.k == 0 && p.off == 0) {
            auto *m = const_cast<Mem *>(m0);
            for (const GepC &g : it->second)
              if (accept(g) == 1 && g.src && g.src->isStructTy() && g.src->isSized()) {
                uint64_t sz = DL.getTypeAllocSize(g.src);
                if (sz > m->size)
                  m->size = sz;
              }
          }
          for (const GepC &g : it->second) {
            int rel = accept(g);
            if (rel != 1) {
              // Proved-different, or a heap with no type yet: the external
              // object of the struct being accessed.
              // Every offset of this heap is not that fact. Empty is not either.
              llvm::Type *st = g.src && g.src->isStructTy() ? g.src : nullptr;
              if (st) {
                P n;
                if (apply(exact(ext(st), 0), g.delta, g.any, n))
                  give(g.dst, n);
                else
                  give(g.dst, any(ext(st)));
              } else
                give(g.dst, any(m0));
              continue;
            }
            if (g.elem)
              continue;
            if (g.step) {
              // A step from an unknown offset, or a step that leaves the
              // array, is every offset of this object.
              if (p.k != 0 || !stepOk(m0, p.off, p.off + g.delta)) {
                give(g.dst, any(m0));
                continue;
              }
            }
            P n;
            if (apply(p, g.delta, g.any, n))
              give(g.dst, n);
          }
        }
        const auto *m = static_cast<const Mem *>(p.obj);
        bool isAny = p.k == 1;
        if (auto it = loads.find(v); it != loads.end())
          for (const llvm::Value *dst : it->second) {
            auto &subs = isAny ? anyLoad[m] : exactLoad[m][p.off];
            if (subs.insert(dst).second)
              contents(m, isAny, p.off, [&](P w) { give(dst, w); });
          }
        if (auto it = storeAt.find(v); it != storeAt.end())
          for (const llvm::Value *val : it->second)
            dumpPts(val, [&](P w) { write(m, isAny, p.off, w); });
      }
      if (auto it = storeOf.find(v); it != storeOf.end())
        for (const llvm::Value *addr : it->second)
          dumpPts(addr, [&](P a) {
            if (a.k == 2)
              return;
            write(static_cast<const Mem *>(a.obj), a.k == 1, a.off, p);
          });
    }
  };
  drain();
  for (const llvm::CallBase *C : indirectRet) {
    bool has = false;
    if (auto it = pts.find(C); it != pts.end())
      for (const P &p : it->second)
        if (p.k != 2)
          has = true;
    if (has)
      continue;
    Mem *m = mem(0);
    heapMems.insert(m);
    localType(C, m);
    addPts(C, exact(m, 0));
  }
  drain();

  // A struct GEP whose base is still only a parameter (no object reached it)
  // names the external object of that struct. Derived GEPs are resolved from
  // that object before any further external object is introduced.
  auto hasMem = [&](const llvm::Value *v) {
    if (const auto *C = llvm::dyn_cast<llvm::Constant>(v)) {
      P p;
      return constPtr(C, p) && p.k != 2;
    }
    for (const P &p : pts[v])
      if (p.k != 2)
        return true;
    return false;
  };
  std::unordered_set<const llvm::Value *> gepDst;
  for (const auto &kv : geps)
    for (const GepC &g : kv.second)
      gepDst.insert(g.dst);
  // Only a pointer that enters as a parameter, and is still not an object,
  // denotes the external object of the struct it is accessed as. A load that
  // read nothing is not such a pointer.
  auto paramDerived = [&](std::unordered_set<const llvm::Value *> &out) {
    out.clear();
    std::deque<const llvm::Value *> q;
    for (llvm::Function &F : M)
      if (!F.isDeclaration())
        for (llvm::Argument &A : F.args())
          if (A.getType()->isPointerTy() && out.insert(&A).second)
            q.push_back(&A);
    while (!q.empty()) {
      const llvm::Value *v = q.front();
      q.pop_front();
      auto it = copies.find(v);
      if (it == copies.end())
        continue;
      for (const llvm::Value *d : it->second)
        if (out.insert(d).second)
          q.push_back(d);
    }
  };
  std::unordered_set<const llvm::Value *> paramD;
  for (;;) {
    paramDerived(paramD);
    std::vector<GepC> roots;
    std::vector<GepC> derived;
    for (const auto &kv : geps) {
      if (!paramD.count(kv.first) || hasMem(kv.first))
        continue;
      bool baseIsOpenGep = gepDst.count(kv.first) && !hasMem(kv.first);
      for (const GepC &g : kv.second) {
        if (!g.src || !g.src->isStructTy())
          continue;
        (baseIsOpenGep ? derived : roots).push_back(g);
      }
    }
    const std::vector<GepC> &wave = roots.empty() ? derived : roots;
    if (wave.empty())
      break;
    bool grew = false;
    for (const GepC &g : wave) {
      P n;
      if (!apply(exact(ext(g.src), 0), g.delta, g.any, n))
        continue;
      if (pts[g.dst].count(n))
        continue;
      give(g.dst, n);
      grew = true;
    }
    if (!grew)
      break;
    drain();
  }
  // An object that leaves the module (returned, or stored through a parameter)
  // and was accessed as struct T is that external object. Field reads and
  // writes go to both, so a later call that receives the object as a parameter
  // sees the fields written before it escaped. This is not applied to a store
  // into a field of some other object.
  for (;;) {
    paramDerived(paramD);
    std::unordered_set<const Mem *> esc;
    auto take = [&](const llvm::Value *v) {
      dumpPts(v, [&](P p) {
        if (p.k == 0 && p.off == 0)
          esc.insert(static_cast<const Mem *>(p.obj));
      });
    };
    for (const auto &kv : rets)
      for (const llvm::Value *rv : kv.second)
        take(rv);
    for (const auto &kv : storeAt)
      if (paramD.count(kv.first))
        for (const llvm::Value *val : kv.second)
          take(val);
    for (const Mem *O : esc) {
      auto tit = objTy.find(O);
      if (tit == objTy.end())
        continue;
      for (llvm::StructType *ST : tit->second) {
        Mem *E = ext(ST);
        if (E == O)
          continue;
        auto cp = [&](const Mem *from, Mem *to) {
          std::vector<std::pair<int64_t, P>> pending;
          auto fit = field.find(from);
          if (fit == field.end())
            return;
          for (const auto &e : fit->second)
            for (const P &w : e.second)
              pending.push_back({e.first, w});
          for (const auto &e : pending)
            write(to, false, e.first, e.second);
        };
        cp(O, E);
        cp(E, const_cast<Mem *>(O));
      }
    }
    if (wl.empty())
      break;
    drain();
  }
  // A procedure list is named by an access path: a pointer parameter, or one
  // constant field of a pointer parameter. Its elements are an array of
// function pointers. The integer at offset 0 empties the path only when the
// walk compares a load of that integer. A walk loads its callee from an
// element of that array
  // and calls only the procedures stored on a path that reaches it with no
  // such store. The resolved call is an edge of the caller that holds the
  // path, so two callers of one walk do not share callees. The address is a
  // variable element, or a pointer stepped by one and fed back through a phi.
  // A constant index is a slot. A load from a constant struct field is a
  // method, not a walk. A procedure parameter is replaced by the actual at
  // the call; one that remains contributes the functions in its points-to
  // set. Paths whose pointees meet are the same path. If the summary
  // equations do not settle, the path's callees are every procedure stored
  // into a list: the top of this lattice, not a cutoff.
  {
    struct Key {
      unsigned arg = 0;
      int64_t off = -1;
      bool operator==(const Key &o) const { return arg == o.arg && off == o.off; }
    };
    struct KH {
      size_t operator()(const Key &k) const {
        return (size_t)k.arg * 1315423911u ^ (size_t)k.off;
      }
    };
    struct St {
      bool kill = false;
      bool top = false;
      std::unordered_set<const llvm::Function *> fn;
      std::unordered_set<unsigned> arg;
      bool operator==(const St &o) const {
        return kill == o.kill && top == o.top && fn == o.fn && arg == o.arg;
      }
      bool live() const { return kill || top || !fn.empty() || !arg.empty(); }
    };
    using State = std::unordered_map<Key, St, KH>;
    struct Piece {
      bool any = true;
      int64_t c = 0;
      State st;
      bool operator==(const Piece &o) const { return any == o.any && c == o.c && st == o.st; }
    };
    using Org = std::unordered_map<const llvm::Value *, std::unordered_set<unsigned>>;

    auto joinState = [](const State &a, const State &b) {
      State r = a;
      for (const auto &kv : b) {
        auto it = r.find(kv.first);
        if (it == r.end()) {
          St s = kv.second;
          s.kill = false;
          if (s.live())
            r.emplace(kv.first, std::move(s));
          continue;
        }
        St &d = it->second;
        d.kill = d.kill && kv.second.kill;
        d.top = d.top || kv.second.top;
        d.fn.insert(kv.second.fn.begin(), kv.second.fn.end());
        d.arg.insert(kv.second.arg.begin(), kv.second.arg.end());
        if (!d.live())
          r.erase(it);
      }
      for (auto it = r.begin(); it != r.end();) {
        if (!b.count(it->first)) {
          it->second.kill = false;
          if (!it->second.live())
            it = r.erase(it);
          else
            ++it;
        } else
          ++it;
      }
      return r;
    };

    std::unordered_map<const llvm::Function *, Org> orgOf;
    auto ensureOrg = [&](const llvm::Function *F) -> const Org & {
      auto it = orgOf.find(F);
      if (it != orgOf.end())
        return it->second;
      Org org;
      std::deque<const llvm::Value *> q;
      auto mark = [&](const llvm::Value *d, const std::unordered_set<unsigned> &src) {
        if (!d)
          return;
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(d))
          if (I->getFunction() != F)
            return;
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(d))
          if (A->getParent() != F)
            return;
        bool grew = false;
        for (unsigned a : src)
          if (org[d].insert(a).second)
            grew = true;
        if (grew)
          q.push_back(d);
      };
      for (const llvm::Argument &A : F->args())
        if (A.getType()->isPointerTy()) {
          org[&A].insert(A.getArgNo());
          q.push_back(&A);
        }
      while (!q.empty()) {
        const llvm::Value *v = q.front();
        q.pop_front();
        const auto src = org[v];
        for (const llvm::User *U : v->users()) {
          if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U))
            if (I->getFunction() != F)
              continue;
          if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) ||
              llvm::isa<llvm::PHINode>(U) || llvm::isa<llvm::SelectInst>(U) ||
              llvm::isa<llvm::GetElementPtrInst>(U))
            mark(llvm::cast<llvm::Value>(U), src);
          else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
            if (L->getPointerOperand() == v && L->getType()->isPointerTy())
              mark(L, src);
          } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
            if (!C->isIndirectCall() && C->getType()->isPointerTy())
              mark(C, src);
          }
        }
      }
      auto [ins, _] = orgOf.emplace(F, std::move(org));
      return ins->second;
    };
    auto oneArg = [&](const Org &org, const llvm::Value *v, unsigned &a) {
      auto it = org.find(v);
      if (it == org.end() || it->second.size() != 1)
        return false;
      a = *it->second.begin();
      return true;
    };
    std::function<bool(const llvm::Function *, const llvm::Value *, Key &,
                       std::unordered_set<const llvm::Value *> &)>
        actualKey;
    actualKey = [&](const llvm::Function *F, const llvm::Value *v, Key &out,
                    std::unordered_set<const llvm::Value *> &seen) -> bool {
      if (!v || !seen.insert(v).second)
        return false;
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(v)) {
        if (A->getParent() != F)
          return false;
        out = Key{A->getArgNo(), -1};
        return true;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v))
        return actualKey(F, C->getOperand(0), out, seen);
      if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(v))
        return actualKey(F, Fr->getOperand(0), out, seen);
      if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(v)) {
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (G->accumulateConstantOffset(DL, ap) && ap.isZero())
          return actualKey(F, G->getPointerOperand(), out, seen);
        return false;
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(v)) {
        const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(L->getPointerOperand());
        if (!G)
          return false;
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(DL, ap))
          return false;
        Key b;
        if (!actualKey(F, G->getPointerOperand(), b, seen) || b.off != -1)
          return false;
        out = Key{b.arg, ap.getSExtValue()};
        return true;
      }
      if (const auto *P = llvm::dyn_cast<llvm::PHINode>(v)) {
        bool any = false;
        Key k;
        for (const llvm::Value *inc : P->incoming_values()) {
          if (!inc->getType()->isPointerTy() || seen.count(inc))
            continue;
          Key ik;
          if (!actualKey(F, inc, ik, seen))
            return false;
          if (!any) {
            k = ik;
            any = true;
          } else if (!(k == ik))
            return false;
        }
        if (!any)
          return false;
        out = k;
        return true;
      }
      if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(v)) {
        Key a, b;
        if (!actualKey(F, S->getTrueValue(), a, seen) || !actualKey(F, S->getFalseValue(), b, seen) ||
            !(a == b))
          return false;
        out = a;
        return true;
      }
      return false;
    };
    auto translate = [&](const llvm::Function *caller, const llvm::CallBase *call, Key k,
                         Key &out) {
      if (k.arg >= call->arg_size())
        return false;
      Key ak;
      std::unordered_set<const llvm::Value *> seen;
      if (!actualKey(caller, call->getArgOperand(k.arg), ak, seen))
        return false;
      if (k.off < 0) {
        out = ak;
        return true;
      }
      if (ak.off >= 0)
        return false;
      out = Key{ak.arg, k.off};
      return true;
    };

    auto isGenStore = [&](const llvm::StoreInst *S, const Org &org, unsigned &a) {
      if (!S->getValueOperand()->getType()->isPointerTy())
        return false;
      const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(S->getPointerOperand());
      if (!G || !G->getSourceElementType()->isPointerTy())
        return false;
      bool var = false;
      for (const llvm::Value *idx : G->indices())
        if (!llvm::isa<llvm::ConstantInt>(idx))
          var = true;
      if (!var)
        return false;
      return oneArg(org, G, a);
    };
    // Storing integer 0 at offset 0 empties a list only when that integer is
    // the bound a walk compares. The load of the bound may be in this
    // function, or be what a direct callee returns. The walk may call the
    // function that stores 0, as a reset of the same argument.
    std::unordered_map<const llvm::Function *, std::unordered_set<unsigned>> boundCache;
    bool boundReady = false;
    auto feedsCmp = [](const llvm::Value *v) {
      std::vector<const llvm::Value *> st{v};
      std::unordered_set<const llvm::Value *> seen;
      while (!st.empty()) {
        const llvm::Value *x = st.back();
        st.pop_back();
        if (!x || !seen.insert(x).second)
          continue;
        for (const llvm::User *U : x->users()) {
          if (llvm::isa<llvm::ICmpInst>(U))
            return true;
          if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::PHINode>(U) || llvm::isa<llvm::FreezeInst>(U))
            st.push_back(llvm::cast<llvm::Value>(U));
        }
      }
      return false;
    };
    // Offset 0 is the pointer itself: a load of the first integer field has
    // no getelementptr. A nonzero index is a different field.
    auto field0 = [&](const llvm::Function *F, const llvm::Value *v, unsigned &arg) {
      const auto *L = llvm::dyn_cast<llvm::LoadInst>(v->stripPointerCasts());
      if (!L || !L->getType()->isIntegerTy())
        return false;
      std::function<bool(const llvm::Value *, unsigned &, std::unordered_set<const llvm::Value *> &)> zeroArg;
      zeroArg = [&](const llvm::Value *p, unsigned &out, std::unordered_set<const llvm::Value *> &seen) -> bool {
        if (!p || !seen.insert(p).second)
          return false;
        p = p->stripPointerCasts();
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(p)) {
          if (A->getParent() != F)
            return false;
          out = A->getArgNo();
          return true;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(p))
          return zeroArg(C->getOperand(0), out, seen);
        if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(p))
          return zeroArg(Fr->getOperand(0), out, seen);
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(p)) {
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(DL, ap) || !ap.isZero())
            return false;
          return zeroArg(G->getPointerOperand(), out, seen);
        }
        if (const auto *P = llvm::dyn_cast<llvm::PHINode>(p)) {
          bool any = false;
          unsigned acc = 0;
          for (const llvm::Value *inc : P->incoming_values()) {
            unsigned one = 0;
            if (!zeroArg(inc, one, seen))
              return false;
            if (!any)
              acc = one;
            else if (acc != one)
              return false;
            any = true;
          }
          if (!any)
            return false;
          out = acc;
          return true;
        }
        return false;
      };
      std::unordered_set<const llvm::Value *> seen;
      return zeroArg(L->getPointerOperand(), arg, seen);
    };
    auto argBounded = [&](const llvm::Function *F, unsigned arg) {
      if (!F)
        return false;
      if (!boundReady) {
        boundReady = true;
        std::unordered_map<const llvm::Function *, unsigned> boundRet;
        for (llvm::Function &BF : M) {
          if (BF.isDeclaration() || BF.empty())
            continue;
          unsigned got = 0;
          bool any = false, bad = false;
          for (const llvm::Instruction &I : llvm::instructions(BF)) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
            if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isIntegerTy())
              continue;
            unsigned a = 0;
            if (!field0(&BF, R->getReturnValue(), a)) {
              bad = true;
              break;
            }
            if (!any)
              got = a;
            else if (got != a)
              bad = true;
            any = true;
          }
          if (any && !bad)
            boundRet[&BF] = got;
        }
        auto cursor = [](const llvm::Value *v, auto &self, std::unordered_set<const llvm::Value *> &seen) -> bool {
          if (!v || !seen.insert(v).second)
            return false;
          const llvm::Value *x = v->stripPointerCasts();
          if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(x)) {
            if (!G->getSourceElementType()->isPointerTy())
              return false;
            for (const llvm::Value *idx : G->indices())
              if (!llvm::isa<llvm::ConstantInt>(idx))
                return true;
            const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(G->getNumOperands() - 1));
            if (CI && CI->isOne() && llvm::isa<llvm::PHINode>(G->getPointerOperand()->stripPointerCasts()))
              return true;
            return false;
          }
          if (const auto *P = llvm::dyn_cast<llvm::PHINode>(x)) {
            for (const llvm::Value *inc : P->incoming_values())
              if (self(inc, self, seen))
                return true;
          }
          return false;
        };
        for (llvm::Function &W : M) {
          if (W.isDeclaration())
            continue;
          const Org &o = ensureOrg(&W);
          std::unordered_set<unsigned> walked, compared;
          for (const llvm::Instruction &I : llvm::instructions(W)) {
            if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
              if (C->isIndirectCall()) {
                unsigned w = 0;
                if (!oneArg(o, C->getCalledOperand(), w))
                  continue;
                const llvm::Value *callee = C->getCalledOperand()->stripPointerCasts();
                const auto *slot = llvm::dyn_cast<llvm::LoadInst>(callee);
                if (!slot)
                  continue;
                std::unordered_set<const llvm::Value *> seenC;
                if (cursor(slot->getPointerOperand(), cursor, seenC))
                  walked.insert(w);
              } else if (const llvm::Function *D = C->getCalledFunction()) {
                auto bit = boundRet.find(D);
                if (bit == boundRet.end() || bit->second >= C->arg_size() || !feedsCmp(C))
                  continue;
                unsigned w = 0;
                if (oneArg(o, C->getArgOperand(bit->second), w))
                  compared.insert(w);
              }
            }
            if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
              unsigned w = 0;
              if (field0(&W, L, w) && feedsCmp(L))
                compared.insert(w);
            }
          }
          for (unsigned w : walked) {
            if (!compared.count(w))
              continue;
            boundCache[&W].insert(w);
            for (const llvm::Instruction &I : llvm::instructions(W)) {
              const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!C || C->isIndirectCall())
                continue;
              const llvm::Function *D = C->getCalledFunction();
              if (!D || D->isDeclaration())
                continue;
              for (unsigned i = 0; i < C->arg_size(); ++i) {
                unsigned src = 0;
                if (!oneArg(o, C->getArgOperand(i), src) || src != w)
                  continue;
                // Operand i is the callee's parameter. It is the walker's list.
                boundCache[D].insert(i);
              }
            }
          }
        }
      }
      auto it = boundCache.find(F);
      return it != boundCache.end() && it->second.count(arg) != 0;
    };
    auto isKillStore = [&](const llvm::StoreInst *S, const Org &org, unsigned &a) {
      const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(S->getValueOperand());
      if (!CI || !CI->isZero() || S->getValueOperand()->getType()->isPointerTy())
        return false;
      const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(S->getPointerOperand());
      if (!G)
        return false;
      llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
      if (!G->accumulateConstantOffset(DL, ap) || !ap.isZero())
        return false;
      if (!oneArg(org, G, a))
        return false;
      return argBounded(S->getFunction(), a);
    };

    std::unordered_set<const llvm::Function *> seeds;
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      const Org &org = ensureOrg(&F);
      for (const llvm::Instruction &I : llvm::instructions(F)) {
        const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!S)
          continue;
        unsigned a = 0;
        if (isGenStore(S, org, a) || isKillStore(S, org, a))
          seeds.insert(&F);
      }
    }
    if (!seeds.empty()) {
      std::unordered_set<const llvm::Function *> live = seeds;
      std::deque<const llvm::Function *> sq(seeds.begin(), seeds.end());
      auto consider = [&](const llvm::Function *G) {
        if (G && !G->isDeclaration() && G->getParent() == &M && live.insert(G).second)
          sq.push_back(G);
      };
      while (!sq.empty()) {
        const llvm::Function *F = sq.front();
        sq.pop_front();
        for (const llvm::Use &U : F->uses()) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(U.getUser());
          if (C && !C->isIndirectCall() && C->getCalledOperand()->stripPointerCasts() == F)
            consider(C->getFunction());
        }
      }
      for (const llvm::Function *E : entries)
        if (E && !E->isDeclaration())
          for (const llvm::Instruction &I : llvm::instructions(*E)) {
            const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!C || !C->isIndirectCall())
              continue;
            bool hit = false;
            dumpPts(C->getCalledOperand(), [&](P p) {
              if (p.k == 2 && live.count(static_cast<const llvm::Function *>(p.obj)))
                hit = true;
            });
            if (hit)
              consider(E);
          }
      while (!sq.empty()) {
        const llvm::Function *F = sq.front();
        sq.pop_front();
        for (const llvm::Use &U : F->uses()) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(U.getUser());
          if (C && !C->isIndirectCall() && C->getCalledOperand()->stripPointerCasts() == F)
            consider(C->getFunction());
        }
      }

      std::unordered_map<const llvm::Function *, std::vector<std::vector<Key>>> groups;
      std::unordered_map<const llvm::Function *, std::unordered_map<Key, std::vector<const Mem *>, KH>>
          mems;
      auto memsOf = [&](const llvm::Function *F, Key k) -> const std::vector<const Mem *> & {
        auto &tab = mems[F];
        auto it = tab.find(k);
        if (it != tab.end())
          return it->second;
        std::vector<const Mem *> r;
        auto take = [&](const llvm::Value *v) {
          if (!v)
            return;
          dumpPts(v, [&](P p) {
            if (p.k == 0 && p.off == 0)
              r.push_back(static_cast<const Mem *>(p.obj));
          });
        };
        if (k.off < 0) {
          if (k.arg < F->arg_size())
            take(F->getArg(k.arg));
        } else {
          for (const llvm::Instruction &I : llvm::instructions(*F)) {
            const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I);
            if (!L || !L->getType()->isPointerTy())
              continue;
            Key ak;
            std::unordered_set<const llvm::Value *> seen;
            if (actualKey(F, L, ak, seen) && ak == k)
              take(L);
          }
        }
        std::sort(r.begin(), r.end());
        r.erase(std::unique(r.begin(), r.end()), r.end());
        auto [ins, _] = tab.emplace(k, std::move(r));
        return ins->second;
      };
      auto buildGroups = [&](const llvm::Function *F) {
        std::vector<Key> keys;
        for (const llvm::Argument &A : F->args())
          if (A.getType()->isPointerTy())
            keys.push_back(Key{A.getArgNo(), -1});
        for (const llvm::Instruction &I : llvm::instructions(*F)) {
          const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I);
          if (!L || !L->getType()->isPointerTy())
            continue;
          Key k;
          std::unordered_set<const llvm::Value *> seen;
          if (actualKey(F, L, k, seen))
            keys.push_back(k);
        }
        std::sort(keys.begin(), keys.end(), [](const Key &a, const Key &b) {
          return a.arg < b.arg || (a.arg == b.arg && a.off < b.off);
        });
        keys.erase(std::unique(keys.begin(), keys.end()), keys.end());
        std::vector<int> parent(keys.size());
        for (unsigned i = 0; i < keys.size(); ++i)
          parent[i] = (int)i;
        auto find = [&](auto &self, int x) -> int {
          if (parent[x] != x)
            parent[x] = self(self, parent[x]);
          return parent[x];
        };
        for (unsigned i = 0; i < keys.size(); ++i)
          for (unsigned j = i + 1; j < keys.size(); ++j) {
            const auto &A = memsOf(F, keys[i]);
            const auto &B = memsOf(F, keys[j]);
            bool meet = false;
            for (const Mem *m : A)
              if (std::binary_search(B.begin(), B.end(), m))
                meet = true;
            if (meet)
              parent[find(find, (int)i)] = find(find, (int)j);
          }
        std::unordered_map<int, std::vector<Key>> g;
        for (unsigned i = 0; i < keys.size(); ++i)
          g[find(find, (int)i)].push_back(keys[i]);
        for (auto &kv : g)
          if (kv.second.size() > 1)
            groups[F].push_back(std::move(kv.second));
      };
      auto spread = [&](const llvm::Function *F, State &st) {
        auto git = groups.find(F);
        if (git == groups.end())
          return;
        for (const auto &g : git->second) {
          St u;
          for (const Key &k : g) {
            auto it = st.find(k);
            if (it == st.end())
              continue;
            u.top = u.top || it->second.top;
            u.fn.insert(it->second.fn.begin(), it->second.fn.end());
            u.arg.insert(it->second.arg.begin(), it->second.arg.end());
          }
          if (!u.top && u.fn.empty() && u.arg.empty())
            continue;
          for (const Key &k : g) {
            St &d = st[k];
            // A length reset is a must-kill of this path only. Copying an
            // alias's procedures back onto it would undo the reset.
            if (d.kill)
              continue;
            d.top = d.top || u.top;
            d.fn.insert(u.fn.begin(), u.fn.end());
            d.arg.insert(u.arg.begin(), u.arg.end());
          }
        }
      };
      for (const llvm::Function *F : live)
        if (!F->isDeclaration())
          buildGroups(F);

      auto takeFn = [&](const llvm::Function *F, St &s, const llvm::Value *v) {
        if (!v) {
          s.top = true;
          return;
        }
        const llvm::Value *x = v;
        std::unordered_set<const llvm::Value *> seen;
        while (x && seen.insert(x).second) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(x)) {
            x = C->getOperand(0);
            continue;
          }
          break;
        }
        if (const auto *A = llvm::dyn_cast<llvm::Argument>(x))
          if (A->getParent() == F) {
            s.arg.insert(A->getArgNo());
            return;
          }
        if (const auto *C = llvm::dyn_cast<llvm::Constant>(x)) {
          P p;
          if (constPtr(C, p) && p.k == 2)
            s.fn.insert(static_cast<const llvm::Function *>(p.obj));
          return;
        }
        unsigned a = 0;
        if (oneArg(ensureOrg(F), x, a)) {
          s.arg.insert(a);
          return;
        }
        dumpPts(x, [&](P p) {
          if (p.k == 2)
            s.fn.insert(static_cast<const llvm::Function *>(p.obj));
        });
      };

      std::unordered_map<const llvm::Function *, std::vector<Piece>> summary;
      std::unordered_map<const llvm::CallBase *, State> atCall;

      auto applySum = [&](const llvm::Function *caller, const State &before, const State &sum,
                          const llvm::CallBase *call) {
        State r = before;
        for (const auto &kv : sum) {
          Key ck;
          // A callee path that is not a parameter or one field of the caller
          // is outside the paths this summary names. It does not rewrite them.
          if (!translate(caller, call, kv.first, ck))
            continue;
          const St &sm = kv.second;
          St got;
          if (!sm.kill) {
            if (auto it = before.find(ck); it != before.end())
              got = it->second;
          } else
            got.kill = true;
          got.top = got.top || sm.top;
          got.fn.insert(sm.fn.begin(), sm.fn.end());
          for (unsigned a : sm.arg) {
            if (a < call->arg_size())
              takeFn(caller, got, call->getArgOperand(a));
          }
          if (got.live())
            r[ck] = std::move(got);
          else
            r.erase(ck);
        }
        spread(caller, r);
        return r;
      };

      auto piecesOf = [&](const llvm::Function *G) {
        std::vector<Piece> out;
        if (G && !G->isDeclaration())
          if (auto it = summary.find(G); it != summary.end() && !it->second.empty())
            return it->second;
        Piece id;
        id.any = true;
        out.push_back(std::move(id));
        return out;
      };
      auto targetsOf = [&](const llvm::CallBase *C) {
        std::vector<const llvm::Function *> tg;
        if (const llvm::Function *D = calledDirect(C, M))
          tg.push_back(D);
        else if (C->isIndirectCall())
          dumpPts(C->getCalledOperand(), [&](P p) {
            if (p.k == 2)
              tg.push_back(static_cast<const llvm::Function *>(p.obj));
          });
        return tg;
      };
      auto allPieces = [&](const llvm::CallBase *C) {
        std::vector<Piece> ps;
        for (const llvm::Function *T : targetsOf(C)) {
          auto part = piecesOf(T);
          ps.insert(ps.end(), part.begin(), part.end());
        }
        if (ps.empty()) {
          Piece id;
          id.any = true;
          ps.push_back(id);
        }
        return ps;
      };

      auto solveFn = [&](const llvm::Function *F) {
        std::vector<Piece> ps;
        if (F->isDeclaration() || F->empty()) {
          Piece id;
          id.any = true;
          summary[F] = {id};
          return;
        }
        const Org &org = ensureOrg(F);
        std::unordered_map<const llvm::BasicBlock *, std::unordered_map<const llvm::BasicBlock *, State>>
            edge;
        std::unordered_map<const llvm::BasicBlock *, State> blockOut;
        std::deque<const llvm::BasicBlock *> wl;
        std::unordered_set<const llvm::BasicBlock *> queued;
        const llvm::BasicBlock *entry = &F->getEntryBlock();
        wl.push_back(entry);
        queued.insert(entry);
        auto enqueue = [&](const llvm::BasicBlock *B) {
          if (queued.insert(B).second)
            wl.push_back(B);
        };
        while (!wl.empty()) {
          const llvm::BasicBlock *BB = wl.front();
          wl.pop_front();
          queued.erase(BB);
          State in;
          if (BB != entry) {
            bool any = false;
            for (const llvm::BasicBlock *pred : llvm::predecessors(BB)) {
              auto pit = edge.find(pred);
              if (pit == edge.end())
                continue;
              auto eit = pit->second.find(BB);
              if (eit == pit->second.end())
                continue;
              in = any ? joinState(in, eit->second) : eit->second;
              any = true;
            }
            if (!any)
              continue;
          }
          const auto *br = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator());
          const llvm::CallBase *split = nullptr;
          const llvm::ConstantInt *splitK = nullptr;
          bool splitNe = false;
          if (br && br->isConditional())
            if (const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(br->getCondition()))
              if (icmp->getPredicate() == llvm::ICmpInst::ICMP_EQ ||
                  icmp->getPredicate() == llvm::ICmpInst::ICMP_NE) {
                const llvm::Value *lhs = icmp->getOperand(0);
                const llvm::Value *rhs = icmp->getOperand(1);
                const llvm::ConstantInt *k = llvm::dyn_cast<llvm::ConstantInt>(rhs);
                const llvm::Value *cv = lhs;
                if (!k) {
                  k = llvm::dyn_cast<llvm::ConstantInt>(lhs);
                  cv = rhs;
                }
                const auto *cb = llvm::dyn_cast<llvm::CallBase>(cv);
                if (k && cb && cb->getParent() == BB) {
                  split = cb;
                  splitK = k;
                  splitNe = icmp->getPredicate() == llvm::ICmpInst::ICMP_NE;
                }
              }
          State cur = in;
          std::unordered_map<const llvm::BasicBlock *, State> outs;
          bool branched = false;
          for (const llvm::Instruction &I : *BB) {
            if (split && &I == split) {
              atCall[split] = cur;
              auto psCall = allPieces(split);
              for (unsigned s = 0; s < br->getNumSuccessors(); ++s) {
                bool wantTrue = s == 0;
                bool wantsEq = splitNe ? !wantTrue : wantTrue;
                State acc;
                bool first = true;
                for (const Piece &p : psCall) {
                  bool take = p.any;
                  if (!take) {
                    bool eqv = p.c == splitK->getSExtValue();
                    take = wantsEq ? eqv : !eqv;
                  }
                  if (!take)
                    continue;
                  State one = applySum(F, cur, p.st, split);
                  acc = first ? std::move(one) : joinState(acc, one);
                  first = false;
                }
                if (first)
                  acc = cur;
                outs[br->getSuccessor(s)] = std::move(acc);
              }
              branched = true;
              break;
            }
            if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              unsigned a = 0;
              if (isKillStore(S, org, a)) {
                St &d = cur[Key{a, -1}];
                d.kill = true;
                d.fn.clear();
                d.arg.clear();
                d.top = false;
              } else if (isGenStore(S, org, a)) {
                St &d = cur[Key{a, -1}];
                takeFn(F, d, S->getValueOperand());
              }
              spread(F, cur);
            } else if (const auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
              if (C->isInlineAsm() || (C->getCalledFunction() && C->getCalledFunction()->isIntrinsic()))
                continue;
              atCall[C] = cur;
              auto psCall = allPieces(C);
              State acc;
              bool first = true;
              for (const Piece &p : psCall) {
                State one = applySum(F, cur, p.st, C);
                acc = first ? std::move(one) : joinState(acc, one);
                first = false;
              }
              if (!first)
                cur = std::move(acc);
            }
          }
          if (!branched) {
            blockOut[BB] = cur;
            const llvm::Instruction *term = BB->getTerminator();
            if (term)
              for (const llvm::BasicBlock *succ : llvm::successors(term))
                outs[succ] = cur;
          }
          for (auto &kv : outs) {
            // operator[] would insert an empty state and then compare equal,
            // so a block whose incoming state is still empty was never visited
            // and a store inside it was dropped.
            auto &from = edge[BB];
            auto eit = from.find(kv.first);
            if (eit == from.end() || !(eit->second == kv.second)) {
              from[kv.first] = std::move(kv.second);
              enqueue(kv.first);
            }
          }
        }
        for (const llvm::BasicBlock &BB : *F) {
          const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
          if (!R)
            continue;
          const llvm::Value *rv = R->getReturnValue();
          const auto *phi = llvm::dyn_cast_or_null<llvm::PHINode>(rv);
          bool onlyPhi = true;
          for (const llvm::Instruction &I : BB)
            if (!llvm::isa<llvm::PHINode>(I) && !llvm::isa<llvm::ReturnInst>(I))
              onlyPhi = false;
          if (phi && phi->getParent() == &BB && onlyPhi) {
            for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
              const llvm::BasicBlock *pred = phi->getIncomingBlock(i);
              auto pit = edge.find(pred);
              if (pit == edge.end() || !pit->second.count(&BB))
                continue;
              Piece p;
              p.st = pit->second[&BB];
              if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(phi->getIncomingValue(i))) {
                p.any = false;
                p.c = CI->getSExtValue();
              }
              ps.push_back(std::move(p));
            }
          } else if (auto it = blockOut.find(&BB); it != blockOut.end()) {
            Piece p;
            p.any = true;
            if (const auto *CI = llvm::dyn_cast_or_null<llvm::ConstantInt>(rv)) {
              p.any = false;
              p.c = CI->getSExtValue();
            }
            p.st = it->second;
            ps.push_back(std::move(p));
          }
        }
        if (ps.empty()) {
          Piece id;
          id.any = true;
          ps.push_back(id);
        }
        summary[F] = std::move(ps);
      };

      std::vector<const llvm::Function *> order;
      std::unordered_set<const llvm::Function *> seenF, stackF;
      std::function<void(const llvm::Function *)> dfs;
      dfs = [&](const llvm::Function *F) {
        if (!live.count(F) || !seenF.insert(F).second)
          return;
        stackF.insert(F);
        for (const llvm::Instruction &I : llvm::instructions(*F)) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!C)
            continue;
          for (const llvm::Function *T : targetsOf(C))
            if (live.count(T) && !stackF.count(T))
              dfs(T);
        }
        stackF.erase(F);
        order.push_back(F);
      };
      for (const llvm::Function *F : live)
        dfs(F);
      bool stable = false;
      for (int round = 0; round < (int)order.size() + 2 && !stable; ++round) {
        stable = true;
        for (const llvm::Function *F : order) {
          auto old = summary[F];
          solveFn(F);
          if (!(summary[F] == old))
            stable = false;
        }
      }
      if (!stable) {
        for (const llvm::Function *F : order) {
          for (Piece &p : summary[F])
            for (auto &kv : p.st) {
              kv.second.top = true;
              kv.second.kill = false;
            }
        }
      }

      std::unordered_set<const llvm::Function *> procs;
      auto harvest = [&](const State &s) {
        for (const auto &kv : s)
          procs.insert(kv.second.fn.begin(), kv.second.fn.end());
      };
      for (const auto &kv : summary)
        for (const Piece &p : kv.second)
          harvest(p.st);
      for (const auto &kv : atCall)
        harvest(kv.second);

      using FS = std::unordered_map<Key, std::unordered_set<const llvm::Function *>, KH>;
      std::unordered_map<const llvm::Function *, FS> entrySet;
      std::unordered_map<const Mem *, std::unordered_set<const llvm::Function *>> heapS;
      auto concrete = [&](const llvm::Function *F, const std::unordered_set<const llvm::Function *> &en,
                          const St *s) {
        std::unordered_set<const llvm::Function *> r;
        if (!s)
          return en;
        if (s->top)
          return procs;
        r = s->fn;
        // A parameter that is still a parameter names the functions in that
        // parameter's points-to set, not every procedure stored on any list.
        if (F)
          for (unsigned a : s->arg)
            if (a < F->arg_size())
              dumpPts(F->getArg(a), [&](P p) {
                if (p.k == 2)
                  r.insert(static_cast<const llvm::Function *>(p.obj));
              });
        if (!s->kill)
          r.insert(en.begin(), en.end());
        return r;
      };
      auto entryOf = [&](const llvm::Function *F, Key k) {
        std::unordered_set<const llvm::Function *> r;
        if (auto it = entrySet.find(F); it != entrySet.end())
          if (auto kt = it->second.find(k); kt != it->second.end())
            r = kt->second;
        if (entries.count(F))
          for (const Mem *m : memsOf(F, k))
            if (auto it = heapS.find(m); it != heapS.end())
              r.insert(it->second.begin(), it->second.end());
        return r;
      };
      auto mentioned = [&](const llvm::Function *F) {
        std::vector<Key> keys;
        if (auto it = summary.find(F); it != summary.end())
          for (const Piece &p : it->second)
            for (const auto &kv : p.st)
              keys.push_back(kv.first);
        for (const llvm::Argument &A : F->args())
          if (A.getType()->isPointerTy())
            keys.push_back(Key{A.getArgNo(), -1});
        std::sort(keys.begin(), keys.end(), [](const Key &a, const Key &b) {
          return a.arg < b.arg || (a.arg == b.arg && a.off < b.off);
        });
        keys.erase(std::unique(keys.begin(), keys.end()), keys.end());
        return keys;
      };
      bool grow = true;
      while (grow) {
        grow = false;
        auto addFS = [&](FS &dst, Key k, const std::unordered_set<const llvm::Function *> &fs) {
          auto &s = dst[k];
          for (const llvm::Function *f : fs)
            if (s.insert(f).second)
              grow = true;
        };
        for (const llvm::Function *F : order) {
          if (entries.count(F))
            for (const Piece &p : summary[F])
              for (const auto &kv : p.st) {
                auto c = concrete(F, entryOf(F, kv.first), &kv.second);
                for (const Mem *m : memsOf(F, kv.first))
                  for (const llvm::Function *f : c)
                    if (heapS[m].insert(f).second)
                      grow = true;
              }
          for (const llvm::Instruction &I : llvm::instructions(*F)) {
            const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!C)
              continue;
            auto at = atCall.find(C);
            for (const llvm::Function *G : targetsOf(C)) {
              if (!live.count(G))
                continue;
              for (const Key &k : mentioned(G)) {
                Key ck;
                if (!translate(F, C, k, ck))
                  continue;
                const St *sp = nullptr;
                if (at != atCall.end())
                  if (auto it = at->second.find(ck); it != at->second.end())
                    sp = &it->second;
                auto c = concrete(F, entryOf(F, ck), sp);
                addFS(entrySet[G], k, c);
              }
            }
          }
        }
      }

      // A list element is a variable index into an array of pointers, or a
      // pointer that this function steps by one and feeds back through a phi.
      // A constant index, including 1, is a fixed slot unless that step is
      // the loop-carried increment of this pointer.
      auto stripC = [](const llvm::Value *v) {
        while (v) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v)) {
            v = C->getOperand(0);
            continue;
          }
          if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(v)) {
            v = Fr->getOperand(0);
            continue;
          }
          break;
        }
        return v;
      };
      auto varElem = [&](const llvm::Value *v) {
        const auto *G = llvm::dyn_cast_or_null<llvm::GetElementPtrInst>(stripC(v));
        if (!G || !G->getSourceElementType()->isPointerTy() || G->getNumIndices() != 1)
          return false;
        return !llvm::isa<llvm::ConstantInt>(G->getOperand(1));
      };
      auto stepOf = [&](const llvm::Value *v, const llvm::Value *cursor) {
        const auto *G = llvm::dyn_cast_or_null<llvm::GetElementPtrInst>(stripC(v));
        if (!G || !G->getSourceElementType()->isPointerTy() || G->getNumIndices() != 1)
          return false;
        const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(G->getOperand(1));
        return CI && CI->isOne() && stripC(G->getPointerOperand()) == cursor;
      };
      std::function<bool(const llvm::Value *, std::unordered_set<const llvm::Value *> &)> cursorAddr;
      cursorAddr = [&](const llvm::Value *v, std::unordered_set<const llvm::Value *> &seen) -> bool {
        if (!v || !seen.insert(v).second)
          return false;
        const llvm::Value *x = stripC(v);
        if (varElem(x))
          return true;
        if (const auto *P = llvm::dyn_cast<llvm::PHINode>(x)) {
          for (const llvm::Value *inc : P->incoming_values())
            if (stepOf(inc, x) || varElem(inc) || cursorAddr(inc, seen))
              return true;
          return false;
        }
        if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(x))
          return cursorAddr(S->getTrueValue(), seen) || cursorAddr(S->getFalseValue(), seen);
        return false;
      };

      for (const llvm::Function *W : order) {
        if (W->isDeclaration())
          continue;
        const Org &org = ensureOrg(W);
        for (const llvm::Instruction &I : llvm::instructions(*W)) {
          const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!C || !C->isIndirectCall())
            continue;
          unsigned a = 0;
          // Kill subtracts procedures. A walk with no kill is not emptied.
          // A cursor that is not one argument does not name a list, so its
          // callees are every procedure stored into a list.
          if (!oneArg(org, C->getCalledOperand(), a)) {
            const llvm::Value *callee = C->getCalledOperand()->stripPointerCasts();
            const auto *slot = llvm::dyn_cast<llvm::LoadInst>(callee);
            std::unordered_set<const llvm::Value *> cseen;
            if (!slot || !cursorAddr(slot->getPointerOperand(), cseen))
              continue;
            bool anyCaller = false;
            for (const llvm::Use &U : W->uses()) {
              const auto *CB = llvm::dyn_cast<llvm::CallBase>(U.getUser());
              if (!CB || CB->isIndirectCall() || CB->getCalledOperand()->stripPointerCasts() != W)
                continue;
              if (!CB->getFunction() || CB->getFunction()->getParent() != &M)
                continue;
              anyCaller = true;
              for (const llvm::Function *T : procs)
                if (T && !T->isDeclaration() && T->getParent() == &M)
                  callers[T].insert(CB->getFunction());
            }
            if (!anyCaller && entries.count(W))
              for (const llvm::Function *T : procs)
                if (T && !T->isDeclaration() && T->getParent() == &M)
                  callers[T].insert(W);
            continue;
          }
          const llvm::Value *callee = C->getCalledOperand()->stripPointerCasts();
          const auto *slot = llvm::dyn_cast<llvm::LoadInst>(callee);
          std::unordered_set<const llvm::Value *> cseen;
          if (!slot || !cursorAddr(slot->getPointerOperand(), cseen))
            continue;
          Key wk{a, -1};
          const St *wst = nullptr;
          if (auto it = atCall.find(C); it != atCall.end())
            if (auto kt = it->second.find(wk); kt != it->second.end())
              wst = &kt->second;
          bool anyCaller = false;
          for (const llvm::Use &U : W->uses()) {
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(U.getUser());
            if (!CB || CB->isIndirectCall() || CB->getCalledOperand()->stripPointerCasts() != W)
              continue;
            if (!CB->getFunction() || CB->getFunction()->getParent() != &M)
              continue;
            anyCaller = true;
            Key ck;
            // The caller's list does not reduce to one argument. Every
            // procedure stored into a list is a callee of that caller.
            if (!translate(CB->getFunction(), CB, wk, ck)) {
              for (const llvm::Function *T : procs)
                if (T && !T->isDeclaration() && T->getParent() == &M)
                  callers[T].insert(CB->getFunction());
              continue;
            }
            const St *sp = nullptr;
            if (auto it = atCall.find(CB); it != atCall.end())
              if (auto kt = it->second.find(ck); kt != it->second.end())
                sp = &kt->second;
            auto held = concrete(CB->getFunction(), entryOf(CB->getFunction(), ck), sp);
            // The walker's symbolic procedure is the caller's actual.
            St framed;
            const St *use = nullptr;
            if (wst) {
              framed = *wst;
              auto args = framed.arg;
              framed.arg.clear();
              for (unsigned a : args)
                if (a < CB->arg_size())
                  takeFn(CB->getFunction(), framed, CB->getArgOperand(a));
              use = &framed;
            }
            auto tg = concrete(CB->getFunction(), held, use);
            for (const llvm::Function *T : tg)
              if (T && !T->isDeclaration() && T->getParent() == &M)
                callers[T].insert(CB->getFunction());
          }
          if (!anyCaller && entries.count(W)) {
            auto held = entryOf(W, wk);
            auto tg = concrete(W, held, wst);
            for (const llvm::Function *T : tg)
              if (T && !T->isDeclaration() && T->getParent() == &M)
                callers[T].insert(W);
          }
        }
      }
    }
  }
}

// Functions stored at one constant field of a struct that has a non-pointer
// member. An all-pointer layout is not a field: LLVM merges those layouts.
struct FieldKey {
  std::string name;
  int64_t off = 0;
  bool operator==(const FieldKey &o) const { return name == o.name && off == o.off; }
};
struct FieldHash {
  size_t operator()(const FieldKey &f) const {
    return std::hash<std::string>{}(f.name) ^ ((size_t)f.off * 1315423911u);
  }
};

// init: a global initializer, visible to every load of the field.
// spec: the class-template specialization that stored the function.
// An empty spec is a function that is not inside a class template.
struct FieldEnt {
  const llvm::Function *fn = nullptr;
  std::string spec;
  bool init = false;
  bool operator==(const FieldEnt &o) const { return fn == o.fn && spec == o.spec && init == o.init; }
};
struct FieldEntHash {
  size_t operator()(const FieldEnt &e) const {
    return std::hash<const void *>{}(e.fn) ^ std::hash<std::string>{}(e.spec) ^ (e.init ? 0x9e3779b9u : 0u);
  }
};
using FieldMap = std::unordered_map<FieldKey, std::unordered_set<FieldEnt, FieldEntHash>, FieldHash>;

// The same C struct is a different LLVM type in each module. A trailing
// ".N" is LLVM's rename of a colliding type, not a different struct.
std::string structKey(const llvm::StructType *ST) {
  if (!ST)
    return {};
  if (!ST->hasName() || ST->getName().empty())
    return std::to_string(reinterpret_cast<uintptr_t>(ST));
  std::string n = ST->getName().str();
  auto dot = n.rfind('.');
  if (dot != std::string::npos && dot + 1 < n.size()) {
    bool digits = true;
    for (size_t i = dot + 1; i < n.size(); ++i)
      if (n[i] < '0' || n[i] > '9')
        digits = false;
    if (digits)
      n.resize(dot);
  }
  return n;
}

bool mixedStruct(const llvm::StructType *ST) {
  if (!ST)
    return false;
  for (llvm::Type *E : ST->elements())
    if (!E->isPointerTy())
      return true;
  return false;
}

void noteField(FieldMap &field, const llvm::DataLayout &DL, const llvm::StructType *ST, int64_t off,
               const llvm::Function *F, const std::string &spec, bool init) {
  if (!mixedStruct(ST) || !F || off < 0)
    return;
  auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(ST));
  if (sz.isScalable() || sz.getFixedValue() == 0)
    return;
  int64_t o = off % (int64_t)sz.getFixedValue();
  if (o < 0)
    o += (int64_t)sz.getFixedValue();
  field[{structKey(ST), o}].insert(FieldEnt{F, spec, init});
}

void placeConst(const llvm::Constant *C, std::vector<std::pair<const llvm::StructType *, int64_t>> frames,
                const llvm::DataLayout &DL, FieldMap &field) {
  if (!C)
    return;
  if (const llvm::Function *F = asFunction(C)) {
    for (const auto &fr : frames)
      noteField(field, DL, fr.first, fr.second, F, {}, true);
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
      placeConst(llvm::cast<llvm::Constant>(CS->getOperand(i)), std::move(next), DL, field);
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
      placeConst(llvm::cast<llvm::Constant>(CA->getOperand(i)), std::move(next), DL, field);
    }
  }
}

void indexFields(llvm::Module &M, FieldMap &field) {
  const llvm::DataLayout &DL = M.getDataLayout();
  for (llvm::GlobalVariable &GV : M.globals())
    if (GV.hasInitializer())
      placeConst(GV.getInitializer(), {}, DL, field);
  for (llvm::Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!S)
        continue;
      const llvm::Function *Fn = asFunction(S->getValueOperand());
      if (!Fn)
        continue;
      const llvm::Value *ptr = strip(S->getPointerOperand());
      const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr);
      if (!GEP)
        continue;
      const auto *ST = llvm::dyn_cast<llvm::StructType>(GEP->getSourceElementType());
      if (!ST)
        continue;
      llvm::APInt ap(DL.getIndexSizeInBits(GEP->getPointerAddressSpace()), 0);
      if (!GEP->accumulateConstantOffset(DL, ap))
        continue;
      noteField(field, DL, ST, ap.getSExtValue(), Fn, classSpec(&F), false);
    }
  }
}

// The call and the function each state a dereferenceable size. The function
// reaches this call only when those sizes are equal. A missing size leaves
// the function in the set.
bool sameBytes(const llvm::Function *Fn, const llvm::CallBase *C) {
  unsigned i = 0;
  const unsigned nCall = C->arg_size();
  const unsigned nFun = Fn->arg_size();
  for (; i < nCall && i < nFun; ++i) {
    if (!C->paramHasAttr(i, llvm::Attribute::Dereferenceable))
      continue;
    if (!Fn->hasParamAttribute(i, llvm::Attribute::Dereferenceable))
      continue;
    if (C->getParamDereferenceableBytes(i) != Fn->getParamDereferenceableBytes(i))
      return false;
  }
  return true;
}

// Functions that reach this callee operand. A load of a mixed struct's
// constant field reaches the functions stored at that field. The LLVM
// function type is not that set. A function reaches the call when the
// dereferenceable sizes both sides state are equal.
void reachCall(const llvm::Value *root, const llvm::CallBase *C, llvm::Module &upstream, const FieldMap &field,
               std::unordered_set<const llvm::Function *> &out) {
  const llvm::Function *in = C->getFunction();
  const llvm::DataLayout &DL = in->getParent()->getDataLayout();
  std::vector<const llvm::Value *> st{root};
  std::unordered_set<const llvm::Value *> seen;
  auto keep = [&](const llvm::Function *Fn) {
    if (!Fn)
      return;
    if (const llvm::Function *U = defined(upstream, Fn->getName()))
      out.insert(U);
  };
  auto keepSized = [&](const llvm::Function *Fn) {
    if (Fn && sameBytes(Fn, C))
      keep(Fn);
  };
  while (!st.empty()) {
    const llvm::Value *V = st.back();
    st.pop_back();
    if (!V || !seen.insert(V).second)
      continue;
    if (const llvm::Function *Fn = asFunction(V)) {
      keep(Fn);
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
    } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      st.push_back(Sel->getTrueValue());
      st.push_back(Sel->getFalseValue());
    } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      const llvm::Value *ptr = strip(L->getPointerOperand());
      if (const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
        if (const auto *ST = llvm::dyn_cast<llvm::StructType>(GEP->getSourceElementType())) {
          llvm::APInt ap(DL.getIndexSizeInBits(GEP->getPointerAddressSpace()), 0);
          if (GEP->accumulateConstantOffset(DL, ap) && mixedStruct(ST)) {
            auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(ST));
            if (!sz.isScalable() && sz.getFixedValue() != 0) {
              FieldKey key{structKey(ST), ap.getSExtValue() % (int64_t)sz.getFixedValue()};
              if (key.off < 0)
                key.off += (int64_t)sz.getFixedValue();
              auto it = field.find(key);
              if (it != field.end()) {
                const std::string home = classSpec(in);
                for (const FieldEnt &e : it->second)
                  if (fieldSpecVisible(e.spec, e.init, home))
                    keepSized(e.fn);
              }
            }
          }
        }
      }
      if (!ptr)
        continue;
      for (const llvm::User *U : ptr->users()) {
        const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
        if (!SI || SI->getFunction() != in)
          continue;
        if (strip(SI->getPointerOperand()) != ptr)
          continue;
        st.push_back(SI->getValueOperand());
      }
    }
  }
}

} // namespace

ChopResult findChops(llvm::Module &upstream, llvm::Module &downstream, const std::string &file,
                     unsigned line) {
  ChopResult r;
  r.sinkFile = file;
  r.sinkLine = line;

  std::unordered_set<const llvm::Function *> sinks;
  for (llvm::Function &F : upstream) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (!onLine(I, file, line))
        continue;
      if (sinks.insert(&F).second)
        r.sinkFns.push_back(show(&F));
      break;
    }
  }

  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> callers;
  std::unordered_set<std::string> defined;
  for (llvm::Function &F : upstream)
    if (!F.isDeclaration())
      defined.insert(F.getName().str());

  FieldMap fields;
  indexFields(upstream, fields);
  indexFields(downstream, fields);
  std::unordered_set<const llvm::Function *> called;
  for (llvm::Function &F : downstream) {
    if (F.isDeclaration() || defined.count(F.getName().str()))
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!C)
        continue;
      if (const llvm::Function *D = calledDirect(C, upstream)) {
        called.insert(D);
        continue;
      }
      // The target does not reduce to one callee. The functions that reach
      // this operand do. The LLVM function type is not that set.
      if (C->isInlineAsm() || !C->isIndirectCall())
        continue;
      reachCall(C->getCalledOperand(), C, upstream, fields, called);
    }
  }
  r.called = (unsigned)called.size();

  promote(upstream);
  fillCallers(upstream, callers, called);

  std::unordered_set<const llvm::Function *> reach;
  std::queue<const llvm::Function *> q;
  for (const llvm::Function *S : sinks) {
    reach.insert(S);
    q.push(S);
  }
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
  r.reach = (unsigned)reach.size();

  std::vector<std::string> names;
  for (const llvm::Function *F : called)
    if (reach.count(F))
      names.push_back(show(F));
  std::sort(names.begin(), names.end());
  names.erase(std::unique(names.begin(), names.end()), names.end());
  r.chops = std::move(names);
  return r;
}

std::string formatChops(const ChopResult &r) {
  std::ostringstream o;
  o << "sink " << r.sinkFile << ":" << r.sinkLine << "\n";
  for (const std::string &f : r.sinkFns)
    o << "sink-fn " << f << "\n";
  o << "reach " << r.reach << "\n";
  o << "called " << r.called << "\n";
  if (r.chops.empty())
    o << "chop (none)\n";
  for (const std::string &w : r.chops)
    o << "chop " << w << "\n";
  return o.str();
}

} // namespace chain
