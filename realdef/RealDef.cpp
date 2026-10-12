#include "RealDef.hpp"

#include "llvm/Demangle/Demangle.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"

#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace llvm;

namespace realdef {

// A value placed in a global initializer. It is a write of that slot even
// though it is not a StoreInst: driver tables and codec tables are constants.
struct InitFact {
  const llvm::GlobalVariable *gv = nullptr;
  const llvm::Value *value = nullptr;
  std::string file;
  unsigned line = 0;
};

namespace {

// Bitcasts only. stripPointerCasts also drops a GEP of field 0, and that
// field is a real slot (code_ent.next is the first field).
const Value *stripCast(const Value *v) {
  std::unordered_set<const Value *> seen;
  while (v && seen.insert(v).second) {
    if (const auto *C = dyn_cast<CastInst>(v)) {
      v = C->getOperand(0);
      continue;
    }
    const auto *CE = dyn_cast<ConstantExpr>(v);
    if (CE && CE->isCast()) {
      v = CE->getOperand(0);
      continue;
    }
    break;
  }
  return v;
}

// The function a call names. A constructor alias (C1 of C2) is that function.
const Function *calledFn(const CallBase *C) {
  if (!C || C->isInlineAsm())
    return nullptr;
  const Value *v = C->getCalledOperand();
  if (!v)
    return nullptr;
  return dyn_cast<Function>(v->stripPointerCastsAndAliases());
}

std::string baseName(StringRef p) {
  auto s = p.find_last_of("/\\");
  return (s == StringRef::npos ? p : p.drop_front(s + 1)).str();
}

bool onLine(const Instruction &I, StringRef file, unsigned line) {
  const DebugLoc &DL = I.getDebugLoc();
  if (!DL || DL.getLine() != line)
    return false;
  const DILocation *S = DL.get();
  return S && S->getFile() && baseName(S->getFile()->getFilename()) == file;
}

// Field path of a pointer. The first GEP index selects the pointer, so it is
// skipped. A variable index is "*". Outer GEPs are kept, so methods[i] is
// distinguished from other pointer arrays.
std::string fieldKeyRec(const Value *v, std::unordered_set<const Value *> &seen) {
  if (!v || !seen.insert(v).second)
    return {};
  std::string key;
  const Value *cur = v->stripPointerCasts();
  if (const auto *L = dyn_cast<LoadInst>(cur))
    return fieldKeyRec(L->getPointerOperand(), seen);
  if (const auto *Al = dyn_cast<AllocaInst>(cur)) {
    for (const User *U : Al->users()) {
      const auto *S = dyn_cast<StoreInst>(U);
      if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
        continue;
      if (!S->getValueOperand()->getType()->isPointerTy())
        continue;
      std::string k = fieldKeyRec(S->getValueOperand(), seen);
      if (!k.empty())
        return k;
    }
    return {};
  }
  if (const auto *P = dyn_cast<PHINode>(cur)) {
    if (P->getNumIncomingValues() == 0)
      return {};
    std::string k = fieldKeyRec(P->getIncomingValue(0), seen);
    for (unsigned i = 1; i < P->getNumIncomingValues(); ++i)
      if (fieldKeyRec(P->getIncomingValue(i), seen) != k)
        return {};
    return k;
  }
  while (const auto *G = dyn_cast<GEPOperator>(cur)) {
    Type *ty = G->getSourceElementType();
    bool first = true;
    bool stop = false;
    for (auto it = G->idx_begin(); it != G->idx_end() && !stop; ++it) {
      if (first) {
        first = false;
        continue;
      }
      if (auto *ST = dyn_cast<StructType>(ty)) {
        const auto *CI = dyn_cast<ConstantInt>(*it);
        if (!CI) {
          key += ".*";
          stop = true;
          break;
        }
        unsigned f = (unsigned)CI->getZExtValue();
        key += "/" + (ST->hasName() ? ST->getName().str() : "struct") + "." + std::to_string(f);
        if (f < ST->getNumElements())
          ty = ST->getElementType(f);
        continue;
      }
      const auto *CI = dyn_cast<ConstantInt>(*it);
      if (!CI) {
        key += "/*";
        stop = true;
        break;
      }
      key += "/" + std::to_string(CI->getSExtValue());
      if (auto *AT = dyn_cast<ArrayType>(ty))
        ty = AT->getElementType();
      else
        break;
    }
    const Value *next = stripCast(G->getPointerOperand());
    if (next == cur || next == G || !isa<GEPOperator>(next) || !seen.insert(next).second)
      break;
    cur = next;
  }
  return key;
}

std::string fieldKey(const Value *v) {
  std::unordered_set<const Value *> seen;
  return fieldKeyRec(v, seen);
}

// Byte offset of an address, with "/*" when a trailing index is not constant.
// The key is the slot inside an object. Struct type names are not part of it,
// so a named struct and a layout-identical literal name the same slot.
std::string offsetKeyRec(const Value *v, const DataLayout &DL,
                         std::unordered_set<const Value *> &seen) {
  if (!v || !seen.insert(v).second)
    return {};
  const Value *cur = stripCast(v);
  // A zero-index struct laid over a byte address is still that byte address.
  if (const auto *G = dyn_cast<GEPOperator>(cur)) {
    if (isa<StructType>(G->getSourceElementType())) {
      bool zero = true;
      unsigned n = 0;
      for (auto it = G->idx_begin(); it != G->idx_end(); ++it, ++n) {
        const auto *CI = dyn_cast<ConstantInt>(*it);
        if (!CI || !CI->isZero())
          zero = false;
      }
      const Value *under = stripCast(G->getPointerOperand());
      if (zero && n > 0 && isa<GEPOperator>(under) &&
          !isa<StructType>(cast<GEPOperator>(under)->getSourceElementType()))
        cur = under;
    }
  }
  // A loaded pointer is a new base. Following it would name the slot the
  // pointer was loaded from, not the slot being accessed through it.
  if (isa<LoadInst>(cur))
    return {};
  if (const auto *C = dyn_cast<CastInst>(cur))
    return offsetKeyRec(C->getOperand(0), DL, seen);
  if (const auto *P = dyn_cast<PHINode>(cur)) {
    if (P->getNumIncomingValues() == 0)
      return {};
    std::string k = offsetKeyRec(P->getIncomingValue(0), DL, seen);
    for (unsigned i = 1; i < P->getNumIncomingValues(); ++i)
      if (offsetKeyRec(P->getIncomingValue(i), DL, seen) != k)
        return {};
    return k;
  }
  bool any = false;
  bool var = false;
  uint64_t off = 0;
  // Outermost named struct. Byte offset alone collides across different
  // structs stored into one pointer (every codec's tif_data).
  std::string tyName;
  while (const auto *G = dyn_cast<GEPOperator>(cur)) {
    any = true;
    Type *ty = G->getSourceElementType();
    bool first = true;
    bool stop = false;
    for (auto it = G->idx_begin(); it != G->idx_end() && !stop; ++it) {
      if (first) {
        first = false;
        // The first index selects an element. A non-zero step stays on this
        // array, so the key keeps the later field offset and records "/*".
        // Adding the stride made the next element look like another field.
        if (!isa<ConstantInt>(*it) || !cast<ConstantInt>(*it)->isZero())
          var = true;
        continue;
      }
      if (auto *ST = dyn_cast<StructType>(ty)) {
        const auto *CI = dyn_cast<ConstantInt>(*it);
        if (tyName.empty() && ST->hasName())
          tyName = ST->getName().str();
        if (!CI || CI->getZExtValue() >= ST->getNumElements()) {
          var = true;
          break;
        }
        unsigned f = (unsigned)CI->getZExtValue();
        off += DL.getStructLayout(ST)->getElementOffset(f);
        ty = ST->getElementType(f);
        continue;
      }
      Type *elem = ty;
      if (auto *AT = dyn_cast<ArrayType>(ty))
        elem = AT->getElementType();
      const auto *CI = dyn_cast<ConstantInt>(*it);
      if (!CI || !elem->isSized()) {
        var = true;
        break;
      }
      off += CI->getZExtValue() * DL.getTypeAllocSize(elem).getFixedValue();
      ty = elem;
    }
    const Value *next = stripCast(G->getPointerOperand());
    if (next == cur || next == G || !isa<GEPOperator>(next) || !seen.insert(next).second)
      break;
    cur = next;
  }
  if (!any)
    return {};
  std::string k = std::to_string(off) + (var ? "/*" : "");
  if (!tyName.empty())
    k = tyName + "@" + k;
  return k;
}

using RootSet = std::unordered_set<const Value *>;
using KeySet = std::unordered_set<std::string>;

// A call through an embedded public struct has a field path that is a prefix
// of the store into the concrete object. A bare "*" is not a prefix.
// "11" and "11/*" are the same field: one side has the element, the other any
// element. This is not enough on its own. The objects still have to match.
bool sameField(const std::string &a, const std::string &b) {
  auto split = [](const std::string &s) -> std::pair<std::string, std::string> {
    auto at = s.find('@');
    if (at == std::string::npos)
      return {{}, s};
    return {s.substr(0, at), s.substr(at + 1)};
  };
  auto stem = [](const std::string &s) -> std::string {
    if (s.empty() || s[0] < '0' || s[0] > '9')
      return {};
    auto slash = s.find('/');
    if (slash == std::string::npos)
      return s;
    if (s.compare(slash, std::string::npos, "/*") != 0)
      return {};
    return s.substr(0, slash);
  };
  auto [ta, ra] = split(a);
  auto [tb, rb] = split(b);
  if (ta != tb)
    return false;
  std::string sa = stem(ra), sb = stem(rb);
  return !sa.empty() && sa == sb;
}

bool slotMatch(const std::string &a, const std::string &b) {
  if (a.empty() || b.empty())
    return false;
  if (a == b)
    return true;
  auto pref = [](const std::string &shorter, const std::string &longer) {
    if (shorter.find('.') == std::string::npos || longer.size() <= shorter.size())
      return false;
    if (longer.compare(0, shorter.size(), shorter) != 0 || longer[shorter.size()] != '/')
      return false;
    // "T@11/*" is the element wildcard, not a nested field of "T@11".
    return longer.compare(shorter.size(), std::string::npos, "/*") != 0;
  };
  return pref(a, b) || pref(b, a);
}

void merge(RootSet &dst, const RootSet &src) { dst.insert(src.begin(), src.end()); }

bool hit(const RootSet &a, const RootSet &b) {
  if (a.empty() || b.empty())
    return false;
  const RootSet &small = a.size() < b.size() ? a : b;
  const RootSet &big = a.size() < b.size() ? b : a;
  for (const Value *v : small)
    if (big.count(v))
      return true;
  return false;
}

// A write is a store or a global initializer, keyed by struct and offset.
// An allocation is an alloca, a global, or a pointer-returning call.
// A function pointer among those writes names an indirect callee. The global
// that holds it is the class pointer of that call: the callee's pointer
// arguments carry it, and a field load of such an object carries it too.
// Two accesses are the same slot when the allocation is the same and the
// offset is the same. A class pointer on both sides must be the same global.
// From the sink, a load is replaced by the writes of that slot. A function
// that returns a field, a load, an address, or an allocation is that value.
// A store of another slot is a copy. A store of anything else is a def.
// A call through a loaded function pointer is the function written at that
// constant offset. memcpy and memmove copy the bytes in their length.
class Flow {
public:
  explicit Flow(Module &M, Module *ds = nullptr) : M_(M), ds_(ds) {
    index();
    solveDirect();
    if (ds_) {
      linkDownstream();
      if (!extra_.empty())
        solveDirect();
    }
    // A pointer variable with no field holds the allocation stored there.
    // Field stores stay demand-driven, from the sink.
    solveSlots();
    // The class pointer that selected the callee distinguishes the allocation.
    bindClassPointer();
    // A call that returns a field of its argument is that field at this call.
    summarizeForwards();
    // A pointer stored in a slot carries its offset to the load. The store
    // through that load is a write of that offset.
    propagatePointerKeys();
    indexStores();
    indexInits();
    indexByteCopies();
    // A constant offset into the object the call loads. The function written
    // there is the callee. New caller edges are solved again.
    if (resolveIndirect()) {
      solveDirect();
      solveSlots();
    }
    // Caller edges added while resolving indirect calls are part of the class.
    classOf_.clear();
    classSeen_.clear();
    // The class is recorded on the argument. The allocation that argument
    // points at carries the same class when only one class reaches it.
    carryClass();
  }

  // memcpy and memmove copy bytes. The call is not a definition of those bytes.
  static bool isByteCopy(const CallBase *C, const Value *&src) {
    src = nullptr;
    if (!C || C->arg_size() < 2)
      return false;
    const Function *F = calledFn(C);
    if (!F)
      return false;
    bool copy = false;
    if (F->isIntrinsic()) {
      Intrinsic::ID id = F->getIntrinsicID();
      copy = id == Intrinsic::memcpy || id == Intrinsic::memmove;
    } else {
      StringRef n = F->getName();
      copy = n == "memcpy" || n == "memmove" || n == "__memcpy_chk" || n == "__memmove_chk";
    }
    if (!copy)
      return false;
    src = C->getArgOperand(1);
    return true;
  }

  // The application can write this object when it can name the global, when
  // it calls the function that takes the argument, or when it passed the
  // object in. An empty set did not reduce, so it is not proved unreachable.
  bool exposed(const RootSet &want) const {
    if (!ds_)
      return false;
    ensureExposed();
    if (want.empty())
      return true;
    for (const Value *v : want) {
      if (const auto *GV = dyn_cast<GlobalVariable>(v)) {
        if (!GV->hasLocalLinkage() && !GV->hasHiddenVisibility())
          return true;
        continue;
      }
      if (const auto *A = dyn_cast<Argument>(v)) {
        if (dsCalled_.count(A->getParent()))
          return true;
      }
      if (fromDs_.count(v))
        return true;
    }
    return false;
  }

  // Functions that can call `sink`, including `sink`. A callee of the sink
  // is not in this set.
  std::unordered_set<const Function *> reaching(const Function *sink) const {
    std::unordered_set<const Function *> reach;
    if (!sink)
      return reach;
    std::vector<const Function *> q{sink};
    reach.insert(sink);
    for (size_t i = 0; i < q.size(); ++i) {
      auto it = callers_.find(q[i]);
      if (it == callers_.end())
        continue;
      for (const CallBase *C : it->second) {
        const Function *P = C->getFunction();
        if (P && reach.insert(P).second)
          q.push_back(P);
      }
    }
    return reach;
  }

  // The named object is a global the application can name, or a parameter of
  // a function the downstream calls that reaches the function containing the
  // sink. Another allocation that merely aliases the pointer is not that
  // parameter.
  std::vector<const Value *> exposedPlaces(const RootSet &want, const Function *sinkFn) const {
    std::vector<const Value *> out;
    if (!ds_ || want.empty() || !sinkFn)
      return out;
    ensureExposed();
    const auto reach = reaching(sinkFn);
    for (const Value *v : want) {
      if (const auto *GV = dyn_cast<GlobalVariable>(v)) {
        if (!GV->hasLocalLinkage() && !GV->hasHiddenVisibility())
          out.push_back(v);
        continue;
      }
      const auto *A = dyn_cast<Argument>(v);
      if (!A)
        continue;
      const Function *P = A->getParent();
      if (dsCalled_.count(P) && reach.count(P))
        out.push_back(v);
    }
    return out;
  }

  void ensureExposed() const {
    if (expReady_)
      return;
    expReady_ = true;
    if (!ds_)
      return;
    std::unordered_set<std::string> names;
    for (const Function &F : M_)
      if (!F.isDeclaration())
        names.insert(F.getName().str());
    for (Function &F : *ds_) {
      if (F.isDeclaration() || names.count(F.getName().str()))
        continue;
      for (Instruction &I : instructions(F)) {
        const auto *C = dyn_cast<CallBase>(&I);
        if (!C)
          continue;
        const Function *D = calledFn(C);
        if (!D)
          continue;
        Function *U = M_.getFunction(D->getName());
        if (U && !U->isDeclaration())
          dsCalled_.insert(U);
      }
    }
    for (const auto &kv : extra_)
      fromDs_.insert(kv.second.begin(), kv.second.end());
    fromDs_.insert(handed_.begin(), handed_.end());
  }

  // Objects a pointer may refer to. Loads of pointers are replaced by what
  // was stored there.
  RootSet objects(const Value *v) {
    v = v->stripPointerCasts();
    std::vector<const LoadInst *> loads;
    std::unordered_set<const LoadInst *> seen;
    collectLoads(v, loads, seen);
    // The loads that produce this pointer. A load that merely appears in the
    // points-to is a value stored in some slot. Solving every one of them
    // walks the module, and the store that copied it is followed separately.
    if (!loads.empty())
      solveLoads(loads, true, false);
    return expand(v, mem_);
  }

  // True when this address names a field. A load of a local does not.
  bool keyed(const Value *v) const { return !keysOf(v).empty(); }

  // The same allocation and the same class pointer. Nothing else widens it.
  bool sameObject(const RootSet &a, const RootSet &b) const {
    return hit(a, b) && sameContext(a, b);
  }

  // Stores whose address may be the same field of the same object as `addr`.
  // A byte copy also takes stores whose offset lies in the copied span.
  std::vector<const StoreInst *> aliasingStores(const Value *addr, Type *ty, const RootSet &want,
                                               bool bytes = false,
                                               std::optional<uint64_t> copyLen = std::nullopt) {
    std::vector<const StoreInst *> cs = candidates(addr);
    if (bytes)
      addCopyRange(addr, copyLen, cs);
    std::vector<const LoadInst *> bases;
    std::unordered_set<const LoadInst *> seenB;
    // The store's object is often itself a field load (available_sizes).
    // Solve those loads once, then test the allocation. Do not enqueue them
    // again from inside the fixpoint.
    bool bareAddr = indexOnly(addr);
    auto bytesOf = [&](Type *st) {
      if (bytes)
        return byteMem(st);
      return st == ty || (bareAddr && byteMem(ty) && byteMem(st));
    };
    for (const StoreInst *S : cs) {
      if (!bytesOf(S->getValueOperand()->getType()))
        continue;
      for (const Value *r : directOf(S->getPointerOperand())) {
        const auto *L = dyn_cast<LoadInst>(r);
        if (L && seenB.insert(L).second)
          bases.push_back(L);
      }
    }
    if (!bases.empty())
      solveLoads(bases, true);

    // mem_ does not change in this loop. The same address is expanded once.
    useExpCache_ = true;
    expCache_.clear();
    expDepth_.clear();
    std::vector<const StoreInst *> out;
    for (const StoreInst *S : cs) {
      if (!bytesOf(S->getValueOperand()->getType()))
        continue;
      RootSet got = expand(S->getPointerOperand(), mem_);
      if (!slotOrRange(addr, S->getPointerOperand(), want, got, bytes, copyLen))
        continue;
      if (!classesAgree(addr, S->getPointerOperand(), true))
        continue;
      if (sameObject(got, want))
        out.push_back(S);
    }
    useExpCache_ = false;
    expCache_.clear();
    expDepth_.clear();
    return out;
  }

  // Initializers of this slot whose global is the object being read.
  std::vector<InitFact> aliasingInits(const Value *addr, Type *ty, const RootSet &want,
                                     bool bytes = false) {
    std::vector<InitFact> out;
    KeySet ks = keysOf(addr);
    if (ks.empty())
      return {};
    for (const auto &e : initByKey_) {
      bool exact = false;
      bool field = false;
      for (const auto &k : ks) {
        if (slotMatch(k, e.first))
          exact = true;
        else if (sameField(k, e.first))
          field = true;
      }
      if (!exact && !field)
        continue;
      for (const InitFact &I : e.second) {
        if (!I.value)
          continue;
        if (bytes) {
          if (!byteMem(I.value->getType()))
            continue;
        } else if (I.value->getType() != ty) {
          continue;
        }
        RootSet got{I.gv};
        if (!exact && !pinnedHit(want, got))
          continue;
        if (!sameObject(got, want))
          continue;
        out.push_back(I);
      }
    }
    return out;
  }

  void indexByteCopies() {
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *C = dyn_cast<CallBase>(&I);
        const Value *src = nullptr;
        if (!isByteCopy(C, src))
          continue;
        ByteCopy b;
        b.call = C;
        b.dst = C->getArgOperand(0);
        b.src = src;
        byteCopies_.push_back(b);
      }
    }
  }

  // A byte copy whose destination is this slot. The source holds the same bytes.
  std::vector<const Value *> byteSources(const Value *addr, const RootSet &want) {
    std::vector<const LoadInst *> bases;
    std::unordered_set<const LoadInst *> seenB;
    for (const ByteCopy &B : byteCopies_) {
      for (const Value *r : directOf(B.dst)) {
        const auto *L = dyn_cast<LoadInst>(r);
        if (L && seenB.insert(L).second)
          bases.push_back(L);
      }
    }
    if (!bases.empty())
      solveLoads(bases, true);
    std::vector<const Value *> out;
    for (const ByteCopy &B : byteCopies_) {
      RootSet got = expand(B.dst, mem_);
      if (!sameSlot(addr, B.dst, want, got))
        continue;
      if (!classesAgree(addr, B.dst))
        continue;
      if (sameObject(got, want) && B.src)
        out.push_back(B.src);
    }
    return out;
  }

private:
  Module &M_;
  Module *ds_ = nullptr;
  // Upstream argument -> objects a downstream caller actually passes.
  // Filled after the first solveDirect, then solved again.
  std::unordered_map<const Argument *, RootSet> extra_;
  // Objects a downstream indirect call passes. The callee did not reduce,
  // so these are the objects handed in, not the formals of every function
  // of that type.
  RootSet handed_;
  mutable bool expReady_ = false;
  mutable std::unordered_set<const Function *> dsCalled_;
  mutable std::unordered_set<const Value *> fromDs_;
  std::unordered_map<const Function *, std::vector<const CallBase *>> callers_;
  std::unordered_map<const CallBase *, std::vector<const Function *>> resolved_;
  // A function written at a constant byte offset of a global. Vtable slots
  // and a global function pointer are the same kind of write.
  std::unordered_map<const GlobalVariable *, std::unordered_map<uint64_t, std::vector<const Function *>>> fnAt_;
  struct SlotStore {
    const Value *base = nullptr;
    uint64_t off = 0;
    const GlobalVariable *gv = nullptr;
    uint64_t gvOff = 0;
    const StoreInst *store = nullptr;
  };
  // A store of the address of such a global into an object. The call adds its
  // own constant offset to gvOff.
  std::vector<SlotStore> slotStores_;
  struct ByteCopy {
    const CallBase *call = nullptr;
    const Value *dst = nullptr;
    const Value *src = nullptr;
  };
  std::vector<ByteCopy> byteCopies_;
  std::unordered_map<const Function *, std::vector<const ReturnInst *>> rets_;
  std::vector<const Value *> ptrs_;
  std::vector<const StoreInst *> stores_;
  std::unordered_map<std::string, std::vector<const StoreInst *>> byKey_;
  std::unordered_map<std::string, std::vector<InitFact>> initByKey_;
  std::unordered_map<const Value *, RootSet> direct_;
  std::unordered_map<const LoadInst *, RootSet> mem_;
  mutable std::unordered_map<const Value *, KeySet> keys_;
  // The offset a pointer value carries. A store of that pointer writes this
  // offset of the object the pointer points to, even when the store address
  // is the pointer register itself.
  std::unordered_map<std::string, KeySet> carried_;
  std::unordered_map<const Value *, KeySet> slotCarried_;
  mutable std::unordered_map<const Value *, KeySet> loadKeys_;
  // A load whose points-to is being solved. The pointer it reads is solved
  // first, and that walk must not re-enter this load.
  std::unordered_set<const LoadInst *> solving_;
  // Downstream stores of a pointer, by the offset of the address. The call
  // edge reads the value stored there. The rest of the downstream is not solved.
  const Function *allocScope_ = nullptr;
  std::unordered_map<const Value *, RootSet> allocDone_;
  // An address a function returns, as an argument and the offset from it.
  // Computed once from the body. It does not depend on points-to.
  struct RetArg {
    bool ok = false;
    unsigned arg = 0;
    std::string key;
  };
  // A store this function performs into one of its arguments. The key is the
  // offset from that argument. The value is another argument, or the stored
  // value itself. Callees that write an argument passed through are included.
  struct ArgStore {
    unsigned slot = 0;
    std::string key;
    int valArg = -1;
    const Value *val = nullptr;
  };
  struct ArgRed {
    const Argument *arg = nullptr;
    std::string key;
  };
  struct PtrView {
    const Value *base = nullptr;
    std::string key;
  };
  std::unordered_map<const Function *, RetArg> retArg_;
  // A function whose every return is a fresh allocation. Each call is its own
  // object. The allocation instruction inside the callee is not shared.
  mutable std::unordered_map<const Function *, bool> fresh_;
  mutable std::unordered_set<const Function *> freshStack_;
  std::unordered_set<const Function *> retArgStack_;
  std::unordered_map<const Function *, std::vector<ArgStore>> argFacts_;
  std::unordered_set<const Function *> argFactsStack_;
  std::unordered_map<const Function *, std::unordered_set<const Function *>> reachFrom_;
  mutable std::unordered_map<const Function *, KeySet> dsFnKey_;
  mutable std::unordered_map<const Function *, std::vector<const LoadInst *>> retLoads_;
  // The global that is the value of a function-pointer field. The initializer
  // is that write. It names the callee.
  std::unordered_map<const Function *, std::unordered_set<const GlobalVariable *>> classPtr_;
  // A pointer reached through that callee carries the global. A field load
  // of such a pointer carries the same global.
  std::unordered_map<const Value *, std::unordered_set<const GlobalVariable *>> limit_;
  // Class of a pointer value. Copied from the argument the selecting global
  // called, through GEPs, casts, phis, and the address of a load. Empty means
  // this pointer was not given a selecting global.
  mutable std::unordered_map<const Value *, std::unordered_set<const GlobalVariable *>> classOf_;
  mutable std::unordered_set<const Value *> classSeen_;
  // A function whose return is a pointer argument, or one field of it.
  // The call is that pointer. An empty key means the argument itself.
  struct Forward {
    unsigned arg = 0;
    std::string key;
  };
  std::unordered_map<const Function *, Forward> forward_;
  mutable std::unordered_set<const CallBase *> fwdStack_;
  // Whole-module slot folding keeps a call as the call. The sink query is
  // what reads the pointer that call returns.
  bool slotFold_ = false;
  // One solveLoads iteration reads one map. The same pointer is expanded
  // once in that iteration.
  mutable bool useExpCache_ = false;
  mutable std::unordered_map<const Value *, RootSet> expCache_;
  mutable std::unordered_map<const Value *, int> expDepth_;
  // Loads an expansion read. A later round repeats an expansion only when one
  // of these loads gained a value.
  mutable std::unordered_set<const LoadInst *> *expReads_ = nullptr;
  mutable std::unordered_map<const Value *, std::unordered_set<const LoadInst *>> expReadOf_;
  mutable bool expSawCycle_ = false;

  bool pinnedHit(const RootSet &a, const RootSet &b) const {
    if (a.empty() || b.empty())
      return false;
    const RootSet &small = a.size() < b.size() ? a : b;
    const RootSet &big = a.size() < b.size() ? b : a;
    for (const Value *v : small) {
      if (!big.count(v))
        continue;
      if (isa<AllocaInst>(v) || isa<CallBase>(v) || isa<GlobalVariable>(v))
        return true;
    }
    return false;
  }

  // An integer or a vector of integers is the bytes of a buffer. A SIMD load
  // and a scalar store of those bytes are the same slot.
  static bool byteMem(Type *t) {
    if (!t)
      return false;
    if (t->isIntegerTy() || t->isFloatingPointTy())
      return true;
    if (const auto *V = dyn_cast<VectorType>(t)) {
      Type *e = V->getElementType();
      return e->isIntegerTy() || e->isFloatingPointTy();
    }
    return false;
  }

  // A raw element index has no struct name. It is one buffer only when both
  // sides name that buffer's allocation. Escape would also accept every other
  // array a public pointer might reach.
  bool indexOnly(const Value *addr) const {
    KeySet ks = keysOf(addr);
    if (ks.empty())
      return false;
    for (const auto &k : ks)
      if (k.find('@') != std::string::npos)
        return false;
    return true;
  }

  // Exact slot, or the same field of one pinned object ("11" and "11/*").
  bool sameSlot(const Value *a, const Value *b, const RootSet &oa, const RootSet &ob) {
    KeySet ka = keysOf(a);
    KeySet kb = keysOf(b);
    bool exact = false;
    bool field = false;
    for (const auto &x : ka)
      for (const auto &y : kb) {
        if (slotMatch(x, y))
          exact = true;
        else if (sameField(x, y))
          field = true;
      }
    if (exact)
      return true;
    return field && pinnedHit(oa, ob);
  }

  void noteClassPointer(const Value *V, const Function *Fn, std::unordered_set<const Value *> &seen) {
    if (!V || !seen.insert(V).second)
      return;
    for (const User *U : V->users()) {
      if (const auto *GV = dyn_cast<GlobalVariable>(U))
        classPtr_[Fn].insert(GV);
      else if (const auto *C = dyn_cast<Constant>(U))
        noteClassPointer(C, Fn, seen);
    }
  }

  // The class pointer carried by this object set.
  std::unordered_set<const GlobalVariable *> contextOf(const RootSet &s) const {
    std::unordered_set<const GlobalVariable *> out;
    for (const Value *v : s) {
      auto it = limit_.find(v);
      if (it == limit_.end())
        continue;
      out.insert(it->second.begin(), it->second.end());
    }
    return out;
  }

  // The selecting global this pointer value carries. A load carries the class
  // of the address it reads through: that is the pointer the access holds.
  // The objects the load may point at are a different component.
  std::unordered_set<const GlobalVariable *> classOf(const Value *v) const {
    static const std::unordered_set<const GlobalVariable *> empty;
    v = stripCast(v);
    if (!v)
      return empty;
    auto it = classOf_.find(v);
    if (it != classOf_.end())
      return it->second;
    if (!classSeen_.insert(v).second)
      return empty;
    std::unordered_set<const GlobalVariable *> out;
    auto take = [&](const Value *p) {
      auto c = classOf(p);
      out.insert(c.begin(), c.end());
    };
    if (const auto *A = dyn_cast<Argument>(v)) {
      // A function the global selected has that global, and no other. A shared
      // callee has no global of its own: its class is the class of the pointer
      // each caller passed.
      auto lit = limit_.find(A);
      if (lit != limit_.end() && !lit->second.empty()) {
        out = lit->second;
      } else {
        auto cit = callers_.find(A->getParent());
        if (cit != callers_.end()) {
          for (const CallBase *C : cit->second) {
            if (A->getArgNo() >= C->arg_size())
              continue;
            take(C->getArgOperand(A->getArgNo()));
          }
        }
      }
    } else if (const auto *Al = dyn_cast<AllocaInst>(v)) {
      // The local holds the pointer. The class is the class of that pointer.
      for (const User *U : Al->users()) {
        const auto *S = dyn_cast<StoreInst>(U);
        if (!S || stripCast(S->getPointerOperand()) != Al)
          continue;
        if (!S->getValueOperand()->getType()->isPointerTy())
          continue;
        take(S->getValueOperand());
      }
    } else if (const auto *G = dyn_cast<GEPOperator>(v)) {
      take(G->getPointerOperand());
    } else if (const auto *C = dyn_cast<CastInst>(v)) {
      take(C->getOperand(0));
    } else if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        take(P->getIncomingValue(i));
    } else if (const auto *S = dyn_cast<SelectInst>(v)) {
      take(S->getTrueValue());
      take(S->getFalseValue());
    } else if (const auto *L = dyn_cast<LoadInst>(v)) {
      take(L->getPointerOperand());
    } else if (const auto *C = dyn_cast<CallBase>(v)) {
      const Forward *f = forwardOf(C);
      if (f && f->arg < C->arg_size())
        take(C->getArgOperand(f->arg));
    }
    classSeen_.erase(v);
    classOf_[v] = std::move(out);
    return classOf_.find(v)->second;
  }

  // Two nonempty classes meet only on a shared global. Points-to still keeps
  // an edge while one class is empty. The def filter (`closed`) does not.
  bool classesAgree(const Value *a, const Value *b, bool closed = false) const {
    auto ca = classOf(a);
    auto cb = classOf(b);
    if (ca.empty() && cb.empty())
      return true;
    if (ca.empty() || cb.empty()) {
      if (!closed)
        return true;
      // The empty side is a different object when its function was selected by
      // a global: that global did not reach this pointer. A shared function
      // has no global, and its store still writes the classed object.
      const Value *emptySide = ca.empty() ? a : b;
      const Function *F = nullptr;
      if (const auto *I = dyn_cast<Instruction>(stripCast(emptySide)))
        F = I->getFunction();
      else if (const auto *Arg = dyn_cast<Argument>(stripCast(emptySide)))
        F = Arg->getParent();
      if (F) {
        for (const Argument &Arg : F->args()) {
          auto lit = limit_.find(&Arg);
          if (lit != limit_.end() && !lit->second.empty())
            return false;
        }
      }
      return true;
    }
    for (const GlobalVariable *g : ca)
      if (cb.count(g))
        return true;
    return false;
  }

  // Object sets alias when a class pointer reached both and the pointers
  // differ. The class of the access itself is classesAgree.
  bool sameContext(const RootSet &a, const RootSet &b) const {
    auto ca = contextOf(a);
    auto cb = contextOf(b);
    // The class is recorded on the argument the global selected. The
    // allocation value often has no class of its own, and still meets that
    // argument. Two nonempty sets agree only when they share a global.
    if (ca.empty() || cb.empty())
      return true;
    for (const GlobalVariable *g : ca)
      if (cb.count(g))
        return true;
    return false;
  }

  // The callee selected by a function-pointer field receives only the global
  // that held that pointer. One allocation call is then a different object
  // for each such global.
  void bindClassPointer() {
    for (const auto &kv : classPtr_) {
      const Function *F = kv.first;
      if (!F || F->isDeclaration())
        continue;
      for (const Argument &A : F->args()) {
        if (!A.getType()->isPointerTy())
          continue;
        limit_[&A] = kv.second;
      }
    }
  }

  // An allocation reached from one classed argument carries that class.
  // Two classes on one allocation leave it shared: the classes do not merge.
  void carryClass() {
    std::unordered_map<const Value *, std::unordered_set<const GlobalVariable *>> got;
    std::unordered_set<const Value *> shared;
    for (const auto &kv : limit_) {
      if (!isa<Argument>(kv.first) || kv.second.empty())
        continue;
      for (const Value *p : pinsOf(directOf(kv.first))) {
        if (p == kv.first || shared.count(p))
          continue;
        auto it = got.find(p);
        if (it != got.end() && it->second != kv.second) {
          shared.insert(p);
          got.erase(p);
          continue;
        }
        got[p] = kv.second;
      }
    }
    for (const auto &kv : got) {
      auto &dst = limit_[kv.first];
      if (dst.empty())
        dst = kv.second;
    }
  }

  void addConstSlot(const Value *V, const Function *Fn,
                    std::unordered_map<std::string, std::vector<const Function *>> &fieldFns,
                    std::unordered_set<const Value *> &seen) {
    if (!V || !seen.insert(V).second)
      return;
    for (const User *U : V->users()) {
      if (const auto *CE = dyn_cast<ConstantExpr>(U)) {
        if (CE->isCast())
          addConstSlot(CE, Fn, fieldFns, seen);
        continue;
      }
      const auto *CS = dyn_cast<ConstantStruct>(U);
      if (!CS)
        continue;
      const auto *ST = cast<StructType>(CS->getType());
      for (unsigned i = 0; i < CS->getNumOperands(); ++i) {
        if (CS->getOperand(i)->stripPointerCasts() != V->stripPointerCasts())
          continue;
        if (ST->hasName())
          fieldFns["/" + ST->getName().str() + "." + std::to_string(i)].push_back(Fn);
        {
          std::unordered_set<const Value *> seenG;
          noteClassPointer(CS, Fn, seenG);
        }
        // Same layout, whatever the LLVM struct is named. Size plus field
        // offset is that field.
        if (i < ST->getNumElements() && ST->isSized()) {
          auto *mut = const_cast<StructType *>(ST);
          uint64_t sz = M_.getDataLayout().getTypeAllocSize(mut).getFixedValue();
          uint64_t off = M_.getDataLayout().getStructLayout(mut)->getElementOffset(i);
          fieldFns["L" + std::to_string(sz) + "@" + std::to_string(off)].push_back(Fn);
        }
      }
      addConstSlot(CS, Fn, fieldFns, seen);
    }
  }

  // Layout identity of a function-pointer slot: sizeof(struct) and the field offset.
  std::string layoutKeyOf(const Value *v, std::unordered_set<const Value *> &seen) const {
    if (!v || !seen.insert(v).second)
      return {};
    const DataLayout &DL = M_.getDataLayout();
    // The address of field 0 is the address of the object. The field name is
    // fieldKey. Layout stays the byte offset, which is 0 for that field.
    const Value *cur = v->stripPointerCasts();
    if (const auto *L = dyn_cast<LoadInst>(cur))
      return layoutKeyOf(L->getPointerOperand(), seen);
    if (const auto *C = dyn_cast<CastInst>(cur))
      return layoutKeyOf(C->getOperand(0), seen);
    if (const auto *Al = dyn_cast<AllocaInst>(cur)) {
      for (const User *U : Al->users()) {
        const auto *S = dyn_cast<StoreInst>(U);
        if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
          continue;
        if (!S->getValueOperand()->getType()->isPointerTy())
          continue;
        std::string k = layoutKeyOf(S->getValueOperand(), seen);
        if (!k.empty())
          return k;
      }
      return {};
    }
    if (const auto *P = dyn_cast<PHINode>(cur)) {
      if (P->getNumIncomingValues() == 0)
        return {};
      std::string k = layoutKeyOf(P->getIncomingValue(0), seen);
      for (unsigned i = 1; i < P->getNumIncomingValues(); ++i)
        if (layoutKeyOf(P->getIncomingValue(i), seen) != k)
          return {};
      return k;
    }
    const auto *G = dyn_cast<GEPOperator>(cur);
    if (!G)
      return {};
    auto *ST = dyn_cast<StructType>(G->getSourceElementType());
    if (!ST || !ST->isSized())
      return layoutKeyOf(G->getPointerOperand(), seen);
    bool first = true;
    uint64_t off = 0;
    bool got = false;
    Type *ty = ST;
    for (auto it = G->idx_begin(); it != G->idx_end(); ++it) {
      if (first) {
        first = false;
        continue;
      }
      auto *STy = dyn_cast<StructType>(ty);
      const auto *CI = dyn_cast<ConstantInt>(*it);
      if (!STy || !CI || CI->getZExtValue() >= STy->getNumElements())
        return {};
      unsigned f = (unsigned)CI->getZExtValue();
      off += DL.getStructLayout(STy)->getElementOffset(f);
      ty = STy->getElementType(f);
      got = true;
    }
    if (!got)
      return {};
    uint64_t sz = DL.getTypeAllocSize(ST).getFixedValue();
    return "L" + std::to_string(sz) + "@" + std::to_string(off);
  }

  static const RootSet &lookup(const Value *v, const std::unordered_map<const Value *, RootSet> &m) {
    static const RootSet empty;
    if (!v)
      return empty;
    auto it = m.find(v->stripPointerCasts());
    return it == m.end() ? empty : it->second;
  }

  // Constant GEPs peel off. What remains is the object, plus a byte offset.
  bool splitPtr(const Value *v, const Value *&base, uint64_t &off) const {
    off = 0;
    const DataLayout &DL = M_.getDataLayout();
    v = stripCast(v);
    while (const auto *G = dyn_cast<GEPOperator>(v)) {
      APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
      if (!G->accumulateConstantOffset(DL, ap))
        return false;
      off += ap.getZExtValue();
      v = stripCast(G->getPointerOperand());
    }
    base = v;
    return base != nullptr;
  }

  bool constGlobal(const Value *v, const GlobalVariable *&gv, uint64_t &off) const {
    const Value *base = nullptr;
    if (!splitPtr(v, base, off))
      return false;
    gv = dyn_cast<GlobalVariable>(base);
    return gv != nullptr;
  }

  void noteFnAt(const GlobalVariable *gv, uint64_t off, const Function *Fn) {
    if (!gv || !Fn || Fn->isIntrinsic() || Fn->isDeclaration())
      return;
    auto &row = fnAt_[gv][off];
    for (const Function *E : row)
      if (E == Fn)
        return;
    row.push_back(Fn);
  }

  void walkFnAt(const GlobalVariable *gv, const Constant *c, uint64_t base) {
    if (!c)
      return;
    if (const auto *Fn = dyn_cast<Function>(stripCast(c))) {
      noteFnAt(gv, base, Fn);
      return;
    }
    const DataLayout &DL = M_.getDataLayout();
    if (const auto *CS = dyn_cast<ConstantStruct>(c)) {
      auto *ST = const_cast<StructType *>(CS->getType());
      if (!ST->isSized())
        return;
      const StructLayout *SL = DL.getStructLayout(ST);
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        walkFnAt(gv, CS->getOperand(i), base + SL->getElementOffset(i));
      return;
    }
    if (const auto *CA = dyn_cast<ConstantArray>(c)) {
      Type *et = CA->getType()->getElementType();
      if (!et->isSized())
        return;
      uint64_t sz = DL.getTypeAllocSize(et).getFixedValue();
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        walkFnAt(gv, CA->getOperand(i), base + (uint64_t)i * sz);
    }
  }

  void indexFnSlots() {
    for (GlobalVariable &G : M_.globals()) {
      if (!G.hasInitializer() || G.isDeclaration())
        continue;
      walkFnAt(&G, G.getInitializer(), 0);
    }
    for (const StoreInst *S : stores_) {
      const GlobalVariable *gv = nullptr;
      uint64_t go = 0;
      if (const auto *Fn = dyn_cast<Function>(stripCast(S->getValueOperand()))) {
        if (constGlobal(S->getPointerOperand(), gv, go))
          noteFnAt(gv, go, Fn);
        continue;
      }
      if (!constGlobal(S->getValueOperand(), gv, go) || !fnAt_.count(gv))
        continue;
      const Value *base = nullptr;
      uint64_t bo = 0;
      if (!splitPtr(S->getPointerOperand(), base, bo) || isa<Constant>(base))
        continue;
      SlotStore ss;
      ss.base = base;
      ss.off = bo;
      ss.gv = gv;
      ss.gvOff = go;
      ss.store = S;
      slotStores_.push_back(ss);
    }
  }

  // True when some path reaches a return without another write of this slot.
  // A constructor that overwrites the base vptr does not leave the base one.
  bool storeLeaves(const StoreInst *from, const std::unordered_set<const Instruction *> &over) const {
    std::vector<const Instruction *> wl;
    std::unordered_set<const Instruction *> seen;
    auto pushAfter = [&](const Instruction *I) {
      if (const Instruction *N = I->getNextNode()) {
        wl.push_back(N);
        return;
      }
      for (const BasicBlock *S : successors(I->getParent()))
        if (!S->empty())
          wl.push_back(&S->front());
    };
    pushAfter(from);
    while (!wl.empty()) {
      const Instruction *I = wl.back();
      wl.pop_back();
      if (!seen.insert(I).second)
        continue;
      if (over.count(I))
        continue;
      if (isa<ReturnInst>(I))
        return true;
      pushAfter(I);
    }
    return false;
  }

  // The call loads a function pointer from a constant offset. That offset
  // names the function in the global, or in the global whose address was
  // stored into this object.
  bool resolveIndirect() {
    slotFold_ = true;
    indexFnSlots();
    // A member pointer is stored as { function address, this adjustment }.
    // The call inttoptr's the first field. That store names the callee.
    struct MemFn {
      const StoreInst *store = nullptr;
      const Function *fn = nullptr;
    };
    std::vector<MemFn> memFns;
    auto fnIn = [](const Value *v, auto &&self) -> const Function * {
      if (!v)
        return nullptr;
      if (const auto *Fn = dyn_cast<Function>(v->stripPointerCasts()))
        return Fn->isDeclaration() ? nullptr : Fn;
      if (const auto *CE = dyn_cast<ConstantExpr>(v)) {
        if (CE->getOpcode() == Instruction::PtrToInt)
          return self(CE->getOperand(0), self);
      }
      if (const auto *CS = dyn_cast<ConstantStruct>(v)) {
        if (CS->getNumOperands() == 0)
          return nullptr;
        return self(CS->getOperand(0), self);
      }
      return nullptr;
    };
    for (const StoreInst *S : stores_) {
      const Function *Fn = fnIn(S->getValueOperand(), fnIn);
      if (!Fn)
        continue;
      memFns.push_back({S, Fn});
    }
    bool grew = false;
    std::unordered_map<const Value *, RootSet> cache;
    auto objs = [&](const Value *v) {
      v = stripCast(v);
      auto it = cache.find(v);
      if (it != cache.end())
        return it->second;
      RootSet r = objects(v);
      cache.emplace(v, r);
      return r;
    };
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *C = dyn_cast<CallBase>(&I);
        if (!C || calledFn(C) || C->isInlineAsm())
          continue;
        auto rit = resolved_.find(C);
        if (rit != resolved_.end() && !rit->second.empty())
          continue;
        const auto *L = dyn_cast<LoadInst>(stripCast(C->getCalledOperand()));
        if (!L)
          continue;
        const Value *base = nullptr;
        uint64_t off = 0;
        if (!splitPtr(L->getPointerOperand(), base, off))
          continue;
        std::vector<const Function *> found;
        std::unordered_set<const Function *> uniq;
        auto addAt = [&](const GlobalVariable *gv, uint64_t at) {
          auto git = fnAt_.find(gv);
          if (git == fnAt_.end())
            return;
          auto oit = git->second.find(at);
          if (oit == git->second.end())
            return;
          for (const Function *Fn : oit->second)
            if (uniq.insert(Fn).second)
              found.push_back(Fn);
        };
        if (const auto *GV = dyn_cast<GlobalVariable>(stripCast(base))) {
          addAt(GV, off);
        } else if (const auto *L2 = dyn_cast<LoadInst>(stripCast(base))) {
          const Value *slot = nullptr;
          uint64_t slotOff = 0;
          if (!splitPtr(L2->getPointerOperand(), slot, slotOff))
            continue;
          RootSet obj = objs(slot);
          std::vector<const SlotStore *> hits;
          std::unordered_set<const Instruction *> overs;
          for (const SlotStore &ss : slotStores_) {
            if (ss.off != slotOff || !ss.store)
              continue;
            if (!hit(objs(ss.base), obj))
              continue;
            hits.push_back(&ss);
            overs.insert(ss.store);
          }
          for (const SlotStore *ss : hits) {
            if (!storeLeaves(ss->store, overs))
              continue;
            addAt(ss->gv, ss->gvOff + off);
          }
        }
        // A byte copy writes the function pointer that was in the source.
        // Field 0 has the same address as the object, so the copy is what
        // names the callee.
        if (found.empty()) {
          for (const ByteCopy &B : byteCopies_) {
            const Value *db = nullptr;
            uint64_t dOff = 0;
            if (!B.call || B.call->arg_size() < 3 || !splitPtr(B.dst, db, dOff))
              continue;
            const auto *Len = dyn_cast<ConstantInt>(B.call->getArgOperand(2));
            if (!Len)
              continue;
            uint64_t n = Len->getZExtValue();
            if (off < dOff || off >= dOff + n)
              continue;
            const GlobalVariable *gv = nullptr;
            uint64_t sOff = 0;
            if (!constGlobal(B.src, gv, sOff) || !fnAt_.count(gv))
              continue;
            // The copy and the call name the same object. Asking whether two
            // different pointers alias here solves the module.
            if (stripCast(db) != stripCast(base))
              continue;
            addAt(gv, sOff + (off - dOff));
          }
        }
        if (found.empty())
          continue;
        resolved_[C] = std::move(found);
        for (const Function *Fn : resolved_[C])
          callers_[Fn].push_back(C);
        grew = true;
      }
    }
    // The virtual call is a caller only after the load above is resolved.
    // The member pointer is stored by that callee, so the object set has to
    // include the receiver before the stored function is named.
    if (grew)
      solveDirect();
    cache.clear();
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *C = dyn_cast<CallBase>(&I);
        if (!C || calledFn(C) || C->isInlineAsm())
          continue;
        auto rit = resolved_.find(C);
        if (rit != resolved_.end() && !rit->second.empty())
          continue;
        if (dyn_cast<LoadInst>(stripCast(C->getCalledOperand())))
          continue;
        // inttoptr(extractvalue(load {fn, adj}, 0)). The functions stored
        // into that slot are the callees. A virtual bit takes the other
        // incoming of the phi and is not this load.
        std::vector<const LoadInst *> mloads;
        std::unordered_set<const Value *> mseen;
        auto memLoad = [&](auto &&self, const Value *v) -> void {
          v = stripCast(v);
          if (!v || !mseen.insert(v).second)
            return;
          if (const auto *IP = dyn_cast<IntToPtrInst>(v)) {
            self(self, IP->getOperand(0));
            return;
          }
          if (const auto *E = dyn_cast<ExtractValueInst>(v)) {
            if (E->getNumIndices() == 1 && E->getIndices()[0] == 0)
              self(self, E->getAggregateOperand());
            return;
          }
          if (const auto *P = dyn_cast<PHINode>(v)) {
            for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
              self(self, P->getIncomingValue(i));
            return;
          }
          if (const auto *Ld = dyn_cast<LoadInst>(v))
            if (Ld->getType()->isAggregateType())
              mloads.push_back(Ld);
        };
        memLoad(memLoad, C->getCalledOperand());
        if (mloads.empty())
          continue;
        std::vector<const Function *> found;
        std::unordered_set<const Function *> uniq;
        for (const LoadInst *Ld : mloads) {
          std::vector<const MemFn *> hits;
          std::unordered_set<const Instruction *> overs;
          RootSet obj = objs(Ld->getPointerOperand());
          for (const MemFn &M : memFns) {
            if (!sameSlot(Ld->getPointerOperand(), M.store->getPointerOperand(), obj,
                          objs(M.store->getPointerOperand())))
              continue;
            if (!sameObject(objs(M.store->getPointerOperand()), obj))
              continue;
            hits.push_back(&M);
            overs.insert(M.store);
          }
          for (const MemFn *M : hits) {
            if (!storeLeaves(M->store, overs))
              continue;
            if (uniq.insert(M->fn).second)
              found.push_back(M->fn);
          }
        }
        if (found.empty())
          continue;
        resolved_[C] = std::move(found);
        for (const Function *Fn : resolved_[C])
          callers_[Fn].push_back(C);
        grew = true;
      }
    }
    slotFold_ = false;
    return grew;
  }

  void index() {
    std::unordered_map<std::string, std::vector<const Function *>> fieldFns;
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        if (const auto *R = dyn_cast<ReturnInst>(&I)) {
          if (R->getReturnValue() && R->getReturnValue()->getType()->isPointerTy())
            rets_[&F].push_back(R);
        }
        if (const auto *S = dyn_cast<StoreInst>(&I)) {
          stores_.push_back(S);
          if (const auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
            std::string k = fieldKey(S->getPointerOperand());
            if (!k.empty())
              fieldFns[k].push_back(Fn);
          }
        }
      }
    }
    // Driver tables are constant initializers, not stores.
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      std::unordered_set<const Value *> seen;
      addConstSlot(&F, &F, fieldFns, seen);
    }
    for (Function &F : M_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *C = dyn_cast<CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        std::vector<const Function *> tg;
        if (const Function *D = calledFn(C)) {
          if (!D->isIntrinsic())
            tg.push_back(D);
        } else {
          std::string k = fieldKey(C->getCalledOperand());
          std::unordered_set<const Value *> lseen;
          std::string lk = layoutKeyOf(C->getCalledOperand(), lseen);
          std::unordered_set<const Function *> uniq;
          for (const auto &e : fieldFns) {
            bool named = !k.empty() && slotMatch(k, e.first);
            bool layout = !lk.empty() && lk == e.first;
            if (!named && !layout)
              continue;
            for (const Function *Fn : e.second)
              if (uniq.insert(Fn).second)
                tg.push_back(Fn);
          }
        }
        resolved_[C] = std::move(tg);
        for (const Function *T : resolved_[C])
          callers_[T].push_back(C);
      }
      for (Argument &A : F.args())
        if (A.getType()->isPointerTy())
          ptrs_.push_back(&A);
      for (Instruction &I : instructions(F))
        if (I.getType()->isPointerTy())
          ptrs_.push_back(&I);
    }
    for (GlobalVariable &G : M_.globals())
      ptrs_.push_back(&G);
  }

  RootSet evalDirect(const Value *v, const std::unordered_map<const Value *, RootSet> &prev) const {
    v = v->stripPointerCasts();
    RootSet out;
    if (isa<AllocaInst>(v) || isa<GlobalVariable>(v)) {
      out.insert(v);
      return out;
    }
    if (const auto *L = dyn_cast<LoadInst>(v)) {
      out.insert(L);
      return out;
    }
    // A call is its own object. Folding in the callee's return value would
    // make every call to that function the same allocation.
    if (const auto *C = dyn_cast<CallBase>(v)) {
      out.insert(C);
      return out;
    }
    if (const auto *A = dyn_cast<Argument>(v)) {
      // Keep the argument even when callers are known. A cycle of arguments
      // otherwise collapses to nothing, and a path that enters from outside
      // stays visible next to the callers' objects.
      out.insert(A);
      auto it = callers_.find(A->getParent());
      if (it != callers_.end()) {
        for (const CallBase *C : it->second) {
          if (A->getArgNo() >= C->arg_size())
            continue;
          const Value *act = stripCast(C->getArgOperand(A->getArgNo()));
          merge(out, lookup(act, prev));
          // -O0 passes the argument through a load of its local. That load's
          // value is the caller's argument, so this parameter carries the
          // same allocation.
          const auto *Ld = dyn_cast<LoadInst>(act);
          if (!Ld)
            continue;
          const auto *Al = dyn_cast<AllocaInst>(stripCast(Ld->getPointerOperand()));
          if (!Al)
            continue;
          const Argument *held = nullptr;
          bool ok = true;
          for (const User *U : Al->users()) {
            const auto *S = dyn_cast<StoreInst>(U);
            if (!S || stripCast(S->getPointerOperand()) != Al)
              continue;
            const Value *sv = stripCast(S->getValueOperand());
            if (const auto *K = dyn_cast<Constant>(sv)) {
              if (K->isNullValue())
                continue;
            }
            const auto *SA = dyn_cast<Argument>(sv);
            if (!SA || (held && held != SA)) {
              ok = false;
              break;
            }
            held = SA;
          }
          if (ok && held)
            merge(out, lookup(held, prev));
        }
      }
      auto ex = extra_.find(A);
      if (ex != extra_.end())
        merge(out, ex->second);
      return out;
    }
    if (const auto *G = dyn_cast<GEPOperator>(v))
      return lookup(G->getPointerOperand(), prev);
    if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        merge(out, lookup(P->getIncomingValue(i), prev));
      return out;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      merge(out, lookup(S->getTrueValue(), prev));
      merge(out, lookup(S->getFalseValue(), prev));
      return out;
    }
    if (const auto *C = dyn_cast<CastInst>(v))
      return lookup(C->getOperand(0), prev);
    return out;
  }

  void solveDirect() {
    std::unordered_map<const Value *, RootSet> cur;
    for (;;) {
      bool grew = false;
      std::unordered_map<const Value *, RootSet> next;
      for (const Value *v : ptrs_) {
        RootSet n = evalDirect(v, cur);
        auto it = cur.find(v->stripPointerCasts());
        if (it == cur.end() || it->second != n)
          grew = true;
        next[v->stripPointerCasts()] = std::move(n);
      }
      cur.swap(next);
      if (!grew)
        break;
    }
    direct_.swap(cur);
  }

  RootSet directOf(const Value *v) const {
    if (!v)
      return {};
    v = v->stripPointerCasts();
    auto it = direct_.find(v);
    if (it != direct_.end())
      return it->second;
    return evalDirect(v, direct_);
  }

  static RootSet pinsOf(const RootSet &s) {
    RootSet o;
    for (const Value *v : s)
      if (isa<AllocaInst>(v) || isa<CallBase>(v) || isa<GlobalVariable>(v))
        o.insert(v);
    return o;
  }

  // One struct field, without walking phis. Used only to match a downstream
  // store of an upstream pointer with the load that passes it onward.
  static std::string flatKey(const Value *p) {
    p = stripCast(p);
    const auto *G = dyn_cast<GEPOperator>(p);
    if (!G)
      return {};
    auto *ST = dyn_cast<StructType>(G->getSourceElementType());
    if (!ST || !ST->hasName())
      return {};
    std::string k = ST->getName().str();
    bool first = true;
    for (auto it = G->idx_begin(); it != G->idx_end(); ++it) {
      if (first) {
        first = false;
        continue;
      }
      const auto *CI = dyn_cast<ConstantInt>(*it);
      if (!CI)
        return k + "/*";
      k += "/" + std::to_string(CI->getZExtValue());
    }
    return k;
  }

  // Objects an upstream function writes through an argument with no field
  // offset (`*aface = malloc`). A call that forwards that argument counts
  // too (`FT_New_Memory_Face` passes `aface` into `ft_open_face_internal`).
  // Field stores (`cinfo->mem = ...`) are not a new object for the slot.
  RootSet writtenThrough(const Function *F, unsigned argNo,
                         std::unordered_set<const Argument *> &seen) const {
    RootSet o;
    if (!F || F->isDeclaration() || argNo >= F->arg_size())
      return o;
    const Argument *A = F->getArg(argNo);
    if (!seen.insert(A).second)
      return o;
    for (const StoreInst *S : stores_) {
      if (S->getFunction() != F)
        continue;
      if (!S->getValueOperand()->getType()->isPointerTy())
        continue;
      if (stripCast(S->getPointerOperand()) != A)
        continue;
      RootSet pins = pinsOf(directOf(S->getValueOperand()));
      // `*aface = face` where face is still an alloca (its address escaped,
      // so mem2reg left it). The pins are the stores into that alloca.
      if (pins.empty()) {
        if (const auto *L = dyn_cast<LoadInst>(stripCast(S->getValueOperand()))) {
          const Value *slot = stripCast(L->getPointerOperand());
          if (isa<AllocaInst>(slot) && L->getFunction() == F) {
            for (const StoreInst *T : stores_) {
              if (T->getFunction() != F || T == S)
                continue;
              if (!T->getValueOperand()->getType()->isPointerTy())
                continue;
              if (stripCast(T->getPointerOperand()) != slot)
                continue;
              merge(pins, pinsOf(directOf(T->getValueOperand())));
            }
            // The callee stored through this alloca (`open_face(..., &face)`).
            for (Instruction &J : instructions(*const_cast<Function *>(F))) {
              const auto *C = dyn_cast<CallBase>(&J);
              if (!C)
                continue;
              auto cit = resolved_.find(C);
              if (cit == resolved_.end())
                continue;
              for (unsigned i = 0; i < C->arg_size(); ++i) {
                if (stripCast(C->getArgOperand(i)) != slot)
                  continue;
                for (const Function *G : cit->second)
                  merge(pins, writtenThrough(G, i, seen));
              }
            }
          }
        }
      }
      merge(o, pins);
    }
    for (Instruction &I : instructions(*const_cast<Function *>(F))) {
      const auto *C = dyn_cast<CallBase>(&I);
      if (!C)
        continue;
      auto it = resolved_.find(C);
      if (it == resolved_.end())
        continue;
      for (unsigned i = 0; i < C->arg_size(); ++i) {
        if (stripCast(C->getArgOperand(i)) != A)
          continue;
        for (const Function *G : it->second)
          merge(o, writtenThrough(G, i, seen));
      }
    }
    return o;
  }

  // Follow only the pointers that downstream carries from one upstream call
  // to the next. A returned malloc, or a pointer stored through an
  // out-parameter, is the object of the later argument. Unrelated downstream
  // memory is not visited.
  void linkDownstream() {
    std::unordered_map<std::string, const Function *> usByName;
    for (Function &F : M_)
      if (!F.isDeclaration())
        usByName[F.getName().str()] = &F;

    std::unordered_map<const Value *, std::vector<const LoadInst *>> loadsByPtr;
    std::unordered_map<std::string, std::vector<const LoadInst *>> loadsByField;
    std::unordered_map<const Function *, std::vector<const CallBase *>> callsOf;
    for (Function &F : *ds_) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        if (const auto *L = dyn_cast<LoadInst>(&I)) {
          if (!L->getType()->isPointerTy())
            continue;
          const Value *p = stripCast(L->getPointerOperand());
          // Field keys of every load would walk the whole downstream module.
          // Alloca and global slots are enough to follow a pointer that is
          // saved and loaded again in -O0. A field copy is matched later,
          // only for slots that actually received an upstream object.
          if (isa<AllocaInst>(p) || isa<GlobalVariable>(p))
            loadsByPtr[p].push_back(L);
          else {
            std::string k = flatKey(p);
            if (!k.empty())
              loadsByField[k].push_back(L);
          }
        } else if (const auto *C = dyn_cast<CallBase>(&I)) {
          if (const Function *D = calledFn(C))
            if (!D->isIntrinsic())
              callsOf[D].push_back(C);
        }
      }
    }

    std::unordered_map<const Value *, RootSet> valObjs;
    std::unordered_map<const Value *, RootSet> ptrSlot;
    std::unordered_map<std::string, RootSet> fieldSlot;
    std::unordered_map<const Function *, RootSet> retObjs;
    std::vector<const Value *> q;

    auto give = [&](const Value *v, const RootSet &o) {
      if (!v || o.empty())
        return;
      RootSet &dst = valObjs[v];
      size_t n = dst.size();
      merge(dst, o);
      if (dst.size() != n)
        q.push_back(v);
    };
    auto givePtr = [&](const Value *slot, const RootSet &o) {
      if (!slot || o.empty())
        return;
      RootSet &dst = ptrSlot[slot];
      size_t n = dst.size();
      merge(dst, o);
      if (dst.size() == n)
        return;
      auto it = loadsByPtr.find(slot);
      if (it == loadsByPtr.end())
        return;
      for (const LoadInst *L : it->second)
        give(L, o);
    };
    auto giveField = [&](const std::string &k, const RootSet &o) {
      if (k.empty() || o.empty())
        return;
      RootSet &dst = fieldSlot[k];
      size_t n = dst.size();
      merge(dst, o);
      if (dst.size() == n)
        return;
      auto it = loadsByField.find(k);
      if (it == loadsByField.end())
        return;
      for (const LoadInst *L : it->second)
        give(L, o);
    };
    auto giveSlot = [&](const Value *addr, const RootSet &o) {
      const Value *p = stripCast(addr);
      if (isa<AllocaInst>(p) || isa<GlobalVariable>(p)) {
        givePtr(p, o);
        return;
      }
      std::string k = flatKey(p);
      if (!k.empty())
        giveField(k, o);
    };

    // A downstream call names the declaration. The same name in this module
    // may be an alias of the function that runs. The call is that function.
    auto upstreamOf = [&](const Function *D) -> const Function * {
      if (!D)
        return nullptr;
      auto us = usByName.find(D->getName().str());
      if (us != usByName.end())
        return us->second;
      const GlobalAlias *A = M_.getNamedAlias(D->getName());
      if (!A || !A->getAliasee())
        return nullptr;
      const auto *Fn = dyn_cast<Function>(A->getAliasee()->stripPointerCastsAndAliases());
      if (!Fn || Fn->isDeclaration())
        return nullptr;
      return Fn;
    };

    std::unordered_map<const Function *, std::vector<std::pair<bool, RootSet>>> through;
    auto throughOf = [&](const Function *F, unsigned i) -> const RootSet & {
      static const RootSet empty;
      auto &row = through[F];
      if (row.size() != F->arg_size())
        row.assign(F->arg_size(), {false, {}});
      if (i >= row.size())
        return empty;
      if (!row[i].first) {
        std::unordered_set<const Argument *> seen;
        row[i].second = writtenThrough(F, i, seen);
        row[i].first = true;
      }
      return row[i].second;
    };

    auto onArg = [&](const CallBase *C, unsigned i, const RootSet &o) {
      const Function *D = calledFn(C);
      if (!D || i >= C->arg_size() || o.empty())
        return;
      if (const Function *Us = upstreamOf(D)) {
        if (i >= Us->arg_size())
          return;
        if (!Us->getArg(i)->getType()->isPointerTy())
          return;
        RootSet &dst = extra_[Us->getArg(i)];
        merge(dst, o);
        return;
      }
      Function *body = ds_->getFunction(D->getName());
      if (!body || body->isDeclaration() || i >= body->arg_size())
        return;
      give(body->getArg(i), o);
    };

    auto pump = [&]() {
      for (size_t qi = 0; qi < q.size(); ++qi) {
        const Value *v = q[qi];
        RootSet o = valObjs[v];
        if (o.empty())
          continue;
        for (const User *U : v->users()) {
          if (const auto *CE = dyn_cast<ConstantExpr>(U)) {
            if (CE->isCast())
              give(CE, o);
            continue;
          }
          const auto *I = dyn_cast<Instruction>(U);
          if (!I)
            continue;
          if (isa<CastInst>(I) || isa<PHINode>(I) || isa<SelectInst>(I)) {
            give(I, o);
            continue;
          }
          if (const auto *S = dyn_cast<StoreInst>(I)) {
            if (stripCast(S->getValueOperand()) == stripCast(v))
              giveSlot(S->getPointerOperand(), o);
            continue;
          }
          if (const auto *R = dyn_cast<ReturnInst>(I)) {
            RootSet &dst = retObjs[R->getFunction()];
            size_t n = dst.size();
            merge(dst, o);
            if (dst.size() == n)
              continue;
            auto cit = callsOf.find(R->getFunction());
            if (cit == callsOf.end())
              continue;
            for (const CallBase *C : cit->second)
              give(C, o);
            continue;
          }
          if (const auto *C = dyn_cast<CallBase>(I)) {
            for (unsigned i = 0; i < C->arg_size(); ++i)
              if (stripCast(C->getArgOperand(i)) == stripCast(v))
                onArg(C, i, o);
          }
        }
      }
    };

    // A call crosses into this module when the caller is not itself a copy of
    // an upstream function. Calls inside the library are not that edge.
    auto crosses = [&](const CallBase *C) {
      const Function *caller = C->getFunction();
      return caller && !usByName.count(caller->getName().str());
    };
    for (const auto &kv : callsOf) {
      const Function *F = upstreamOf(kv.first);
      if (!F)
        continue;
      RootSet ret;
      auto rt = rets_.find(F);
      if (rt != rets_.end())
        for (const ReturnInst *R : rt->second)
          if (R->getReturnValue())
            merge(ret, pinsOf(directOf(R->getReturnValue())));
      for (const CallBase *C : kv.second) {
        if (!crosses(C))
          continue;
        if (!ret.empty() && C->getType()->isPointerTy())
          give(C, ret);
        for (unsigned i = 0; i < C->arg_size() && i < F->arg_size(); ++i) {
          const RootSet &w = throughOf(F, i);
          if (!w.empty())
            giveSlot(C->getArgOperand(i), w);
        }
      }
    }
    pump();
    // The actual argument is the object, including the allocation a local
    // load in the caller holds. Two calls that receive it are that object.
    for (const auto &kv : callsOf) {
      const Function *F = upstreamOf(kv.first);
      if (!F)
        continue;
      for (const CallBase *C : kv.second) {
        if (!crosses(C))
          continue;
        for (unsigned i = 0; i < C->arg_size() && i < F->arg_size(); ++i) {
          if (!F->getArg(i)->getType()->isPointerTy())
            continue;
          std::unordered_set<const Value *> seen;
          allocDone_.clear();
          allocScope_ = C->getFunction();
          merge(extra_[F->getArg(i)], actualAlloc(C->getArgOperand(i), seen));
          allocScope_ = nullptr;
        }
      }
    }
    // An indirect call that leaves the application does not name a callee.
    // The objects it passes are handed in. Every function of the call's type
    // is not that set: a shared type would mark a library buffer as written
    // by the application.
    for (Function &F : *ds_) {
      if (F.isDeclaration() || usByName.count(F.getName().str()))
        continue;
      for (Instruction &I : instructions(F)) {
        const auto *C = dyn_cast<CallBase>(&I);
        if (!C || C->isInlineAsm() || !C->isIndirectCall())
          continue;
        for (const Value *a : C->args()) {
          if (!a->getType()->isPointerTy())
            continue;
          std::unordered_set<const Value *> seen;
          allocDone_.clear();
          allocScope_ = C->getFunction();
          merge(handed_, actualAlloc(a, seen));
          allocScope_ = nullptr;
        }
      }
    }
  }

  const DataLayout &dlOf(const Value *v) const {
    if (ds_) {
      if (const auto *I = dyn_cast<Instruction>(v)) {
        if (I->getFunction() && I->getFunction()->getParent() == ds_)
          return ds_->getDataLayout();
      }
      if (const auto *A = dyn_cast<Argument>(v)) {
        if (A->getParent() && A->getParent()->getParent() == ds_)
          return ds_->getDataLayout();
      }
    }
    return M_.getDataLayout();
  }

  // The offset of an address a downstream function returns. A chain of calls
  // that ends at a GEP is that GEP. Returned by value: the cache map is
  // updated while callers still hold the previous result.
  KeySet fnAddrKey(const Function *F) const {
    if (!F)
      return {};
    auto it = dsFnKey_.find(F);
    if (it != dsFnKey_.end())
      return it->second;
    dsFnKey_[F] = {};
    if (F->isDeclaration())
      return {};
    KeySet out;
    for (const BasicBlock &BB : *F) {
      const auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      std::unordered_set<const Value *> pseen;
      const Value *p = stripCast(peel(R->getReturnValue(), pseen));
      if (!p)
        continue;
      if (const auto *K = dyn_cast<Constant>(p)) {
        if (K->isNullValue())
          continue;
      }
      if (const auto *G = dyn_cast<GEPOperator>(p)) {
        std::unordered_set<const Value *> oseen;
        std::string k = offsetKeyRec(G, dlOf(G), oseen);
        if (!k.empty())
          out.insert(std::move(k));
        continue;
      }
    if (const auto *C = dyn_cast<CallBase>(p)) {
      int arg = soleCopiedArg(calledFn(C));
      if (arg >= 0 && (unsigned)arg < C->arg_size()) {
        KeySet ks = dsAddrKey(C->getArgOperand(arg));
        out.insert(ks.begin(), ks.end());
        continue;
      }
      KeySet ks = fnAddrKey(calledFn(C));
      out.insert(ks.begin(), ks.end());
    }
    }
    dsFnKey_[F] = out;
    return out;
  }

  KeySet dsAddrKey(const Value *v) const {
    KeySet out;
    v = stripCast(v);
    if (!v)
      return out;
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      std::unordered_set<const Value *> oseen;
      std::string k = offsetKeyRec(G, dlOf(G), oseen);
      if (!k.empty())
        out.insert(std::move(k));
      return out;
    }
    if (const auto *C = dyn_cast<CallBase>(v)) {
      // The body is not in the module. It does not return a fresh object, and
      // the only pointer it received is its argument, so the address it
      // returns is that argument.
      int arg = soleCopiedArg(calledFn(C));
      if (arg >= 0 && (unsigned)arg < C->arg_size()) {
        KeySet ks = dsAddrKey(C->getArgOperand(arg));
        out.insert(ks.begin(), ks.end());
        return out;
      }
      KeySet ks = fnAddrKey(calledFn(C));
      out.insert(ks.begin(), ks.end());
    }
    return out;
  }

  // A declaration that does not claim a fresh object and has exactly one
  // pointer parameter returns that parameter. The parameter's position does
  // not matter. Several pointer parameters are a set, handled where the
  // result is a set. None, or a fresh result, is not a copy.
  int soleCopiedArg(const Function *F) const {
    if (!F || !F->isDeclaration() || F->isIntrinsic() || F->isVarArg())
      return -1;
    if (!F->getReturnType()->isPointerTy() || F->returnDoesNotAlias())
      return -1;
    int found = -1;
    unsigned n = 0;
    for (unsigned i = 0; i < F->arg_size(); ++i) {
      if (!F->getArg(i)->getType()->isPointerTy())
        continue;
      found = (int)i;
      ++n;
    }
    return n == 1 ? found : -1;
  }

  bool returnsItsArgument(const Function *F) const { return soleCopiedArg(F) >= 0; }

  // Loads a downstream function returns. A call that only returns a load is
  // that load. A declaration has no body, so it is not.
  bool returnsLoaded(const Function *F, std::vector<const LoadInst *> &out) const {
    if (!F || F->isDeclaration())
      return false;
    auto it = retLoads_.find(F);
    if (it != retLoads_.end()) {
      if (it->second.empty())
        return false;
      out.insert(out.end(), it->second.begin(), it->second.end());
      return true;
    }
    retLoads_[F] = {};
    bool any = false;
    bool bad = false;
    std::vector<const LoadInst *> one;
    for (const BasicBlock &BB : *F) {
      if (bad)
        break;
      const auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      std::unordered_set<const Value *> pseen;
      const Value *p = stripCast(peel(R->getReturnValue(), pseen));
      if (!p)
        continue;
      if (const auto *K = dyn_cast<Constant>(p)) {
        if (K->isNullValue())
          continue;
      }
      if (const auto *L = dyn_cast<LoadInst>(p)) {
        one.push_back(L);
        any = true;
        continue;
      }
      const auto *C = dyn_cast<CallBase>(p);
      if (!C) {
        bad = true;
        break;
      }
      std::vector<const LoadInst *> sub;
      if (!returnsLoaded(calledFn(C), sub)) {
        bad = true;
        break;
      }
      one.insert(one.end(), sub.begin(), sub.end());
      any = true;
    }
    if (bad || !any)
      return false;
    retLoads_[F] = one;
    out.insert(out.end(), one.begin(), one.end());
    return true;
  }

  // The object a field address is taken from. A returned GEP is that field
  // of the callee's argument.
  const Value *fieldBase(const Value *v, std::unordered_set<const Function *> &stack) const {
    v = stripCast(v);
    if (!v)
      return nullptr;
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      const Value *b = G->getPointerOperand();
      while (const auto *Inner = dyn_cast<GEPOperator>(stripCast(b)))
        b = Inner->getPointerOperand();
      return fieldBase(stripCast(b), stack);
    }
    const auto *C = dyn_cast<CallBase>(v);
    if (!C)
      return v;
    const Function *F = calledFn(C);
    int arg = soleCopiedArg(F);
    if (arg >= 0 && (unsigned)arg < C->arg_size())
      return fieldBase(C->getArgOperand(arg), stack);
    if (!F || F->isDeclaration() || !stack.insert(F).second)
      return C;
    const Value *base = nullptr;
    bool ok = true;
    for (const BasicBlock &BB : *F) {
      if (!ok)
        break;
      const auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      std::unordered_set<const Value *> pseen;
      const Value *p = stripCast(peel(R->getReturnValue(), pseen));
      if (!p)
        continue;
      if (const auto *K = dyn_cast<Constant>(p)) {
        if (K->isNullValue())
          continue;
      }
      const Value *b = fieldBase(p, stack);
      if (!base)
        base = b;
      else if (base != b)
        ok = false;
    }
    stack.erase(F);
    return ok && base ? base : C;
  }

  static std::string composeKey(const std::string &outer, const std::string &inner) {
    if (outer.empty())
      return inner;
    if (inner.empty())
      return outer;
    return outer + ">>" + inner;
  }

  // The pointer a call returns, named as one argument and the offset from it.
  // A declaration that returns its only pointer returns that argument.
  // A defined function returns whatever its body returns. A cycle has no answer.
  RetArg returnedFormal(const Function *F) {
    RetArg none;
    if (!F)
      return none;
    auto it = retArg_.find(F);
    if (it != retArg_.end())
      return it->second;
    if (F->isDeclaration()) {
      int arg = soleCopiedArg(F);
      if (arg >= 0) {
        RetArg r;
        r.ok = true;
        r.arg = (unsigned)arg;
        retArg_[F] = r;
        return r;
      }
      retArg_[F] = none;
      return none;
    }
    if (!retArgStack_.insert(F).second)
      return none;
    bool any = false;
    bool bad = false;
    unsigned arg = 0;
    std::string key;
    for (const BasicBlock &BB : *F) {
      if (bad)
        break;
      const auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      const Value *rv = stripCast(R->getReturnValue());
      if (const auto *K = dyn_cast<Constant>(rv)) {
        if (K->isNullValue())
          continue;
      }
      std::unordered_set<const Value *> seen;
      ArgRed red = reduceToArg(rv, seen);
      if (!red.arg || red.arg->getParent() != F) {
        bad = true;
        break;
      }
      if (!any) {
        any = true;
        arg = red.arg->getArgNo();
        key = std::move(red.key);
        continue;
      }
      if (arg != red.arg->getArgNo() || key != red.key) {
        bad = true;
        break;
      }
    }
    retArgStack_.erase(F);
    RetArg r;
    if (any && !bad) {
      r.ok = true;
      r.arg = arg;
      r.key = std::move(key);
    }
    retArg_[F] = r;
    return r;
  }

  // Walk an address back to an argument of the function that holds it.
  // A GEP keeps its offset. A call that returns an argument keeps that
  // argument's offset, then the offset of this call's actual. A load of a
  // local is the value stored there. A load of a field is a different object.
  ArgRed reduceToArg(const Value *v, std::unordered_set<const Value *> &seen) {
    ArgRed none;
    v = stripCast(v);
    if (!v || !seen.insert(v).second)
      return none;
    if (const auto *A = dyn_cast<Argument>(v)) {
      if (!A->getType()->isPointerTy())
        return none;
      ArgRed r;
      r.arg = A;
      return r;
    }
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      const Value *base = G->getPointerOperand();
      std::unordered_set<const Value *> gseen;
      while (const auto *Inner = dyn_cast<GEPOperator>(stripCast(base))) {
        if (!gseen.insert(base).second)
          break;
        base = Inner->getPointerOperand();
      }
      ArgRed b = reduceToArg(stripCast(base), seen);
      if (!b.arg)
        return none;
      std::unordered_set<const Value *> oseen;
      b.key = composeKey(b.key, offsetKeyRec(G, dlOf(G), oseen));
      return b;
    }
    auto fromAlloca = [&](const Value *slot) -> ArgRed {
      const Value *stored = nullptr;
      bool many = false;
      for (const User *U : slot->users()) {
        const auto *S = dyn_cast<StoreInst>(U);
        if (!S || stripCast(S->getPointerOperand()) != slot)
          continue;
        const Value *sv = S->getValueOperand();
        if (const auto *K = dyn_cast<Constant>(stripCast(sv))) {
          if (K->isNullValue())
            continue;
        }
        if (!stored)
          stored = sv;
        else if (stripCast(stored) != stripCast(sv))
          many = true;
      }
      if (many || !stored)
        return none;
      return reduceToArg(stored, seen);
    };
    if (isa<AllocaInst>(v))
      return fromAlloca(v);
    if (const auto *L = dyn_cast<LoadInst>(v)) {
      const Value *slot = stripCast(L->getPointerOperand());
      std::unordered_set<const Value *> peeled;
      while (const auto *C = dyn_cast<CallBase>(slot)) {
        if (!peeled.insert(slot).second)
          break;
        const Function *Fn = calledFn(C);
        int arg = soleCopiedArg(Fn);
        if (arg >= 0 && (unsigned)arg < C->arg_size()) {
          slot = stripCast(C->getArgOperand(arg));
          continue;
        }
        // A defined function that returns its argument with no added offset
        // is that argument. The load reads the local the caller passed.
        RetArg r = returnedFormal(Fn);
        if (!r.ok || !r.key.empty() || r.arg >= C->arg_size())
          break;
        slot = stripCast(C->getArgOperand(r.arg));
      }
      if (!isa<AllocaInst>(slot))
        return none;
      return fromAlloca(slot);
    }
    if (const auto *P = dyn_cast<PHINode>(v)) {
      ArgRed acc;
      bool any = false;
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
        const Value *inc = P->getIncomingValue(i);
        if (const auto *K = dyn_cast<Constant>(stripCast(inc))) {
          if (K->isNullValue())
            continue;
        }
        ArgRed r = reduceToArg(inc, seen);
        if (!r.arg)
          return none;
        if (!any) {
          acc = r;
          any = true;
          continue;
        }
        if (acc.arg != r.arg || acc.key != r.key)
          return none;
      }
      return any ? acc : none;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      ArgRed a = reduceToArg(S->getTrueValue(), seen);
      ArgRed b = reduceToArg(S->getFalseValue(), seen);
      if (!a.arg || a.arg != b.arg || a.key != b.key)
        return none;
      return a;
    }
    if (const auto *C = dyn_cast<CallBase>(v)) {
      const Function *F = calledFn(C);
      int arg = soleCopiedArg(F);
      if (arg >= 0 && (unsigned)arg < C->arg_size())
        return reduceToArg(C->getArgOperand(arg), seen);
      RetArg r = returnedFormal(F);
      if (!r.ok || r.arg >= C->arg_size())
        return none;
      ArgRed inner = reduceToArg(C->getArgOperand(r.arg), seen);
      if (!inner.arg)
        return none;
      inner.key = composeKey(inner.key, r.key);
      return inner;
    }
    return none;
  }

  // Stores into this function's arguments, including stores performed by a
  // callee on an argument this function passed. Each function is summarized
  // once. The summary does not solve points-to.
  std::vector<ArgStore> argFacts(const Function *F) {
    if (!F || !ds_ || F->isDeclaration() || F->getParent() != ds_)
      return {};
    auto it = argFacts_.find(F);
    if (it != argFacts_.end())
      return it->second;
    if (!argFactsStack_.insert(F).second)
      return {};
    std::vector<ArgStore> facts;
    for (Instruction &I : instructions(*const_cast<Function *>(F))) {
      const auto *S = dyn_cast<StoreInst>(&I);
      if (!S || !S->getValueOperand()->getType()->isPointerTy())
        continue;
      std::unordered_set<const Value *> seen;
      ArgRed a = reduceToArg(S->getPointerOperand(), seen);
      if (!a.arg || a.arg->getParent() != F)
        continue;
      ArgStore f;
      f.slot = a.arg->getArgNo();
      f.key = std::move(a.key);
      std::unordered_set<const Value *> vseen;
      ArgRed vr = reduceToArg(S->getValueOperand(), vseen);
      if (vr.arg && vr.arg->getParent() == F && vr.key.empty())
        f.valArg = (int)vr.arg->getArgNo();
      else
        f.val = S->getValueOperand();
      facts.push_back(std::move(f));
    }
    for (Instruction &I : instructions(*const_cast<Function *>(F))) {
      const auto *C = dyn_cast<CallBase>(&I);
      if (!C)
        continue;
      const Function *Cal = calledFn(C);
      if (!Cal || Cal->isDeclaration() || Cal->getParent() != ds_)
        continue;
      std::vector<ArgStore> sub = argFacts(Cal);
      for (const ArgStore &fact : sub) {
        if (fact.slot >= C->arg_size())
          continue;
        std::unordered_set<const Value *> seen;
        ArgRed actual = reduceToArg(C->getArgOperand(fact.slot), seen);
        if (!actual.arg || actual.arg->getParent() != F)
          continue;
        ArgStore n;
        n.slot = actual.arg->getArgNo();
        n.key = composeKey(actual.key, fact.key);
        if (fact.valArg >= 0 && (unsigned)fact.valArg < C->arg_size()) {
          std::unordered_set<const Value *> vseen;
          ArgRed vv = reduceToArg(C->getArgOperand(fact.valArg), vseen);
          if (vv.arg && vv.arg->getParent() == F && vv.key.empty())
            n.valArg = (int)vv.arg->getArgNo();
          else
            n.val = C->getArgOperand(fact.valArg);
        } else {
          n.val = fact.val;
        }
        facts.push_back(std::move(n));
      }
    }
    argFactsStack_.erase(F);
    argFacts_[F] = facts;
    return facts;
  }

  // Functions reached by direct calls from `F`, including `F`.
  void reachableFrom(const Function *F) {
    if (!F || !ds_ || reachFrom_.count(F))
      return;
    std::unordered_set<const Function *> set;
    std::vector<const Function *> q;
    set.insert(F);
    q.push_back(F);
    for (size_t i = 0; i < q.size(); ++i) {
      if (q[i]->isDeclaration() || q[i]->getParent() != ds_)
        continue;
      for (Instruction &I : instructions(*const_cast<Function *>(q[i]))) {
        const auto *C = dyn_cast<CallBase>(&I);
        if (!C)
          continue;
        const Function *Cal = calledFn(C);
        if (!Cal || Cal->isDeclaration() || Cal->getParent() != ds_)
          continue;
        if (set.insert(Cal).second)
          q.push_back(Cal);
      }
    }
    reachFrom_[F] = std::move(set);
  }

  // The same pointer. Two GEPs match when their offset and their base match.
  // Two loads of one slot match. The points-to of either side is not solved.
  bool samePtr(const Value *a, const Value *b, std::unordered_set<const Value *> &seen) {
    a = stripCast(a);
    b = stripCast(b);
    if (!a || !b)
      return false;
    if (a == b)
      return true;
    if (!seen.insert(a).second)
      return false;
    const auto *GA = dyn_cast<GEPOperator>(a);
    const auto *GB = dyn_cast<GEPOperator>(b);
    if (GA && GB) {
      std::unordered_set<const Value *> sa, sb;
      std::string ka = offsetKeyRec(GA, dlOf(GA), sa);
      std::string kb = offsetKeyRec(GB, dlOf(GB), sb);
      if (ka.empty() || ka != kb)
        return false;
      return samePtr(GA->getPointerOperand(), GB->getPointerOperand(), seen);
    }
    const auto *LA = dyn_cast<LoadInst>(a);
    const auto *LB = dyn_cast<LoadInst>(b);
    if (LA && LB)
      return stripCast(LA->getPointerOperand()) == stripCast(LB->getPointerOperand());
    return false;
  }

  // Where `arg` at `key` stands in `target`. Callers substitute the actual.
  // The walk stays inside functions `target` reaches, so a store in a callee
  // of `target` is named by the actual `target` passed.
  void viewsAt(const Function *target, const Argument *A, const std::string &key,
               std::vector<PtrView> &out) {
    if (!target || !A || !A->getParent())
      return;
    reachableFrom(target);
    auto rit = reachFrom_.find(target);
    if (rit == reachFrom_.end())
      return;
    const std::unordered_set<const Function *> &reach = rit->second;
    struct Item {
      const Value *base;
      std::string key;
      const Function *fn;
    };
    struct Vis {
      const Function *fn;
      const Value *base;
      std::string key;
      bool operator==(const Vis &o) const {
        return fn == o.fn && base == o.base && key == o.key;
      }
    };
    struct VisHash {
      size_t operator()(const Vis &v) const {
        size_t h = std::hash<uintptr_t>{}(reinterpret_cast<uintptr_t>(v.fn));
        h ^= std::hash<uintptr_t>{}(reinterpret_cast<uintptr_t>(v.base)) + 0x9e3779b97f4a7c15ULL +
             (h << 6) + (h >> 2);
        h ^= std::hash<std::string>{}(v.key) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        return h;
      }
    };
    std::unordered_set<Vis, VisHash> seenV;
    std::vector<Item> q;
    auto push = [&](const Value *base, const std::string &k, const Function *fn) {
      base = stripCast(base);
      if (!base || !fn)
        return;
      if (!seenV.insert(Vis{fn, base, k}).second)
        return;
      q.push_back(Item{base, k, fn});
    };
    push(A, key, A->getParent());
    for (size_t i = 0; i < q.size(); ++i) {
      Item it = q[i];
      if (it.fn == target) {
        out.push_back(PtrView{it.base, it.key});
        continue;
      }
      if (!reach.count(it.fn))
        continue;
      const Function *fn = it.fn;
      auto consider = [&](const CallBase *C) {
        if (!C || calledFn(C) != fn)
          return;
        const Function *caller = C->getFunction();
        if (!caller || (caller != target && !reach.count(caller)))
          return;
        if (const auto *Arg = dyn_cast<Argument>(it.base)) {
          if (Arg->getParent() == fn && Arg->getArgNo() < C->arg_size())
            push(C->getArgOperand(Arg->getArgNo()), it.key, caller);
          return;
        }
        std::unordered_set<const Value *> rseen;
        ArgRed rr = reduceToArg(it.base, rseen);
        if (!rr.arg || rr.arg->getParent() != fn || rr.arg->getArgNo() >= C->arg_size())
          return;
        push(C->getArgOperand(rr.arg->getArgNo()), composeKey(rr.key, it.key), caller);
      };
      for (const User *U : fn->users()) {
        if (const auto *C = dyn_cast<CallBase>(U))
          consider(C);
        else if (const auto *CE = dyn_cast<Constant>(U)) {
          for (const User *U2 : CE->users())
            if (const auto *C = dyn_cast<CallBase>(U2))
              consider(C);
        }
      }
    }
  }

  // The allocation a downstream actual refers to. A call that returns a load
  // is that load. A load is the value stored in its slot. A local slot is the
  // stores to that alloca. A field slot is the stores of that offset whose
  // object is the same. The rest of the downstream module is not solved.
  RootSet actualAlloc(const Value *v, std::unordered_set<const Value *> &seen) {
    RootSet out;
    if (!v)
      return out;
    v = stripCast(v);
    if (!v)
      return out;
    auto done = allocDone_.find(v);
    if (done != allocDone_.end())
      return done->second;
    if (!seen.insert(v).second) {
      // The caller chain is still being solved. The argument, the allocation,
      // and the call are already that object.
      if (isa<Argument>(v) || isa<AllocaInst>(v) || isa<GlobalVariable>(v) ||
          isa<CallBase>(v)) {
        out.insert(v);
        return out;
      }
      return out;
    }
    struct Publish {
      std::unordered_map<const Value *, RootSet> &m;
      const Value *key;
      RootSet &out;
      ~Publish() {
        if (!out.empty())
          m[key] = out;
      }
    } publish{allocDone_, v, out};
    (void)publish;
    if (const auto *A = dyn_cast<Argument>(v)) {
      out.insert(A);
      if (ds_ && A->getParent() && A->getParent()->getParent() == ds_) {
        for (const User *U : A->getParent()->users()) {
          const auto *C = dyn_cast<CallBase>(U);
          if (!C || calledFn(C) != A->getParent())
            continue;
          if (A->getArgNo() >= C->arg_size())
            continue;
          merge(out, actualAlloc(C->getArgOperand(A->getArgNo()), seen));
        }
      }
      return out;
    }
    if (isa<AllocaInst>(v) || isa<GlobalVariable>(v)) {
      out.insert(v);
      return out;
    }
    if (const auto *C = dyn_cast<CallBase>(v)) {
      std::vector<const LoadInst *> loads;
      if (returnsLoaded(calledFn(C), loads)) {
        for (const LoadInst *L : loads)
          merge(out, actualAlloc(L, seen));
        if (!out.empty())
          return out;
      }
      out.insert(C);
      return out;
    }
    if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        merge(out, actualAlloc(P->getIncomingValue(i), seen));
      return out;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      merge(out, actualAlloc(S->getTrueValue(), seen));
      merge(out, actualAlloc(S->getFalseValue(), seen));
      return out;
    }
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      out = actualAlloc(G->getPointerOperand(), seen);
      return out;
    }
    const auto *L = dyn_cast<LoadInst>(v);
    if (!L)
      return out;
    const Value *orig = stripCast(L->getPointerOperand());
    const Value *slot = orig;
    while (const auto *C = dyn_cast<CallBase>(slot)) {
      int arg = soleCopiedArg(calledFn(C));
      if (arg < 0 || (unsigned)arg >= C->arg_size())
        break;
      slot = stripCast(C->getArgOperand(arg));
    }
    bool viaCall = isa<CallBase>(orig);
    const Value *base = slot;
    while (const auto *Inner = dyn_cast<GEPOperator>(base))
      base = stripCast(Inner->getPointerOperand());
    bool any = false;
    if (isa<AllocaInst>(base) || isa<GlobalVariable>(base)) {
      for (const User *U : slot->users()) {
        const auto *S = dyn_cast<StoreInst>(U);
        if (!S || stripCast(S->getPointerOperand()) != slot)
          continue;
        if (S->getValueOperand()->getType() != L->getType())
          continue;
        merge(out, actualAlloc(S->getValueOperand(), seen));
        any = true;
      }
    } else if (allocScope_ && ds_ && L->getFunction() && L->getFunction()->getParent() == ds_) {
      // A call returns the address of an argument at a fixed offset, and a
      // callee stores through the same offset of the same argument. The value
      // stored there is what this load reads. The summary names that store
      // from the call in the crossing function. It does not solve the callee.
      if (viaCall) {
        std::unordered_set<const Value *> rseen;
        ArgRed red = reduceToArg(slot, rseen);
        if (red.arg && red.arg->getParent() == L->getFunction()) {
          std::vector<PtrView> views;
          viewsAt(allocScope_, red.arg, red.key, views);
          for (Instruction &I : instructions(*const_cast<Function *>(allocScope_))) {
            if (views.empty())
              break;
            const auto *C = dyn_cast<CallBase>(&I);
            if (!C)
              continue;
            const Function *Cal = calledFn(C);
            if (!Cal || Cal->isDeclaration() || Cal->getParent() != ds_)
              continue;
            bool pass = false;
            for (unsigned a = 0; a < C->arg_size() && !pass; ++a) {
              if (!C->getArgOperand(a)->getType()->isPointerTy())
                continue;
              for (const PtrView &vw : views) {
                std::unordered_set<const Value *> pseen;
                if (samePtr(C->getArgOperand(a), vw.base, pseen)) {
                  pass = true;
                  break;
                }
              }
            }
            if (!pass)
              continue;
            for (const ArgStore &f : argFacts(Cal)) {
              if (f.slot >= C->arg_size() || !C->getArgOperand(f.slot)->getType()->isPointerTy())
                continue;
              bool ok = false;
              for (const PtrView &vw : views) {
                if (vw.key != f.key)
                  continue;
                std::unordered_set<const Value *> pseen;
                if (samePtr(C->getArgOperand(f.slot), vw.base, pseen)) {
                  ok = true;
                  break;
                }
              }
              if (!ok)
                continue;
              const Value *val = nullptr;
              if (f.valArg >= 0 && (unsigned)f.valArg < C->arg_size())
                val = C->getArgOperand(f.valArg);
              else
                val = f.val;
              if (!val || val->getType() != L->getType())
                continue;
              merge(out, actualAlloc(val, seen));
              any = true;
            }
          }
        }
      }
      // Stores of this field in the function that passed the pointer.
      // The rest of the downstream module is not solved.
      KeySet ks = dsAddrKey(slot);
      if (!ks.empty()) {
        std::vector<const Function *> fq;
        std::unordered_set<const Function *> seenF;
        auto addF = [&](const Function *Fn) {
          if (Fn && !Fn->isDeclaration() && Fn->getParent() == ds_ && seenF.insert(Fn).second)
            fq.push_back(Fn);
        };
        addF(allocScope_);
        addF(L->getFunction());
        std::unordered_set<const Function *> fb;
        RootSet want = actualAlloc(fieldBase(slot, fb), seen);
        fb.clear();
        want = actualAlloc(fieldBase(slot, fb), seen);
        for (size_t qi = 0; qi < fq.size(); ++qi) {
          for (Instruction &I : instructions(*const_cast<Function *>(fq[qi]))) {
            const auto *S = dyn_cast<StoreInst>(&I);
            if (!S || S->getValueOperand()->getType() != L->getType())
              continue;
            KeySet sk = dsAddrKey(S->getPointerOperand());
            bool slotOk = false;
            bool storeViaCall = isa<CallBase>(stripCast(S->getPointerOperand()));
            auto atZero = [](const std::string &k) {
              auto at = k.rfind('@');
              if (at == std::string::npos)
                return k == "0";
              return k.compare(at + 1, std::string::npos, "0") == 0;
            };
            for (const auto &a : ks)
              for (const auto &b : sk)
                if (slotMatch(a, b) || sameField(a, b) ||
                    (viaCall && storeViaCall && atZero(a) && atZero(b)))
                  slotOk = true;
            if (!slotOk)
              continue;
            std::unordered_set<const Function *> sb;
            RootSet got = actualAlloc(fieldBase(S->getPointerOperand(), sb), seen);
            if (!hit(want, got))
              continue;
            merge(out, actualAlloc(S->getValueOperand(), seen));
            any = true;
          }
        }
      }
    }
    if (!any || out.empty())
      out.insert(L);
    return out;
  }

  // A load of a pointer carries the offset of the value that was stored.
  const KeySet &loadKeysOf(const LoadInst *L) const {
    auto it = loadKeys_.find(L);
    if (it != loadKeys_.end())
      return it->second;
    loadKeys_[L] = {};
    KeySet out;
    if (L->getType()->isPointerTy()) {
      const Value *addr = L->getPointerOperand();
      KeySet ak = keysOf(addr);
      auto take = [&](const KeySet &src) { out.insert(src.begin(), src.end()); };
      if (ak.empty()) {
        for (const Value *p : pinsOf(directOf(addr))) {
          auto s = slotCarried_.find(p);
          if (s != slotCarried_.end())
            take(s->second);
        }
      } else {
        for (const auto &k : ak) {
          auto s = carried_.find(k);
          if (s != carried_.end())
            take(s->second);
          std::string stem = fieldStemKey(k);
          if (stem.empty())
            continue;
          auto a = carried_.find(stem);
          if (a != carried_.end())
            take(a->second);
          auto b = carried_.find(stem + "/*");
          if (b != carried_.end())
            take(b->second);
        }
      }
    }
    loadKeys_[L] = std::move(out);
    return loadKeys_.find(L)->second;
  }

  // The offset stored into a pointer moves with that pointer.
  void propagatePointerKeys() {
    for (;;) {
      loadKeys_.clear();
      // An argument, phi, or cast reads the offset a load carries. That
      // offset is filled by this walk, so a key cached before the walk
      // still says the pointer has none.
      for (auto it = keys_.begin(); it != keys_.end();) {
        const Value *v = it->first;
        if (isa<Argument>(v) || isa<PHINode>(v) || isa<SelectInst>(v) || isa<CastInst>(v))
          it = keys_.erase(it);
        else
          ++it;
      }
      bool grew = false;
      for (const StoreInst *S : stores_) {
        if (!S->getValueOperand()->getType()->isPointerTy())
          continue;
        KeySet vk = keysOf(S->getValueOperand());
        if (vk.empty())
          continue;
        KeySet ak = keysOf(S->getPointerOperand());
        if (ak.empty()) {
          for (const Value *p : pinsOf(directOf(S->getPointerOperand())))
            for (const auto &q : vk)
              if (slotCarried_[p].insert(q).second)
                grew = true;
        } else {
          for (const auto &k : ak)
            for (const auto &q : vk)
              if (carried_[k].insert(q).second)
                grew = true;
        }
      }
      if (!grew)
        break;
    }
  }

  const KeySet &keysOf(const Value *v) const {
    static const KeySet empty;
    if (!v)
      return empty;
    v = stripCast(v);
    if (const auto *L = dyn_cast<LoadInst>(v))
      return loadKeysOf(L);
    auto it = keys_.find(v);
    if (it != keys_.end())
      return it->second;
    keys_[v] = {};
    KeySet out;
    if (isa<GEPOperator>(v)) {
      std::unordered_set<const Value *> oseen;
      std::string k = offsetKeyRec(v, M_.getDataLayout(), oseen);
      if (!k.empty())
        out.insert(std::move(k));
    } else if (const auto *A = dyn_cast<Argument>(v)) {
      auto cit = callers_.find(A->getParent());
      if (cit != callers_.end()) {
        for (const CallBase *C : cit->second) {
          if (A->getArgNo() >= C->arg_size())
            continue;
          KeySet ks = keysOf(C->getArgOperand(A->getArgNo()));
          out.insert(ks.begin(), ks.end());
        }
      }
    } else if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
        KeySet ks = keysOf(P->getIncomingValue(i));
        out.insert(ks.begin(), ks.end());
      }
    } else if (const auto *S = dyn_cast<SelectInst>(v)) {
      {
        KeySet ks = keysOf(S->getTrueValue());
        out.insert(ks.begin(), ks.end());
      }
      {
        KeySet ks = keysOf(S->getFalseValue());
        out.insert(ks.begin(), ks.end());
      }
    } else if (const auto *C = dyn_cast<CallBase>(v)) {
      // A function that returns an address (operator[]) is that address.
      std::vector<const Value *> bases;
      KeySet ks;
      std::unordered_set<const Function *> stack;
      if (addressReturn(C, bases, ks, stack))
        out.insert(ks.begin(), ks.end());
    } else if (const auto *C = dyn_cast<CastInst>(v)) {
      {
        KeySet ks = keysOf(C->getOperand(0));
        out.insert(ks.begin(), ks.end());
      }
    }
    keys_[v] = std::move(out);
    return keys_.find(v)->second;
  }

  // The local a pointer was stored into. move and forward return the argument
  // they were given, so the load reads the caller's slot. The result is the
  // value that was stored, and the address of this load stays the address.
  void callerSlots(const Value *v, RootSet &pins, std::unordered_set<const Value *> &seen) const {
    v = stripCast(v);
    if (!v || !seen.insert(v).second)
      return;
    if (const auto *C = dyn_cast<CallBase>(v)) {
      std::vector<const Value *> got;
      std::unordered_set<const Function *> st;
      if (!returnedPins(C, got, st) || got.empty())
        return;
      for (const Value *p : got)
        if (!isa<Argument>(stripCast(p)))
          return;
      for (const Value *p : got)
        callerSlots(p, pins, seen);
      return;
    }
    if (const auto *A = dyn_cast<Argument>(v)) {
      for (const Value *o : directOf(A))
        if (stripCast(o) != A)
          callerSlots(o, pins, seen);
      return;
    }
    if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        callerSlots(P->getIncomingValue(i), pins, seen);
      return;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      callerSlots(S->getTrueValue(), pins, seen);
      callerSlots(S->getFalseValue(), pins, seen);
      return;
    }
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      callerSlots(G->getPointerOperand(), pins, seen);
      return;
    }
    if (isa<AllocaInst>(v) || isa<GlobalVariable>(v))
      pins.insert(v);
  }

  // Loads and stores of a pointer variable itself, not of a struct field.
  void solveSlots() {
    slotFold_ = true;
    std::unordered_map<const Value *, std::vector<const StoreInst *>> writes;
    for (const StoreInst *S : stores_) {
      if (!S->getValueOperand()->getType()->isPointerTy())
        continue;
      if (!keysOf(S->getPointerOperand()).empty())
        continue;
      for (const Value *p : pinsOf(directOf(S->getPointerOperand())))
        writes[p].push_back(S);
    }
    std::vector<const LoadInst *> wl;
    std::unordered_map<const LoadInst *, std::vector<const StoreInst *>> ofLoad;
    std::unordered_set<const LoadInst *> in;
    for (const Value *v : ptrs_) {
      const auto *L = dyn_cast<LoadInst>(v);
      if (!L || !L->getType()->isPointerTy())
        continue;
      if (!keysOf(L->getPointerOperand()).empty())
        continue;
      if (!in.insert(L).second)
        continue;
      std::unordered_set<const StoreInst *> seenS;
      for (const Value *p : pinsOf(directOf(L->getPointerOperand()))) {
        auto it = writes.find(p);
        if (it == writes.end())
          continue;
        for (const StoreInst *S : it->second)
          if (S->getValueOperand()->getType() == L->getType() && seenS.insert(S).second)
            ofLoad[L].push_back(S);
      }
      if (!ofLoad[L].empty())
        wl.push_back(L);
    }
    std::unordered_map<const LoadInst *, RootSet> cur;
    // One iteration reads one map. The same pointer is expanded once.
    useExpCache_ = true;
    for (;;) {
      expCache_.clear();
      expDepth_.clear();
      bool grew = false;
      std::unordered_map<const LoadInst *, RootSet> next;
      for (const LoadInst *L : wl) {
        RootSet n;
        for (const StoreInst *S : ofLoad[L])
          merge(n, expand(S->getValueOperand(), cur));
        auto it = cur.find(L);
        if (it == cur.end() || it->second != n)
          grew = true;
        next[L] = std::move(n);
      }
      cur.swap(next);
      if (!grew)
        break;
    }
    expCache_.clear();
    expDepth_.clear();
    useExpCache_ = false;
    for (auto &kv : direct_) {
      RootSet folded = expand(kv.first, cur);
      kv.second.swap(folded);
    }
    // A load through move or forward is the object the caller stored in that
    // slot. Recorded on the load, so a later read of the value is that object.
    for (const Value *v : ptrs_) {
      const auto *L = dyn_cast<LoadInst>(v);
      if (!L || !L->getType()->isPointerTy())
        continue;
      if (!keysOf(L->getPointerOperand()).empty())
        continue;
      if (!isa<CallBase>(stripCast(L->getPointerOperand())))
        continue;
      RootSet pins;
      std::unordered_set<const Value *> seen;
      callerSlots(L->getPointerOperand(), pins, seen);
      RootSet val;
      for (const Value *p : pins) {
        auto it = writes.find(p);
        if (it == writes.end())
          continue;
        for (const StoreInst *S : it->second)
          if (S->getValueOperand()->getType() == L->getType())
            merge(val, expand(S->getValueOperand(), cur));
      }
      if (!val.empty())
        direct_[L] = std::move(val);
    }
    slotFold_ = false;
  }

  void indexStores() {
    for (const StoreInst *S : stores_) {
      KeySet ks = keysOf(S->getPointerOperand());
      if (ks.empty()) {
        byKey_[""].push_back(S);
      } else {
        for (const auto &k : ks)
          byKey_[k].push_back(S);
      }
    }
  }

  // "T@11" and "T@11/*" are one field. Nested "T@11/3" stays on its own key.
  static std::string fieldStemKey(const std::string &k) {
    auto at = k.find('@');
    std::string ty = at == std::string::npos ? std::string() : k.substr(0, at);
    std::string rest = at == std::string::npos ? k : k.substr(at + 1);
    if (rest.empty() || rest[0] < '0' || rest[0] > '9')
      return {};
    auto slash = rest.find('/');
    if (slash != std::string::npos && rest.compare(slash, std::string::npos, "/*") != 0)
      return {};
    std::string num = slash == std::string::npos ? rest : rest.substr(0, slash);
    return ty.empty() ? num : ty + "@" + num;
  }

  std::vector<const StoreInst *> candidates(const Value *addr) {
    KeySet ks = keysOf(addr);
    std::vector<const StoreInst *> out;
    std::unordered_set<const StoreInst *> seen;
    auto add = [&](const std::string &k) {
      auto it = byKey_.find(k);
      if (it == byKey_.end())
        return;
      for (const StoreInst *S : it->second)
        if (seen.insert(S).second)
          out.push_back(S);
    };
    if (ks.empty())
      return {};
    // The field's own stores, including the element wildcard. Scanning every
    // key in the module makes one sink walk the whole library.
    for (const auto &k : ks) {
      add(k);
      std::string stem = fieldStemKey(k);
      if (!stem.empty()) {
        add(stem);
        add(stem + "/*");
      }
    }
    return out;
  }

  struct KeyOff {
    std::string ty;
    uint64_t off = 0;
    bool var = false;
    bool ok = false;
  };

  // "T@12/*" is byte 12 inside a variable element of T. A bare "2/*" has no type.
  static KeyOff parseKey(const std::string &k) {
    KeyOff o;
    auto at = k.find('@');
    o.ty = at == std::string::npos ? std::string() : k.substr(0, at);
    std::string rest = at == std::string::npos ? k : k.substr(at + 1);
    if (rest.size() >= 2 && rest.compare(rest.size() - 2, 2, "/*") == 0) {
      o.var = true;
      rest.resize(rest.size() - 2);
    }
    if (rest.empty())
      return o;
    uint64_t n = 0;
    for (char c : rest) {
      if (c < '0' || c > '9')
        return o;
      n = n * 10 + static_cast<uint64_t>(c - '0');
    }
    o.off = n;
    o.ok = true;
    return o;
  }

  // A variable index is one element. The copy covers the bytes of that element
  // when the length is unknown or larger than the element, and the constant
  // length when it is smaller.
  static bool inSpan(const KeyOff &src, const KeyOff &st, std::optional<uint64_t> len, uint64_t elem) {
    if (!src.ok || !st.ok || src.ty != st.ty || src.var != st.var)
      return false;
    if (!src.var)
      return st.off == src.off;
    uint64_t span = 0;
    if (len && *len > 0 && elem > 0)
      span = *len < elem ? *len : elem;
    else if (elem > 0)
      span = elem;
    else if (len && *len > 0)
      span = *len;
    else
      return true;
    return st.off >= src.off && st.off - src.off < span;
  }

  uint64_t elementSpan(const Value *addr) const {
    const auto *G = dyn_cast<GEPOperator>(stripCast(addr));
    if (!G)
      return 0;
    Type *ty = G->getSourceElementType();
    if (!ty || !ty->isSized())
      return 0;
    return M_.getDataLayout().getTypeAllocSize(ty).getFixedValue();
  }

  bool slotOrRange(const Value *addr, const Value *storeAddr, const RootSet &want, const RootSet &got,
                   bool bytes, std::optional<uint64_t> len) {
    if (sameSlot(addr, storeAddr, want, got))
      return true;
    if (!bytes)
      return false;
    uint64_t elem = elementSpan(addr);
    for (const auto &a : keysOf(addr))
      for (const auto &b : keysOf(storeAddr))
        if (inSpan(parseKey(a), parseKey(b), len, elem))
          return true;
    return false;
  }

  void addCopyRange(const Value *addr, std::optional<uint64_t> len, std::vector<const StoreInst *> &cs) {
    KeySet ks = keysOf(addr);
    if (ks.empty())
      return;
    uint64_t elem = elementSpan(addr);
    std::unordered_set<const StoreInst *> seen(cs.begin(), cs.end());
    for (const auto &e : byKey_) {
      bool take = false;
      for (const auto &k : ks)
        if (inSpan(parseKey(k), parseKey(e.first), len, elem))
          take = true;
      if (!take)
        continue;
      for (const StoreInst *S : e.second)
        if (seen.insert(S).second)
          cs.push_back(S);
    }
  }

  void collectLoads(const Value *v, std::vector<const LoadInst *> &loads,
                    std::unordered_set<const LoadInst *> &seen) {
    for (const Value *r : directOf(v)) {
      const auto *L = dyn_cast<LoadInst>(r);
      if (!L || !seen.insert(L).second)
        continue;
      loads.push_back(L);
      collectLoads(L->getPointerOperand(), loads, seen);
    }
  }

  // Copies, and the -O0 alloca that only holds one of them, peel off.
  // What remains is the argument, the field load, or the call being returned.
  const Value *peel(const Value *v, std::unordered_set<const Value *> &seen) const {
    if (!v || !seen.insert(v).second)
      return v;
    v = stripCast(v);
    auto null = [](const Value *n) {
      if (!n)
        return true;
      const auto *C = dyn_cast<Constant>(stripCast(n));
      return C && C->isNullValue();
    };
    if (const auto *P = dyn_cast<PHINode>(v)) {
      const Value *same = nullptr;
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
        const Value *n = peel(P->getIncomingValue(i), seen);
        if (null(n))
          continue;
        if (!same)
          same = n;
        else if (same != n)
          return v;
      }
      return same ? same : v;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      const Value *a = peel(S->getTrueValue(), seen);
      const Value *b = peel(S->getFalseValue(), seen);
      if (null(a))
        return null(b) ? v : b;
      if (null(b))
        return a;
      return a == b ? a : v;
    }
    if (const auto *L = dyn_cast<LoadInst>(v)) {
      const Value *slot = stripCast(L->getPointerOperand());
      if (!isa<AllocaInst>(slot))
        return v;
      const Value *stored = nullptr;
      for (const StoreInst *S : stores_) {
        if (S->getFunction() != L->getFunction())
          continue;
        if (stripCast(S->getPointerOperand()) != slot)
          continue;
        const Value *n = peel(S->getValueOperand(), seen);
        if (null(n))
          continue;
        if (!stored)
          stored = n;
        else if (stored != n)
          return v;
      }
      return stored ? stored : v;
    }
    return v;
  }

  // Walk a returned pointer back to an argument. A field load of that
  // argument keeps the field key. A call is forwarded only when its callee
  // already has a summary, so the caller is retried.
  bool returnedForward(const Value *v, Forward &out, bool &wait) const {
    std::unordered_set<const Value *> seen;
    v = peel(v, seen);
    if (!v)
      return false;
    if (const auto *A = dyn_cast<Argument>(v)) {
      out.arg = A->getArgNo();
      out.key.clear();
      return true;
    }
    if (const auto *C = dyn_cast<CallBase>(stripCast(v))) {
      const Function *F = calledFn(C);
      if (!F || F->isDeclaration())
        return false;
      auto it = forward_.find(F);
      if (it == forward_.end()) {
        wait = true;
        return false;
      }
      if (it->second.arg >= C->arg_size())
        return false;
      std::unordered_set<const Value *> seen2;
      const Value *actual = peel(C->getArgOperand(it->second.arg), seen2);
      const auto *A = dyn_cast<Argument>(stripCast(actual));
      if (!A)
        return false;
      out.arg = A->getArgNo();
      out.key = it->second.key;
      return true;
    }
    const auto *L = dyn_cast<LoadInst>(stripCast(v));
    if (!L)
      return false;
    const Value *addr = stripCast(L->getPointerOperand());
    std::string key;
    if (isa<GEPOperator>(addr)) {
      std::unordered_set<const Value *> kseen;
      key = offsetKeyRec(addr, M_.getDataLayout(), kseen);
      while (const auto *G = dyn_cast<GEPOperator>(addr))
        addr = stripCast(G->getPointerOperand());
    }
    std::unordered_set<const Value *> seen3;
    addr = peel(addr, seen3);
    const auto *A = dyn_cast<Argument>(stripCast(addr));
    if (!A)
      return false;
    out.arg = A->getArgNo();
    out.key = std::move(key);
    return true;
  }

  void summarizeForwards() {
    bool grew = true;
    while (grew) {
      grew = false;
      for (Function &F : M_) {
        if (F.isDeclaration() || forward_.count(&F) || rets_.find(&F) == rets_.end())
          continue;
        Forward one;
        bool any = false;
        bool wait = false;
        bool bad = false;
        for (const ReturnInst *R : rets_[&F]) {
          Forward cur;
          bool w = false;
          if (!R->getReturnValue() || !returnedForward(R->getReturnValue(), cur, w)) {
            if (w)
              wait = true;
            else
              bad = true;
            break;
          }
          if (!any) {
            one = cur;
            any = true;
          } else if (one.arg != cur.arg || one.key != cur.key) {
            bad = true;
            break;
          }
          // A named field, including one element of an array field.
          // Returning the argument itself, or a bare byte offset, is not a field.
          if (one.key.empty() || one.key.find('@') == std::string::npos)
            bad = true;
        }
        if (bad || !any || wait)
          continue;
        forward_[&F] = one;
        grew = true;
      }
    }
  }

  const Forward *forwardOf(const CallBase *C) const {
    if (!C)
      return nullptr;
    auto one = [&](const Function *F) -> const Forward * {
      if (!F)
        return nullptr;
      auto it = forward_.find(F);
      if (it == forward_.end() || it->second.arg >= C->arg_size())
        return nullptr;
      return &it->second;
    };
    if (const Function *F = calledFn(C))
      return one(F);
    // An indirect call forwards only when every resolved body returns the
    // same field. A declaration is not a body.
    auto it = resolved_.find(C);
    if (it == resolved_.end())
      return nullptr;
    const Forward *found = nullptr;
    for (const Function *F : it->second) {
      if (!F || F->isDeclaration())
        continue;
      const Forward *f = one(F);
      if (!f)
        return nullptr;
      if (found && (found->arg != f->arg || found->key != f->key))
        return nullptr;
      found = f;
    }
    return found;
  }

  // Stores of this field whose address is this object. The value is what a
  // load of the field reads. A class pointer on the object stays with the value.
  RootSet fieldValues(const std::string &key, const RootSet &base,
                      const std::unordered_map<const LoadInst *, RootSet> &mem) const {
    RootSet out;
    if (key.empty() || byKey_.empty())
      return out;
    std::vector<const StoreInst *> cs;
    std::unordered_set<const StoreInst *> seenS;
    auto add = [&](const std::string &k) {
      auto it = byKey_.find(k);
      if (it == byKey_.end())
        return;
      for (const StoreInst *S : it->second)
        if (seenS.insert(S).second)
          cs.push_back(S);
    };
    add(key);
    std::string stem = fieldStemKey(key);
    if (!stem.empty()) {
      add(stem);
      add(stem + "/*");
    }
    for (const StoreInst *S : cs) {
      if (!S->getValueOperand()->getType()->isPointerTy())
        continue;
      bool keyed = false;
      for (const auto &k : keysOf(S->getPointerOperand()))
        if (k == key || sameField(k, key))
          keyed = true;
      if (!keyed)
        continue;
      RootSet got = expand(S->getPointerOperand(), mem);
      if (!sameObject(got, base))
        continue;
      merge(out, expand(S->getValueOperand(), mem));
    }
    for (const Value *v : base)
      if (limit_.count(v))
        out.insert(v);
    return out;
  }

  // A function that returns an interior pointer. The call is that address:
  // the key is the address's key, and the object is the buffer it indexes.
  bool addressReturnFn(const Function *F, std::vector<const Value *> &bases, KeySet &keys,
                       std::unordered_set<const Function *> &stack) const {
    if (!F || F->isDeclaration() || !stack.insert(F).second)
      return false;
    auto it = rets_.find(F);
    if (it == rets_.end()) {
      stack.erase(F);
      return false;
    }
    bool any = false;
    bool bad = false;
    for (const ReturnInst *R : it->second) {
      if (bad)
        break;
      std::unordered_set<const Value *> seen;
      const Value *v = peel(R->getReturnValue(), seen);
      if (!v)
        continue;
      if (const auto *K = dyn_cast<Constant>(stripCast(v))) {
        if (K->isNullValue())
          continue;
      }
      if (const auto *G = dyn_cast<GEPOperator>(stripCast(v))) {
        std::unordered_set<const Value *> oseen;
        std::string k = offsetKeyRec(G, M_.getDataLayout(), oseen);
        const Value *base = stripCast(G->getPointerOperand());
        while (const auto *Inner = dyn_cast<GEPOperator>(base))
          base = stripCast(Inner->getPointerOperand());
        bases.push_back(base);
        if (!k.empty())
          keys.insert(std::move(k));
        any = true;
        continue;
      }
      const auto *Call = dyn_cast<CallBase>(stripCast(v));
      if (!Call || !addressReturn(Call, bases, keys, stack)) {
        bad = true;
        break;
      }
      any = true;
    }
    stack.erase(F);
    return any && !bad;
  }

  bool addressReturn(const CallBase *C, std::vector<const Value *> &bases, KeySet &keys,
                     std::unordered_set<const Function *> &stack) const {
    if (!C)
      return false;
    std::vector<const Function *> tg;
    if (const Function *F = calledFn(C))
      tg.push_back(F);
    else {
      auto it = resolved_.find(C);
      if (it == resolved_.end())
        return false;
      tg = it->second;
    }
    bool any = false;
    for (const Function *F : tg) {
      if (!F || F->isDeclaration())
        continue;
      if (!addressReturnFn(F, bases, keys, stack))
        return false;
      any = true;
    }
    return any;
  }

  // The pointer a function returns when it is an allocation, an argument, or a
  // call. A load is a copy and an address is handled above. A declaration has
  // no body, so the call itself stays the allocation.
  bool returnedPinsFn(const Function *F, std::vector<const Value *> &pins,
                      std::unordered_set<const Function *> &stack) const {
    if (!F || F->isDeclaration() || !stack.insert(F).second)
      return false;
    auto it = rets_.find(F);
    if (it == rets_.end()) {
      stack.erase(F);
      return false;
    }
    bool any = false;
    bool bad = false;
    for (const ReturnInst *R : it->second) {
      if (bad)
        break;
      std::unordered_set<const Value *> seen;
      const Value *v = peel(R->getReturnValue(), seen);
      if (!v)
        continue;
      v = stripCast(v);
      if (const auto *K = dyn_cast<Constant>(v)) {
        if (K->isNullValue())
          continue;
      }
      if (isa<LoadInst>(v) || isa<GEPOperator>(v)) {
        bad = true;
        break;
      }
      if (isa<CallBase>(v) || isa<AllocaInst>(v) || isa<GlobalVariable>(v) || isa<Argument>(v)) {
        pins.push_back(v);
        any = true;
        continue;
      }
      bad = true;
      break;
    }
    stack.erase(F);
    return any && !bad;
  }

  bool returnedPins(const CallBase *C, std::vector<const Value *> &pins,
                    std::unordered_set<const Function *> &stack) const {
    if (!C)
      return false;
    std::vector<const Function *> tg;
    if (const Function *F = calledFn(C))
      tg.push_back(F);
    else {
      auto it = resolved_.find(C);
      if (it == resolved_.end())
        return false;
      tg = it->second;
    }
    bool any = false;
    for (const Function *F : tg) {
      if (!F || F->isDeclaration())
        continue;
      if (!returnedPinsFn(F, pins, stack))
        return false;
      any = true;
    }
    return any;
  }

  // Loads a function returns, when every non-null return is a load or a call
  // that itself returns only loads. A return of an allocation stays the call.
  // A declaration is ignored, so a pure virtual does not hide the override.
  bool loadedReturns(const Function *F, std::vector<const LoadInst *> &out,
                     std::unordered_set<const Function *> &stack) const {
    if (!F || F->isDeclaration() || !stack.insert(F).second)
      return false;
    auto it = rets_.find(F);
    if (it == rets_.end()) {
      stack.erase(F);
      return false;
    }
    std::vector<const LoadInst *> one;
    bool any = false;
    bool bad = false;
    for (const ReturnInst *R : it->second) {
      if (bad)
        break;
      std::unordered_set<const Value *> seen;
      const Value *v = peel(R->getReturnValue(), seen);
      if (!v)
        continue;
      if (const auto *K = dyn_cast<Constant>(stripCast(v))) {
        if (K->isNullValue())
          continue;
      }
      if (const auto *L = dyn_cast<LoadInst>(stripCast(v))) {
        one.push_back(L);
        any = true;
        continue;
      }
      const auto *Call = dyn_cast<CallBase>(stripCast(v));
      if (!Call) {
        bad = true;
        break;
      }
      std::vector<const Function *> tg;
      if (const Function *D = calledFn(Call))
        tg.push_back(D);
      else {
        auto rit = resolved_.find(Call);
        if (rit != resolved_.end())
          tg = rit->second;
      }
      bool got = false;
      for (const Function *G : tg) {
        if (!G || G->isDeclaration())
          continue;
        std::vector<const LoadInst *> sub;
        if (!loadedReturns(G, sub, stack)) {
          bad = true;
          break;
        }
        one.insert(one.end(), sub.begin(), sub.end());
        got = true;
      }
      if (!got)
        bad = true;
      else
        any = true;
    }
    stack.erase(F);
    if (bad || !any)
      return false;
    out.insert(out.end(), one.begin(), one.end());
    return true;
  }

  void copyReturns(const CallBase *C, std::vector<const LoadInst *> &loads) const {
    if (!C)
      return;
    std::vector<const Function *> tg;
    if (const Function *F = calledFn(C))
      tg.push_back(F);
    else {
      auto it = resolved_.find(C);
      if (it == resolved_.end())
        return;
      tg = it->second;
    }
    std::vector<const LoadInst *> one;
    bool any = false;
    for (const Function *F : tg) {
      if (!F || F->isDeclaration())
        continue;
      std::vector<const LoadInst *> sub;
      std::unordered_set<const Function *> stack;
      if (!loadedReturns(F, sub, stack))
        return;
      one.insert(one.end(), sub.begin(), sub.end());
      any = true;
    }
    if (any)
      loads.insert(loads.end(), one.begin(), one.end());
  }

  // True when every value this function returns is a fresh allocation.
  // A copy of an argument or a field is not fresh. Each call is then its own
  // object, and callers do not share the instruction inside the callee.
  bool freshAlloc(const Function *F) const {
    if (!F || F->isIntrinsic())
      return false;
    auto it = fresh_.find(F);
    if (it != fresh_.end())
      return it->second;
    if (!freshStack_.insert(F).second)
      return false;
    bool result = false;
    if (F->isDeclaration()) {
      result = F->getReturnType()->isPointerTy() && F->returnDoesNotAlias();
    } else if (F->getReturnType()->isPointerTy()) {
      std::unordered_set<const Value *> seenV;
      auto valueFresh = [&](const Value *v, auto &&self) -> bool {
        v = stripCast(v);
        if (!v || !seenV.insert(v).second)
          return false;
        if (const auto *K = dyn_cast<Constant>(v))
          return K->isNullValue();
        if (isa<Argument>(v) || isa<GEPOperator>(v))
          return false;
        if (const auto *L = dyn_cast<LoadInst>(v)) {
          const auto *Al = dyn_cast<AllocaInst>(stripCast(L->getPointerOperand()));
          if (!Al)
            return false;
          bool any = false;
          for (const User *U : Al->users()) {
            const auto *S = dyn_cast<StoreInst>(U);
            if (!S || stripCast(S->getPointerOperand()) != Al)
              continue;
            const Value *sv = stripCast(S->getValueOperand());
            if (const auto *K = dyn_cast<Constant>(sv)) {
              if (K->isNullValue())
                continue;
            }
            if (!self(sv, self))
              return false;
            any = true;
          }
          return any;
        }
        const auto *C = dyn_cast<CallBase>(v);
        if (!C)
          return false;
        const Function *Cal = calledFn(C);
        return Cal && freshAlloc(Cal);
      };
      bool any = false;
      bool bad = false;
      for (const BasicBlock &BB : *F) {
        if (bad)
          break;
        const auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue())
          continue;
        const Value *rv = stripCast(R->getReturnValue());
        if (const auto *K = dyn_cast<Constant>(rv)) {
          if (K->isNullValue())
            continue;
        }
        if (!valueFresh(rv, valueFresh)) {
          bad = true;
          break;
        }
        any = true;
      }
      result = any && !bad;
    }
    freshStack_.erase(F);
    fresh_[F] = result;
    return result;
  }

  RootSet expand(const Value *v, const std::unordered_map<const LoadInst *, RootSet> &mem) const {
    if (useExpCache_) {
      auto depth = expDepth_.find(v);
      if (depth != expDepth_.end()) {
        // This value is already being expanded. One re-entry still runs, so a
        // cycle contributes the objects the other transfers name. A second
        // re-entry is the allocation itself.
        if (depth->second >= 2) {
          RootSet o = pinsOf(directOf(v));
          const Value *s = stripCast(v);
          if (s && (isa<Argument>(s) || isa<CallBase>(s) || isa<AllocaInst>(s) ||
                    isa<GlobalVariable>(s)))
            o.insert(s);
          expSawCycle_ = true;
          return o;
        }
      } else {
        auto it = expCache_.find(v);
        if (it != expCache_.end()) {
          if (expReads_) {
            auto rd = expReadOf_.find(v);
            if (rd != expReadOf_.end())
              expReads_->insert(rd->second.begin(), rd->second.end());
          }
          return it->second;
        }
      }
      expDepth_[v]++;
    }
    std::unordered_set<const LoadInst *> mine;
    auto *parentReads = expReads_;
    expReads_ = &mine;
    RootSet out;
    std::vector<const LoadInst *> stack;
    std::unordered_set<const LoadInst *> seen;
    // A forwarded call is the field it returns, at this call's argument.
    // Until field stores are indexed, the call remains its own object.
    auto absorb = [&](const Value *r) {
      if (const auto *C = dyn_cast<CallBase>(stripCast(r))) {
        const Function *Fn = calledFn(C);
        // A fresh allocation is this call. Callers do not share the instruction
        // inside the callee.
        if (Fn && freshAlloc(Fn)) {
          out.insert(C);
          return;
        }
        if (!Fn) {
          auto rit = resolved_.find(C);
          if (rit != resolved_.end() && !rit->second.empty()) {
            bool allFresh = true;
            for (const Function *T : rit->second)
              if (!freshAlloc(T))
                allFresh = false;
            if (allFresh) {
              out.insert(C);
              return;
            }
          }
        }
        const Forward *f = forwardOf(C);
        if (f && !(!f->key.empty() && byKey_.empty()) && fwdStack_.insert(C).second) {
          RootSet base = expand(C->getArgOperand(f->arg), mem);
          RootSet got = f->key.empty() ? base : fieldValues(f->key, base, mem);
          fwdStack_.erase(C);
          if (!got.empty()) {
            merge(out, got);
            return;
          }
        }
        // The callee reads a pointer and returns it. The call is that load.
        if (fwdStack_.insert(C).second) {
          std::vector<const LoadInst *> loads;
          copyReturns(C, loads);
          fwdStack_.erase(C);
          if (!loads.empty()) {
            for (const LoadInst *L : loads)
              stack.push_back(L);
            return;
          }
        }
        // The callee returns an interior pointer. The call is that element,
        // so the object is the buffer the address is computed from.
        // Slot folding does not do this: it would copy every returned
        // pointer into every slot before the sink asks.
        if (!slotFold_ && fwdStack_.insert(C).second) {
          std::vector<const Value *> bases;
          KeySet keys;
          std::unordered_set<const Function *> st;
          bool addr = addressReturn(C, bases, keys, st);
          if (addr) {
            for (const Value *b : bases)
              merge(out, expand(b, mem));
            fwdStack_.erase(C);
            return;
          }
          fwdStack_.erase(C);
        }
        // The callee returns an allocation or an argument. The call is that
        // pointer, so a store through it is a store of this call.
        if (!slotFold_ && fwdStack_.insert(C).second) {
          std::vector<const Value *> pins;
          std::unordered_set<const Function *> st;
          if (returnedPins(C, pins, st)) {
            for (const Value *p : pins)
              merge(out, expand(p, mem));
            fwdStack_.erase(C);
            return;
          }
          fwdStack_.erase(C);
        }
      }
      // A load of the local that holds an argument is that argument's
      // allocation. The argument node stays. Only the allocation is copied:
      // walking every load in the argument's set does not finish.
      if (const auto *A = dyn_cast<Argument>(stripCast(r))) {
        // The argument's objects are the allocations in its direct set. A load
        // there is a copy of one of those allocations, already solved; walking
        // the load again re-enters every caller.
        out.insert(A);
        for (const Value *x : pinsOf(directOf(A)))
          out.insert(x);
        return;
      }
      if (const auto *L = dyn_cast<LoadInst>(r))
        stack.push_back(L);
      else if (r)
        out.insert(stripCast(r));
    };
    for (const Value *r : directOf(v))
      absorb(r);
    while (!stack.empty()) {
      const LoadInst *L = stack.back();
      stack.pop_back();
      if (!seen.insert(L).second)
        continue;
      if (expReads_)
        expReads_->insert(L);
      const RootSet *rs = nullptr;
      auto it = mem.find(L);
      if (it != mem.end() && !it->second.empty())
        rs = &it->second;
      else {
        auto persisted = mem_.find(L);
        if (persisted != mem_.end() && !persisted->second.empty())
          rs = &persisted->second;
      }
      // An empty resolution is the slot itself. Dropping it erases the pointer
      // and every access reached through it.
      if (!rs) {
        out.insert(L);
        continue;
      }
      // The load is the use under the class pointer that reached it. The
      // pointees are the allocation, which one call shares across classes.
      if (limit_.count(L))
        out.insert(L);
      for (const Value *x : *rs)
        absorb(x);
    }
    expReads_ = parentReads;
    if (parentReads)
      parentReads->insert(mine.begin(), mine.end());
    if (useExpCache_) {
      int d = --expDepth_[v];
      if (d <= 0) {
        expDepth_.erase(v);
        expCache_[v] = out;
        expReadOf_[v] = std::move(mine);
      }
    }
    return out;
  }

  void indexInits() {
    for (GlobalVariable &G : M_.globals()) {
      if (!G.hasInitializer() || G.isDeclaration())
        continue;
      std::string file;
      unsigned line = 0;
      SmallVector<DIGlobalVariableExpression *, 1> dis;
      G.getDebugInfo(dis);
      if (!dis.empty() && dis[0] && dis[0]->getVariable()) {
        const DIGlobalVariable *V = dis[0]->getVariable();
        line = V->getLine();
        if (V->getFile())
          file = baseName(V->getFile()->getFilename());
      }
      walkInit(&G, G.getInitializer(), 0, false, file, line);
    }
  }

  void addInit(GlobalVariable *gv, const std::string &key, const Value *val, const std::string &file,
               unsigned line) {
    if (!gv || key.empty() || !val)
      return;
    if (const auto *C = dyn_cast<Constant>(val))
      if (C->isNullValue() || C->isZeroValue())
        return;
    InitFact I;
    I.gv = gv;
    I.value = val;
    I.file = file;
    I.line = line;
    initByKey_[key].push_back(std::move(I));
  }

  // Nested constants become one write per field. An array index is "/*":
  // element 1 is the same field as element 0, not a different offset.
  void walkInit(GlobalVariable *gv, const Constant *c, uint64_t base, bool anyElem,
                const std::string &file, unsigned line) {
    if (!c || c->isZeroValue())
      return;
    const DataLayout &DL = M_.getDataLayout();
    if (const auto *CS = dyn_cast<ConstantStruct>(c)) {
      auto *ST = const_cast<StructType *>(CS->getType());
      std::string ty = ST->hasName() ? ST->getName().str() : "";
      const StructLayout *SL = DL.getStructLayout(ST);
      for (unsigned i = 0; i < CS->getNumOperands(); ++i) {
        const Constant *el = CS->getOperand(i);
        if (!el || el->isZeroValue())
          continue;
        uint64_t off = base + SL->getElementOffset(i);
        if (isa<ConstantAggregate>(el))
          walkInit(gv, el, off, anyElem, file, line);
        else {
          std::string k = std::to_string(off) + (anyElem ? "/*" : "");
          if (!ty.empty())
            k = ty + "@" + k;
          addInit(gv, k, el, file, line);
        }
      }
      return;
    }
    if (const auto *CA = dyn_cast<ConstantArray>(c)) {
      for (unsigned i = 0; i < CA->getNumOperands(); ++i) {
        const Constant *el = CA->getOperand(i);
        if (!el || el->isZeroValue())
          continue;
        if (isa<ConstantAggregate>(el))
          walkInit(gv, el, base, true, file, line);
        else
          addInit(gv, std::to_string(base) + "/*", el, file, line);
      }
    }
  }

  // Loads that produce this pointer. The object of a load is the allocation
  // those loads read, at the offset this pointer already carries.
  void pointerLoads(const Value *v, std::vector<const LoadInst *> &out,
                    std::unordered_set<const Value *> &seen) const {
    if (!v || !seen.insert(v).second)
      return;
    v = stripCast(v);
    if (const auto *L = dyn_cast<LoadInst>(v)) {
      out.push_back(L);
      return;
    }
    if (const auto *G = dyn_cast<GEPOperator>(v)) {
      pointerLoads(G->getPointerOperand(), out, seen);
      return;
    }
    if (const auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        pointerLoads(P->getIncomingValue(i), out, seen);
      return;
    }
    if (const auto *S = dyn_cast<SelectInst>(v)) {
      pointerLoads(S->getTrueValue(), out, seen);
      pointerLoads(S->getFalseValue(), out, seen);
      return;
    }
    if (const auto *C = dyn_cast<CastInst>(v)) {
      pointerLoads(C->getOperand(0), out, seen);
      return;
    }
    const auto *Call = dyn_cast<CallBase>(v);
    if (Call) {
      std::vector<const Value *> bases;
      KeySet keys;
      std::unordered_set<const Function *> stack;
      if (addressReturn(Call, bases, keys, stack)) {
        for (const Value *b : bases)
          pointerLoads(b, out, seen);
        return;
      }
      std::vector<const LoadInst *> loads;
      copyReturns(Call, loads);
      for (const LoadInst *L : loads)
        if (seen.insert(L).second)
          out.push_back(L);
      return;
    }
    // The pointer is an argument or another register. Its points-to is the
    // values stored into it, which may themselves be loads.
    for (const Value *r : directOf(v))
      if (r != v)
        pointerLoads(r, out, seen);
  }

  void solveLoads(const std::vector<const LoadInst *> &seeds, bool chase, bool follow = false) {
    std::vector<const LoadInst *> wl;
    std::unordered_set<const LoadInst *> in;
    for (const LoadInst *L : seeds) {
      if (mem_.count(L) || solving_.count(L) || !in.insert(L).second)
        continue;
      solving_.insert(L);
      wl.push_back(L);
    }
    if (wl.empty())
      return;
    if (follow) {
      std::vector<const LoadInst *> defs;
      std::unordered_set<const Value *> dseen;
      for (const LoadInst *L : wl)
        pointerLoads(L->getPointerOperand(), defs, dseen);
      if (!defs.empty())
        solveLoads(defs, true, true);
    }
    std::unordered_set<const LoadInst *> roots(wl.begin(), wl.end());
    std::unordered_map<const LoadInst *, std::vector<const StoreInst *>> cands;
    for (const LoadInst *L : wl)
      cands[L] = candidates(L->getPointerOperand());

    // The class is a property of the pointer, known before any round. A load
    // keeps it so the allocation underneath stays this access's object.
    for (const LoadInst *L : wl) {
      if (limit_.count(L))
        continue;
      auto c = classOf(L->getPointerOperand());
      if (!c.empty())
        limit_[L] = std::move(c);
    }
    std::unordered_map<const LoadInst *, RootSet> cur;
    std::unordered_set<const LoadInst *> hot(wl.begin(), wl.end());
    std::unordered_map<const LoadInst *, std::unordered_set<const LoadInst *>> deps;
    useExpCache_ = true;
    for (;;) {
      expCache_.clear();
      expDepth_.clear();
      expReadOf_.clear();
      bool grew = false;
      std::unordered_map<const LoadInst *, RootSet> next;
      std::vector<const LoadInst *> extra;
      std::unordered_set<const LoadInst *> changed;
      for (const LoadInst *L : wl) {
        if (!hot.count(L)) {
          auto kept = cur.find(L);
          if (kept != cur.end())
            next[L] = kept->second;
          continue;
        }
        expSawCycle_ = false;
        std::unordered_set<const LoadInst *> reads;
        expReads_ = &reads;
        RootSet addr = expand(L->getPointerOperand(), cur);
        RootSet n;
        for (const StoreInst *S : cands[L]) {
          if (S->getValueOperand()->getType() != L->getType())
            continue;
          // Different selecting globals are different objects. The class is
          // on the pointer, so it does not appear and disappear between rounds.
          if (!classesAgree(L->getPointerOperand(), S->getPointerOperand()))
            continue;
          RootSet sa = expand(S->getPointerOperand(), cur);
          if (!sameSlot(L->getPointerOperand(), S->getPointerOperand(), addr, sa))
            continue;
          bool bare = indexOnly(L->getPointerOperand()) && indexOnly(S->getPointerOperand());
          bool alias = sameObject(sa, addr);
          if (!alias) {
            // The index is applied to the pointer this address still loads.
            // That load is solved, then this access is read again. Other
            // arrays' address loads are not pulled in.
            if (!chase)
              continue;
            if (bare) {
              auto pending = [&](const RootSet &s) {
                bool unresolved = false;
                for (const Value *o : s) {
                  const auto *L2 = dyn_cast<LoadInst>(o);
                  if (!L2 || L2 == L || mem_.count(L2) || cur.count(L2))
                    continue;
                  unresolved = true;
                  if (in.insert(L2).second)
                    extra.push_back(L2);
                }
                return unresolved;
              };
              pending(addr);
              continue;
            }
            if (!roots.count(L))
              continue;
            auto pending = [&](const RootSet &s) {
              bool unresolved = false;
              for (const Value *o : s) {
                const auto *L2 = dyn_cast<LoadInst>(o);
                if (!L2 || L2 == L || mem_.count(L2) || cur.count(L2))
                  continue;
                unresolved = true;
                if (in.insert(L2).second)
                  extra.push_back(L2);
              }
              return unresolved;
            };
            if (!pending(sa) && !pending(addr))
              continue;
            continue;
          }
          // The stored value is this load's memory. Loads inside that value
          // are copies and are followed by the caller. Pulling every load in
          // every aliasing store into this fixpoint walks every face.
          merge(n, expand(S->getValueOperand(), cur));
        }
        expReads_ = nullptr;
        deps[L] = std::move(reads);
        // The join only adds. A round that names nothing, or that names a
        // subset because a cycle returned the allocation, does not retract a
        // store the previous round already read.
        auto it = cur.find(L);
        if (it != cur.end())
          merge(n, it->second);
        if (it == cur.end() || it->second != n) {
          grew = true;
          changed.insert(L);
        }
        next[L] = std::move(n);
      }
      cur.swap(next);
      if (!extra.empty()) {
        for (const LoadInst *L : extra) {
          wl.push_back(L);
          cands[L] = candidates(L->getPointerOperand());
          hot.insert(L);
        }
        grew = true;
      }
      hot.clear();
      for (const LoadInst *L : wl) {
        auto d = deps.find(L);
        if (d == deps.end()) {
          hot.insert(L);
          continue;
        }
        for (const LoadInst *r : d->second)
          if (changed.count(r))
            hot.insert(L);
      }
      if (hot.empty())
        break;
    }
    expReads_ = nullptr;
    useExpCache_ = false;
    expCache_.clear();
    expDepth_.clear();
    for (auto &kv : cur) {
      // An empty read is not a result. The address may still be a load, and
      // recording nothing would keep the later read from seeing the store.
      if (kv.second.empty())
        continue;
      mem_[kv.first] = std::move(kv.second);
    }
    for (const LoadInst *L : wl)
      solving_.erase(L);
  }
};

bool copyOnly(const Value *v, std::unordered_set<const Value *> &seen) {
  if (!v)
    return true;
  v = v->stripPointerCasts();
  if (!seen.insert(v).second)
    return true;
  if (isa<LoadInst>(v))
    return true;
  if (const auto *P = dyn_cast<PHINode>(v)) {
    for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
      if (!copyOnly(P->getIncomingValue(i), seen))
        return false;
    return true;
  }
  if (const auto *S = dyn_cast<SelectInst>(v))
    return copyOnly(S->getTrueValue(), seen) && copyOnly(S->getFalseValue(), seen);
  if (const auto *C = dyn_cast<CastInst>(v))
    return copyOnly(C->getOperand(0), seen);
  return false;
}

void loadsInside(const Value *v, std::vector<const LoadInst *> &out,
                 std::unordered_set<const Value *> &seen) {
  if (!v)
    return;
  v = v->stripPointerCasts();
  if (!seen.insert(v).second)
    return;
  if (const auto *L = dyn_cast<LoadInst>(v)) {
    out.push_back(L);
    return;
  }
  if (const auto *P = dyn_cast<PHINode>(v)) {
    for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
      loadsInside(P->getIncomingValue(i), out, seen);
    return;
  }
  if (const auto *S = dyn_cast<SelectInst>(v)) {
    loadsInside(S->getTrueValue(), out, seen);
    loadsInside(S->getFalseValue(), out, seen);
    return;
  }
  if (const auto *C = dyn_cast<CastInst>(v))
    loadsInside(C->getOperand(0), out, seen);
}

void gatherFrom(const Value *v, std::vector<const LoadInst *> &loads,
                std::unordered_set<const Value *> &seen) {
  if (!v || !seen.insert(v).second)
    return;
  if (const auto *L = dyn_cast<LoadInst>(v)) {
    loads.push_back(L);
    return;
  }
  const auto *I = dyn_cast<Instruction>(v);
  if (!I)
    return;
  if (const auto *G = dyn_cast<GetElementPtrInst>(I)) {
    gatherFrom(G->getPointerOperand(), loads, seen);
    return;
  }
  if (isa<CastInst>(I) || isa<PHINode>(I) || isa<SelectInst>(I) || isa<BinaryOperator>(I) ||
      isa<UnaryOperator>(I) || isa<CmpInst>(I) || isa<FreezeInst>(I)) {
    for (const Use &U : I->operands())
      if (!isa<BasicBlock>(U.get()))
        gatherFrom(U.get(), loads, seen);
  }
}

std::vector<const LoadInst *> usesOf(const Instruction *sink) {
  std::vector<const LoadInst *> loads;
  std::unordered_set<const Value *> seen;
  if (const auto *L = dyn_cast<LoadInst>(sink)) {
    loads.push_back(L);
    return loads;
  }
  if (const auto *S = dyn_cast<StoreInst>(sink)) {
    gatherFrom(S->getValueOperand(), loads, seen);
    return loads;
  }
  if (const auto *C = dyn_cast<CallBase>(sink)) {
    for (const Use &U : C->args())
      gatherFrom(U.get(), loads, seen);
  }
  return loads;
}

std::string pretty(StringRef n) {
  if (n.empty())
    return {};
  std::string d = llvm::demangle(n.str());
  if (d.empty() || d == n)
    return n.str();
  return d;
}

Def externalDef(const Value *v) {
  Def d;
  d.kind = "external";
  if (!v)
    return d;
  if (const auto *GV = dyn_cast<GlobalVariable>(v)) {
    d.func = pretty(GV->getName());
    return d;
  }
  if (const auto *A = dyn_cast<Argument>(v)) {
    d.func = pretty(A->getParent()->getName());
    d.arg = static_cast<int>(A->getArgNo());
    return d;
  }
  if (const auto *I = dyn_cast<Instruction>(v)) {
    d.func = pretty(I->getFunction()->getName());
    if (const DebugLoc &dl = I->getDebugLoc()) {
      d.line = dl.getLine();
      if (dl->getScope() && dl->getScope()->getFile())
        d.file = baseName(dl->getScope()->getFile()->getFilename());
    }
    return d;
  }
  d.func = pretty(v->getName());
  return d;
}

void noteExternal(UseDef &ud, const RootSet &want, const Flow &flow, const Function *sinkFn) {
  if (!flow.exposed(want))
    return;
  auto ws = flow.exposedPlaces(want, sinkFn);
  if (ws.empty()) {
    Def ext;
    ext.kind = "external";
    ud.defs.push_back(std::move(ext));
    return;
  }
  for (const Value *v : ws)
    ud.defs.push_back(externalDef(v));
}

Def fromInst(const Instruction *I, StringRef kind) {
  Def d;
  d.kind = kind.str();
  d.func = I->getFunction()->getName().str();
  if (const DebugLoc &dl = I->getDebugLoc()) {
    d.line = dl.getLine();
    if (dl->getScope() && dl->getScope()->getFile())
      d.file = baseName(dl->getScope()->getFile()->getFilename());
  }
  return d;
}

std::string useText(const LoadInst *L) {
  std::string s;
  raw_string_ostream os(s);
  os << "load";
  if (const DebugLoc &dl = L->getDebugLoc()) {
    os << " ";
    if (dl->getScope() && dl->getScope()->getFile())
      os << baseName(dl->getScope()->getFile()->getFilename()) << ":";
    os << dl.getLine();
  }
  os << " " << L->getFunction()->getName();
  return s;
}

void promote(Module &M) {
  for (Function &F : M) {
    F.removeFnAttr(Attribute::OptimizeNone);
    F.removeFnAttr(Attribute::NoInline);
  }
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PassBuilder PB;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
  ModulePassManager MPM;
  MPM.addPass(createModuleToFunctionPassAdaptor(PromotePass()));
  MPM.run(M, MAM);
}

} // namespace

// A store reaches `use` when some path gets there without a later store to the
// same slot. The use may be in another function: then the store has to reach
// a return, leaving the value in the object. A copy still overwrites the slot.
bool storeReaches(const StoreInst *from, const Instruction *use,
                  const std::unordered_set<const Instruction *> &overwrites) {
  std::vector<const Instruction *> wl;
  std::unordered_set<const Instruction *> seen;
  auto pushAfter = [&](const Instruction *I) {
    if (const Instruction *N = I->getNextNode()) {
      wl.push_back(N);
      return;
    }
    for (const BasicBlock *S : successors(I->getParent()))
      if (!S->empty())
        wl.push_back(&S->front());
  };
  pushAfter(from);
  bool left = false;
  while (!wl.empty()) {
    const Instruction *I = wl.back();
    wl.pop_back();
    if (!seen.insert(I).second)
      continue;
    if (use && I == use)
      return true;
    if (overwrites.count(I))
      continue;
    if (isa<ReturnInst>(I)) {
      left = true;
      continue;
    }
    pushAfter(I);
  }
  return use && use->getFunction() != from->getFunction() && left;
}

std::vector<UseDef> findDefs(Module &M, const std::string &file, unsigned line, Module *ds) {
  promote(M);
  Flow flow(M, ds);

  std::vector<const LoadInst *> uses;
  std::unordered_set<const LoadInst *> copyAddr;
  std::vector<const CallBase *> copies;
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (Instruction &I : instructions(F)) {
      if (!onLine(I, file, line))
        continue;
      const Value *src = nullptr;
      if (const auto *C = dyn_cast<CallBase>(&I)) {
        if (Flow::isByteCopy(C, src)) {
          copies.push_back(C);
          std::vector<const LoadInst *> addr;
          std::unordered_set<const Value *> seen;
          for (const Use &U : C->args())
            gatherFrom(U.get(), addr, seen);
          for (const LoadInst *L : addr)
            copyAddr.insert(L);
          continue;
        }
      }
      if (!isa<LoadInst>(I) && !isa<StoreInst>(I) && !isa<CallBase>(I))
        continue;
      auto more = usesOf(&I);
      uses.insert(uses.end(), more.begin(), more.end());
    }
  }

  std::vector<UseDef> out;

  auto takeStores = [&](UseDef &ud, const Instruction *use,
                        const std::vector<const StoreInst *> &stores,
                        std::vector<const LoadInst *> &work,
                        std::unordered_set<const Instruction *> &reported) {
    std::unordered_set<const Instruction *> overwrites(stores.begin(), stores.end());
    for (const StoreInst *S : stores) {
      if (!storeReaches(S, use, overwrites))
        continue;
      std::unordered_set<const Value *> seen;
      // A pointer loaded from another slot is that slot. The bytes a store
      // writes are the value the later read sees, so that store is the def.
      if (S->getValueOperand()->getType()->isPointerTy() && copyOnly(S->getValueOperand(), seen)) {
        std::vector<const LoadInst *> inner;
        std::unordered_set<const Value *> seenL;
        loadsInside(S->getValueOperand(), inner, seenL);
        // A local only holds the pointer. The store into the field is the
        // def. A load of another field is a copy of that field.
        bool field = inner.empty();
        for (const LoadInst *IL : inner)
          if (flow.keyed(IL->getPointerOperand()))
            field = true;
        if (field) {
          work.insert(work.end(), inner.begin(), inner.end());
          continue;
        }
      }
      if (reported.insert(S).second)
        ud.defs.push_back(fromInst(S, "store"));
    }
  };

  auto takeInits = [&](UseDef &ud, const std::vector<InitFact> &inits,
                       std::vector<const LoadInst *> &work) {
    for (const InitFact &I : inits) {
      std::unordered_set<const Value *> seen;
      if (copyOnly(I.value, seen)) {
        std::vector<const LoadInst *> inner;
        std::unordered_set<const Value *> seenL;
        loadsInside(I.value, inner, seenL);
        work.insert(work.end(), inner.begin(), inner.end());
        continue;
      }
      Def d;
      d.kind = "init";
      d.func = I.gv->getName().str();
      d.file = I.file;
      d.line = I.line;
      ud.defs.push_back(std::move(d));
    }
  };

  auto publish = [&](UseDef ud) {
    std::unordered_set<std::string> uniq;
    std::vector<Def> deduped;
    for (const Def &d : ud.defs) {
      std::string k = d.kind + " " + d.func + " " + d.file + ":" + std::to_string(d.line) + "#" +
                      std::to_string(d.arg);
      if (uniq.insert(k).second)
        deduped.push_back(d);
    }
    ud.defs.swap(deduped);
    out.push_back(std::move(ud));
  };

  std::unordered_set<const LoadInst *> seenUse;
  for (const LoadInst *L : uses) {
    if (!seenUse.insert(L).second || copyAddr.count(L))
      continue;
    UseDef ud;
    ud.use = useText(L);
    std::vector<const LoadInst *> work{L};
    std::unordered_set<const LoadInst *> followed;
    std::unordered_set<const Instruction *> reported;
    while (!work.empty()) {
      const LoadInst *cur = work.back();
      work.pop_back();
      if (!followed.insert(cur).second)
        continue;
      RootSet want = flow.objects(cur->getPointerOperand());
      auto stores = flow.aliasingStores(cur->getPointerOperand(), cur->getType(), want);
      auto inits = flow.aliasingInits(cur->getPointerOperand(), cur->getType(), want);
      noteExternal(ud, want, flow, L->getFunction());
      if (stores.empty() && inits.empty())
        continue;
      takeStores(ud, cur, stores, work, reported);
      takeInits(ud, inits, work);
    }
    publish(std::move(ud));
  }

  for (const CallBase *C : copies) {
    const Value *src = nullptr;
    if (!Flow::isByteCopy(C, src) || !src)
      continue;
    UseDef ud;
    ud.use = "copy " + file + ":" + std::to_string(line) + " " + C->getFunction()->getName().str();
    std::vector<const Value *> addrs{src};
    std::unordered_set<const Value *> seenAddr;
    std::vector<const LoadInst *> work;
    std::unordered_set<const LoadInst *> followed;
    std::unordered_set<const Instruction *> reported;
    while (!addrs.empty() || !work.empty()) {
      while (!work.empty()) {
        const LoadInst *cur = work.back();
        work.pop_back();
        if (!followed.insert(cur).second)
          continue;
        RootSet want = flow.objects(cur->getPointerOperand());
        noteExternal(ud, want, flow, C->getFunction());
        auto stores = flow.aliasingStores(cur->getPointerOperand(), cur->getType(), want);
        auto inits = flow.aliasingInits(cur->getPointerOperand(), cur->getType(), want);
        takeStores(ud, C, stores, work, reported);
        takeInits(ud, inits, work);
      }
      if (addrs.empty())
        break;
      const Value *addr = addrs.back();
      addrs.pop_back();
      if (!seenAddr.insert(addr).second)
        continue;
      RootSet want = flow.objects(addr);
      noteExternal(ud, want, flow, C->getFunction());
      std::optional<uint64_t> nlen;
      if (addr == src && C->arg_size() >= 3)
        if (const auto *CI = dyn_cast<ConstantInt>(C->getArgOperand(2)))
          nlen = CI->getZExtValue();
      auto stores = flow.aliasingStores(addr, nullptr, want, true, nlen);
      auto inits = flow.aliasingInits(addr, nullptr, want, true);
      takeStores(ud, C, stores, work, reported);
      takeInits(ud, inits, work);
      for (const Value *next : flow.byteSources(addr, want))
        addrs.push_back(next);
    }
    publish(std::move(ud));
  }
  return out;
}

} // namespace realdef
