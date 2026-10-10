#include "Entry.hpp"

#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <deque>
#include <map>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {

namespace {

std::string show(const llvm::Function *F) {
  std::string n = F->getName().str();
  std::string d = llvm::demangle(n);
  if (d.empty() || d == n)
    return n;
  return d;
}

bool strongExport(const llvm::Function *F) {
  if (!F || F->isDeclaration() || F->isIntrinsic() || !F->hasName())
    return false;
  if (F->hasLocalLinkage())
    return false;
  if (F->getVisibility() == llvm::GlobalValue::HiddenVisibility)
    return false;
  return true;
}

const llvm::Function *asFunction(const llvm::Value *V) {
  if (!V)
    return nullptr;
  return llvm::dyn_cast<llvm::Function>(V->stripPointerCastsAndAliases());
}

bool sameType(const llvm::Function *F, const llvm::CallBase *C) {
  return F && C && F->getFunctionType() == C->getFunctionType();
}

struct CodePtr {
  const llvm::GlobalVariable *gv = nullptr;
  int64_t off = 0;
  bool operator==(const CodePtr &o) const { return gv == o.gv && off == o.off; }
};

struct CodeHash {
  size_t operator()(const CodePtr &c) const {
    return (size_t)(uintptr_t)c.gv ^ ((size_t)c.off * 1315423911u);
  }
};

struct Field {
  const llvm::StructType *ty = nullptr;
  int64_t off = 0;
  bool operator==(const Field &o) const { return ty == o.ty && off == o.off; }
};

struct FieldHash {
  size_t operator()(const Field &f) const {
    return (size_t)(uintptr_t)f.ty ^ ((size_t)f.off * 1315423911u);
  }
};

struct Slot {
  int id = 0;
  Field field;
  bool operator==(const Slot &o) const { return id == o.id && field == o.field; }
};

struct SlotHash {
  size_t operator()(const Slot &s) const { return FieldHash{}(s.field) ^ ((size_t)s.id * 2654435761u); }
};

// Function-pointer fields are one slot per (struct type, constant offset).
// Virtual-call tables are per object, and only along the copy path described
// in Entry.hpp. Tokens name those objects.
class Solve {
 public:
  explicit Solve(llvm::Module &M) : M(M), DL(M.getDataLayout()) { run(); }

  std::vector<const llvm::Function *> callees(const llvm::CallBase *C, bool unnamed) const {
    std::vector<const llvm::Function *> out;
    std::unordered_set<const llvm::Function *> seen;
    auto add = [&](const llvm::Function *F) {
      if (F && seen.insert(F).second)
        out.push_back(F);
    };
    if (const llvm::Function *D = asFunction(C->getCalledOperand())) {
      add(D);
      return out;
    }
    // The call and the function each state a dereferenceable size. The
    // function reaches this call only when those sizes are equal. A missing
    // size leaves the function in the set. LLVM merges every std::function
    // instantiation into one struct; the size is the instantiation.
    auto sameBytes = [&](const llvm::Function *F) {
      unsigned i = 0;
      const unsigned nCall = C->arg_size();
      const unsigned nFun = F->arg_size();
      for (; i < nCall && i < nFun; ++i) {
        if (!C->paramHasAttr(i, llvm::Attribute::Dereferenceable))
          continue;
        if (!F->hasParamAttribute(i, llvm::Attribute::Dereferenceable))
          continue;
        if (C->getParamDereferenceableBytes(i) != F->getParamDereferenceableBytes(i))
          return false;
      }
      return true;
    };
    auto addSized = [&](const llvm::Function *F) {
      if (F && sameBytes(F))
        add(F);
    };
    auto typeWide = [&](bool tracked) {
      std::unordered_set<const llvm::Value *> walked;
      for (const llvm::Function *F : fnsOf(C->getCalledOperand(), walked, C->getFunction())) {
        if (!sameType(F, C))
          continue;
        // An instruction store belongs to the object it was copied into.
        // When that copy reduces, the object is the callee. When it does
        // not, the stored function stays a target of a load of this field:
        // dropping it removes a call the copies might reach. The
        // dereferenceable size both sides state keeps a different
        // instantiation out of that field. An initializer stays with the
        // struct type.
        if (tracked && objectStored.count(F) && !unresolved.count(F))
          continue;
        addSized(F);
      }
    };
    auto addFlow = [&]() {
      auto flowed = flowAt.find(C);
      if (flowed == flowAt.end())
        return;
      for (const llvm::Function *F : flowed->second)
        if (sameType(F, C))
          addSized(F);
    };
    if (openQuery.count(C)) {
      // The copies that reached this address stay. A function that is
      // unresolved somewhere else is not a callee here: the same LLVM type
      // is not the same object.
      addFlow();
      typeWide(false);
    } else if (unnamed) {
      if (flowAt.count(C)) {
        addFlow();
        typeWide(true);
      } else {
        typeWide(false);
      }
    } else if (flowAt.count(C)) {
      addFlow();
      typeWide(true);
    } else {
      // The address stayed on a parameter or an alloca. That object was
      // named, so the unnamed top is not a named target.
      typeWide(false);
    }
    const llvm::Value *obj = nullptr;
    int64_t delta = 0;
    std::unordered_set<const llvm::Value *> seenV;
    if (vtableCall(C->getCalledOperand(), obj, delta, seenV)) {
      auto it = tok.find(obj);
      if (it != tok.end()) {
        for (int t : it->second) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + delta});
            if (fit != fnAt.end() && fit->second && fit->second->getFunctionType() == C->getFunctionType())
              add(fit->second);
          }
        }
      }
    }
    return out;
  }

  // A call through a field of an argument. The functions are those stored
  // into that argument's object, not every function stored into the struct
  // type: one LLVM type can be every std::function.
  bool argField(const llvm::CallBase *C, int &arg, int64_t &off) const {
    std::unordered_set<const llvm::Value *> seen;
    std::vector<const llvm::Value *> stack{C->getCalledOperand()};
    const llvm::LoadInst *load = nullptr;
    while (!stack.empty()) {
      const llvm::Value *V = stack.back();
      stack.pop_back();
      if (!V || !seen.insert(V).second)
        continue;
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        load = L;
        break;
      }
      if (const auto *X = llvm::dyn_cast<llvm::CastInst>(V))
        stack.push_back(X->getOperand(0));
      else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        stack.push_back(Fr->getOperand(0));
      else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values())
          stack.push_back(inc);
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        stack.push_back(Sel->getTrueValue());
        stack.push_back(Sel->getFalseValue());
      }
    }
    if (!load)
      return false;
    auto f = fieldOf(load->getPointerOperand());
    if (!f)
      return false;
    const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(load->getPointerOperand()));
    if (!G)
      return false;
    std::vector<int> args;
    std::unordered_set<const llvm::Value *> seenA;
    whichArgs(G->getPointerOperand(), C->getFunction(), seenA, args);
    if (args.size() != 1)
      return false;
    arg = args[0];
    off = f->off;
    return true;
  }

  // Edges from the callers that pass the object, when a function was stored
  // into that object. Returns false when nothing was stored, so the type-wide
  // field remains the edge.
  template <class Note>
  bool noteObjectField(const llvm::CallBase *C, Note note) const {
    int arg = -1;
    int64_t off = 0;
    if (asFunction(C->getCalledOperand()) || !argField(C, arg, off))
      return false;
    auto sit = directSites.find(C->getFunction());
    if (sit == directSites.end())
      return false;
    bool any = false;
    for (const llvm::CallBase *S : sit->second) {
      if (static_cast<unsigned>(arg) >= S->arg_size())
        continue;
      std::vector<const llvm::Function *> fns;
      std::unordered_set<const llvm::Value *> seen;
      objectFieldFns(S->getArgOperand(static_cast<unsigned>(arg)), off, fns, seen);
      if (fns.empty())
        continue;
      any = true;
      for (const llvm::Function *D : fns)
        if (sameType(D, C))
          note(S->getFunction(), D);
    }
    return any;
  }

  void objectFieldFns(const llvm::Value *obj, int64_t off, std::vector<const llvm::Function *> &out,
                      std::unordered_set<const llvm::Value *> &seen) const {
    if (!obj || !seen.insert(obj).second)
      return;
    std::deque<const llvm::Value *> q;
    q.push_back(obj);
    std::unordered_set<const llvm::Value *> local{obj};
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
            llvm::isa<llvm::SelectInst>(U)) {
          if (local.insert(U).second)
            q.push_back(U);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          int64_t go = 0;
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            if (offsetOf(G, go) && go == 0 && local.insert(G).second)
              q.push_back(G);
            else if (auto f = fieldOf(G))
              if (f->off == off)
                for (const llvm::User *SU : G->users())
                  if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(SU))
                    if (S->getPointerOperand() == G || stripCasts(S->getPointerOperand()) == G)
                      if (const llvm::Function *Fn = asFunction(S->getValueOperand()))
                        out.push_back(Fn);
          }
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(U);
        if (!C)
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto it = fnPut.find(D);
        if (it == fnPut.end())
          continue;
        for (const FnPut &p : it->second) {
          if (p.off != off || p.arg < 0 || static_cast<unsigned>(p.arg) >= C->arg_size())
            continue;
          if (C->getArgOperand(static_cast<unsigned>(p.arg)) != V)
            continue;
          if (p.fn)
            out.push_back(p.fn);
        }
      }
    }
  }

 private:
  llvm::Module &M;
  const llvm::DataLayout &DL;
  struct SpecFn {
    const llvm::Function *fn = nullptr;
    std::string spec;
    bool init = false;
  };
  std::unordered_map<Field, std::vector<SpecFn>, FieldHash> fieldFn;
  std::map<std::pair<const llvm::GlobalVariable *, int64_t>, const llvm::Function *> fnAt;
  std::unordered_set<const llvm::GlobalVariable *> tables;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::Function *>> retFn;
  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> retSeen;
  std::unordered_map<const llvm::Value *, std::vector<int>> tok;
  std::unordered_map<const llvm::Value *, std::unordered_set<int>> tokSeen;
  std::unordered_map<int, std::unordered_set<CodePtr, CodeHash>> vtbl;
  std::unordered_set<const llvm::Value *> slice;
  // Fields that lie on a path from an allocation to a loaded virtual table.
  // A field the pointer reaches later is not a new object.
  std::unordered_set<const llvm::Value *> demand;
  std::unordered_map<const llvm::Value *, int> rootId;
  std::unordered_set<int> allocTok;
  std::unordered_map<int, int> tokDepth;
  int nextId = 1;
  std::deque<const llvm::Value *> wl;
  std::unordered_set<const llvm::Value *> queued;
  std::unordered_map<Field, std::vector<const llvm::LoadInst *>, FieldHash> fieldLoads;
  std::unordered_map<Field, std::vector<const llvm::Value *>, FieldHash> fieldStored;
  std::unordered_map<const llvm::Value *, std::vector<Slot>> addr;
  std::unordered_map<const llvm::Value *, std::unordered_set<Slot, SlotHash>> addrSeen;
  std::unordered_map<Slot, int, SlotHash> subId;
  std::unordered_map<Slot, std::vector<int>, SlotHash> slotTok;
  std::unordered_map<Slot, std::unordered_set<int>, SlotHash> slotSeen;
  std::unordered_map<Slot, std::vector<const llvm::LoadInst *>, SlotHash> slotLoads;
  std::unordered_map<Slot, std::unordered_set<const llvm::LoadInst *>, SlotHash> slotLoadSeen;
  bool live = false;
  std::unordered_map<const llvm::AllocaInst *, std::vector<const llvm::LoadInst *>> allocaLoads;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> directSites;
  std::vector<const llvm::StoreInst *> vtableStores;

  // A function may return the pointer loaded from a byte offset of one
  // argument, or the address of that field, or store a pointer there. The
  // slot is that argument and that offset.
  struct BoxOff {
    int arg = -1;
    int64_t off = 0;
    bool operator==(const BoxOff &o) const { return arg == o.arg && off == o.off; }
  };
  struct BoxMove {
    int dst = -1;
    int src = -1;
    int64_t off = 0;
    bool operator==(const BoxMove &o) const { return dst == o.dst && src == o.src && off == o.off; }
  };
  std::unordered_map<const llvm::Function *, std::vector<BoxOff>> retBox;
  std::unordered_map<const llvm::Function *, std::vector<BoxOff>> retAddr;
  std::unordered_map<const llvm::Function *, std::vector<BoxMove>> putBox;
  std::unordered_map<const llvm::Function *, std::vector<BoxMove>> mvBox;
  struct FnPut {
    int arg = -1;
    int64_t off = 0;
    const llvm::Function *fn = nullptr;
    bool operator==(const FnPut &o) const { return arg == o.arg && off == o.off && fn == o.fn; }
  };
  std::unordered_map<const llvm::Function *, std::vector<FnPut>> fnPut;
  // Indirect calls whose function pointer flows from a store into the loaded
  // object. Absent means the struct-type set is the edge.
  std::unordered_map<const llvm::CallBase *, std::vector<const llvm::Function *>> flowAt;
  std::unordered_set<const llvm::Function *> objectStored;
  // Every function constant stored by an instruction or an initializer.
  // An all-pointer struct is not a source type, so a load that does not
  // reduce uses this set, keyed by the call's function type.
  std::unordered_set<const llvm::Function *> storedAny;
  // Stored into an all-pointer slot. The merged layout is not a field, so
  // these functions share the call's type and not the struct's name.
  struct GlobFn {
    const llvm::GlobalVariable *gv = nullptr;
    int64_t off = 0;
    const llvm::Function *fn = nullptr;
  };
  std::vector<GlobFn> globFns;
  // A function whose copy could not be reduced to an object. It stays with
  // the struct type: excluding it would drop a call the copies might reach.
  std::unordered_set<const llvm::Function *> unresolved;
  std::unordered_set<const llvm::CallBase *> openQuery;

  bool offsetOf(const llvm::GEPOperator *GEP, int64_t &off) const {
    if (!GEP || !GEP->hasAllConstantIndices())
      return false;
    llvm::APInt ap(DL.getIndexTypeSizeInBits(GEP->getType()), 0);
    if (!GEP->accumulateConstantOffset(DL, ap))
      return false;
    off = ap.getSExtValue();
    return true;
  }

  // stripPointerCasts also drops a getelementptr whose indices are all zero.
  // Field 0 is that getelementptr: the address matches the object, and the
  // instruction still names the field.
  const llvm::Value *stripCasts(const llvm::Value *V) const {
    while (V) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0) {
          V = CE->getOperand(0);
          continue;
        }
      }
      break;
    }
    return V;
  }

  std::optional<Field> fieldOf(const llvm::Value *addr) const {
    const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(addr));
    if (!GEP)
      return std::nullopt;
    const auto *ST = llvm::dyn_cast<llvm::StructType>(GEP->getSourceElementType());
    if (!ST || !ST->isSized())
      return std::nullopt;
    int64_t off = 0;
    if (!offsetOf(GEP, off) || off < 0)
      return std::nullopt;
    auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(ST));
    if (sz.isScalable() || sz.getFixedValue() == 0)
      return std::nullopt;
    return Field{ST, off % (int64_t)sz.getFixedValue()};
  }

  bool ptrIndex(const llvm::Value *addr, const llvm::Value *&base, int64_t &delta) const {
    const auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(addr->stripPointerCasts());
    if (!GEP || !GEP->getSourceElementType()->isPointerTy() || !offsetOf(GEP, delta) || delta < 0)
      return false;
    base = GEP->getPointerOperand();
    return true;
  }

  void addFieldFn(Field f, const llvm::Function *F, const std::string &spec, bool init) {
    if (!F)
      return;
    auto &v = fieldFn[f];
    for (const SpecFn &e : v)
      if (e.fn == F && e.spec == spec && e.init == init)
        return;
    v.push_back(SpecFn{F, spec, init});
  }

  // An all-pointer struct is not a source type. LLVM merges every struct of
  // that layout into one type, so a lock table and an allocator become one
  // field. A struct with any other field keeps its layout.
  bool mixedStruct(const llvm::StructType *ST) const {
    if (!ST)
      return false;
    for (llvm::Type *E : ST->elements())
      if (!E->isPointerTy())
        return true;
    return false;
  }

  void place(const llvm::Constant *C, int64_t absOff, std::vector<std::pair<const llvm::StructType *, int64_t>> frames,
             const llvm::GlobalVariable *Root) {
    if (!C)
      return;
    if (const llvm::Function *F = asFunction(C)) {
      storedAny.insert(F);
      if (Root)
        globFns.push_back(GlobFn{Root, absOff, F});
      for (const auto &fr : frames) {
        if (!mixedStruct(fr.first))
          continue;
        auto sz = DL.getTypeAllocSize(const_cast<llvm::StructType *>(fr.first));
        if (sz.isScalable() || sz.getFixedValue() == 0 || fr.second < 0)
          continue;
        addFieldFn({fr.first, fr.second % (int64_t)sz.getFixedValue()}, F, {}, true);
      }
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
        place(llvm::cast<llvm::Constant>(CS->getOperand(i)), absOff + fo, std::move(next), Root);
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
        place(llvm::cast<llvm::Constant>(CA->getOperand(i)), absOff + (int64_t)i * step, std::move(next), Root);
      }
      return;
    }
    if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(C->stripPointerCastsAndAliases())) {
      if (tables.count(GV)) {
        for (const auto &fr : frames) {
          (void)fr;
        }
      }
    }
  }

  void indexTables(const llvm::GlobalVariable *GV, const llvm::Constant *C, int64_t off) {
    if (const llvm::Function *F = asFunction(C)) {
      fnAt[{GV, off}] = F;
      tables.insert(GV);
      return;
    }
    if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      const auto *SL = DL.getStructLayout(const_cast<llvm::StructType *>(CS->getType()));
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        indexTables(GV, llvm::cast<llvm::Constant>(CS->getOperand(i)), off + (int64_t)SL->getElementOffset(i));
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
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        indexTables(GV, llvm::cast<llvm::Constant>(CA->getOperand(i)), off + (int64_t)i * step);
    }
  }

  CodePtr codePtr(const llvm::Value *V) const {
    if (!V || asFunction(V))
      return {};
    const llvm::Value *S = V->stripPointerCastsAndAliases();
    const llvm::GlobalVariable *GV = nullptr;
    int64_t off = 0;
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(S)) {
      GV = llvm::dyn_cast<llvm::GlobalVariable>(G->getPointerOperand()->stripPointerCastsAndAliases());
      if (!GV || !offsetOf(G, off))
        return {};
    } else
      GV = llvm::dyn_cast<llvm::GlobalVariable>(S);
    if (!GV || !tables.count(GV))
      return {};
    return {GV, off};
  }

  int idOf(const llvm::Value *V) {
    auto it = rootId.find(V);
    if (it != rootId.end())
      return it->second;
    int id = nextId++;
    rootId.emplace(V, id);
    return id;
  }

  void addTok(const llvm::Value *V, int t) {
    if (!V || t <= 0)
      return;
    if (slice.insert(V).second)
      maybeSeed(V);
    if (!tokSeen[V].insert(t).second)
      return;
    tok[V].push_back(t);
    if (queued.insert(V).second)
      wl.push_back(V);
  }

  void maybeSeed(const llvm::Value *V) {
    if (!live || !V || !slice.count(V))
      return;
    if (llvm::isa<llvm::AllocaInst>(V) ||
        (llvm::isa<llvm::CallBase>(V) && V->getType()->isPointerTy() &&
         llvm::cast<llvm::CallBase>(V)->hasRetAttr(llvm::Attribute::NoAlias) &&
         !llvm::cast<llvm::CallBase>(V)->isInlineAsm())) {
      int id = idOf(V);
      allocTok.insert(id);
      tokDepth[id] = 0;
      addTok(V, id);
    }
  }

  int subToken(int parent, Field f) {
    Slot s{parent, f};
    auto it = subId.find(s);
    if (it != subId.end())
      return it->second;
    int id = nextId++;
    subId.emplace(s, id);
    tokDepth[id] = tokDepth[parent] + 1;
    return id;
  }

  void addSlot(Slot s, int t) {
    if (!slotSeen[s].insert(t).second)
      return;
    slotTok[s].push_back(t);
    auto it = slotLoads.find(s);
    if (it == slotLoads.end())
      return;
    for (const llvm::LoadInst *L : it->second)
      addTok(L, t);
  }

  void addAddr(const llvm::Value *V, Slot s) {
    if (!V || s.id <= 0)
      return;
    slice.insert(V);
    if (!addrSeen[V].insert(s).second)
      return;
    addr[V].push_back(s);
    if (queued.insert(V).second)
      wl.push_back(V);
  }

  void addSlice(const llvm::Value *V) {
    if (!V || !slice.insert(V).second)
      return;
    maybeSeed(V);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        addSlice(inc);
      return;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
      addSlice(S->getTrueValue());
      addSlice(S->getFalseValue());
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      addSlice(C->getOperand(0));
      return;
    }
    if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      if (CE->isCast() && CE->getNumOperands() > 0)
        addSlice(CE->getOperand(0));
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      addSlice(Fr->getOperand(0));
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      addSlice(G->getPointerOperand());
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      const llvm::Value *ptr = L->getPointerOperand()->stripPointerCasts();
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(ptr)) {
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              addSlice(SI->getValueOperand());
        return;
      }
      if (fieldOf(L->getPointerOperand())) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand())))
          addSlice(G->getPointerOperand());
      }
      return;
    }
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      const llvm::Function *Parent = A->getParent();
      unsigned idx = A->getArgNo();
      auto sit = directSites.find(Parent);
      if (sit == directSites.end())
        return;
      for (const llvm::CallBase *C : sit->second)
        if (idx < C->arg_size())
          addSlice(C->getArgOperand(idx));
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
      if (const llvm::Function *D = asFunction(C->getCalledOperand())) {
        if (!D->isDeclaration()) {
          for (const llvm::Instruction &I : llvm::instructions(*D))
            if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I))
              if (R->getReturnValue())
                addSlice(R->getReturnValue());
        }
      }
    }
  }

  void flowAddr(const llvm::Value *From, const llvm::User *U, const std::vector<Slot> &tags) {
    auto put = [&](const llvm::Value *D) {
      for (const Slot &s : tags)
        addAddr(D, s);
    };
    if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U)) {
      put(U);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
      if (Sel->getTrueValue() == From || Sel->getFalseValue() == From)
        put(Sel);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
      if (G->getPointerOperand() == From || G->getPointerOperand()->stripPointerCasts() == From) {
        int64_t off = 0;
        if (offsetOf(G, off) && off == 0)
          put(G);
      }
      return;
    }
    if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
      if (S->getValueOperand() == From) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
          for (const llvm::LoadInst *L : allocaLoads[AI])
            put(L);
      }
      if (S->getPointerOperand() == From || S->getPointerOperand()->stripPointerCasts() == From) {
        addSlice(S->getValueOperand());
        auto it = tok.find(S->getValueOperand());
        if (it != tok.end())
          for (const Slot &s : tags)
            for (int t : it->second)
              addSlot(s, t);
      }
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
      if (L->getPointerOperand() != From && L->getPointerOperand()->stripPointerCasts() != From)
        return;
      for (const Slot &s : tags) {
        if (slotLoadSeen[s].insert(L).second)
          slotLoads[s].push_back(L);
        auto it = slotTok.find(s);
        if (it != slotTok.end())
          for (int t : it->second)
            addTok(L, t);
      }
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
      const llvm::Function *D = asFunction(C->getCalledOperand());
      if (!D || D->isDeclaration())
        return;
      for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i)
        if (C->getArgOperand(i) == From)
          put(D->getArg(i));
      return;
    }
    if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
      if (R->getReturnValue() != From)
        return;
      for (const llvm::CallBase *C : directSites[R->getFunction()])
        put(C);
    }
  }

  void prop(const llvm::Value *V) {
    std::vector<int> mine = tok[V];
    std::vector<Slot> tags;
    if (auto at = addr.find(V); at != addr.end())
      tags = at->second;
    for (const llvm::User *U : V->users()) {
      if (!mine.empty()) {
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            if (auto f = fieldOf(G))
              for (int t : mine)
                addAddr(G, Slot{t, *f});
          }
        }
      }
      if (!tags.empty())
        flowAddr(V, U, tags);
      bool structural = llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) ||
                        llvm::isa<llvm::PHINode>(U) || llvm::isa<llvm::SelectInst>(U) ||
                        llvm::isa<llvm::GEPOperator>(U);
      if (!slice.count(U) && !structural && !llvm::isa<llvm::StoreInst>(U) && !llvm::isa<llvm::CallBase>(U) &&
          !llvm::isa<llvm::ReturnInst>(U))
        continue;
      if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
          llvm::isa<llvm::GEPOperator>(U)) {
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
            for (int t : mine)
              addTok(Sel, t);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            int64_t off = 0;
            if (offsetOf(G, off) && off == 0) {
              for (int t : mine)
                addTok(G, t);
            } else if (auto f = fieldOf(G)) {
              // The field of an allocation is its own object. A field of that
              // object keeps the object: the table loaded from it is the
              // object's table. Splitting again would name every nested byte
              // offset a new object and walk that token through the module.
              if (demand.count(G))
                for (int t : mine) {
                  if (tokDepth[t] == 0)
                    addTok(G, subToken(t, *f));
                  else
                    addTok(G, t);
                }
            }
          }
          continue;
        }
        for (int t : mine)
          addTok(U, t);
        continue;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
        if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
          for (int t : mine)
            addTok(Sel, t);
        continue;
      }
      if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
        if (S->getValueOperand() == V) {
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
            for (const llvm::LoadInst *L : allocaLoads[AI])
              for (int t : mine)
                addTok(L, t);
          auto at = addr.find(S->getPointerOperand());
          if (at != addr.end())
            for (const Slot &s : at->second)
              for (int t : mine)
                addSlot(s, t);
        }
        if (S->getPointerOperand() == V || S->getPointerOperand()->stripPointerCasts() == V) {
          CodePtr cp = codePtr(S->getValueOperand());
          if (cp.gv)
            for (int t : mine)
              vtbl[t].insert(cp);
        }
        continue;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D || D->isDeclaration())
          continue;
        for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i) {
          if (C->getArgOperand(i) != V)
            continue;
          for (int t : mine)
            addTok(D->getArg(i), t);
        }
        continue;
      }
      if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
        if (R->getReturnValue() != V)
          continue;
        for (const llvm::CallBase *C : directSites[R->getFunction()])
          for (int t : mine)
            addTok(C, t);
      }
    }
  }

  bool vtableCall(const llvm::Value *V, const llvm::Value *&obj, int64_t &delta,
                  std::unordered_set<const llvm::Value *> &seen) const {
    if (!V || !seen.insert(V).second)
      return false;
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        if (vtableCall(inc, obj, delta, seen))
          return true;
      return false;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V))
      return vtableCall(S->getTrueValue(), obj, delta, seen) || vtableCall(S->getFalseValue(), obj, delta, seen);
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return vtableCall(C->getOperand(0), obj, delta, seen);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return vtableCall(Fr->getOperand(0), obj, delta, seen);
    const auto *L = llvm::dyn_cast<llvm::LoadInst>(V);
    if (!L)
      return false;
    const llvm::Value *base = nullptr;
    if (!ptrIndex(L->getPointerOperand(), base, delta))
      return false;
    const llvm::Value *B = base->stripPointerCasts();
    if (const auto *BL = llvm::dyn_cast<llvm::LoadInst>(B))
      obj = BL->getPointerOperand();
    else
      obj = B;
    return true;
  }

  // A direct call may return the address of a field. A store through that
  // pointer is a store of the field. The address may cross a cast, a phi, a
  // select, a freeze, or an alloca.
  void addrFields(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seenVals,
                  std::unordered_set<const llvm::Function *> &seenFns, std::vector<Field> &out) {
    if (!V || !seenVals.insert(V).second)
      return;
    if (auto f = fieldOf(V)) {
      out.push_back(*f);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      addrFields(C->getOperand(0), seenVals, seenFns, out);
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      addrFields(Fr->getOperand(0), seenVals, seenFns, out);
      return;
    }
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        addrFields(inc, seenVals, seenFns, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      addrFields(Sel->getTrueValue(), seenVals, seenFns, out);
      addrFields(Sel->getFalseValue(), seenVals, seenFns, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              addrFields(SI->getValueOperand(), seenVals, seenFns, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D || D->isDeclaration() || !seenFns.insert(D).second)
        return;
      for (const llvm::Instruction &I : llvm::instructions(*D)) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
        if (R && R->getReturnValue())
          addrFields(R->getReturnValue(), seenVals, seenFns, out);
      }
    }
  }

  // A stored parameter may be any function passed for it at a direct call.
  // The pointer may sit in an alloca between the parameter and the store.
  void argFns(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen,
              std::vector<const llvm::Function *> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (const llvm::Function *F = asFunction(V)) {
      out.push_back(F);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      argFns(C->getOperand(0), seen, out);
      return;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      argFns(Fr->getOperand(0), seen, out);
      return;
    }
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        argFns(inc, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      argFns(Sel->getTrueValue(), seen, out);
      argFns(Sel->getFalseValue(), seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              argFns(SI->getValueOperand(), seen, out);
      return;
    }
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      unsigned idx = A->getArgNo();
      auto sit = directSites.find(A->getParent());
      if (sit == directSites.end())
        return;
      for (const llvm::CallBase *C : sit->second)
        if (idx < C->arg_size())
          argFns(C->getArgOperand(idx), seen, out);
    }
  }

  std::vector<const llvm::Function *> fnsOf(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen,
                                            const llvm::Function *home) const {
    std::vector<const llvm::Function *> out;
    if (!V || !seen.insert(V).second)
      return out;
    if (const llvm::Function *F = asFunction(V)) {
      out.push_back(F);
      return out;
    }
    auto take = [&](const llvm::Value *U) {
      for (const llvm::Function *F : fnsOf(U, seen, home))
        out.push_back(F);
    };
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        take(inc);
      return out;
    }
    if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
      take(S->getTrueValue());
      take(S->getFalseValue());
      return out;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      take(C->getOperand(0));
      return out;
    }
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      take(Fr->getOperand(0));
      return out;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (auto f = fieldOf(L->getPointerOperand())) {
        auto it = fieldFn.find(*f);
        if (it != fieldFn.end()) {
          const std::string homeSpec = classSpec(home);
          for (const SpecFn &s : it->second)
            if (fieldSpecVisible(s.spec, s.init, homeSpec))
              out.push_back(s.fn);
        }
      }
      // A function pointer may sit in an alloca between the field load and
      // the indirect call. The load may be any function stored there.
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              take(SI->getValueOperand());
      return out;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CallBase>(V)) {
      std::vector<const llvm::Function *> ts;
      if (const llvm::Function *D = asFunction(C->getCalledOperand()))
        ts.push_back(D);
      else {
        std::unordered_set<const llvm::Value *> w;
        ts = fnsOf(C->getCalledOperand(), w, home);
      }
      for (const llvm::Function *D : ts) {
        auto it = retFn.find(D);
        if (it != retFn.end())
          out.insert(out.end(), it->second.begin(), it->second.end());
      }
    }
    return out;
  }

  // The receiver of a vtable call is the object the table was loaded from.
  // Carry that object only along copies of the pointer: casts, phi, select,
  // freeze, a zero-offset getelementptr, an alloca store and its loads, a
  // direct call's matching parameter, and a returned pointer. A load through
  // the pointer is a field or a table, not a copy.
  void recv(const llvm::Value *Start, int t, std::deque<const llvm::Value *> &q,
            std::unordered_set<const llvm::Value *> &inq,
            const std::unordered_map<const llvm::Value *, std::vector<int>> &byObj) {
    if (!Start || t <= 0)
      return;
    std::deque<const llvm::Value *> stack;
    stack.push_back(Start);
    while (!stack.empty()) {
      const llvm::Value *V = stack.back();
      stack.pop_back();
      if (!V || !tokSeen[V].insert(t).second)
        continue;
      tok[V].push_back(t);
      if (byObj.count(V) && inq.insert(V).second)
        q.push_back(V);
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U)) {
          stack.push_back(U);
          continue;
        }
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getTrueValue() == V || Sel->getFalseValue() == V)
            stack.push_back(Sel);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) {
            int64_t off = 0;
            if (offsetOf(G, off) && off == 0)
              stack.push_back(G);
          }
          continue;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (S->getValueOperand() != V)
            continue;
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
            for (const llvm::LoadInst *L : allocaLoads[AI])
              stack.push_back(L);
          continue;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CallBase>(U)) {
          const llvm::Function *D = asFunction(C->getCalledOperand());
          if (!D || D->isDeclaration())
            continue;
          for (unsigned i = 0; i < C->arg_size() && i < D->arg_size(); ++i)
            if (C->getArgOperand(i) == V)
              stack.push_back(D->getArg(i));
          continue;
        }
        if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(U)) {
          if (R->getReturnValue() != V)
            continue;
          for (const llvm::CallBase *C : directSites[R->getFunction()])
            stack.push_back(C);
        }
      }
    }
  }


  template <class T>
  bool pushNew(std::vector<T> &v, const T &x) {
    if (std::find(v.begin(), v.end(), x) != v.end())
      return false;
    v.push_back(x);
    return true;
  }

  void whichArgs(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
                 std::vector<int> &out) const {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (A->getParent() == F)
        out.push_back(static_cast<int>(A->getArgNo()));
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return whichArgs(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return whichArgs(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        whichArgs(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      whichArgs(Sel->getTrueValue(), F, seen, out);
      whichArgs(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              whichArgs(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      int64_t off = 0;
      if (offsetOf(G, off) && off == 0)
        whichArgs(G->getPointerOperand(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retAddr.find(D);
      if (it == retAddr.end())
        return;
      for (const BoxOff &b : it->second)
        if (b.off == 0 && b.arg >= 0 && static_cast<unsigned>(b.arg) < CB->arg_size())
          whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seen, out);
    }
  }

  void boxOf(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
             std::vector<BoxOff> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (auto f = fieldOf(V)) {
      const auto *G = llvm::cast<llvm::GEPOperator>(stripCasts(V));
      std::vector<int> args;
      std::unordered_set<const llvm::Value *> seenA;
      whichArgs(G->getPointerOperand(), F, seenA, args);
      for (int a : args)
        out.push_back({a, f->off});
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return boxOf(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return boxOf(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        boxOf(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      boxOf(Sel->getTrueValue(), F, seen, out);
      boxOf(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              boxOf(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retAddr.find(D);
      if (it == retAddr.end())
        return;
      for (const BoxOff &b : it->second) {
        if (b.arg < 0 || static_cast<unsigned>(b.arg) >= CB->arg_size())
          continue;
        std::vector<int> args;
        std::unordered_set<const llvm::Value *> seenA;
        whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seenA, args);
        for (int a : args)
          out.push_back({a, b.off});
      }
    }
  }

  void loadedBox(const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
                 std::vector<BoxOff> &out) {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      std::unordered_set<const llvm::Value *> seenB;
      boxOf(L->getPointerOperand(), F, seenB, out);
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              loadedBox(SI->getValueOperand(), F, seen, out);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return loadedBox(C->getOperand(0), F, seen, out);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return loadedBox(Fr->getOperand(0), F, seen, out);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        loadedBox(inc, F, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      loadedBox(Sel->getTrueValue(), F, seen, out);
      loadedBox(Sel->getFalseValue(), F, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      const llvm::Function *D = asFunction(CB->getCalledOperand());
      if (!D)
        return;
      auto it = retBox.find(D);
      if (it == retBox.end())
        return;
      for (const BoxOff &b : it->second) {
        if (b.arg < 0 || static_cast<unsigned>(b.arg) >= CB->arg_size())
          continue;
        std::vector<int> args;
        std::unordered_set<const llvm::Value *> seenA;
        whichArgs(CB->getArgOperand(static_cast<unsigned>(b.arg)), F, seenA, args);
        for (int a : args)
          out.push_back({a, b.off});
      }
    }
  }

  void learnBoxes() {
    std::deque<const llvm::Function *> work;
    std::unordered_set<const llvm::Function *> queuedF;
    auto pushF = [&](const llvm::Function *F) {
      if (F && !F->isDeclaration() && queuedF.insert(F).second)
        work.push_back(F);
    };
    for (llvm::Function &F : M)
      pushF(&F);
    while (!work.empty()) {
      const llvm::Function *F = work.front();
      work.pop_front();
      queuedF.erase(F);
      bool grew = false;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        if (const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
          if (!R->getReturnValue())
            continue;
          std::vector<BoxOff> ls;
          std::unordered_set<const llvm::Value *> seen;
          loadedBox(R->getReturnValue(), F, seen, ls);
          for (const BoxOff &b : ls)
            grew = pushNew(retBox[F], b) || grew;
          std::vector<BoxOff> as;
          seen.clear();
          boxOf(R->getReturnValue(), F, seen, as);
          for (const BoxOff &b : as)
            grew = pushNew(retAddr[F], b) || grew;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          std::vector<BoxOff> dst;
          std::unordered_set<const llvm::Value *> seen;
          boxOf(S->getPointerOperand(), F, seen, dst);
          std::vector<int> srcA;
          seen.clear();
          whichArgs(S->getValueOperand(), F, seen, srcA);
          for (const BoxOff &b : dst)
            for (int s : srcA)
              grew = pushNew(putBox[F], BoxMove{b.arg, s, b.off}) || grew;
          std::vector<BoxOff> srcL;
          seen.clear();
          loadedBox(S->getValueOperand(), F, seen, srcL);
          for (const BoxOff &b : dst)
            for (const BoxOff &s : srcL)
              if (s.arg != b.arg && s.off == b.off)
                grew = pushNew(mvBox[F], BoxMove{b.arg, s.arg, b.off}) || grew;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto lift = [&](int d, int s, int64_t off, bool asMove) {
          if (d < 0 || s < 0 || static_cast<unsigned>(d) >= C->arg_size() || static_cast<unsigned>(s) >= C->arg_size())
            return;
          std::vector<int> ds;
          std::unordered_set<const llvm::Value *> seenD;
          whichArgs(C->getArgOperand(static_cast<unsigned>(d)), F, seenD, ds);
          std::vector<int> ss;
          std::unordered_set<const llvm::Value *> seenS;
          whichArgs(C->getArgOperand(static_cast<unsigned>(s)), F, seenS, ss);
          for (int dst : ds)
            for (int src : ss)
              if (dst != src)
                grew = pushNew(asMove ? mvBox[F] : putBox[F], BoxMove{dst, src, off}) || grew;
          if (asMove)
            return;
          std::vector<BoxOff> loaded;
          seenS.clear();
          loadedBox(C->getArgOperand(static_cast<unsigned>(s)), F, seenS, loaded);
          for (int dst : ds)
            for (const BoxOff &src : loaded)
              if (dst != src.arg && src.off == off)
                grew = pushNew(mvBox[F], BoxMove{dst, src.arg, off}) || grew;
        };
        auto pit = putBox.find(D);
        if (pit != putBox.end())
          for (const BoxMove &m : pit->second)
            lift(m.dst, m.src, m.off, false);
        auto mit = mvBox.find(D);
        if (mit != mvBox.end())
          for (const BoxMove &m : mit->second)
            lift(m.dst, m.src, m.off, true);
      }
      if (!grew)
        continue;
      auto sit = directSites.find(F);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second)
        pushF(C->getFunction());
    }
  }

  void give(const llvm::Value *obj, const llvm::Value *src) {
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> seen;
    q.push_back(src);
    seen.insert(src);
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      auto it = tok.find(V);
      if (it != tok.end())
        for (int t : it->second) {
          if (vtbl.count(t) && tokSeen[obj].insert(t).second)
            tok[obj].push_back(t);
        }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
        if (seen.insert(C->getOperand(0)).second)
          q.push_back(C->getOperand(0));
      } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V)) {
        if (seen.insert(Fr->getOperand(0)).second)
          q.push_back(Fr->getOperand(0));
      } else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values())
          if (seen.insert(inc).second)
            q.push_back(inc);
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        if (seen.insert(Sel->getTrueValue()).second)
          q.push_back(Sel->getTrueValue());
        if (seen.insert(Sel->getFalseValue()).second)
          q.push_back(Sel->getFalseValue());
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          for (const llvm::User *U : AI->users())
            if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
              if (SI->getPointerOperand()->stripPointerCasts() == AI && seen.insert(SI->getValueOperand()).second)
                q.push_back(SI->getValueOperand());
      }
    }
  }

  void storedInto(const llvm::Value *box, int64_t off, std::set<std::pair<const llvm::Value *, int64_t>> &seenBox,
                  const llvm::Value *obj) {
    if (!box || !seenBox.insert({box, off}).second)
      return;
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> seen;
    q.push_back(box);
    seen.insert(box);
    while (!q.empty()) {
      const llvm::Value *V = q.front();
      q.pop_front();
      for (const llvm::User *U : V->users()) {
        if (llvm::isa<llvm::CastInst>(U) || llvm::isa<llvm::FreezeInst>(U) || llvm::isa<llvm::PHINode>(U) ||
            llvm::isa<llvm::SelectInst>(U)) {
          if (seen.insert(U).second)
            q.push_back(U);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          int64_t go = 0;
          if ((G->getPointerOperand() == V || G->getPointerOperand()->stripPointerCasts() == V) && offsetOf(G, go) &&
              go == 0 && seen.insert(G).second)
            q.push_back(G);
          continue;
        }
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (S->getValueOperand() == V) {
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
              for (const llvm::User *LU : AI->users())
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(LU))
                  if (L->getPointerOperand()->stripPointerCasts() == AI && seen.insert(L).second)
                    q.push_back(L);
          }
          continue;
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(U);
        if (!C)
          continue;
        const llvm::Function *D = asFunction(C->getCalledOperand());
        if (!D)
          continue;
        auto pit = putBox.find(D);
        if (pit != putBox.end())
          for (const BoxMove &m : pit->second)
            if (m.off == off && m.dst >= 0 && m.src >= 0 && static_cast<unsigned>(m.dst) < C->arg_size() &&
                static_cast<unsigned>(m.src) < C->arg_size() && C->getArgOperand(static_cast<unsigned>(m.dst)) == V)
              give(obj, C->getArgOperand(static_cast<unsigned>(m.src)));
        auto mit = mvBox.find(D);
        if (mit == mvBox.end())
          continue;
        for (const BoxMove &m : mit->second)
          if (m.off == off && m.dst >= 0 && m.src >= 0 && static_cast<unsigned>(m.dst) < C->arg_size() &&
              static_cast<unsigned>(m.src) < C->arg_size() && C->getArgOperand(static_cast<unsigned>(m.dst)) == V)
            storedInto(C->getArgOperand(static_cast<unsigned>(m.src)), off, seenBox, obj);
      }
    }
  }

  void fromField(const llvm::Value *V, std::unordered_set<const llvm::Value *> &seen, const llvm::Value *obj,
                 std::set<std::pair<const llvm::Value *, int64_t>> &seenBox) {
    if (!V || !seen.insert(V).second)
      return;
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
      return fromField(C->getOperand(0), seen, obj, seenBox);
    if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
      return fromField(Fr->getOperand(0), seen, obj, seenBox);
    if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (const llvm::Value *inc : P->incoming_values())
        fromField(inc, seen, obj, seenBox);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      fromField(Sel->getTrueValue(), seen, obj, seenBox);
      fromField(Sel->getFalseValue(), seen, obj, seenBox);
      return;
    }
    if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        for (const llvm::User *U : AI->users())
          if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
            if (SI->getPointerOperand()->stripPointerCasts() == AI)
              fromField(SI->getValueOperand(), seen, obj, seenBox);
      return;
    }
    const auto *CB = llvm::dyn_cast<llvm::CallBase>(V);
    if (!CB)
      return;
    const llvm::Function *D = asFunction(CB->getCalledOperand());
    if (!D)
      return;
    auto it = retBox.find(D);
    if (it == retBox.end())
      return;
    for (const BoxOff &b : it->second)
      if (b.arg >= 0 && static_cast<unsigned>(b.arg) < CB->arg_size())
        storedInto(CB->getArgOperand(static_cast<unsigned>(b.arg)), b.off, seenBox, obj);
  }

  // A virtual call's receiver may be a pointer loaded from one object's field.
  // Copy onto that receiver only the objects stored into that field.
  void carryFields() {
    learnBoxes();
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (!vtableCall(C->getCalledOperand(), obj, delta, seenV) || !obj)
          continue;
        std::unordered_set<const llvm::Value *> seen;
        std::set<std::pair<const llvm::Value *, int64_t>> seenBox;
        fromField(obj, seen, obj, seenBox);
      }
    }
  }

  // A function pointer stored into an object reaches a load of that object
  // along copies of the pointer and along direct calls that take the object.
  // The struct type is not the carrier: one LLVM struct can be every
  // instantiation.
  void learnObjects() {
    struct Addr {
      const llvm::Value *obj = nullptr;
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
      bool operator==(const Addr &o) const {
        return obj == o.obj && storage == o.storage && off == o.off && inner == o.inner;
      }
    };
    struct AddrHash {
      size_t operator()(const Addr &a) const {
        size_t h = (size_t)(uintptr_t)a.obj ^ ((size_t)a.off * 1315423911u) ^ ((size_t)a.inner * 2654435761u);
        return a.storage ? h ^ 0x9e3779b97f4a7c15ull : h;
      }
    };
    struct Ret {
      bool has = false;
      int arg = -1;
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
    };
    std::unordered_map<const llvm::Function *, Ret> retOf;
    std::unordered_map<const llvm::Value *, std::optional<Addr>> rmemo;

    std::function<std::optional<Addr>(const llvm::Value *, const llvm::Function *,
                                      std::unordered_set<const llvm::Value *> &, bool)>
        root;
    root = [&](const llvm::Value *V, const llvm::Function *F, std::unordered_set<const llvm::Value *> &seen,
               bool calls) -> std::optional<Addr> {
      if (!V)
        return std::nullopt;
      if (auto it = rmemo.find(V); it != rmemo.end())
        return it->second;
      if (!seen.insert(V).second)
        return std::nullopt;
      struct Save {
        std::unordered_map<const llvm::Value *, std::optional<Addr>> &m;
        const llvm::Value *v;
        std::optional<Addr> r;
        ~Save() { m[v] = r; }
      } save{rmemo, V, std::nullopt};
      auto ok = [&](std::optional<Addr> r) {
        save.r = std::move(r);
        return save.r;
      };
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == F)
          return ok(Addr{A, false, 0, 0});
        return ok(std::nullopt);
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V))
        return ok(Addr{AI, false, 0, 0});
      if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(V))
        return ok(Addr{GV, false, 0, 0});
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
        return ok(root(C->getOperand(0), F, seen, calls));
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0)
          return ok(root(CE->getOperand(0), F, seen, calls));
      }
      if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        return ok(root(Fr->getOperand(0), F, seen, calls));
      if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        std::optional<Addr> acc;
        for (const llvm::Value *inc : P->incoming_values()) {
          auto one = root(inc, F, seen, calls);
          if (!one)
            return ok(std::nullopt);
          if (!acc)
            acc = one;
          else if (!(*acc == *one))
            return ok(std::nullopt);
        }
        return ok(acc);
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        auto a = root(Sel->getTrueValue(), F, seen, calls);
        auto b = root(Sel->getFalseValue(), F, seen, calls);
        if (!a || !b || !(*a == *b))
          return ok(std::nullopt);
        return ok(a);
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        auto base = root(G->getPointerOperand(), F, seen, calls);
        if (!base)
          return ok(std::nullopt);
        int64_t delta = 0;
        if (offsetOf(G, delta)) {
          if (base->storage)
            base->inner += delta;
          else
            base->off += delta;
          return ok(base);
        }
        if (!base->storage) {
          base->storage = true;
          base->inner = 0;
        } else
          base->inner = 0;
        return ok(base);
      }
      if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          std::optional<Addr> acc;
          bool any = false;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
              continue;
            any = true;
            auto one = root(SI->getValueOperand(), F, seen, calls);
            if (!one)
              return ok(std::nullopt);
            if (!acc)
              acc = one;
            else if (!(*acc == *one))
              return ok(std::nullopt);
          }
          if (any)
            return ok(acc);
        }
        auto addr = root(L->getPointerOperand(), F, seen, calls);
        if (!addr || !L->getType()->isPointerTy())
          return ok(std::nullopt);
        // begin and finish are two fields of one all-pointer struct and one
        // allocation. The load is the buffer of the object that contains
        // that struct, not a distinct buffer per field.
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand()))) {
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType())) {
            if (!mixedStruct(ST)) {
              int64_t delta = 0;
              if (offsetOf(G, delta)) {
                if (addr->storage)
                  addr->inner -= delta;
                else
                  addr->off -= delta;
              }
            }
          }
        }
        if (!addr->storage) {
          addr->storage = true;
          addr->inner = 0;
        } else
          addr->inner = 0;
        return ok(addr);
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (!calls)
          return ok(std::nullopt);
        if (const llvm::Function *D = asFunction(CB->getCalledOperand())) {
          // Itanium __dynamic_cast(src, srcType, dstType, src2dst). A
          // non-negative src2dst is the offset of the source subobject in
          // the destination, so the destination is src minus that offset.
          // -1 and -2 are not a known adjustment.
          if (D->getName() == "__dynamic_cast" && CB->arg_size() >= 4) {
            if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(3))) {
              int64_t src2dst = CI->getSExtValue();
              if (src2dst >= 0) {
                auto src = root(CB->getArgOperand(0), F, seen, calls);
                if (src) {
                  if (src->storage)
                    src->inner -= src2dst;
                  else
                    src->off -= src2dst;
                  return ok(src);
                }
              }
            }
          }
          auto it = retOf.find(D);
          if (it != retOf.end() && it->second.has && it->second.arg >= 0 &&
              static_cast<unsigned>(it->second.arg) < CB->arg_size()) {
            const Ret &r = it->second;
            auto arg = root(CB->getArgOperand(static_cast<unsigned>(r.arg)), F, seen, calls);
            if (arg) {
              if (r.storage) {
                if (!arg->storage) {
                  arg->storage = true;
                  arg->inner = r.inner;
                } else
                  arg->inner += r.inner;
                return ok(arg);
              }
              if (arg->storage)
                arg->inner += r.off;
              else
                arg->off += r.off;
              return ok(arg);
            }
          }
        }
        // A noalias allocation is an object of its own. operator new is not an
        // argument of its caller, and a field of the allocated object is still
        // that allocation.
        if (CB->getType()->isPointerTy() && CB->hasRetAttr(llvm::Attribute::NoAlias) && !CB->isInlineAsm())
          return ok(Addr{CB, false, 0, 0});
        return ok(std::nullopt);
      }
      return ok(std::nullopt);
    };

    auto summarize = [&](const llvm::Function *F) -> bool {
      if (retOf.count(F))
        return false;
      Ret acc;
      bool saw = false;
      bool bad = false;
      for (const llvm::Instruction &I : llvm::instructions(*F)) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
        if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
          continue;
        if (llvm::isa<llvm::ConstantPointerNull>(R->getReturnValue()))
          continue;
        std::unordered_set<const llvm::Value *> seen;
        auto one = root(R->getReturnValue(), F, seen, true);
        if (!one || !llvm::isa<llvm::Argument>(one->obj) ||
            llvm::cast<llvm::Argument>(one->obj)->getParent() != F) {
          bad = true;
          break;
        }
        Ret cur;
        cur.has = true;
        cur.arg = (int)llvm::cast<llvm::Argument>(one->obj)->getArgNo();
        cur.storage = one->storage;
        cur.off = one->off;
        cur.inner = one->inner;
        if (!saw)
          acc = cur;
        else if (acc.arg != cur.arg || acc.storage != cur.storage || acc.off != cur.off || acc.inner != cur.inner) {
          bad = true;
          break;
        }
        saw = true;
      }
      if (bad || !saw)
        return false;
      retOf[F] = acc;
      return true;
    };
    std::deque<const llvm::Function *> retQ;
    for (llvm::Function &F : M)
      if (!F.isDeclaration())
        retQ.push_back(&F);
    while (!retQ.empty()) {
      const llvm::Function *F = retQ.front();
      retQ.pop_front();
      if (!summarize(F))
        continue;
      auto sit = directSites.find(F);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second)
        if (!retOf.count(C->getFunction()))
          retQ.push_back(C->getFunction());
    }

    // A relative address names a field of an argument. Applied to the actual
    // at one callsite, it is that field of that object. Two calls stay two
    // objects: the argument is not a location shared by its callers.
    auto apply = [](Addr base, const Addr &rel) {
      if (rel.storage) {
        if (!base.storage) {
          base.storage = true;
          base.inner = rel.inner;
          base.off += rel.off;
        } else
          base.inner += rel.off + rel.inner;
        return base;
      }
      if (base.storage)
        base.inner += rel.off;
      else
        base.off += rel.off;
      return base;
    };

    // Every object a value may name. A phi or a select is the union of its
    // inputs, not a failure: dropping one input would lose a copy.
    std::unordered_map<const llvm::Value *, std::vector<Addr>> pmemo;
    std::function<std::vector<Addr>(const llvm::Value *, const llvm::Function *,
                                    std::unordered_set<const llvm::Value *> &)>
        places;
    places = [&](const llvm::Value *V, const llvm::Function *F,
                 std::unordered_set<const llvm::Value *> &seen) -> std::vector<Addr> {
      if (!V)
        return {};
      if (auto it = pmemo.find(V); it != pmemo.end())
        return it->second;
      if (!seen.insert(V).second)
        return {};
      std::vector<Addr> result;
      auto commit = [&]() {
        std::vector<Addr> uniq;
        for (const Addr &a : result) {
          if (!a.obj)
            continue;
          bool dup = false;
          for (const Addr &b : uniq)
            if (a == b)
              dup = true;
          if (!dup)
            uniq.push_back(a);
        }
        pmemo.emplace(V, uniq);
        return uniq;
      };
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
        if (A->getParent() == F)
          result.push_back(Addr{A, false, 0, 0});
        return commit();
      }
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(V)) {
        result.push_back(Addr{AI, false, 0, 0});
        return commit();
      }
      if (const auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(V)) {
        result.push_back(Addr{GV, false, 0, 0});
        return commit();
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
        result = places(C->getOperand(0), F, seen);
      else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast() && CE->getNumOperands() > 0)
          result = places(CE->getOperand(0), F, seen);
      } else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
        result = places(Fr->getOperand(0), F, seen);
      else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (const llvm::Value *inc : P->incoming_values()) {
          auto one = places(inc, F, seen);
          result.insert(result.end(), one.begin(), one.end());
        }
      } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        auto a = places(Sel->getTrueValue(), F, seen);
        auto b = places(Sel->getFalseValue(), F, seen);
        result = std::move(a);
        result.insert(result.end(), b.begin(), b.end());
      } else if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        auto bases = places(G->getPointerOperand(), F, seen);
        int64_t delta = 0;
        bool constant = offsetOf(G, delta);
        for (Addr b : bases) {
          if (constant) {
            if (b.storage)
              b.inner += delta;
            else
              b.off += delta;
          } else if (!b.storage) {
            b.storage = true;
            b.inner = 0;
          } else
            b.inner = 0;
          result.push_back(b);
        }
      } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          bool any = false;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getPointerOperand()->stripPointerCasts() != AI)
              continue;
            any = true;
            auto one = places(SI->getValueOperand(), F, seen);
            result.insert(result.end(), one.begin(), one.end());
          }
          if (any)
            return commit();
        }
        if (!L->getType()->isPointerTy())
          return commit();
        auto bases = places(L->getPointerOperand(), F, seen);
        int64_t sub = 0;
        bool fold = false;
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(L->getPointerOperand()))) {
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(G->getSourceElementType())) {
            if (!mixedStruct(ST)) {
              int64_t delta = 0;
              if (offsetOf(G, delta)) {
                fold = true;
                sub = delta;
              }
            }
          }
        }
        for (Addr addr : bases) {
          if (fold) {
            if (addr.storage)
              addr.inner -= sub;
            else
              addr.off -= sub;
          }
          if (!addr.storage) {
            addr.storage = true;
            addr.inner = 0;
          } else
            addr.inner = 0;
          result.push_back(addr);
        }
      } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
        if (const llvm::Function *D = asFunction(CB->getCalledOperand())) {
          if (D->getName() == "__dynamic_cast" && CB->arg_size() >= 4) {
            if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(3))) {
              int64_t src2dst = CI->getSExtValue();
              if (src2dst >= 0) {
                auto srcs = places(CB->getArgOperand(0), F, seen);
                for (Addr s : srcs) {
                  if (s.storage)
                    s.inner -= src2dst;
                  else
                    s.off -= src2dst;
                  result.push_back(s);
                }
                if (!result.empty())
                  return commit();
              }
            }
          }
          auto it = retOf.find(D);
          if (it != retOf.end() && it->second.has && it->second.arg >= 0 &&
              static_cast<unsigned>(it->second.arg) < CB->arg_size()) {
            const Ret &r = it->second;
            auto args = places(CB->getArgOperand(static_cast<unsigned>(r.arg)), F, seen);
            for (Addr arg : args) {
              if (r.storage) {
                if (!arg.storage) {
                  arg.storage = true;
                  arg.inner = r.inner;
                } else
                  arg.inner += r.inner;
              } else if (arg.storage)
                arg.inner += r.off;
              else
                arg.off += r.off;
              result.push_back(arg);
            }
            if (!result.empty())
              return commit();
          }
        }
        if (CB->getType()->isPointerTy() && CB->hasRetAttr(llvm::Attribute::NoAlias) && !CB->isInlineAsm())
          result.push_back(Addr{CB, false, 0, 0});
      }
      return commit();
    };

    // A load/store copy puts one pointer in two cells. The component is one
    // pointer. A global or a noalias allocation names it; a load of either
    // cell is that object. Other components keep the address they already
    // had, so a parameter that was not copied from such an object stays one.
    bool canonReady = false;
    std::unordered_map<Addr, Addr, AddrHash> ufParent;
    auto ufFind = [&](Addr a) {
      std::vector<Addr> path;
      while (true) {
        auto it = ufParent.find(a);
        if (it == ufParent.end()) {
          ufParent[a] = a;
          break;
        }
        if (it->second == a)
          break;
        path.push_back(a);
        a = it->second;
      }
      for (const Addr &p : path)
        ufParent[p] = a;
      return a;
    };
    auto canonAddr = [&](Addr a) {
      if (!canonReady || !a.storage || !a.obj)
        return a;
      Addr cell{a.obj, false, a.off, 0};
      if (!ufParent.count(cell))
        return a;
      Addr r = ufFind(cell);
      if (r == cell || !r.obj)
        return a;
      if (!llvm::isa<llvm::GlobalVariable>(r.obj) && !llvm::isa<llvm::CallBase>(r.obj))
        return a;
      a.obj = r.obj;
      a.off = r.off;
      a.storage = true;
      return a;
    };

    struct Sub {
      std::vector<Addr> out;
      bool failed = false;
    };
    // failed: the actual does not reduce to an object. An empty result that
    // is not failed is the same address passed back. A different offset of
    // that parameter is a different field.
    auto substPlaces = [&](const llvm::CallBase *C, Addr a) {
      Sub r;
      const auto *A = llvm::dyn_cast<llvm::Argument>(a.obj);
      if (!A) {
        r.out.push_back(a);
        return r;
      }
      const llvm::Function *Cal = asFunction(C->getCalledOperand());
      if (!Cal || A->getParent() != Cal) {
        r.out.push_back(a);
        return r;
      }
      if (A->getArgNo() >= C->arg_size()) {
        r.failed = true;
        return r;
      }
      std::unordered_set<const llvm::Value *> seen;
      auto found = places(C->getArgOperand(A->getArgNo()), C->getFunction(), seen);
      if (found.empty()) {
        r.failed = true;
        return r;
      }
      for (Addr b : found) {
        // The same address is the parameter passed back: no new object.
        // A different offset is that field of the same parameter.
        Addr got = canonAddr(apply(b, a));
        if (got == a)
          continue;
        r.out.push_back(got);
      }
      return r;
    };

    struct Copy {
      Addr src, dst;
      const llvm::Function *fn = nullptr;
    };
    std::vector<std::pair<Addr, const llvm::Function *>> seeds;
    std::vector<Copy> copies;
    // A noalias allocation stored into a cell. Functions at an offset of the
    // allocation are at that offset of the cell's pointee.
    std::unordered_map<const llvm::Value *, std::vector<Addr>> heldIn;
    std::vector<std::pair<const llvm::CallBase *, Addr>> queries;
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (!S->getValueOperand()->getType()->isPointerTy())
            continue;
          std::unordered_set<const llvm::Value *> seenD, seenS;
          auto dsts = places(S->getPointerOperand(), &F, seenD);
          if (const llvm::Function *Fn = asFunction(S->getValueOperand())) {
            objectStored.insert(Fn);
            storedAny.insert(Fn);
            if (dsts.empty())
              unresolved.insert(Fn);
            else
              for (const Addr &d : dsts)
                seeds.push_back({d, Fn});
          } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(S->getValueOperand())) {
            auto srcs = places(L->getPointerOperand(), &F, seenS);
            for (const Addr &s : srcs)
              for (const Addr &d : dsts)
                copies.push_back(Copy{s, d, &F});
          } else {
            // A store of a noalias allocation itself. Casts do not change
            // the object. A function at an offset of the allocation is at
            // that offset of this cell's pointee.
            const llvm::Value *v = S->getValueOperand();
            std::unordered_set<const llvm::Value *> seenV;
            while (v && seenV.insert(v).second) {
              if (const auto *C = llvm::dyn_cast<llvm::CastInst>(v))
                v = C->getOperand(0);
              else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(v))
                v = Fr->getOperand(0);
              else
                break;
            }
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(v);
            if (CB && !CB->isInlineAsm() && CB->hasRetAttr(llvm::Attribute::NoAlias))
              for (const Addr &d : dsts)
                if (d.obj)
                  heldIn[CB].push_back(d);
          }
        }
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        std::unordered_set<const llvm::Value *> seen;
        const llvm::Value *op = C->getCalledOperand();
        const llvm::LoadInst *load = nullptr;
        std::vector<const llvm::Value *> stack{op};
        std::unordered_set<const llvm::Value *> walked;
        while (!stack.empty()) {
          const llvm::Value *V = stack.back();
          stack.pop_back();
          if (!V || !walked.insert(V).second)
            continue;
          if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
            load = L;
            break;
          }
          if (const auto *X = llvm::dyn_cast<llvm::CastInst>(V))
            stack.push_back(X->getOperand(0));
          else if (const auto *Fr = llvm::dyn_cast<llvm::FreezeInst>(V))
            stack.push_back(Fr->getOperand(0));
        }
        if (!load)
          continue;
        std::unordered_set<const llvm::Value *> seenA;
        auto addrs = places(load->getPointerOperand(), &F, seenA);
        if (addrs.empty())
          openQuery.insert(C);
        else
          for (const Addr &a : addrs)
            queries.push_back({C, a});
      }
    }

    for (const GlobFn &g : globFns)
      if (g.gv && g.fn)
        seeds.push_back({Addr{g.gv, false, g.off, 0}, g.fn});

    // Inclusion edges. An edge inside a function may name its parameters.
    // At each direct call those parameters are the actuals, so the edge
    // becomes an edge between the caller's objects. A callsite whose actual
    // does not reduce keeps the functions that reach that actual on the
    // parameter. The LLVM type is not that set.
    std::unordered_map<Addr, std::vector<Addr>, AddrHash> intraSucc;
    std::unordered_map<Addr, std::vector<Addr>, AddrHash> cross;
    std::unordered_set<Addr, AddrHash> leakAt;
    // Functions that reach an actual the call cannot name. They stay on that
    // parameter. A function that does not reach the actual is not carried,
    // and the LLVM type is not that set.
    auto reaching = [&](const llvm::Value *rootV, const llvm::Function *in) {
      std::vector<const llvm::Function *> out;
      std::unordered_set<const llvm::Function *> have;
      std::unordered_set<const llvm::Value *> seen;
      std::vector<const llvm::Value *> st{rootV};
      while (!st.empty()) {
        const llvm::Value *V = st.back();
        st.pop_back();
        if (!V || !seen.insert(V).second)
          continue;
        if (const llvm::Function *Fn = asFunction(V)) {
          if (have.insert(Fn).second)
            out.push_back(Fn);
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
        } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(V)) {
          st.push_back(S->getTrueValue());
          st.push_back(S->getFalseValue());
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(V)) {
          // An alloca is one object. A store through any other pointer is
          // not proved to be this value, and the LLVM type is not the set.
          const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(stripCasts(L->getPointerOperand()));
          if (!AI)
            continue;
          for (const llvm::User *U : AI->users()) {
            const auto *SI = llvm::dyn_cast<llvm::StoreInst>(U);
            if (!SI || SI->getFunction() != in)
              continue;
            if (stripCasts(SI->getPointerOperand()) != AI)
              continue;
            st.push_back(SI->getValueOperand());
          }
        }
      }
      return out;
    };
    for (const Copy &c : copies) {
      if (!c.src.obj || !c.dst.obj)
        continue;
      intraSucc[c.src].push_back(c.dst);
      const auto *A = llvm::dyn_cast<llvm::Argument>(c.src.obj);
      if (!A || !c.fn)
        continue;
      auto sit = directSites.find(c.fn);
      if (sit == directSites.end())
        continue;
      for (const llvm::CallBase *C : sit->second) {
        auto ss = substPlaces(C, c.src);
        auto ds = substPlaces(C, c.dst);
        if (ss.failed) {
          if (A->getArgNo() < C->arg_size())
            for (const llvm::Function *Fn : reaching(C->getArgOperand(A->getArgNo()), C->getFunction()))
              seeds.push_back({c.src, Fn});
          continue;
        }
        if (ds.failed) {
          // The caller-side destination has no object. The functions at the
          // source stay on the named destination inside this function.
          for (const Addr &s : ss.out)
            cross[s].push_back(c.dst);
          continue;
        }
        for (const Addr &s : ss.out)
          for (const Addr &d : ds.out)
            cross[s].push_back(d);
      }
    }

    auto betterCell = [](Addr a, Addr b) {
      auto rank = [](const llvm::Value *v) {
        if (llvm::isa<llvm::GlobalVariable>(v))
          return 0;
        if (llvm::isa<llvm::CallBase>(v))
          return 1;
        return 2;
      };
      int ra = a.obj ? rank(a.obj) : 3;
      int rb = b.obj ? rank(b.obj) : 3;
      if (ra != rb)
        return ra < rb ? a : b;
      return (uintptr_t)a.obj <= (uintptr_t)b.obj ? a : b;
    };
    auto uniteCell = [&](Addr a, Addr b) {
      if (!a.obj || !b.obj || a.storage || b.storage)
        return;
      a = ufFind(a);
      b = ufFind(b);
      if (a == b)
        return;
      Addr w = betterCell(a, b);
      Addr l = (w == a) ? b : a;
      ufParent[l] = w;
    };
    for (const auto &kv : intraSucc)
      for (const Addr &d : kv.second)
        uniteCell(kv.first, d);
    for (const auto &kv : cross)
      for (const Addr &d : kv.second)
        uniteCell(kv.first, d);
    canonReady = true;

    // Copies out of a parameter, in the callee's frame. At a call the
    // parameter is the actual, so two calls stay two objects. A callee of
    // that callee is the same equation. The set of destinations is finite:
    // a field offset is one a copy already names, and a walk that returns
    // to a function at a new offset does not name a field.
    std::unordered_map<const llvm::Function *, std::vector<std::pair<Addr, Addr>>> argCopy;
    struct Pat {
      bool storage = false;
      int64_t off = 0;
      int64_t inner = 0;
      bool operator<(const Pat &o) const {
        if (storage != o.storage)
          return storage < o.storage;
        if (off != o.off)
          return off < o.off;
        return inner < o.inner;
      }
    };
    std::set<Pat> patterns;
    for (const Copy &c : copies) {
      if (!llvm::isa<llvm::Argument>(c.src.obj) || !c.fn)
        continue;
      argCopy[c.fn].push_back({c.src, c.dst});
      if (c.src.off != 0 || c.src.inner != 0 || c.src.storage)
        patterns.insert(Pat{c.src.storage, c.src.off, c.src.inner});
    }
    struct Site {
      const llvm::CallBase *C = nullptr;
      const llvm::Function *D = nullptr;
      std::vector<std::pair<const llvm::Argument *, std::vector<Addr>>> args;
    };
    std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> callsIn;
    for (const auto &kv : directSites)
      for (const llvm::CallBase *C : kv.second)
        if (C->getFunction())
          callsIn[C->getFunction()].push_back(C);
    std::unordered_map<const llvm::Function *, std::vector<Site>> sitesIn;
    auto ensureSites = [&](const llvm::Function *F) {
      if (!F || sitesIn.count(F))
        return;
      std::vector<Site> out;
      auto cit = callsIn.find(F);
      if (cit != callsIn.end()) {
        for (const llvm::CallBase *C : cit->second) {
          const llvm::Function *D = asFunction(C->getCalledOperand());
          if (!D || D->isDeclaration())
            continue;
          Site s;
          s.C = C;
          s.D = D;
          unsigned n = C->arg_size();
          if (D->arg_size() < n)
            n = static_cast<unsigned>(D->arg_size());
          for (unsigned i = 0; i < n; ++i) {
            const llvm::Value *arg = C->getArgOperand(i);
            if (!arg->getType()->isPointerTy())
              continue;
            std::unordered_set<const llvm::Value *> seenP;
            auto ps = places(arg, F, seenP);
            if (ps.empty())
              continue;
            s.args.push_back({D->getArg(i), std::move(ps)});
          }
          if (!s.args.empty())
            out.push_back(std::move(s));
        }
      }
      sitesIn.emplace(F, std::move(out));
    };

    struct SeenKey {
      const llvm::Value *obj = nullptr;
      int64_t off = 0;
      int64_t inner = 0;
      bool storage = false;
      const llvm::Function *fn = nullptr;
      bool operator==(const SeenKey &o) const {
        return obj == o.obj && off == o.off && inner == o.inner && storage == o.storage && fn == o.fn;
      }
    };
    struct SeenHash {
      size_t operator()(const SeenKey &k) const {
        return AddrHash{}(Addr{k.obj, k.storage, k.off, k.inner}) ^ (size_t)(uintptr_t)k.fn;
      }
    };
    struct Edge {
      const llvm::CallBase *call = nullptr;
      Addr formal;
      const llvm::Function *callee = nullptr;
    };
    struct Node {
      int state = 0;
      bool leak = false;
      std::vector<Addr> dst;
      std::vector<Edge> edges;
    };
    std::unordered_map<SeenKey, Node, SeenHash> nodes;
    std::unordered_map<SeenKey, std::vector<SeenKey>, SeenHash> parents;
    std::unordered_set<const llvm::Function *> gray;
    std::deque<SeenKey> kq;
    std::unordered_set<SeenKey, SeenHash> inQ;
    auto enqueue = [&](const SeenKey &k) {
      if (inQ.insert(k).second)
        kq.push_back(k);
    };
    auto keyOf = [](const llvm::Function *D, Addr a) {
      return SeenKey{a.obj, a.off, a.inner, a.storage, D};
    };
    // The relative field is the one difference of the actual and the address
    // that holds the function. A difference no copy names is not a field.
    auto formalsFor = [&](const llvm::Argument *arg, const std::vector<Addr> &locs, Addr target,
                          const llvm::Function *callee) {
      std::vector<Addr> cands;
      std::unordered_set<Addr, AddrHash> seen;
      auto add = [&](Addr f) {
        if (f.obj && seen.insert(f).second)
          cands.push_back(f);
      };
      for (const Addr &base : locs) {
        if (!arg || base.obj != target.obj)
          continue;
        Addr rel{arg, false, 0, 0};
        bool ok = false;
        if (!base.storage && !target.storage && base.inner == target.inner) {
          rel.off = target.off - base.off;
          ok = true;
        } else if (base.storage && target.storage && base.off == target.off) {
          rel.off = target.inner - base.inner;
          ok = true;
        } else if (!base.storage && target.storage) {
          rel.storage = true;
          rel.off = target.off - base.off;
          rel.inner = target.inner;
          ok = true;
        }
        if (!ok)
          continue;
        bool whole = !rel.storage && rel.off == 0 && rel.inner == 0;
        if (whole || patterns.count(Pat{rel.storage, rel.off, rel.inner}))
          add(rel);
      }
      if (callee) {
        if (auto it = argCopy.find(callee); it != argCopy.end())
          for (const auto &e : it->second)
            if (e.first.obj == arg)
              add(e.first);
      }
      return cands;
    };
    std::function<void(const llvm::Function *, Addr)> build;
    build = [&](const llvm::Function *D, Addr src) {
      if (!D || !llvm::isa<llvm::Argument>(src.obj) ||
          llvm::cast<llvm::Argument>(src.obj)->getParent() != D)
        return;
      SeenKey key = keyOf(D, src);
      if (auto it = nodes.find(key); it != nodes.end() && it->second.state != 0)
        return;
      if (gray.count(D)) {
        nodes[key].leak = true;
        nodes[key].state = 2;
        return;
      }
      nodes[key].state = 1;
      gray.insert(D);
      std::vector<Addr> direct;
      std::unordered_set<Addr, AddrHash> have;
      if (auto it = argCopy.find(D); it != argCopy.end()) {
        for (const auto &e : it->second)
          if (e.first == src && e.second.obj && have.insert(e.second).second)
            direct.push_back(e.second);
      }
      std::vector<Edge> edges;
      ensureSites(D);
      if (auto sit = sitesIn.find(D); sit != sitesIn.end()) {
        std::vector<Site> mine = sit->second;
        for (const Site &site : mine) {
          for (const auto &ag : site.args) {
            bool touch = false;
            for (const Addr &loc : ag.second)
              if (loc.obj == src.obj)
                touch = true;
            if (!touch)
              continue;
            for (const Addr &formal : formalsFor(ag.first, ag.second, src, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed) {
                nodes[key].leak = true;
                continue;
              }
              bool eq = false;
              for (const Addr &s : ss.out)
                if (s == src)
                  eq = true;
              if (!eq)
                continue;
              SeenKey child = keyOf(site.D, formal);
              build(site.D, formal);
              // The same address again adds no object. A summary that was
              // not built, or that is still open, is not a proof that the
              // copy went somewhere else.
              if (child == key)
                continue;
              auto cit = nodes.find(child);
              if (cit == nodes.end() || cit->second.state != 2) {
                nodes[key].leak = true;
                continue;
              }
              if (cit->second.leak)
                nodes[key].leak = true;
              edges.push_back(Edge{site.C, formal, site.D});
              parents[child].push_back(key);
            }
          }
        }
      }
      gray.erase(D);
      {
        auto &n = nodes[key];
        n.dst = std::move(direct);
        n.edges = std::move(edges);
        n.state = 2;
      }
      enqueue(key);
    };
    auto solve = [&]() {
      while (!kq.empty()) {
        SeenKey k = kq.front();
        kq.pop_front();
        inQ.erase(k);
        auto nit = nodes.find(k);
        if (nit == nodes.end() || nit->second.state != 2)
          continue;
        Node &n = nit->second;
        std::unordered_set<Addr, AddrHash> have(n.dst.begin(), n.dst.end());
        bool grew = false;
        bool wasLeak = n.leak;
        for (const Edge &e : n.edges) {
          auto cit = nodes.find(keyOf(e.callee, e.formal));
          if (cit == nodes.end()) {
            n.leak = true;
            continue;
          }
          if (cit->second.leak)
            n.leak = true;
          for (const Addr &d : cit->second.dst) {
            auto ds = substPlaces(e.call, d);
            if (ds.failed) {
              n.leak = true;
              continue;
            }
            for (const Addr &x : ds.out) {
              if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(x.obj)) {
                if (Arg->getParent() != e.call->getFunction()) {
                  n.leak = true;
                  continue;
                }
              }
              if (have.insert(x).second) {
                n.dst.push_back(x);
                grew = true;
              }
            }
          }
        }
        if (grew || (n.leak && !wasLeak))
          for (const SeenKey &p : parents[k])
            enqueue(p);
      }
    };

    std::unordered_map<Addr, std::vector<const llvm::Function *>, AddrHash> cellFn;
    std::unordered_set<SeenKey, SeenHash> cellSeen;
    std::deque<std::pair<Addr, const llvm::Function *>> wl;
    for (const auto &s : seeds)
      wl.push_back(s);
    while (!wl.empty()) {
      Addr a = wl.front().first;
      const llvm::Function *Fn = wl.front().second;
      wl.pop_front();
      if (!a.obj || !Fn)
        continue;
      if (!cellSeen.insert(SeenKey{a.obj, a.off, a.inner, a.storage, Fn}).second)
        continue;
      if (leakAt.count(a))
        unresolved.insert(Fn);
      cellFn[a].push_back(Fn);
      Addr named = canonAddr(a);
      if (!(named == a)) {
        if (leakAt.count(named))
          unresolved.insert(Fn);
        cellFn[named].push_back(Fn);
      }
      // A global initializer is already named by the struct type. Walking
      // every use of the global is the module. Copies that name it as an
      // address are edges and are followed below.
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(a.obj)) {
        auto sit = directSites.find(A->getParent());
        if (sit != directSites.end()) {
          for (const llvm::CallBase *C : sit->second) {
            auto ps = substPlaces(C, a);
            if (ps.failed)
              continue;
            for (const Addr &p : ps.out)
              wl.push_back({p, Fn});
          }
        }
      }
      if (auto it = intraSucc.find(a); it != intraSucc.end())
        for (const Addr &d : it->second)
          wl.push_back({d, Fn});
      if (auto it = cross.find(a); it != cross.end())
        for (const Addr &d : it->second)
          wl.push_back({d, Fn});
      if (auto hit = heldIn.find(a.obj); hit != heldIn.end()) {
        for (Addr cell : hit->second) {
          if (!cell.storage) {
            cell.storage = true;
            cell.inner = 0;
          }
          // The offset of the function in the allocation is the offset in
          // the pointee. A storage address already names that pointee offset.
          Addr rel{nullptr, a.storage, a.off, a.inner};
          wl.push_back({apply(cell, rel), Fn});
        }
      }
      const llvm::Function *home = nullptr;
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(a.obj))
        home = AI->getFunction();
      else if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(a.obj))
        home = Arg->getParent();
      else if (const auto *Ins = llvm::dyn_cast<llvm::Instruction>(a.obj))
        home = Ins->getFunction();
      if (!home)
        continue;
      ensureSites(home);
      auto cit = sitesIn.find(home);
      if (cit == sitesIn.end())
        continue;
      std::vector<Site> mine = cit->second;
      for (const Site &site : mine) {
        for (const auto &ag : site.args) {
          bool touch = false;
          for (const Addr &loc : ag.second)
            if (loc.obj == a.obj)
              touch = true;
          if (!touch)
            continue;
          for (const Addr &formal : formalsFor(ag.first, ag.second, a, site.D)) {
            auto ss = substPlaces(site.C, formal);
            if (ss.failed)
              continue;
            bool eq = false;
            for (const Addr &s : ss.out)
              if (s == a)
                eq = true;
            if (!eq)
              continue;
            build(site.D, formal);
            solve();
            auto nit = nodes.find(keyOf(site.D, formal));
            if (nit == nodes.end() || nit->second.state != 2) {
              unresolved.insert(Fn);
              continue;
            }
            if (nit->second.leak)
              unresolved.insert(Fn);
            for (const Addr &d : nit->second.dst) {
              auto ds = substPlaces(site.C, d);
              if (ds.failed)
                continue;
              for (const Addr &x : ds.out) {
                if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(x.obj)) {
                  if (Arg->getParent() != home) {
                    unresolved.insert(Fn);
                    continue;
                  }
                }
                wl.push_back({x, Fn});
              }
            }
          }
        }
      }
    }

    // A load/store copy may sit in a callee that was handed the object.
    // `dest` is the parameter the pointer is written into. The sources are
    // the addresses in this function, or a global, that were stored there.
    auto identityOf = [](Addr a) {
      if (a.storage)
        return Addr{a.obj, false, a.off, 0};
      return a;
    };
    auto covers = [](Addr written, Addr target) {
      if (!written.obj || written.obj != target.obj || written.off != target.off ||
          written.storage != target.storage)
        return false;
      if (!written.storage)
        return written.inner == target.inner;
      return written.inner == target.inner || written.inner == 0;
    };
    auto asPointee = [](Addr src, Addr query) {
      if (query.storage && !src.storage) {
        src.storage = true;
        src.inner = query.inner;
      }
      return src;
    };
    struct FromNode {
      int state = 0;
      bool leak = false;
      std::vector<Addr> srcs;
    };
    std::unordered_map<SeenKey, FromNode, SeenHash> fromNodes;
    std::unordered_set<const llvm::Function *> fromGray;
    std::function<void(const llvm::Function *, Addr)> fromBuild;
    fromBuild = [&](const llvm::Function *D, Addr dest) {
      if (!D || !llvm::isa<llvm::Argument>(dest.obj) ||
          llvm::cast<llvm::Argument>(dest.obj)->getParent() != D)
        return;
      SeenKey key = keyOf(D, dest);
      if (auto it = fromNodes.find(key); it != fromNodes.end() && it->second.state != 0)
        return;
      if (fromGray.count(D)) {
        fromNodes[key].leak = true;
        fromNodes[key].state = 2;
        return;
      }
      fromNodes[key].state = 1;
      fromGray.insert(D);
      std::vector<Addr> srcs;
      std::unordered_set<Addr, AddrHash> have;
      if (auto it = argCopy.find(D); it != argCopy.end())
        for (const auto &e : it->second)
          if (covers(e.second, dest) && e.first.obj && have.insert(e.first).second)
            srcs.push_back(e.first);
      ensureSites(D);
      if (auto sit = sitesIn.find(D); sit != sitesIn.end()) {
        std::vector<Site> mine = sit->second;
        for (const Site &site : mine) {
          for (const auto &ag : site.args) {
            for (const Addr &formal : formalsFor(ag.first, ag.second, dest, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed) {
                fromNodes[key].leak = true;
                continue;
              }
              bool hit = false;
              for (const Addr &s : ss.out)
                if (s == dest || covers(s, dest))
                  hit = true;
              if (!hit)
                continue;
              SeenKey child = keyOf(site.D, formal);
              fromBuild(site.D, formal);
              if (child == key)
                continue;
              auto cit = fromNodes.find(child);
              if (cit == fromNodes.end() || cit->second.state != 2) {
                fromNodes[key].leak = true;
                continue;
              }
              if (cit->second.leak)
                fromNodes[key].leak = true;
              for (const Addr &s : cit->second.srcs) {
                auto ps = substPlaces(site.C, s);
                if (ps.failed) {
                  fromNodes[key].leak = true;
                  continue;
                }
                for (const Addr &p : ps.out)
                  if (p.obj && have.insert(p).second)
                    srcs.push_back(p);
              }
            }
          }
        }
      }
      fromGray.erase(D);
      auto &n = fromNodes[key];
      n.srcs = std::move(srcs);
      n.state = 2;
    };

    struct QKey {
      const llvm::Value *obj = nullptr;
      int64_t off = 0;
      int64_t inner = 0;
      bool storage = false;
      bool operator==(const QKey &o) const {
        return obj == o.obj && off == o.off && inner == o.inner && storage == o.storage;
      }
    };
    struct QHash {
      size_t operator()(const QKey &k) const { return AddrHash{}(Addr{k.obj, k.storage, k.off, k.inner}); }
    };
    std::unordered_set<const llvm::CallBase *> grounded;
    std::unordered_map<const llvm::CallBase *, std::vector<const llvm::Function *>> found;
    for (const auto &q : queries) {
      if (openQuery.count(q.first))
        continue;
      std::deque<Addr> wq;
      std::unordered_set<QKey, QHash> st;
      std::unordered_set<const llvm::Function *> haveFn;
      wq.push_back(q.second);
      bool open = false;
      while (!wq.empty() && !open) {
        Addr a = wq.front();
        wq.pop_front();
        if (!a.obj || !st.insert(QKey{a.obj, a.off, a.inner, a.storage}).second)
          continue;
        auto take = [&](const Addr &key) {
          if (auto it = cellFn.find(key); it != cellFn.end())
            for (const llvm::Function *Fn : it->second)
              if (haveFn.insert(Fn).second)
                found[q.first].push_back(Fn);
        };
        take(a);
        Addr named = canonAddr(a);
        if (!(named == a))
          take(named);
        auto groundOf = [](const Addr &key) {
          return key.obj && (llvm::isa<llvm::GlobalVariable>(key.obj) || llvm::isa<llvm::CallBase>(key.obj));
        };
        if (groundOf(a) || groundOf(named))
          grounded.insert(q.first);
        // The union of every callsite's actual is already on this parameter.
        if (open)
          break;
        if (!llvm::isa<llvm::AllocaInst>(a.obj) && !llvm::isa<llvm::CallBase>(a.obj))
          continue;
        const llvm::Function *home = nullptr;
        if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(a.obj))
          home = AI->getFunction();
        else if (const auto *Ins = llvm::dyn_cast<llvm::Instruction>(a.obj))
          home = Ins->getFunction();
        if (!home)
          continue;
        Addr id = identityOf(a);
        ensureSites(home);
        auto cit = sitesIn.find(home);
        if (cit == sitesIn.end())
          continue;
        std::vector<Site> mine = cit->second;
        for (const Site &site : mine) {
          if (open)
            break;
          for (const auto &ag : site.args) {
            if (open)
              break;
            for (const Addr &formal : formalsFor(ag.first, ag.second, id, site.D)) {
              auto ss = substPlaces(site.C, formal);
              if (ss.failed)
                continue;
              bool hit = false;
              for (const Addr &s : ss.out)
                if (s == id || covers(s, id))
                  hit = true;
              if (!hit)
                continue;
              fromBuild(site.D, formal);
              auto fit = fromNodes.find(keyOf(site.D, formal));
              if (fit == fromNodes.end() || fit->second.state != 2)
                continue;
              if (fit->second.leak)
                continue;
              for (const Addr &src : fit->second.srcs) {
                auto ps = substPlaces(site.C, src);
                if (ps.failed)
                  continue;
                for (const Addr &p : ps.out)
                  wq.push_back(asPointee(p, a));
              }
            }
          }
        }
      }
      if (open)
        openQuery.insert(q.first);
    }
    for (auto &kv : found) {
      std::unordered_set<const llvm::Function *> seen;
      std::vector<const llvm::Function *> uniq;
      for (const llvm::Function *Fn : kv.second)
        if (seen.insert(Fn).second)
          uniq.push_back(Fn);
      flowAt[kv.first] = std::move(uniq);
    }
    for (const auto &q : queries) {
      if (openQuery.count(q.first) || flowAt.count(q.first) || !grounded.count(q.first))
        continue;
      // The load reduced to a global or a noalias allocation, and no copy
      // put a function there. An instruction-stored function is absent only
      // when every copy of it reduced. A copy whose actual does not reduce
      // keeps the functions that reach that actual on the parameter.
      flowAt[q.first] = {};
    }
  }

  void run() {
    for (llvm::GlobalVariable &GV : M.globals())
      if (GV.hasInitializer())
        indexTables(&GV, GV.getInitializer(), 0);
    for (llvm::GlobalVariable &GV : M.globals())
      if (GV.hasInitializer()) {
        const llvm::Constant *C = GV.getInitializer();
        if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C))
          place(CS, 0, {}, &GV);
        else if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C))
          place(CA, 0, {}, &GV);
        else
          place(C, 0, {}, &GV);
      }

    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm())
          continue;
        if (const llvm::Function *D = asFunction(C->getCalledOperand()))
          if (!D->isDeclaration())
            directSites[D].push_back(C);
      }
    }
    learnObjects();
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          std::vector<Field> fields;
          if (auto f = fieldOf(S->getPointerOperand()))
            fields.push_back(*f);
          else {
            std::unordered_set<const llvm::Value *> seenVals;
            std::unordered_set<const llvm::Function *> seenFns;
            addrFields(S->getPointerOperand(), seenVals, seenFns, fields);
          }
          for (const Field &f : fields) {
            fieldStored[f].push_back(S->getValueOperand());
            if (!mixedStruct(f.ty))
              continue;
            std::unordered_set<const llvm::Value *> seen;
            const std::string spec = classSpec(S->getFunction());
            for (const llvm::Function *Fn : fnsOf(S->getValueOperand(), seen, S->getFunction()))
              addFieldFn(f, Fn, spec, false);
            std::unordered_set<const llvm::Value *> seenA;
            std::vector<const llvm::Function *> passed;
            argFns(S->getValueOperand(), seenA, passed);
            for (const llvm::Function *Fn : passed)
              addFieldFn(f, Fn, spec, false);
            if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(stripCasts(S->getPointerOperand()))) {
              std::vector<int> args;
              std::unordered_set<const llvm::Value *> seenB;
              whichArgs(G->getPointerOperand(), S->getFunction(), seenB, args);
              // A load of the same field is the type-wide set. Recording that
              // here would copy every std::function target into every object.
              // Only a function constant, or a parameter that is one, is a
              // store into this argument.
              std::vector<const llvm::Function *> stored = passed;
              if (const llvm::Function *Fn = asFunction(S->getValueOperand()))
                stored.push_back(Fn);
              for (int a : args)
                for (const llvm::Function *Fn : stored)
                  pushNew(fnPut[S->getFunction()], FnPut{a, f.off, Fn});
            }
          }
          if (codePtr(S->getValueOperand()).gv)
            vtableStores.push_back(S);
        }
        if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
            allocaLoads[AI].push_back(L);
          if (auto f = fieldOf(L->getPointerOperand()))
            fieldLoads[*f].push_back(L);
        }
      }
    }

    bool grew = true;
    while (grew) {
      grew = false;
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I);
          if (!R || !R->getReturnValue())
            continue;
          std::unordered_set<const llvm::Value *> seen;
          for (const llvm::Function *Fn : fnsOf(R->getReturnValue(), seen, &F)) {
            if (retSeen[&F].insert(Fn).second) {
              retFn[&F].push_back(Fn);
              grew = true;
            }
          }
        }
      }
    }

    for (const llvm::StoreInst *S : vtableStores)
      addSlice(S->getPointerOperand());
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seen;
        if (vtableCall(C->getCalledOperand(), obj, delta, seen) && obj)
          addSlice(obj);
      }
    }

    demand = slice;
    live = true;
    std::vector<const llvm::Value *> roots(slice.begin(), slice.end());
    for (const llvm::Value *V : roots)
      maybeSeed(V);
    while (!wl.empty()) {
      const llvm::Value *V = wl.front();
      wl.pop_front();
      queued.erase(V);
      prop(V);
    }
    for (const llvm::StoreInst *S : vtableStores) {
      CodePtr cp = codePtr(S->getValueOperand());
      auto it = tok.find(S->getPointerOperand());
      if (it == tok.end())
        continue;
      for (int t : it->second)
        vtbl[t].insert(cp);
    }
    // An indirect call returns the objects its targets return, the same way a
    // direct call does. A factory stored in a map is not a direct call, and
    // the allocated object would otherwise die at the call. Only an object
    // that holds a table is copied. Function-pointer fields still do not
    // carry a receiver in the other direction.
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        std::unordered_set<const llvm::Value *> walked;
        std::vector<const llvm::Function *> ts = fnsOf(C->getCalledOperand(), walked, &F);
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (vtableCall(C->getCalledOperand(), obj, delta, seenV) && obj) {
          auto it = tok.find(obj);
          if (it != tok.end())
            for (int t : it->second) {
              auto vt = vtbl.find(t);
              if (vt == vtbl.end())
                continue;
              for (const CodePtr &cp : vt->second) {
                auto fit = fnAt.find({cp.gv, cp.off + delta});
                if (fit != fnAt.end() && fit->second)
                  ts.push_back(fit->second);
              }
            }
        }
        for (const llvm::Function *D : ts) {
          if (!D || D->isDeclaration() || D->getFunctionType() != C->getFunctionType())
            continue;
          for (const llvm::Instruction &RI : llvm::instructions(*D)) {
            const auto *R = llvm::dyn_cast<llvm::ReturnInst>(&RI);
            if (!R || !R->getReturnValue())
              continue;
            auto rt = tok.find(R->getReturnValue());
            if (rt == tok.end())
              continue;
            for (int t : rt->second)
              if (vtbl.count(t))
                addTok(C, t);
          }
        }
      }
    }
    while (!wl.empty()) {
      const llvm::Value *V = wl.front();
      wl.pop_front();
      queued.erase(V);
      prop(V);
    }
    carryFields();
    // A vtable call passes its receiver into each function at that slot, so a
    // later vtable call on the same object can see the table. Function-pointer
    // fields stay shared by struct type and do not carry an object.
    struct Site {
      const llvm::CallBase *call;
      const llvm::Value *obj;
      int64_t delta;
      int arg;
    };
    std::vector<Site> sites;
    std::unordered_map<const llvm::Value *, std::vector<int>> byObj;
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!C || C->isInlineAsm() || asFunction(C->getCalledOperand()))
          continue;
        const llvm::Value *obj = nullptr;
        int64_t delta = 0;
        std::unordered_set<const llvm::Value *> seenV;
        if (!vtableCall(C->getCalledOperand(), obj, delta, seenV) || !obj)
          continue;
        int arg = -1;
        const llvm::Value *base = stripCasts(obj);
        for (unsigned i = 0; i < C->arg_size(); ++i)
          if (stripCasts(C->getArgOperand(i)) == base) {
            arg = static_cast<int>(i);
            break;
          }
        byObj[obj].push_back(static_cast<int>(sites.size()));
        sites.push_back({C, obj, delta, arg});
      }
    }
    std::deque<const llvm::Value *> q;
    std::unordered_set<const llvm::Value *> inq;
    for (const auto &kv : byObj) {
      if (!tok.count(kv.first))
        continue;
      q.push_back(kv.first);
      inq.insert(kv.first);
    }
    while (!q.empty()) {
      const llvm::Value *obj = q.front();
      q.pop_front();
      inq.erase(obj);
      auto have = tok.find(obj);
      if (have == tok.end())
        continue;
      std::vector<int> mine = have->second;
      for (int si : byObj[obj]) {
        const Site &site = sites[si];
        if (site.arg < 0)
          continue;
        std::unordered_set<const llvm::Function *> ts;
        for (int t : mine) {
          auto vt = vtbl.find(t);
          if (vt == vtbl.end())
            continue;
          for (const CodePtr &cp : vt->second) {
            auto fit = fnAt.find({cp.gv, cp.off + site.delta});
            if (fit != fnAt.end() && fit->second && !fit->second->isDeclaration())
              ts.insert(fit->second);
          }
        }
        for (const llvm::Function *D : ts) {
          if (static_cast<unsigned>(site.arg) >= D->arg_size())
            continue;
          const llvm::Argument *formal = D->getArg(static_cast<unsigned>(site.arg));
          for (int t : mine)
            recv(formal, t, q, inq, byObj);
        }
      }
    }
  }
};

} // namespace

std::vector<EntryGroup> findEntries(llvm::Module &downstream, const std::vector<std::string> &chops) {
  std::unordered_set<std::string> want(chops.begin(), chops.end());
  Solve solve(downstream);

  std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> namedCallers, mayCallers;
  std::unordered_map<std::string, std::unordered_set<const llvm::Function *>> namedSeeds, maySeeds;
  auto note = [&](const llvm::Function *caller, const llvm::Function *D, bool named) {
    std::string name = show(D);
    if (want.count(name)) {
      if (named)
        namedSeeds[name].insert(caller);
      maySeeds[name].insert(caller);
    }
    if (!D->isDeclaration() && D->getParent() == &downstream) {
      if (named)
        namedCallers[D].insert(caller);
      mayCallers[D].insert(caller);
    }
  };
  for (llvm::Function &F : downstream) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      const auto *C = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!C || C->isInlineAsm())
        continue;
      auto namedNote = [&](const llvm::Function *caller, const llvm::Function *D) { note(caller, D, true); };
      // An object-field edge is one named edge. It does not replace the
      // field lattice: a function still in that lattice stays a named callee.
      solve.noteObjectField(C, namedNote);
      for (const llvm::Function *D : solve.callees(C, false))
        note(&F, D, true);
      for (const llvm::Function *D : solve.callees(C, true))
        note(&F, D, false);
    }
  }

  auto reachOf = [&](const std::unordered_set<const llvm::Function *> &seed,
                     const std::unordered_map<const llvm::Function *, std::unordered_set<const llvm::Function *>> &callers) {
    std::unordered_set<const llvm::Function *> reach = seed;
    std::queue<const llvm::Function *> q;
    for (const llvm::Function *F : reach)
      q.push(F);
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
    return reach;
  };
  auto exports = [](const std::unordered_set<const llvm::Function *> &reach) {
    std::vector<std::string> names;
    for (const llvm::Function *F : reach)
      if (strongExport(F))
        names.push_back(show(F));
    std::sort(names.begin(), names.end());
    names.erase(std::unique(names.begin(), names.end()), names.end());
    return names;
  };

  std::vector<EntryGroup> groups;
  for (const std::string &chop : chops) {
    EntryGroup g;
    g.chop = chop;
    auto named = reachOf(namedSeeds[chop], namedCallers);
    auto may = reachOf(maySeeds[chop], mayCallers);
    g.entries = exports(named);
    std::unordered_set<std::string> have(g.entries.begin(), g.entries.end());
    for (const std::string &n : exports(may))
      if (!have.count(n))
        g.residual.push_back(n);
    groups.push_back(std::move(g));
  }
  return groups;
}

std::string formatEntries(const ChopResult &chop, const std::vector<EntryGroup> &groups) {
  std::ostringstream o;
  o << "sink " << chop.sinkFile << ":" << chop.sinkLine << "\n";
  for (const std::string &f : chop.sinkFns)
    o << "sink-fn " << f << "\n";
  for (const EntryGroup &g : groups) {
    o << "chop " << g.chop << "\n";
    if (g.entries.empty())
      o << "entry (none)\n";
    for (const std::string &e : g.entries)
      o << "entry " << e << "\n";
    for (const std::string &e : g.residual)
      o << "residual " << e << "\n";
  }
  return o.str();
}

} // namespace chain
