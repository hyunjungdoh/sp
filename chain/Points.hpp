#pragma once

// Demand-driven, field-sensitive points-to.
//
// A cell is a pair (object, byte offset). Offsets are an additive monoid:
// a getelementptr by a constant δ sends (a, k) to (a, k+δ). The top element
// Any absorbs every addition and is the result of a non-constant index.
// Two concrete offsets of one object stay two cells.
//
// Memory is a second relation: a store through a pointer whose points-to
// set contains (a, k) adds the stored pointer's cells to mem(a, k). A load
// at a constant offset k reads mem(a, k). A load through Any reads every
// mem cell of that object that exists. A store through Any stays in
// mem(a, Any): it is collected on that cell, and it is not a definition of
// a constant field. A flag or a function pointer kept at a constant offset
// is that field's cell.
//
// Call and return are inclusion edges (context-insensitive). That is a
// sound over-approximation of matched call-strings: every concrete flow
// is kept, and some flows that a Dyck match would separate are merged.
// A call whose callee operand's points-to set contains a function object
// is a caller of that function, and the actuals flow into the formals.
// Indirect calls are matched by points-to, not by function type.
// Every pointer formal of a harness function contains one harness object,
// so a store through one export and a load through another can meet. They
// meet at one byte offset. A cell at offset k is filled when a query reads
// k or a reached store writes k, by a walk of address arithmetic inside
// harness functions. Other offsets of those functions are not solved.
// A byte-range copy forwards mem cells from the source to the destination.
// A fact is not pushed into an undemanded callee.
// Recursive call strings stay finite because each function is one copy.
//
// A points-to fact is pushed into a callee or a call result only when that
// value has been demanded. Pushing every actual into every callee is the
// whole module, and that fixpoint is not a query.
// A query solves only the values and objects reachable from it. Cells no
// query reaches are not materialised.

#include "llvm/ADT/SparseBitVector.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"

#include <cstdint>
#include <deque>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {

class Points {
public:
  enum class Kind { Alloca, Global, Alloc, Func, Outside, Harness };
  struct Obj {
    Kind kind = Kind::Outside;
    const llvm::Value *site = nullptr;
    unsigned ctx = 0;
  };
  static constexpr int64_t Any = INT64_MIN;
  struct Loc {
    unsigned obj = 0;
    int64_t off = 0;
  };
  struct Write {
    const llvm::Instruction *inst = nullptr;
    int64_t off = 0;
    int64_t len = -1;
    unsigned ctx = 0;
  };
  struct PtrLoad {
    const llvm::LoadInst *inst = nullptr;
    int64_t off = 0;
  };
  struct Hooks {
    std::function<std::vector<const llvm::Function *>(const llvm::CallBase *)> callees;
    std::function<const llvm::Function *(const llvm::Function *)> body;
    std::function<bool(const llvm::Function *)> harness;
    std::function<bool(const llvm::CallBase *)> allocates;
    std::function<std::optional<uint64_t>(const llvm::CallBase *)> allocSize;
    std::function<std::optional<std::pair<unsigned, std::optional<unsigned>>>(const llvm::CallBase *)>
        allocSizeArgs;
    std::function<const llvm::Value *(const llvm::CallBase *)> allocSource;
    std::function<bool(const llvm::CallBase *, const llvm::Value *&, const llvm::Value *&)> byteCopy;
  };

  Points(const llvm::Module &M, const llvm::Module &U, Hooks h);

  // Queries solve on demand. saturate does not enter the whole module.
  void saturate();

  const llvm::SparseBitVector<> &of(const llvm::Value *v);
  const llvm::SparseBitVector<> &of(const llvm::Value *v, const llvm::CallBase *site);

  const llvm::CallBase *site(unsigned ctx) const { return ctxs[ctx].site; }
  Loc loc(unsigned id) const { return locs[id]; }
  const Obj &obj(unsigned o) const { return objs[o]; }

  const std::vector<Write> &writes(unsigned o);
  const std::vector<PtrLoad> &ptrLoads(unsigned o);
  const std::vector<const llvm::CallBase *> &escapes(unsigned o);
  std::vector<const llvm::Function *> callees(const llvm::CallBase *C);
  bool unresolved(const llvm::CallBase *C);
  const std::vector<const llvm::CallBase *> &callers(const llvm::Function *F);
  bool perCall(const llvm::Function *F) const { return F && cloned.count(F); }

  struct Def {
    const llvm::Instruction *inst = nullptr;
    unsigned ctx = 0;
    int64_t off = 0;
    int64_t len = -1;
  };
  struct Regions {
    uint64_t epoch = 0;
    std::vector<int64_t> bounds;
    size_t leaves = 1;
    std::vector<std::vector<Def>> tree;
    std::vector<Def> any;
  };
  const Regions &regions(unsigned o);
  static int regionIndex(const Regions &r, int64_t off);
  static void nodeLeaves(const Regions &r, size_t k, size_t &lo, size_t &hi);
  static void leafBytes(const Regions &r, size_t a, size_t b, int64_t &lo, bool &loInf, int64_t &hi,
                        bool &hiInf);

  uint64_t solution() {
    drain();
    return epoch;
  }

private:
  struct Ctx {
    const llvm::CallBase *site = nullptr;
  };
  const llvm::Module &M;
  const llvm::Module &U;
  Hooks hooks;
  const llvm::DataLayout &DL;

  std::vector<Ctx> ctxs;
  std::vector<Obj> objs;
  std::vector<Loc> locs;
  std::unordered_set<const llvm::Function *> cloned;
  uint64_t epoch = 1;

  struct PairHash {
    size_t operator()(const std::pair<unsigned, int64_t> &p) const noexcept {
      size_t h = p.first;
      h ^= static_cast<size_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
    size_t operator()(const std::pair<const void *, int64_t> &p) const noexcept {
      size_t h = reinterpret_cast<uintptr_t>(p.first);
      h ^= static_cast<size_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
    size_t operator()(const std::pair<const void *, unsigned> &p) const noexcept {
      size_t h = reinterpret_cast<uintptr_t>(p.first);
      h ^= static_cast<size_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
    size_t operator()(const std::pair<const void *, const void *> &p) const noexcept {
      size_t h = reinterpret_cast<uintptr_t>(p.first);
      h ^= reinterpret_cast<uintptr_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
  };
  struct WKey {
    unsigned obj;
    int64_t off;
    int64_t len;
    const llvm::Instruction *inst;
    bool operator==(const WKey &o) const {
      return obj == o.obj && off == o.off && len == o.len && inst == o.inst;
    }
  };
  struct WHash {
    size_t operator()(const WKey &k) const noexcept {
      size_t h = k.obj;
      h ^= static_cast<size_t>(k.off) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      h ^= static_cast<size_t>(k.len) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      h ^= reinterpret_cast<uintptr_t>(k.inst);
      return h;
    }
  };

  std::unordered_map<std::pair<const void *, unsigned>, unsigned, PairHash> objOf;
  std::unordered_map<std::pair<unsigned, int64_t>, unsigned, PairHash> locOf;
  // One value holding two concrete offsets of one object is a join (a phi
  // or a gep cycle). The value becomes Any. The cells themselves stay
  // distinct on the values that hold a single offset.
  struct OffState {
    bool any = false;
    bool have = false;
    int64_t one = 0;
  };
  std::unordered_map<const llvm::Value *, std::unordered_map<unsigned, OffState>> offState;
  unsigned outsideObj = 0;
  unsigned harnessObj = 0;
  std::unordered_set<int64_t> filledHarness;
  // A store into the harness cell (object, k) whose value's points-to set
  // grows later. insertPt of that value writes the new cell into mem.
  std::unordered_map<const llvm::Value *, std::vector<int64_t>> harnessStore;

  std::unordered_map<const llvm::Value *, llvm::SparseBitVector<>> pt;
  std::unordered_map<unsigned, std::unordered_map<int64_t, llvm::SparseBitVector<>>> mem;

  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> directCallers;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::ReturnInst *>> returnsOf;
  std::vector<const llvm::CallBase *> indirectCalls;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> indirectBound;
  std::unordered_set<std::pair<const void *, const void *>, PairHash> bound;

  std::unordered_map<const llvm::Value *, std::vector<const llvm::Value *>> copyTo;
  std::deque<std::vector<Write>> writesOf;
  std::deque<std::vector<PtrLoad>> ptrLoadsOf;
  std::deque<std::vector<const llvm::CallBase *>> escapesOf;
  std::unordered_set<WKey, WHash> writeSeen;
  std::unordered_set<std::pair<const void *, const void *>, PairHash> ptrLoadSeen;
  std::unordered_set<std::pair<const void *, const void *>, PairHash> escapeSeen;

  std::map<std::pair<unsigned, int64_t>, std::vector<const llvm::LoadInst *>> readers;
  std::unordered_map<unsigned, std::vector<const llvm::LoadInst *>> anyReaders;
  std::unordered_set<std::pair<const void *, unsigned>, PairHash> readerAnySeen;
  std::set<std::tuple<const llvm::LoadInst *, unsigned, int64_t>> readerSeen;

  std::unordered_set<const llvm::Value *> demanded;
  std::unordered_set<const llvm::Function *> scannedIndirect;
  std::unordered_set<const llvm::GlobalVariable *> seededGlobal;
  std::unordered_set<const llvm::Function *> seededFunc;
  std::unordered_set<const llvm::CallBase *> seededCall;
  std::unordered_set<std::pair<const void *, unsigned>, PairHash> seenProp;

  std::vector<const llvm::Value *> demandQ;
  struct Prop {
    const llvm::Value *v;
    unsigned loc;
  };
  std::vector<Prop> propQ;
  bool draining = false;
  bool changed = false;

  struct OfSlot {
    uint64_t ep = 0;
    llvm::SparseBitVector<> bits;
  };
  std::unordered_map<const llvm::Value *, OfSlot> ofCache;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> callerCache;
  std::unordered_map<const llvm::Function *, uint64_t> callerEpoch;

  std::deque<Regions> regionsOf;

  const llvm::Function *bodyOf(const llvm::Function *F) const;
  const llvm::DataLayout &dlOf(const llvm::Value *v) const;
  bool pointerLike(const llvm::Type *T) const { return T && T->isPointerTy(); }
  void ensureObjSlots(unsigned o);
  unsigned newObj(Kind k, const llvm::Value *site);
  unsigned objectFor(Kind k, const llvm::Value *site);
  unsigned location(unsigned o, int64_t off);
  int64_t gepOff(const llvm::GEPOperator *G) const;
  static int64_t addOff(int64_t k, int64_t d);

  void demand(const llvm::Value *v);
  void install(const llvm::Value *v);
  void insertPt(const llvm::Value *v, unsigned loc);
  void propagate(const llvm::Value *v, unsigned loc);
  void propagateUser(const llvm::Value *v, unsigned loc, const llvm::User *U);
  void bind(const llvm::CallBase *C, const llvm::Function *F);
  void memAdd(unsigned obj, int64_t off, unsigned loc);
  void readMem(const llvm::LoadInst *L, Loc addr);
  void fillHarness(int64_t target);
  void recordWrite(unsigned obj, int64_t off, int64_t len, const llvm::Instruction *I);
  void noteEscape(unsigned obj, const llvm::CallBase *C);
  void notePtrLoad(unsigned obj, int64_t off, const llvm::LoadInst *L);
  void seedGlobal(const llvm::GlobalVariable *G);
  void seedFunc(const llvm::Function *F);
  void fillConst(unsigned obj, int64_t base, const llvm::Constant *C);
  void scanIndirect(const llvm::Function *F);
  void drain();
  std::vector<unsigned> snapshot(const llvm::Value *v) const;
  int64_t copyLen(const llvm::CallBase *C) const;
};

} // namespace chain
