#pragma once

// The downstream context of one sequence is a formula on the export's cells.
//
// A cell is a constant-offset access path from an export argument. The same
// cell has the same root and the same suffix of (struct type, constant
// byte offset). The struct type is the source type of the object (Source.h),
// not the IR struct the linker may have merged it into. A variable index of
// an array held by a constant field is one element cell. A variable field
// of a struct is not a cell.
//
// State 0 leaves every cell unknown. The formula is one memory per sequence
// function. An instruction is on the transition only when every path to the
// next call, or to the sink, executes it. In that order, a constant store
// writes the next value of its cell, a constant-length copy makes the two
// cells the same value, and a branch condition that is the only successor
// reaching the goal constrains the value the cell has at that instruction.
// Equality, disequality, and an ordered comparison with a constant or with
// another cell are that constraint. A conjunction of comparisons is each
// one of them. A disjunction is not a constraint.
// A condition after a copy constrains the cell the bytes were copied from,
// at the entry of the step. A cell the step does not store keeps its value,
// so a condition in a later function is the entry value when no store is
// between them. The chain is every function on the sequence, not only the
// first call. An indirect call's cell is the next function when that call is
// the edge, or one of the functions reached from that call when there are
// several. A cell with no such fact stays unknown. Two constants forced on
// one cell at one state make the sequence unsatisfiable, and the next
// sequence is tried. The harness writes the entry of the residual. The
// residual runs once.
//
// An operand of a required comparison is the load when that load is a cell.
// Otherwise it is the value of the store that dominates the branch, and a
// call that returns one of its arguments is that argument. A call that does
// not reduce this way stays the call: the formula is that its result stands
// in the same relation to the constant. An argument the call can return
// unchanged is its fallback, the value of a missing key. The witness is a
// constant that satisfies every predicate on that call. The fallback is the
// witness when it already satisfies them. A witness the fallback does not
// meet is the input that selects the branch. A call that stores only into
// its own locals is a lookup. The harness returns its integer witness, and
// returns null when a pointer result may be null, when no later call on the
// path reads that object except through a lookup. A later call that is not
// a lookup and receives the same cell, or a cell inside it, reads the bytes
// the witness would have hidden, so the call stays, the harness assumes the
// result, and those bytes stay the entry. A pointer is not that
// integer. Non-null means an object, so the integer 1 is never a pointer
// result. A call that writes an argument, or whose body returns the pointer,
// stays the call, and the harness assumes the comparison. A comparison of a
// pointer is with null. A declaration has no body and cannot allocate. When
// its result must be a non-null pointer, that result is a fresh object whose
// size is the constant-offset extent of the bytes the continuation reads or
// writes through it, including a negative displacement from an interior
// pointer. The returned pointer addresses the zero point of that extent.
// Unnamed bytes of the object are symbolic. A pointer and an integer the
// callee reads as a count are that buffer. The count, when it is a constant,
// is the size. When the count is an entry cell and no constant access gives
// a size, the buffer is 2^16 bytes and the count is that size: a count the
// formula does not pin, inside the bound on an object. An extent of zero names no
// bytes, and an extent above 2^20 bytes is not materialized; the call stays
// and the comparison is assumed. An integer argument may be a size the call
// computes, so a declaration that has one stays as well. A cell used as
// a callee holds one of the functions stored there. When none remains, the
// slot keeps the zero the object was cleared to.
//
// Sequence 0 is the best simple path from an interface function of D to
// the sink: fewer indirect edges, then fewer calls, then earlier call sites
// and demangled names. The interface is the functions a client calls: D's
// exports that an installed header declares. A dynamic symbol outside that
// set is not a start. Without the set, a caller-facing export stands in:
// one that reaches the sink and is not called by another function on those
// paths. Index k is that path in the graph that no longer contains the last
// edge of any earlier path.

#include "Calls.h"
#include "Source.h"
#include "../../engine/klee/include/klee/Support/CallTargets.h"

#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <charconv>
#include <cstdint>
#include <limits>
#include <system_error>
#include <deque>
#include <iterator>
#include <filesystem>
#include <fstream>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <queue>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace llvm;

namespace fs = std::filesystem;

struct Step {
  std::string type;
  int64_t off = 0;
  // True when this field is inside the object a pointer load produced.
  // The bytes live in that object. The pointer itself sits at the previous step.
  bool deref = false;
  bool operator==(const Step &o) const { return type == o.type && off == o.off && deref == o.deref; }
  bool operator<(const Step &o) const {
    if (type != o.type)
      return type < o.type;
    if (off != o.off)
      return off < o.off;
    return deref < o.deref;
  }
};

using Suffix = std::vector<Step>;

// A constant GEP moves the address by a byte offset, and that offset is the
// step whatever type the GEP indexes. A named struct source records the
// source type of the struct alongside it; any other source records none. An untyped GEP
// of offset zero does not move the address, so it adds no step.
inline bool constStep(const DataLayout &dl, GEPOperator *G, Step &st) {
  if (!G->hasAllConstantIndices())
    return false;
  APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
  if (!G->accumulateConstantOffset(dl, off))
    return false;
  st = Step{};
  st.off = off.getSExtValue();
  st.type = source::container(G, dl);
  return true;
}

inline bool movesAddress(const Step &st) { return !st.type.empty() || st.off != 0; }

// The local a pointer addresses and its constant byte offset into it.
inline const AllocaInst *localBase(const DataLayout &dl, Value *V, int64_t &off) {
  APInt d(64, 0);
  Value *B = V->stripAndAccumulateConstantOffsets(dl, d, true);
  auto *A = dyn_cast<AllocaInst>(B);
  if (!A)
    return nullptr;
  off = d.getSExtValue();
  return A;
}

inline std::optional<int64_t> asI64(const std::string &s) {
  if (s.empty())
    return std::nullopt;
  int64_t v = 0;
  const char *b = s.data();
  auto r = std::from_chars(b, b + s.size(), v);
  if (r.ec != std::errc() || r.ptr != b + s.size())
    return std::nullopt;
  return v;
}

inline std::optional<uint64_t> asU64(const std::string &s) {
  if (s.empty() || s[0] == '-')
    return std::nullopt;
  uint64_t v = 0;
  const char *b = s.data();
  auto r = std::from_chars(b, b + s.size(), v);
  if (r.ec != std::errc() || r.ptr != b + s.size())
    return std::nullopt;
  return v;
}

inline const char *icmpName(unsigned p) {
  switch (p) {
  case ICmpInst::ICMP_EQ:
    return "==";
  case ICmpInst::ICMP_NE:
    return "!=";
  case ICmpInst::ICMP_UGT:
    return "ugt";
  case ICmpInst::ICMP_UGE:
    return "uge";
  case ICmpInst::ICMP_ULT:
    return "ult";
  case ICmpInst::ICMP_ULE:
    return "ule";
  case ICmpInst::ICMP_SGT:
    return "sgt";
  case ICmpInst::ICMP_SGE:
    return "sge";
  case ICmpInst::ICMP_SLT:
    return "slt";
  case ICmpInst::ICMP_SLE:
    return "sle";
  default:
    return "?";
  }
}

// One cell at one state. known is one constant. any is a disjunction the
// slice named. ban is a constant the unique successor excluded. The ordered
// bounds are inclusive limits a unique successor comparison named.
struct SlotVal {
  bool known = false;
  std::string val;
  std::set<std::string> any;
  std::set<std::string> ban;
  bool slo = false, shi = false, ulo = false, uhi = false;
  int64_t sloV = 0, shiV = 0;
  uint64_t uloV = 0, uhiV = 0;
  unsigned ordBytes = 0;
  // §3.8 비트 원자: 1이어야 하는 비트(oneBits)와 0이어야 하는 비트(zeroBits).
  uint64_t oneBits = 0, zeroBits = 0;
};

struct Transition {
  bool conflict = false;

  void pin(SlotVal &s, const std::string &v) {
    if (s.known && s.val != v)
      conflict = true;
    if (s.ban.count(v))
      conflict = true;
    if (!s.any.empty() && !s.any.count(v))
      conflict = true;
    s.known = true;
    s.val = v;
    s.any.clear();
  }

  void allow(SlotVal &s, const std::set<std::string> &vs) {
    if (vs.empty())
      return;
    if (vs.size() == 1) {
      pin(s, *vs.begin());
      return;
    }
    if (s.known) {
      if (!vs.count(s.val))
        conflict = true;
      return;
    }
    if (s.any.empty())
      s.any = vs;
    else {
      std::set<std::string> both;
      std::set_intersection(s.any.begin(), s.any.end(), vs.begin(), vs.end(), std::inserter(both, both.end()));
      if (both.empty())
        conflict = true;
      s.any.swap(both);
    }
    for (const std::string &b : s.ban)
      s.any.erase(b);
    if (!s.ban.empty() && s.any.empty())
      conflict = true;
  }

  void forbid(SlotVal &s, const std::set<std::string> &vs) {
    s.ban.insert(vs.begin(), vs.end());
    if (s.known && s.ban.count(s.val))
      conflict = true;
    if (!s.any.empty()) {
      for (const std::string &b : vs)
        s.any.erase(b);
      if (s.any.empty())
        conflict = true;
    }
  }
};

// A value in terms of the entry arguments. addr(arg, []) is the argument
// itself; addr(s . st) is addr(s) + st.off, or *addr(s) + st.off when st
// is a dereference. The value is addr(arg, suf), or *addr(arg, suf) when
// pointee is set.
struct Loc {
  int arg = -1;
  Suffix suf;
  bool pointee = false;
  bool operator==(const Loc &o) const {
    return arg == o.arg && suf == o.suf && pointee == o.pointee;
  }
};

inline std::string pretty(StringRef name) {
  std::string d = demangle(name.str());
  return d.empty() ? name.str() : d;
}

inline bool sinkHere(const Instruction &I, StringRef file, unsigned line) {
  const DebugLoc &dl = I.getDebugLoc();
  if (!dl)
    return false;
  if (dl.getLine() != line)
    return false;
  StringRef fn = dl->getFilename();
  return fn == file || fn.ends_with(file) || fn.ends_with(("/" + file).str());
}

// A copy of a fixed number of bytes. The destination is argument 0.
struct Copy {
  unsigned dst = 0;
  unsigned src = 1;
  uint64_t len = 0;
  bool ok = false;
};

inline Copy fixedCopy(const CallBase &CB) {
  Copy c;
  if (CB.arg_size() < 3)
    return c;
  if (!CB.getArgOperand(0)->getType()->isPointerTy() || !CB.getArgOperand(1)->getType()->isPointerTy())
    return c;
  auto *N = dyn_cast<ConstantInt>(CB.getArgOperand(2));
  // A byte count is a magnitude. A negative constant is not one.
  if (!N || N->isNegative())
    return c;
  for (unsigned i = 3; i < CB.arg_size(); ++i) {
    Type *T = CB.getArgOperand(i)->getType();
    if (!T->isIntegerTy())
      return c;
  }
  c.len = N->getZExtValue();
  c.ok = true;
  return c;
}

// A read with no body. The buffer is the first pointer the call may write.
// The count sits immediately after it.
struct Read {
  unsigned buf = 0;
  unsigned count = 0;
  int file = -1;
  int handle = -1;
  std::optional<uint64_t> len;
  bool ok = false;
};

inline Read asRead(const CallBase &CB) {
  Read r;
  if (!CB.getType()->isIntegerTy())
    return r;
  // memory(argmem: read) reads every pointer. A readonly argument is not
  // the buffer. The buffer is the writable pointer the count follows.
  if (CB.onlyReadsMemory())
    return r;
  int buf = -1;
  for (unsigned i = 0; i + 1 < CB.arg_size(); ++i) {
    if (!CB.getArgOperand(i)->getType()->isPointerTy())
      continue;
    if (CB.onlyReadsMemory(i))
      continue;
    if (!CB.getArgOperand(i + 1)->getType()->isIntegerTy())
      continue;
    buf = (int)i;
    break;
  }
  if (buf < 0)
    return r;
  int count = -1;
  unsigned nConst = 0;
  uint64_t prod = 1;
  bool allConst = true;
  int file = -1;
  for (unsigned i = (unsigned)buf + 1; i < CB.arg_size(); ++i) {
    Value *Op = CB.getArgOperand(i);
    if (Op->getType()->isPointerTy()) {
      file = (int)i;
      break;
    }
    if (!Op->getType()->isIntegerTy())
      break;
    if (count < 0)
      count = (int)i;
    if (auto *C = dyn_cast<ConstantInt>(Op)) {
      if (C->isNegative()) {
        allConst = false;
        ++nConst;
        continue;
      }
      uint64_t v = C->getZExtValue();
      if (nConst < 2 && v != 0 && prod > ~uint64_t{0} / v)
        allConst = false;
      else if (nConst < 2)
        prod *= v;
      ++nConst;
    } else
      allConst = false;
  }
  if (count < 0)
    return r;
  // No pointer follows: the first integer is the count. A later integer is
  // flags, not another factor. A pointer follows: the two integers are the
  // factors of the count.
  if (file < 0) {
    allConst = false;
    nConst = 0;
    if (auto *C = dyn_cast<ConstantInt>(CB.getArgOperand((unsigned)count))) {
      if (!C->isNegative()) {
        allConst = true;
        nConst = 1;
        prod = C->getZExtValue();
      }
    }
  }
  if (file < 0 && buf > 0 && CB.getArgOperand((unsigned)buf - 1)->getType()->isPointerTy())
    file = buf - 1;
  int handle = -1;
  for (int i = buf - 1; i >= 0; --i)
    if (CB.getArgOperand((unsigned)i)->getType()->isIntegerTy()) {
      handle = i;
      break;
    }
  r.buf = (unsigned)buf;
  r.count = (unsigned)count;
  r.file = file;
  r.handle = handle;
  if (allConst && nConst >= 1 && nConst <= 2)
    r.len = prod;
  r.ok = true;
  return r;
}

inline bool ignorable(const Function *F) {
  if (!F)
    return false;
  return F->isIntrinsic() || F->getName().starts_with("llvm.dbg.") || F->getName().starts_with("llvm.lifetime.");
}

class Model {
 public:
  // D's interface I: exports an installed header declares. Midpoint tests
  // and the call graph use I; starts use startNames (I★) when set.
  std::set<std::string> interfaceNames;
  // P1 starts B_entry ⊆ I★: entryCallable public functions only.
  std::set<std::string> startNames;
  // P1: after φ SAT, reject paths whose indirect edges are still open under
  // Definition D; those hops are banned and the search continues.
  std::function<std::vector<std::pair<std::string, std::string>>(const std::vector<Function *> &)>
      openDispatch;
  Model(Module &down, Module &up, StringRef file, unsigned line) : down(down), up(up), dl(down.getDataLayout()), sinkFile(file), sinkLine(line) {}

  void run(int seqPick, raw_ostream &out);
  // The index run builds before its search, and the precise resolution of
  // local-held pointers the search uses; enough for indirectTargets.
  void index();
  void resolvePrecisely() { resolveHeld = true; }
  // §3.10: targetsOf at every indirect call site of D and U, after run.
  calls::Table indirectTargets() const;


 private:
  Module &down;
  Module &up;
  const DataLayout &dl;
  StringRef sinkFile;
  unsigned sinkLine;
  std::vector<Function *> sinks;
  std::map<Suffix, std::vector<Suffix>> besidePtr;
  std::map<Suffix, std::vector<Function *>> builderOf;
  std::map<Function *, std::vector<std::pair<unsigned, Suffix>>> argStored;
  // An initializer of a struct: a function that stores a constant function
  // into field (type, offset) of the object its formal points to. Running it
  // on an object sets that field together with every field it stores beside.
  struct InitSite {
    Function *fn = nullptr;
    unsigned arg = 0;
    Function *stored = nullptr;
  };
  std::map<std::pair<std::string, int64_t>, std::vector<InitSite>> initSites;
  // The maximal initializers of a struct for a set of its function cells:
  // sites that are not methods of those cells (the functions they hold and
  // the helpers only those call), lifted to callers that pass their own
  // object and scalars, without those whose every caller is an initializer.
  std::vector<InitSite> initializers(const std::string &type, const std::set<int64_t> &cells) const;
  mutable std::map<std::pair<std::string, std::set<int64_t>>, std::vector<InitSite>> initMemo;
  // The reaching-definition resolution of a pointer a local holds (slotHeld)
  // is a property the harness needs at sequence-solving time, not in the
  // eager index passes that only map operands to formals. It is off during
  // indexing and on once solving begins, so a large module is indexed by the
  // cheap reload path and resolved precisely only on the sequence cone.
  mutable bool resolveHeld = false;
  struct VTab {
    GlobalVariable *g = nullptr;
    uint64_t base = 0;
    int64_t field = 0;
    // The function that stores the table, and the largest object it lays
    // out through its receiver.
    Function *by = nullptr;
    uint64_t extent = 0;
    // Some construction ends with this table in the field: a caller of the
    // storing function stores no table into that field afterwards.
    bool last = true;
  };
  mutable std::map<std::string, std::vector<VTab>> vtOf;
  mutable std::vector<VTab> vtAll;
  mutable bool vtReady = false;
  mutable std::map<std::string, uint64_t> typeSize;
  mutable std::unordered_map<const CallBase *, std::vector<Function *>> vtableCache;
  mutable std::unordered_map<const Function *, std::unordered_set<const Function *>> reachFrom;
  mutable std::map<std::pair<const Function *, Suffix>, std::set<std::string>> besideCache;
  mutable std::unordered_map<const CallBase *, std::vector<Function *>> readCache;
  mutable std::unordered_map<const Function *, bool> readBody;
  mutable std::unordered_map<const Function *, Suffix> retCache;
  mutable std::unordered_map<const Function *, int> carryCache;
  // Where a function's pointer arguments go, independent of any export.
  // ret is the address the function returns. A put stores a pointer into
  // an object the function was given; srcLoad means the stored pointer is
  // the one loaded from that source address.
  struct ArgRef {
    const Value *root = nullptr;
    int arg = -1;
    Suffix suf;
    int64_t bytes = 0;
    bool ok = false;
  };
  struct PtrPut {
    const Value *dstRoot = nullptr;
    int dstArg = -1;
    Suffix dstSuf;
    int64_t dstBytes = 0;
    int srcArg = -1;
    Suffix srcSuf;
    int64_t srcBytes = 0;
    bool srcLoad = false;
    // Set when the stored pointer is a cast result: the vptr the witness
    // dynamic type requires, and the IR type it names.
    std::string vtable;
    uint64_t vbyte = 0;
    std::string vtype;
  };
  struct FnMove {
    bool retOk = false;
    ArgRef ret;
    std::vector<PtrPut> puts;
    // One edge per call that passes an address. The callee's transfers are
    // applied from this edge when a field is queried, not copied in here.
    struct Edge {
      Function *callee = nullptr;
      std::vector<const Value *> op;
      std::vector<ArgRef> actual;
    };
    std::vector<Edge> edges;
  };
  // A map, not a hash map: a reference to one summary stays valid while
  // another function's summary is inserted.
  mutable std::map<const Function *, FnMove> moveCache;
  mutable std::unordered_set<const Function *> moveStack;
  // putsAt is the least fixed point of the direct transfers. The key is the
  // field written: a root address when the root is set, otherwise formal arg
  // at that byte. The map is the only store of a composed transfer, and only
  // a field that is queried is entered. A key already on the stack has no
  // name.
  mutable std::map<std::tuple<const Function *, const Value *, int, int64_t>, std::vector<PtrPut>> putMemo;
  mutable std::set<std::tuple<const Function *, const Value *, int, int64_t>> putStack;
  mutable std::unordered_map<std::string, std::optional<Loc>> valueCache;
  mutable std::unordered_set<std::string> valueStack;
  struct Solved {
    int arg = -1;
    Suffix suf;
    std::set<std::string> vals;
    std::set<std::string> ban;
    bool slo = false, shi = false, ulo = false, uhi = false;
    int64_t sloV = 0, shiV = 0;
    uint64_t uloV = 0, uhiV = 0;
    unsigned ordBytes = 0;
    std::set<std::string> text;
    unsigned width = 8;
    bool file = false;
    bool pathPtr = false;
    // The load of this cell is a callee. It is not a symbolic address.
    bool code = false;
    FunctionType *fty = nullptr;
    std::optional<uint64_t> len;
    // The constant address a constructor stored into this slot.
    std::string glob;
    uint64_t gbyte = 0;
  };
  // One argument of the call that enters the residual. A located argument is
  // a cell of the export object. address is the pointer to that cell; a
  // loaded pointer passes the value stored there. Anything an equation does
  // not name stays missing and is symbolic.
  struct Act {
    std::optional<Loc> loc;
    bool address = true;
    bool nullPtr = false;
    bool haveInt = false;
    int64_t ival = 0;
    unsigned ibits = 0;
    std::string fn;
    bool missing = true;
  };
  std::map<Function *, std::set<std::string>> regKeys;
  std::unordered_map<const Function *, std::map<unsigned, int64_t>> keyArgCache;
  std::vector<Function *> exports;
  Function *entry = nullptr;
  std::vector<Solved> solvedCells;
  // A comparison of two entry cells that neither side has pinned.
  struct Rel {
    unsigned pred = 0;
    int a = -1;
    Suffix asuf;
    int b = -1;
    Suffix bsuf;
    unsigned bytes = 8;
  };
  std::vector<Rel> rels;
  // A no-body call that produces the file handle, or the read that fills a
  // buffer from it. The harness defines that call: the path "f" yields a
  // handle, and the read symbolizes the buffer for the count it is given.
  struct FileIO {
    std::string name;
    bool opener = false;
    bool retPtr = false;
    int pathArg = 0;
    int bufArg = -1;
    int countArg = -1;
    int count2 = -1;
  };
  std::vector<FileIO> fileIO;
  std::vector<Act> callActs;
  std::map<int, uint64_t> argExtent;
  // The path cell is assigned from this export argument before the sink
  // reads it. The harness writes the path into that argument. fieldType is
  // the struct that was assigned, so its pointer and the integer after it
  // receive the path and that text's length.
  struct PathSrc {
    int arg = -1;
    std::string fieldType;
  };
  std::vector<PathSrc> pathSrc;
  // The sequence subtracts these two pointer slots. They bound one byte region.
  struct PtrSpan {
    int arg = -1;
    Suffix begin;
    Suffix end;
  };
  std::vector<PtrSpan> ptrSpan;
  std::map<std::pair<int, Suffix>, uint64_t> readBytes;
  // A count an upstream call reads that many bytes by: the entry cell that
  // holds it, the most the materialized buffer admits, and its width.
  struct CountCap {
    uint64_t most = 0;
    unsigned bytes = 8;
  };
  std::map<std::pair<int, Suffix>, CountCap> countCap;
  std::map<std::pair<int, Suffix>, uint64_t> fileLen;
  std::map<int, uint64_t> argFileLen;
  std::vector<Function *> starts;
  std::unordered_set<Function *> cone;
  // Indirect hops rejected by openDispatch during this run; sequences() skips them.
  std::set<std::pair<std::string, std::string>> hopBan;
  std::unordered_map<Function *, std::vector<Function *>> callersOf;
  std::map<Suffix, std::set<std::string>> facts;
  std::unordered_map<std::string, std::vector<StructType *>> namedByShape;
  std::unordered_map<const Type *, std::string> shapeMemo;
  mutable std::unordered_map<std::string, std::vector<std::string>> accessNames;
  bool shapesReady = false;
  mutable bool accessReady = false;

  Function *define(StringRef name) const;

  // The callee reads up to n bytes through p: some access to the object p
  // points into is bounded by a value that depends on n. Dependence follows
  // SSA and local reloads context-sensitively, and memory only as a field
  // pair: p and n stored to two fields of one object, read back together.
  bool pairRead(Function *D, unsigned p, unsigned n) const;
  struct FlowIndex;
  mutable std::shared_ptr<FlowIndex> flowIdx;
  mutable std::map<std::tuple<const Function *, unsigned, unsigned>, bool> pairMemo;


  // A call whose callee is not a function in the module. Its body is not
  // available, so the call itself is the equation.
  bool noBody(CallBase *CB);


  template <typename Fn>
  void eachBody(Fn &&fn) const {
    for (Module *M : {&down, &up})
      for (Function &F : *M)
        if (!F.isDeclaration())
          fn(F);
  }

  std::vector<Function *> findSinks();


  Suffix suffix(Value *V) const;




  static std::string dec(const ConstantInt *CI);


  void noteScalar(const Suffix &suf, const std::string &v);


  std::string shape(Type *T);


  void ensureShapes();


  // A literal struct in an initializer is the named struct with the same
  // field layout. The load names that struct; the initializer often does not.
  std::vector<StructType *> namesFor(StructType *ST);


  void noteZero(Type *Ty, const Suffix &suf);


  // smash: the elements of an array are one element (the resolution's cells).
  void eachLeaf(Constant *C, Type *Ty, const Suffix &suf, const DIType *D,
                const std::function<void(Constant *, const Suffix &)> &leaf, bool smash = false);
  void walkInit(Constant *C, Type *Ty, const Suffix &suf, bool scalars, const DIType *D = nullptr);


  static bool typeNameMatches(StringRef llvmName, StringRef access);


  // A store through a byte offset keeps the struct and offset in its access
  // tag. That is the same cell as a field load of that struct at that offset.
  void ensureAccess() const;


  Suffix suffixFromAccess(const StoreInst *S) const;


  void indexFunctions();


  // The bytes of a constant string argument.
  static std::string cstring(Value *V);


  // Byte offset from the returned object at which the callee stores each argument.
  std::map<unsigned, int64_t> argOffsets(Function *F);


  // A field is a key when a call loads it and passes that value together with
  // the object. The byte offsets of those fields, per struct.
  std::map<std::string, std::set<int64_t>> keyFields();


  static std::string bareType(StringRef n);


  // A call returns an object, and a later store writes a function into that
  // object. The constant strings stored at the object's key field select it.
  void indexKeys();


  static void addUnique(std::vector<Function *> &v, Function *F);


  // An indirect call of a formal argument calls the functions its callers pass.
  void indexArgFns();


  Suffix returnsOf(const Function *F) const;


  // The function a global initializer places at a byte offset.
  Function *functionAt(Constant *C, uint64_t base, uint64_t want) const;


  // A constructor stores a vtable into the object it builds. The named struct
  // it writes through is the type a later virtual call sees.
  void indexVtables() const;


  struct VSlot {
    bool ok = false;
    Value *obj = nullptr;
    int64_t field = 0;
    uint64_t slot = 0;
  };

  VSlot vslot(CallBase *CB) const;


  std::vector<Function *> fromVtabs(const std::vector<VTab> &tabs, int64_t field, uint64_t slot) const;


  bool containsRead(Function *F) const;


  // Functions reached from From by direct and indirect calls, including From.
  bool reachesFn(Function *From, Function *To) const;


  // Functions stored at this cell by a function that also stores Next.
  // The two stores are one fact: the initializer that installs the next call.
  std::set<std::string> storedBeside(const Suffix &cell, Function *Next) const;


  // An indirect call through a constant slot of a vtable. The vtable is the
  // constant stored into the object by the function that built it.
  std::vector<Function *> vtableTargets(CallBase *CB) const;


  // The argument's dereferenceable size, through one local the function
  // reloads it from.
  uint64_t objectBytes(Value *O, Function *F) const;


  uint64_t typeBytes(const std::string &name) const;


  // The object's static type is not in the caller. Every vtable slot that
  // itself reads is a possible body of this call.
  std::vector<Function *> vtableReads(CallBase *CB) const;


  // The callee of a direct call, or Res(c) of an indirect call (§3.10).
  std::vector<Function *> targetsOf(CallBase *CB) const;

  // §3.5 정의 R: whether a call can return, the least fixpoint flowReach
  // uses, and the blocks of F on a path from entry to a return.
  bool callReturns(CallBase *CB) const;
  std::unordered_set<const BasicBlock *> returnBlocks(Function *F) const;
  mutable std::unordered_set<const Function *> returning;
  mutable bool returningBuilt = false;

  // §3.10 Res: the least solution of the function-constant flow over the
  // bodies of D and U, read by targetsOf at every indirect call.
  void buildResolve();
  std::unordered_map<const CallBase *, std::vector<Function *>> resolved;
  // The same solution at a formal and at a struct field (type, offset).
  std::unordered_map<const Argument *, std::vector<Function *>> formalFns;
  std::map<std::pair<std::string, int64_t>, std::vector<Function *>> fieldFns;
  const std::vector<Function *> &fnsOf(const Argument *A) const;

  static bool exported(const Function &F);


  // An export is a defined library function a caller outside the library can
  // name. The sink's own module is the callee of that library.
  std::vector<Function *> findExports();


  void buildCallers();


  std::unordered_set<Function *> reachSink();


  std::vector<Function *> findStarts();


  struct Path {
    std::vector<Function *> fn;
    int indirect = 0;
  };

  std::vector<Path> sequences(int seqPick);


  // A constant-offset field of a local object passed by address into a
  // callee: the export Loc stored there, and how many loads of that field
  // recover it (0 = the field holds the Loc; 1 = it holds the address of a
  // local slot that holds the Loc). §3.1 maps callee accesses through such
  // packs back to cells of f_0.
  struct PackField {
    Loc val;
    int loads = 0;
    bool operator==(const PackField &o) const { return val == o.val && loads == o.loads; }
  };

  struct Mem {
    std::unordered_map<const Value *, Loc> loc;
    // Formal that addresses a packed local: byte offset → field.
    std::unordered_map<const Argument *, std::map<int64_t, PackField>> pack;
    // The value each store into a local wrote.
    std::unordered_map<const StoreInst *, Loc> stored;
    // slotHeld under these facts. A value stays one as facts grow; an
    // unknown one holds only for the fact count it was found under. The
    // witness is the vptr the reaching definition's cast requires.
    // Keyed by the read the value is asked at: two reads of one local can see
    // different definitions.
    struct Held {
      std::optional<Loc> loc;
      size_t facts = 0;
      std::string vtable;
      uint64_t vbyte = 0;
      std::string vtype;
    };
    std::map<std::tuple<const AllocaInst *, int64_t, const Instruction *>, Held> held;
    // The definitions of a local's field, found once per fact count and
    // shared by every read of that field. No value: one that cannot be named.
    struct SlotDef {
      const Instruction *at = nullptr;
      std::optional<Loc> val;
      std::string vtable;
      uint64_t vbyte = 0;
      std::string vtype;
    };
    struct SlotDefs {
      bool done = false;
      size_t facts = 0;
      bool lost = false;
      std::vector<SlotDef> defs;
    };
    std::map<std::pair<const AllocaInst *, int64_t>, SlotDefs> defs;
    // The vptr pins locating each value produced.
    std::unordered_map<const Value *, std::set<std::string>> pins;
    size_t facts() const { return loc.size() + stored.size(); }
  };

  // The stores into a local whose value a load of it may read: the last
  // store on each path to the load. None when a call or an escaped address
  // may write the local in between.
  const std::vector<const StoreInst *> *reaching(const LoadInst *L) const;
  mutable std::unordered_map<const LoadInst *, std::optional<std::vector<const StoreInst *>>> reachMemo;

  // A reload of a local is the value every reaching store wrote.
  bool reloadLoc(const Mem &m, const LoadInst *L, Loc &out) const;

  // A getter returns a pointer loaded from a constant-offset field of one of
  // its formals: on every return the value is load(formal[arg] + suf). The
  // suffix composes through nested getters. None when the returns disagree or
  // a return is not such a load.
  // __dynamic_cast's exact-type fast path (libc++abi dyn_cast_get_derived_info
  // and dyn_cast_to_derived), evaluated on the vtable constants: the word
  // before the vptr is the offset to the complete object and the word before
  // that is its typeinfo. The witness dynamic type is the destination type,
  // so the cast returns its source pointer plus that offset precisely when
  // the offset equals the negated hint, and the object's vptr is that table.
  struct DynWitness {
    int64_t delta = 0;
    std::string vtable;
    uint64_t vptr = 0;
    std::string type;
  };
  std::optional<DynWitness> dynWitness(const CallBase *CB) const;
  struct VptrPin {
    int arg = -1;
    Suffix suf;
    std::string g;
    uint64_t byte = 0;
  };
  mutable std::map<std::string, VptrPin> vptrPins;
  mutable std::set<std::string> vptrBad;
  void pinVptr(const Loc &obj, const DynWitness &w) const;
  // A pin is a constraint of the witness only when the cast's result is an
  // actual of a sequence edge: the next function then runs on that object.
  // lastPins collects the pins one location query produced, pinsOf keeps them
  // per located value in each memory, and framePins the ones a frame used.
  mutable std::vector<std::string> lastPins;
  mutable std::set<std::string> framePins;
  void notePins(Mem &m, const Value *V) const;
  // V equals the pointer loaded from addr: a zero-adjusting cast of a getter.
  // wit, when passed, receives the first such cast's witness.
  bool castAddr(Function *F, Value *V, ArgRef &addr, DynWitness *wit = nullptr) const;
  mutable std::map<const GlobalVariable *, std::vector<DynWitness>> vtFor;
  mutable bool vtForReady = false;

  std::optional<std::pair<int, Suffix>> loadRet(Function *F) const;
  mutable std::unordered_map<const Function *, std::optional<std::pair<int, Suffix>>> loadRetCache;
  mutable std::unordered_set<const Function *> loadRetStack;

  // Whether D may write bytes [off, off + w) of the object its formal k
  // addresses: a store or a constant copy at a constant offset of that
  // formal that overlaps them, the same of a callee that receives the formal
  // moved by a constant offset, or any write whose address derives from the
  // formal by a variable offset or through a function with no body. A store
  // of a null pointer is not a write, as for reloads of locals. A function
  // already on the stack may write.
  enum class May { No, Yes, Unknown };
  May writesAt(Function *D, int k, int64_t off, uint64_t w) const;
  mutable std::map<std::tuple<const Function *, int, int64_t, uint64_t>, May> writesMemo;
  mutable std::set<std::tuple<const Function *, int, int64_t, uint64_t>> writesStack;

  // The pointer a local holds at byte off, at instruction `at`. Its names are
  // the alloca, its casts, and its constant-offset GEPs; a name kept anywhere
  // else escapes. A definition of [off, off + 8) is a store through a name, or
  // a call that receives a name and whose fnMove puts that field, the value
  // then being the call's source argument at the caller. A call that may write
  // the field without such a put, or a partial overlap, is a definition with
  // no name. A definition reaches `at` when some path from it to `at` crosses
  // no other definition of the field, so a destructor that runs after the read
  // does not count. The value is the one every reaching definition agrees on.
  // No program point (`at` null) takes every definition in the function.
  bool slotHeld(Mem &m, const AllocaInst *A, int64_t off, const Instruction *at, Loc &out) const;
  bool slotHeldOnce(Mem &m, const AllocaInst *A, int64_t off, const Instruction *at, Loc &out, DynWitness &cast) const;
  mutable std::set<std::pair<const AllocaInst *, int64_t>> slotStack;

  // The entry cell at the address a value denotes.
  static bool cellAt(Loc v, Loc &cell);

  static Value *rootOf(Value *V);


  // The pointer a function returns carries a formal when the return is that
  // formal, or the returned object is filled by constant-offset copies from it.
  std::optional<int> carryArg(Function *F) const;


  // The argument is the export object, or a constant-offset field of it.
  // A pointer loaded from that object is a different object.
  bool objectLoc(Mem &m, Value *V, Loc &out) const;


  // Bytes reached from Root by a constant offset. The end is the furthest
  // typed load or store, or the furthest constant-length copy, of that
  // pointer. A callee that receives the pointer contributes the same
  // accesses. A function already on the stack is a cycle. A variable index
  // covers one element. No other length is chosen.
  uint64_t pointedExtent(Function *F, Value *Root, std::unordered_set<const Function *> &stack, int depth) const;


  // The export path of an address. A loaded pointer keeps the field it was
  // loaded from and later steps append. A variable array index stays on
  // that array. A variable struct field is not a cell.
  bool cellLoc(Mem &m, Value *V, Loc &out) const;


  bool locOf(Mem &m, Value *V, Loc &out) const;

  // Load of a packed formal field: loads==0 yields the Loc; loads==1 yields
  // it after one further load of that result. The pack object may be the
  // formal itself or a local reload of it.
  bool packLoad(Mem &m, const LoadInst *L, Loc &out) const;
  const Argument *packObject(Mem &m, const Value *V, int64_t &off) const;

  static bool sameSteps(const Suffix &a, const Suffix &b);


  // The one pointer stored into this alloca, ignoring a null that a later
  // store replaces. Two different stores do not agree, so there is no value.
  Value *storedOnce(const AllocaInst *A) const;


  // The address V names: an argument or an alloca, plus the constant fields
  // walked to reach it. A load of an alloca forwards the address that was
  // saved there. A load of anything else is a pointer value, not an address.
  // A call forwards the address its summary says it returns.
  ArgRef addrIn(Function *F, Value *V) const;


  // Direct transfers of F: a store, a fixed-size copy, or a cast result in F's
  // own body. A callee is not copied into this summary.
  const FnMove &fnMove(Function *F) const;

  // The transfers that write one field of F, each source expressed as a
  // formal of F. Direct puts of F are included. A put of a callee is included
  // after the callee's source formal is replaced by the actual at the call.
  // root set selects the address root; root null selects formal arg. A key
  // re-entered while it is being solved names nothing.
  const std::vector<PtrPut> &putsAt(Function *F, const Value *root, int arg, int64_t bytes) const;


  // The export object a pointer value names. An argument is the formal the
  // caller bound. A field address extends that formal. A load is the pointer
  // a put stored at that address. Two puts that name different objects do
  // not agree, so the load has no location.
  std::optional<Loc> valueAt(Function *F, Value *V, const Mem &m) const;


  void bindFormals(Mem &m, Function *F, const std::vector<std::optional<Loc>> &args) const;

  // Bind packed locals on formals: callee field loads resolve through pack.
  void bindPacks(Mem &m, Function *F, const std::vector<std::map<int64_t, PackField>> &packs) const;

  // Constant-offset stores into local A that name export Locs (directly or
  // as the address of a slot that holds one). Empty when A is not such a pack.
  std::map<int64_t, PackField> packOf(Mem &m, const AllocaInst *A) const;

  // Same as propagate, except a value returned by a call is a new object.
  void propagateObject(Mem &m, Function *F) const;


  void propagate(Mem &m, Function *F) const;


  bool fromFormal(Function *F, Value *V, std::unordered_map<Function *, bool> &pureCache, std::unordered_set<Function *> &stack, int &arg, Suffix &suf) const;


  // A function folds when every store into the export object is a constant
  // offset and every callee that receives the object is the same kind of
  // bundle. A call that does not receive the object is outside the memory.
  // edgeNext is the sequence successor: that call is the boundary, not a
  // callee to fold.
  bool summarizes(Function *F, const std::vector<std::optional<Loc>> &args, std::unordered_map<std::string, bool> &cache,
                  std::unordered_set<std::string> &stack, Function *edgeNext);


  // Blocks that reach the next sequence call or the sink. A callee is on
  // the slice where its blocks reach a return. A function that is not on
  // the sequence and has no return contributes no block.
  std::unordered_set<const BasicBlock *> sliceReach(Function *F, const std::vector<Function *> &seq) const;

  // One simple path from the entry to a goal instruction, inside the blocks
  // that can reach a goal. At a branch every successor that reaches a goal
  // is eligible; the shortest such path is chosen, with the earlier block
  // name breaking ties. The witness formula is the condition of this path.
  std::unordered_set<const BasicBlock *> chosenPath(Function *F, const std::unordered_set<Instruction *> &goals) const;

  // §3.8 정의 3.8.2–3.8.3: 분기 조건 Cond가 이 간선(onTrue)에서 한 비트 β+(c,b)를
  // 요구하고, 그 비트의 확립자 Est(f,b)가 정의된 함수 하나뿐이면 그 함수다.
  Function *memoEstablisher(Value *Cond, bool onTrue) const;
  mutable std::map<std::tuple<std::string, int64_t, uint64_t>, Function *> estCache;


  bool solve(const std::vector<Function *> &seq, raw_ostream &out);


  // Cells at the sequence entry whose bytes the sink's address, its length,
  // or a comparison that reaches the sink still read. The load's value is the
  // last store on every path that reaches it, including a store that does not
  // dominate and a store or a load in a callee that receives the object.
  // A store of a pointer makes the load that pointer. An allocation is an object created on the
  // path; the bytes written into it are followed. A call is that return.
  // An entry cell that no such store covers is an input.
  void inputs(const std::vector<Function *> &seq, raw_ostream &out);


 public:
  Function *exportFn() const;


  StructType *structNamed(StringRef n) const;


  // The field of this struct at this byte offset is a pointer the program loads.
  bool fieldIsPointer(StringRef type, int64_t off) const;

  // The store size of the scalar that begins off bytes into an object of
  // the named type, through nested structs and arrays. 0 when off is not
  // the start of a scalar or the type has no layout.
  uint64_t scalarWidth(StringRef type, int64_t off) const;


  // The harness calls the residual once. Solved cells are the initial memory
  // of the export arguments. The call receives the cells and constants that
  // enter the residual. Bytes no equation names stay symbolic.
  void emit(Module &H) const;
};

// An argument a function can return unchanged. The miss path of a lookup
// returns this argument; the call's constant for it is the fallback value.
inline std::optional<unsigned> fallbackArg(const Function *F) {
  if (!F || F->isDeclaration())
    return std::nullopt;
  std::unordered_map<const Value *, unsigned> exact;
  for (const Argument &A : F->args())
    exact[&A] = A.getArgNo();
  bool changed = true;
  while (changed) {
    changed = false;
    for (const Instruction &I : instructions(*F)) {
      if (exact.count(&I))
        continue;
      if (auto *C = dyn_cast<CastInst>(&I)) {
        auto it = exact.find(C->getOperand(0));
        if (it == exact.end())
          continue;
        exact[&I] = it->second;
        changed = true;
        continue;
      }
      auto *L = dyn_cast<LoadInst>(&I);
      if (!L)
        continue;
      auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      if (!A)
        continue;
      std::optional<unsigned> arg;
      bool ok = false;
      for (const User *U : A->users()) {
        auto *S = dyn_cast<StoreInst>(U);
        if (!S || S->getPointerOperand()->stripPointerCasts() != A)
          continue;
        auto it = exact.find(S->getValueOperand()->stripPointerCasts());
        if (it == exact.end())
          it = exact.find(S->getValueOperand());
        if (it == exact.end() || (arg && *arg != it->second)) {
          ok = false;
          arg.reset();
          break;
        }
        arg = it->second;
        ok = true;
      }
      if (!ok || !arg)
        continue;
      exact[&I] = *arg;
      changed = true;
    }
  }
  std::optional<unsigned> found;
  auto take = [&](unsigned arg) {
    if (found && *found != arg)
      found = std::nullopt;
    else
      found = arg;
  };
  for (const BasicBlock &BB : *F) {
    auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
    if (!R || !R->getReturnValue())
      continue;
    const Value *V = R->getReturnValue();
    if (auto it = exact.find(V); it != exact.end()) {
      take(it->second);
      if (!found)
        return std::nullopt;
      continue;
    }
    auto *P = dyn_cast<PHINode>(V);
    if (!P)
      continue;
    std::optional<unsigned> one;
    for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
      auto it = exact.find(P->getIncomingValue(i));
      if (it == exact.end())
        continue;
      if (one && *one != it->second) {
        one.reset();
        break;
      }
      one = it->second;
    }
    if (!one)
      continue;
    take(*one);
    if (!found)
      return std::nullopt;
  }
  return found;
}

inline bool cmpHolds(unsigned pred, int64_t v, int64_t k) {
  switch (pred) {
  case ICmpInst::ICMP_EQ:
    return v == k;
  case ICmpInst::ICMP_NE:
    return v != k;
  case ICmpInst::ICMP_UGT:
    return (uint64_t)v > (uint64_t)k;
  case ICmpInst::ICMP_UGE:
    return (uint64_t)v >= (uint64_t)k;
  case ICmpInst::ICMP_ULT:
    return (uint64_t)v < (uint64_t)k;
  case ICmpInst::ICMP_ULE:
    return (uint64_t)v <= (uint64_t)k;
  case ICmpInst::ICMP_SGT:
    return v > k;
  case ICmpInst::ICMP_SGE:
    return v >= k;
  case ICmpInst::ICMP_SLT:
    return v < k;
  case ICmpInst::ICMP_SLE:
    return v <= k;
  default:
    return false;
  }
}

// A constant that meets every predicate. The fallback is chosen when it does.
inline std::optional<int64_t> satisfyingValue(const std::vector<std::pair<unsigned, int64_t>> &cs, std::optional<int64_t> fallback) {
  auto ok = [&](int64_t v) {
    for (const auto &c : cs)
      if (!cmpHolds(c.first, v, c.second))
        return false;
    return !cs.empty();
  };
  std::vector<int64_t> cand;
  if (fallback)
    cand.push_back(*fallback);
  for (const auto &c : cs) {
    cand.push_back(c.second);
    if (c.first == ICmpInst::ICMP_NE)
      cand.push_back(c.second == 0 ? 1 : 0);
    if (c.first == ICmpInst::ICMP_SGT || c.first == ICmpInst::ICMP_UGT)
      cand.push_back(c.second + 1);
    if (c.first == ICmpInst::ICMP_SLT || c.first == ICmpInst::ICMP_ULT)
      cand.push_back(c.second - 1);
  }
  cand.push_back(0);
  cand.push_back(1);
  cand.push_back(-1);
  for (int64_t v : cand)
    if (ok(v))
      return v;
  for (int64_t v = -8; v <= 16; ++v)
    if (ok(v))
      return v;
  return std::nullopt;
}

// IR drops the cv-qualifier of the implicit object parameter. The Itanium
// mangling keeps it in a nested name: _ZN <CV-qualifiers> ... with
// <CV-qualifiers> ::= [r] [V] [K]. K makes this a pointer to const, so the
// method does not write its receiver.
inline bool constReceiver(const Function *F) {
  StringRef n = F->getName();
  if (!n.consume_front("_ZN"))
    return false;
  n.consume_front("r");
  n.consume_front("V");
  return n.starts_with("K");
}

// The arguments a declaration cannot write through, by their declared type.
// IR erases pointee qualifiers. The mangled parameter types keep them: a
// pointer or reference whose pointee is const (T const*, T const&) names
// memory the callee only reads. The receiver is the first argument when the
// nested name is const-qualified; a sret slot comes before it.
inline uint64_t constPointees(const Function *F) {
  // Result depends only on the mangled name and arg shape. Key by name so a
  // freed Module's Function* cannot poison a later parse at the same address.
  static std::unordered_map<std::string, uint64_t> memo;
  std::string name = F->getName().str();
  if (auto it = memo.find(name); it != memo.end())
    return it->second;
  uint64_t mask = 0;
  ItaniumPartialDemangler dm;
  if (!dm.partialDemangle(name.c_str()) && dm.isFunction()) {
    size_t len = 0;
    if (char *buf = dm.getFunctionParameters(nullptr, &len)) {
      std::string ps(buf);
      std::free(buf);
      if (ps.size() >= 2 && ps.front() == '(' && ps.back() == ')')
        ps = ps.substr(1, ps.size() - 2);
      std::vector<std::string> params;
      int depth = 0;
      std::string cur;
      for (char c : ps) {
        if (c == '<' || c == '(' || c == '[')
          ++depth;
        else if (c == '>' || c == ')' || c == ']')
          --depth;
        if (c == ',' && depth == 0) {
          params.push_back(cur);
          cur.clear();
          continue;
        }
        cur.push_back(c);
      }
      if (!cur.empty())
        params.push_back(cur);
      for (auto &p : params) {
        size_t b = p.find_first_not_of(' '), e = p.find_last_not_of(' ');
        p = b == std::string::npos ? "" : p.substr(b, e - b + 1);
      }
      params.erase(std::remove_if(params.begin(), params.end(), [](const std::string &p) { return p.empty() || p == "..."; }),
                   params.end());
      // The qualifier binds the pointee when it precedes the outermost * or &.
      // East const (T const*) and west const (const T*) are the same pointee.
      auto pointeeConst = [](const std::string &p) {
        int d = 0;
        long last = -1;
        for (size_t i = 0; i < p.size(); ++i) {
          char c = p[i];
          if (c == '<' || c == '(' || c == '[')
            ++d;
          else if (c == '>' || c == ')' || c == ']')
            --d;
          else if (d == 0 && (c == '*' || c == '&'))
            last = (long)i;
        }
        if (last < 0)
          return false;
        size_t s = (size_t)last;
        while (s > 0 && p[s - 1] == '&')
          --s;
        std::string before = p.substr(0, s);
        while (!before.empty() && before.back() == ' ')
          before.pop_back();
        if (before.size() >= 5 && before.compare(before.size() - 5, 5, "const") == 0)
          return true;
        size_t b = 0;
        while (b < before.size() && before[b] == ' ')
          ++b;
        return before.compare(b, 6, "const ") == 0 || before.compare(b, 6, "const\t") == 0;
      };
      unsigned A = F->arg_size(), P = (unsigned)params.size();
      if (P <= A) {
        unsigned off = A - P;
        for (unsigned i = 0; i < P; ++i)
          if (off + i < 64 && pointeeConst(params[i]))
            mask |= 1ull << (off + i);
        if (constReceiver(F)) {
          unsigned r = A > 0 && F->hasParamAttribute(0, Attribute::StructRet) ? 1 : 0;
          if (r < off)
            mask |= 1ull << r;
        }
      }
    }
  }
  memo[name] = mask;
  return mask;
}

// The function writes only memory that does not outlive the call: its own
// allocas, and the arguments in localMask, which are bound to a caller's
// stack local. A write through any other argument is a change the caller
// observes, so the call is not a lookup. A key under evaluation reads as
// false, so a recursive cycle keeps its real calls; every (F, localMask) key is
// evaluated once, which bounds the recursion.
inline bool lookupOnlyRec(const Function *F, std::map<std::pair<const Function *, uint64_t>, std::optional<bool>> &memo,
                          uint64_t localMask) {
  if (!F || F->isDeclaration())
    return false;
  std::pair<const Function *, uint64_t> key{F, localMask};
  if (auto it = memo.find(key); it != memo.end())
    return it->second && *it->second;
  auto isLocalArg = [&](unsigned i) { return i < 64 && (localMask >> i & 1); };
  memo[key] = std::nullopt;
  std::unordered_set<const AllocaInst *> boxes;
  for (const Instruction &I : instructions(*F))
    if (auto *A = dyn_cast<AllocaInst>(&I))
      boxes.insert(A);
  auto baseAlloca = [&](const Value *P) -> const AllocaInst * {
    const Value *V = P->stripPointerCasts();
    std::unordered_set<const Value *> seen;
    while (V && seen.insert(V).second) {
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        V = G->getPointerOperand()->stripPointerCasts();
        continue;
      }
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0)->stripPointerCasts();
        continue;
      }
      break;
    }
    return dyn_cast<AllocaInst>(V);
  };
  // A local that holds an argument is that argument. -O0 spills this into an
  // alloca and passes the reload, and that reload still names the object.
  std::unordered_set<const AllocaInst *> spill;
  std::unordered_set<const Value *> outside;
  for (const Argument &A : F->args())
    if (A.getType()->isPointerTy() && !isLocalArg(A.getArgNo()))
      outside.insert(&A);
  bool grew = true;
  while (grew) {
    grew = false;
    for (const Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        auto *A = baseAlloca(S->getPointerOperand());
        if (!A || spill.count(A))
          continue;
        const Value *V = S->getValueOperand()->stripPointerCasts();
        if (outside.count(V) || isa<GlobalValue>(V)) {
          spill.insert(A);
          grew = true;
        }
        continue;
      }
      auto *L = dyn_cast<LoadInst>(&I);
      if (!L || !L->getType()->isPointerTy() || outside.count(L))
        continue;
      auto *A = baseAlloca(L->getPointerOperand());
      if (A && spill.count(A)) {
        outside.insert(L);
        grew = true;
      }
    }
  }
  // A local address is one of this frame's allocas or a caller's local, and
  // stays one when -O0 stores it into a slot and loads it back. A slot that
  // also holds an outside pointer names no single region, so its reload is
  // not local.
  std::unordered_set<const AllocaInst *> holds;
  std::unordered_set<const Value *> held;
  for (const Argument &A : F->args())
    if (isLocalArg(A.getArgNo()))
      held.insert(&A);
  for (const AllocaInst *A : boxes)
    if (!spill.count(A))
      held.insert(A);
  // A GEP/cast of a local still names that local. fmt::format spills such a
  // GEP into a slot and stores through the reload; the slot must count as
  // holding a local, or those stores look like writes the caller observes.
  auto rootsHeld = [&](const Value *V) {
    const Value *X = V->stripPointerCasts();
    std::unordered_set<const Value *> seen;
    while (X && seen.insert(X).second) {
      if (held.count(X))
        return true;
      if (auto *G = dyn_cast<GEPOperator>(X)) {
        X = G->getPointerOperand()->stripPointerCasts();
        continue;
      }
      if (auto *C = dyn_cast<CastInst>(X)) {
        X = C->getOperand(0)->stripPointerCasts();
        continue;
      }
      break;
    }
    return false;
  };
  grew = true;
  while (grew) {
    grew = false;
    for (const Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        auto *A = baseAlloca(S->getPointerOperand());
        if (!A || holds.count(A))
          continue;
        if (rootsHeld(S->getValueOperand())) {
          holds.insert(A);
          grew = true;
        }
        continue;
      }
      auto *L = dyn_cast<LoadInst>(&I);
      if (!L || !L->getType()->isPointerTy() || held.count(L))
        continue;
      auto *Slot = baseAlloca(L->getPointerOperand());
      if (Slot && holds.count(Slot) && !spill.count(Slot)) {
        held.insert(L);
        grew = true;
      }
    }
  }
  // Pointers that name a non-local argument of F (the objects the caller
  // passed). A naked global such as stderr is not one: fprintf(stderr) in an
  // assertion path must not disqualify a lookup that never writes the caller's
  // objects. TypeDesc::c_str linked by closeModules is that case.
  auto fromArg = [&](const Value *P) {
    std::vector<const Value *> st{P->stripPointerCasts()};
    std::unordered_set<const Value *> seen;
    while (!st.empty()) {
      const Value *X = st.back();
      st.pop_back();
      if (!X || !seen.insert(X).second)
        continue;
      if (outside.count(X) || isa<Argument>(X))
        return true;
      if (auto *G = dyn_cast<GEPOperator>(X))
        st.push_back(G->getPointerOperand());
      else if (auto *C = dyn_cast<CastInst>(X))
        st.push_back(C->getOperand(0));
      else if (auto *L = dyn_cast<LoadInst>(X)) {
        if (outside.count(L))
          return true;
        st.push_back(L->getPointerOperand());
      }
    }
    return false;
  };
  auto throughLocal = [&](const Value *P) {
    const Value *V = P->stripPointerCasts();
    std::unordered_set<const Value *> seen;
    while (V && seen.insert(V).second) {
      if (held.count(V))
        return true;
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        V = G->getPointerOperand()->stripPointerCasts();
        continue;
      }
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0)->stripPointerCasts();
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        auto *Slot = baseAlloca(L->getPointerOperand());
        if (Slot && holds.count(Slot) && !spill.count(Slot))
          return true;
        break;
      }
      break;
    }
    return false;
  };
  for (const Instruction &I : instructions(*F)) {
    if (auto *S = dyn_cast<StoreInst>(&I)) {
      if (throughLocal(S->getPointerOperand()))
        continue;
      auto *A = baseAlloca(S->getPointerOperand());
      if (!A || !boxes.count(A)) {
        memo[key] = false;
        return false;
      }
      continue;
    }
    auto *CB = dyn_cast<CallBase>(&I);
    if (!CB || CB->isDebugOrPseudoInst())
      continue;
    if (auto *II = dyn_cast<IntrinsicInst>(CB)) {
      if (II->getIntrinsicID() == Intrinsic::memcpy || II->getIntrinsicID() == Intrinsic::memmove || II->getIntrinsicID() == Intrinsic::memset ||
          II->getIntrinsicID() == Intrinsic::memcpy_inline) {
        if (!throughLocal(II->getArgOperand(0)) && !boxes.count(baseAlloca(II->getArgOperand(0)))) {
          memo[key] = false;
          return false;
        }
      }
      continue;
    }
    bool passesOut = false;
    for (const Value *Op : CB->args()) {
      if (!Op->getType()->isPointerTy())
        continue;
      auto *A = baseAlloca(Op);
      if (A && boxes.count(A) && !spill.count(A))
        continue;
      if (fromArg(Op))
        passesOut = true;
    }
    if (!passesOut)
      continue;
    if (CB->onlyReadsMemory())
      continue;
    const Function *Cal = CB->getCalledFunction();
    if (!Cal) {
      memo[key] = false;
      return false;
    }
    // An argument bound to a local of this frame, or to a caller's local,
    // is local in the callee wherever it sits in the argument list.
    uint64_t childMask = 0;
    for (unsigned k = 0; k < CB->arg_size() && k < 64; ++k) {
      const Value *Op = CB->getArgOperand(k);
      if (!Op->getType()->isPointerTy())
        continue;
      auto *A = baseAlloca(Op);
      if ((A && boxes.count(A) && !spill.count(A)) || throughLocal(Op))
        childMask |= 1ull << k;
    }
    if (Cal->isDeclaration()) {
      // Without a body the callee may write any pointer it is given that its
      // type does not make read-only. It is a lookup only when every such
      // pointer is local, or is memory this function itself must not write
      // (a const-qualified argument of F, including west and east const).
      // strlen through char_traits::length(char const*) is the latter: the
      // C declaration carries no mangled const, but F's parameter does.
      const uint64_t ro = constPointees(Cal);
      const uint64_t selfRO = constPointees(F);
      auto fromConstArg = [&](const Value *P) {
        std::vector<const Value *> st{P->stripPointerCasts()};
        std::unordered_set<const Value *> seen;
        while (!st.empty()) {
          const Value *X = st.back();
          st.pop_back();
          if (!X || !seen.insert(X).second)
            continue;
          if (auto *A = dyn_cast<Argument>(X))
            return A->getArgNo() < 64 && (selfRO >> A->getArgNo() & 1);
          if (auto *G = dyn_cast<GEPOperator>(X))
            st.push_back(G->getPointerOperand());
          else if (auto *C = dyn_cast<CastInst>(X))
            st.push_back(C->getOperand(0));
          else if (auto *L = dyn_cast<LoadInst>(X))
            st.push_back(L->getPointerOperand());
          else if (auto *Slot = dyn_cast<AllocaInst>(X)) {
            // -O0 spills the formal into an alloca; strlen sees the reload.
            for (const User *U : Slot->users())
              if (auto *S = dyn_cast<StoreInst>(U))
                if (baseAlloca(S->getPointerOperand()) == Slot)
                  st.push_back(S->getValueOperand()->stripPointerCasts());
          }
        }
        return false;
      };
      bool writesOut = false;
      for (unsigned k = 0; k < CB->arg_size(); ++k) {
        const Value *Op = CB->getArgOperand(k);
        if (!Op->getType()->isPointerTy() || (k < 64 && (childMask >> k & 1)))
          continue;
        bool readOnly = CB->onlyReadsMemory(k) || (k < 64 && (ro >> k & 1)) || fromConstArg(Op);
        if (fromArg(Op) && !readOnly)
          writesOut = true;
      }
      if (!writesOut)
        continue;
      memo[key] = false;
      return false;
    }
    if (!lookupOnlyRec(Cal, memo, childMask)) {
      memo[key] = false;
      return false;
    }
  }
  memo[key] = true;
  return true;
}

inline bool lookupOnly(const Function *F) {
  // Memoize only within one query. A process-wide map keyed by Function* is
  // wrong once a module is freed and another is parsed into the same addresses
  // (MAY_REUSE); a by-name cache is wrong when an earlier phase sees a thinner
  // body of the same symbol and records false for the later client phase.
  if (!F)
    return false;
  std::map<std::pair<const Function *, uint64_t>, std::optional<bool>> memo;
  return lookupOnlyRec(F, memo, 0);
}
