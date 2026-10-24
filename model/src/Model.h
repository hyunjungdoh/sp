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
// residual runs once. The sink instruction stays there. Its overflow is not
// a clause.
//
// Sequence 0 is the best simple path from an interface function of D to
// the sink: fewer indirect edges, then fewer calls, then earlier call sites
// and demangled names. The interface is what D's shared object exports;
// those are the functions a client calls. Without it, a caller-facing
// export stands in: one that reaches the sink and is not called by another
// function on those paths. Index k is that path in the
// graph that no longer contains the last edge of any earlier path.

#include "Source.h"

#include "llvm/Demangle/Demangle.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
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

struct Loc {
  int arg = -1;
  Suffix suf;
  // The value is a pointer loaded from suf. The next field is that pointee,
  // so the pointer sits at suf and is not the pointee's first bytes.
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
  // D's interface: the functions its shared object exports. When known,
  // sequences start only at these, the functions a client can call.
  std::set<std::string> interfaceNames;
  Model(Module &down, Module &up, StringRef file, unsigned line) : down(down), up(up), dl(down.getDataLayout()), sinkFile(file), sinkLine(line) {}

  void run(int seqPick, raw_ostream &out);


 private:
  Module &down;
  Module &up;
  const DataLayout &dl;
  StringRef sinkFile;
  unsigned sinkLine;
  std::vector<Function *> sinks;
  std::map<Suffix, std::vector<Function *>> fnAt;
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
  mutable std::map<Suffix, std::vector<Function *>> slotAt;
  mutable bool slotReady = false;
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
  };
  struct FnMove {
    bool retOk = false;
    ArgRef ret;
    std::vector<PtrPut> puts;
  };
  mutable std::unordered_map<const Function *, FnMove> moveCache;
  mutable std::unordered_set<const Function *> moveStack;
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
  std::map<std::pair<Function *, unsigned>, std::vector<Function *>> argFn;
  std::unordered_map<const CallBase *, std::vector<Function *>> argCallTargets;
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
  std::map<std::pair<int, Suffix>, uint64_t> fileLen;
  std::map<int, uint64_t> argFileLen;
  std::vector<Function *> starts;
  std::unordered_set<Function *> cone;
  std::unordered_map<Function *, std::vector<Function *>> callersOf;
  std::map<Suffix, std::set<std::string>> facts;
  std::unordered_map<std::string, std::vector<StructType *>> namedByShape;
  std::unordered_map<const Type *, std::string> shapeMemo;
  mutable std::unordered_map<std::string, std::vector<std::string>> accessNames;
  bool shapesReady = false;
  mutable bool accessReady = false;

  Function *define(StringRef name) const;


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


  // A private struct often begins with a public struct at offset zero. A call
  // through the public type reads the same slot the private store wrote.
  void ensureSlots() const;
  // The functions the program places in the field a path ends at: those
  // stored at the path inside the last loaded object, else at its innermost
  // struct fields, whatever object encloses them.
  std::vector<Function *> storedAt(const Suffix &s) const;


  void addFn(const Suffix &s, Function *F);


  static std::string dec(const ConstantInt *CI);


  void noteScalar(const Suffix &suf, const std::string &v);


  std::string shape(Type *T);


  void ensureShapes();


  // A literal struct in an initializer is the named struct with the same
  // field layout. The load names that struct; the initializer often does not.
  std::vector<StructType *> namesFor(StructType *ST);


  void noteZero(Type *Ty, const Suffix &suf);


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


  std::vector<Function *> targetsOf(CallBase *CB) const;


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


  struct Mem {
    std::unordered_map<const Value *, Loc> loc;
    std::unordered_map<const AllocaInst *, Loc> slot;
  };

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


  // A load yields the pointer that was stored. That pointer was taken out of a
  // field only when the stored value is itself a load. Reloading an argument
  // gives the same object back, so the next field stays in it.
  bool heldPointer(const LoadInst *L) const;


  // The export path of an address. A loaded pointer keeps the field it was
  // loaded from and later steps append. A variable array index stays on
  // that array. A variable struct field is not a cell.
  bool cellLoc(Mem &m, Value *V, Loc &out) const;


  bool locOf(Mem &m, Value *V, Loc &out) const;


  static bool sameSteps(const Suffix &a, const Suffix &b);


  // The one pointer stored into this alloca, ignoring a null that a later
  // store replaces. Two different stores do not agree, so there is no value.
  Value *storedOnce(const AllocaInst *A) const;


  // The address V names: an argument or an alloca, plus the constant fields
  // walked to reach it. A load of an alloca forwards the address that was
  // saved there. A load of anything else is a pointer value, not an address.
  // A call forwards the address its summary says it returns.
  ArgRef addrIn(Function *F, Value *V) const;


  FnMove fnMove(Function *F) const;


  // The export object a pointer value names. An argument is the formal the
  // caller bound. A field address extends that formal. A load is the pointer
  // a put stored at that address. Two puts that name different objects do
  // not agree, so the load has no location.
  std::optional<Loc> valueAt(Function *F, Value *V, const Mem &m) const;


  void bindFormals(Mem &m, Function *F, const std::vector<std::optional<Loc>> &args) const;


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


  // The harness calls the residual once. Solved cells are the initial memory
  // of the export arguments. The call receives the cells and constants that
  // enter the residual. Bytes no equation names stay symbolic.
  void emit(Module &H) const;
};
