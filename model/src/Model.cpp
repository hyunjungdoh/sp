// The downstream context of one sequence is a formula on the export's cells.
//
// A cell is a constant-offset access path from an export argument. The same
// cell has the same root and the same suffix of (struct type, constant
// byte offset). A variable index of an array held by a constant field is
// one element cell. A variable field of a struct is not a cell.
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
// Sequence 0 is the best simple path from a caller-facing export to the
// sink: fewer indirect edges, then fewer calls, then earlier call sites
// and demangled names. A caller-facing export reaches the sink and is not
// called by another function on those paths. Index k is that path in the
// graph that no longer contains the last edge of any earlier path.

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

static std::optional<int64_t> asI64(const std::string &s) {
  if (s.empty())
    return std::nullopt;
  int64_t v = 0;
  const char *b = s.data();
  auto r = std::from_chars(b, b + s.size(), v);
  if (r.ec != std::errc() || r.ptr != b + s.size())
    return std::nullopt;
  return v;
}

static std::optional<uint64_t> asU64(const std::string &s) {
  if (s.empty() || s[0] == '-')
    return std::nullopt;
  uint64_t v = 0;
  const char *b = s.data();
  auto r = std::from_chars(b, b + s.size(), v);
  if (r.ec != std::errc() || r.ptr != b + s.size())
    return std::nullopt;
  return v;
}

static const char *icmpName(unsigned p) {
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

static std::string pretty(StringRef name) {
  std::string d = demangle(name.str());
  return d.empty() ? name.str() : d;
}

static bool sinkHere(const Instruction &I, StringRef file, unsigned line) {
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

static Copy fixedCopy(const CallBase &CB) {
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

static Read asRead(const CallBase &CB) {
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

static bool ignorable(const Function *F) {
  if (!F)
    return false;
  return F->isIntrinsic() || F->getName().starts_with("llvm.dbg.") || F->getName().starts_with("llvm.lifetime.");
}

class Model {
 public:
  Model(Module &down, Module &up, StringRef file, unsigned line) : down(down), up(up), dl(down.getDataLayout()), sinkFile(file), sinkLine(line) {}

  void run(int seqPick, raw_ostream &out) {
    sinks = findSinks();
    if (sinks.empty()) {
      out << "sink none\n";
      return;
    }
    indexFunctions();
    exports = findExports();
    buildCallers();
    cone = reachSink();
    starts = findStarts();
    out << "starts " << starts.size() << "\n";
    for (int n = seqPick;; ++n) {
      auto paths = sequences(n);
      if ((int)paths.size() <= n) {
        out << "sequence " << n << " absent\n";
        out << "paths " << paths.size() << "\n";
        entry = nullptr;
        solvedCells.clear();
        return;
      }
      const auto &path = paths[(size_t)n];
      out << "sequence " << n << "\n";
      for (Function *F : path.fn)
        out << "fn " << F->getName() << " " << pretty(F->getName()) << "\n";
      if (solve(path.fn, out))
        return;
    }
  }

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
  mutable std::map<Suffix, std::vector<Function *>> slotAt;
  mutable bool slotReady = false;
  struct VTab {
    GlobalVariable *g = nullptr;
    uint64_t base = 0;
    int64_t field = 0;
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

  Function *define(StringRef name) const {
    auto body = [&](Module &M) -> Function * {
      if (Function *F = M.getFunction(name))
        if (!F->isDeclaration())
          return F;
      if (GlobalAlias *A = M.getNamedAlias(name))
        if (Constant *Ali = A->getAliasee())
          if (auto *F = dyn_cast<Function>(Ali->stripPointerCasts()))
            if (!F->isDeclaration())
              return F;
      return nullptr;
    };
    if (Function *D = body(down))
      return D;
    return body(up);
  }

  // A call whose callee is not a function in the module. Its body is not
  // available, so the call itself is the equation.
  bool noBody(CallBase *CB) {
    if (Function *C = CB->getCalledFunction())
      return define(C->getName()) == nullptr;
    for (Function *T : targetsOf(CB))
      if (!T->isDeclaration() || define(T->getName()))
        return false;
    return true;
  }

  template <typename Fn>
  void eachBody(Fn &&fn) const {
    for (Module *M : {&down, &up})
      for (Function &F : *M)
        if (!F.isDeclaration())
          fn(F);
  }

  std::vector<Function *> findSinks() {
    std::vector<Function *> found;
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        found.push_back(&F);
        break;
      }
    });
    std::sort(found.begin(), found.end(), [](Function *A, Function *B) { return A->getName() < B->getName(); });
    found.erase(std::unique(found.begin(), found.end()), found.end());
    return found;
  }

  Suffix suffix(Value *V) const {
    Suffix s;
    std::unordered_set<const Value *> seen;
    if (!V)
      return s;
    {
      Value *U = V;
      while (auto *C = dyn_cast<CastInst>(U))
        U = C->getOperand(0);
      if (auto *L = dyn_cast<LoadInst>(U))
        V = L->getPointerOperand();
    }
    while (V && seen.insert(V).second) {
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      auto *G = dyn_cast<GEPOperator>(V);
      if (G) {
        if (!G->hasAllConstantIndices()) {
          // A variable index of an array is one element cell. A variable
          // field of a struct is not a cell.
          if (isa<StructType>(G->getSourceElementType()))
            return {};
          V = G->getPointerOperand();
          continue;
        }
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return {};
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType())) {
          if (ST->hasName())
            s.insert(s.begin(), Step{ST->getName().str(), off.getSExtValue()});
        }
        V = G->getPointerOperand();
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (!s.empty())
          break;
        V = L->getPointerOperand();
        continue;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        bool bad = false;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in) {
            bad = true;
            break;
          }
          one = in;
        }
        if (bad || !one)
          return {};
        V = one;
        continue;
      }
      break;
    }
    return s;
  }

  // A private struct often begins with a public struct at offset zero. A call
  // through the public type reads the same slot the private store wrote.
  void ensureSlots() const {
    if (slotReady)
      return;
    slotReady = true;
    for (const auto &kv : fnAt) {
      auto put = [&](const Suffix &key, Function *F) {
        auto &v = slotAt[key];
        if (std::find(v.begin(), v.end(), F) == v.end())
          v.push_back(F);
      };
      for (Function *F : kv.second)
        put(kv.first, F);
      for (size_t n = 1; n < kv.first.size(); ++n) {
        bool zero = true;
        for (size_t i = 0; i < n; ++i)
          if (kv.first[i].off != 0)
            zero = false;
        if (!zero)
          continue;
        Suffix tail(kv.first.begin() + (long)n, kv.first.end());
        for (Function *F : kv.second)
          put(tail, F);
      }
    }
  }

  void addFn(const Suffix &s, Function *F) {
    if (!F || s.empty())
      return;
    auto &v = fnAt[s];
    if (std::find(v.begin(), v.end(), F) == v.end())
      v.push_back(F);
  }

  static std::string dec(const ConstantInt *CI) {
    SmallVector<char, 32> buf;
    CI->getValue().toString(buf, 10, true);
    return std::string(buf.begin(), buf.end());
  }

  void noteScalar(const Suffix &suf, const std::string &v) {
    if (!suf.empty())
      facts[suf].insert(v);
  }

  std::string shape(Type *T) {
    auto it = shapeMemo.find(T);
    if (it != shapeMemo.end())
      return it->second;
    shapeMemo[T] = "?";
    std::string s;
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) {
        s = "opaque";
      } else {
        const StructLayout *SL = dl.getStructLayout(ST);
        s = "{";
        for (unsigned i = 0; i < ST->getNumElements(); ++i) {
          s += std::to_string(SL->getElementOffset(i));
          s += ":";
          s += shape(ST->getElementType(i));
          s += ";";
        }
        s += "}";
      }
    } else if (auto *AT = dyn_cast<ArrayType>(T)) {
      s = "[" + std::to_string(AT->getNumElements()) + "x" + shape(AT->getElementType()) + "]";
    } else {
      s = std::to_string(dl.getTypeAllocSize(T).getFixedValue());
    }
    shapeMemo[T] = s;
    return s;
  }

  void ensureShapes() {
    if (shapesReady)
      return;
    shapesReady = true;
    for (Module *M : {&down, &up})
      for (StructType *ST : M->getIdentifiedStructTypes())
        if (ST->hasName() && !ST->isOpaque())
          namedByShape[shape(ST)].push_back(ST);
  }

  // A literal struct in an initializer is the named struct with the same
  // field layout. The load names that struct; the initializer often does not.
  std::vector<StructType *> namesFor(StructType *ST) {
    ensureShapes();
    if (!ST || ST->isOpaque())
      return {};
    if (ST->hasName())
      return {ST};
    auto it = namedByShape.find(shape(ST));
    if (it == namedByShape.end())
      return {};
    std::vector<StructType *> out;
    std::set<std::string> seen;
    for (StructType *N : it->second)
      if (seen.insert(N->getName().str()).second)
        out.push_back(N);
    return out;
  }

  void noteZero(Type *Ty, const Suffix &suf) {
    if (!Ty)
      return;
    if (Ty->isIntegerTy() || Ty->isPointerTy()) {
      noteScalar(suf, "0");
      return;
    }
    if (auto *ST = dyn_cast<StructType>(Ty)) {
      for (StructType *N : namesFor(ST)) {
        const StructLayout *SL = dl.getStructLayout(N);
        for (unsigned i = 0; i < N->getNumElements(); ++i) {
          Suffix n = suf;
          n.push_back(Step{N->getName().str(), (int64_t)SL->getElementOffset(i)});
          noteZero(N->getElementType(i), n);
        }
      }
      return;
    }
    if (auto *AT = dyn_cast<ArrayType>(Ty)) {
      uint64_t es = dl.getTypeAllocSize(AT->getElementType()).getFixedValue();
      for (uint64_t i = 0; i < AT->getNumElements(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        noteZero(AT->getElementType(), n);
      }
    }
  }

  void walkInit(Constant *C, Type *Ty, const Suffix &suf, bool scalars) {
    if (!C)
      return;
    if (isa<ConstantPointerNull>(C) || isa<ConstantAggregateZero>(C))
      return;
    if (auto *F = dyn_cast<Function>(C->stripPointerCasts())) {
      if (Function *D = define(F->getName()))
        F = D;
      addFn(suf, F);
      noteScalar(suf, F->getName().str());
      return;
    }
    if (auto *CI = dyn_cast<ConstantInt>(C)) {
      if (scalars)
        noteScalar(suf, dec(CI));
      return;
    }
    if (auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
      Type *ET = CDS->getElementType();
      uint64_t es = dl.getTypeAllocSize(ET).getFixedValue();
      for (unsigned i = 0; i < CDS->getNumElements(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        walkInit(CDS->getElementAsConstant(i), ET, n, scalars);
      }
      return;
    }
    if (auto *S = dyn_cast<ConstantStruct>(C)) {
      auto *ST = dyn_cast<StructType>(Ty ? Ty : C->getType());
      auto named = namesFor(ST);
      if (named.empty()) {
        for (unsigned i = 0; i < S->getNumOperands(); ++i)
          walkInit(S->getOperand(i), S->getOperand(i)->getType(), suf, scalars);
        return;
      }
      for (StructType *N : named) {
        const StructLayout *SL = dl.getStructLayout(N);
        for (unsigned i = 0; i < S->getNumOperands() && i < N->getNumElements(); ++i) {
          Suffix n = suf;
          n.push_back(Step{N->getName().str(), (int64_t)SL->getElementOffset(i)});
          walkInit(S->getOperand(i), N->getElementType(i), n, scalars);
        }
      }
      return;
    }
    if (auto *A = dyn_cast<ConstantArray>(C)) {
      auto *AT = dyn_cast<ArrayType>(Ty ? Ty : C->getType());
      Type *ET = AT ? AT->getElementType() : nullptr;
      uint64_t es = ET ? dl.getTypeAllocSize(ET).getFixedValue() : 0;
      for (unsigned i = 0; i < A->getNumOperands(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        walkInit(A->getOperand(i), ET, n, scalars);
      }
    }
  }

  static bool typeNameMatches(StringRef llvmName, StringRef access) {
    StringRef n = llvmName;
    if (!n.consume_front("struct.") && !n.consume_front("class."))
      return false;
    if (n == access)
      return true;
    return n.starts_with(access) && n.size() > access.size() && n[access.size()] == '.';
  }

  // A store through a byte offset keeps the struct and offset in its access
  // tag. That is the same cell as a field load of that struct at that offset.
  void ensureAccess() const {
    if (accessReady)
      return;
    accessReady = true;
    for (Module *M : {&down, &up}) {
      for (StructType *ST : M->getIdentifiedStructTypes()) {
        if (!ST->hasName())
          continue;
        StringRef n = ST->getName();
        if (!n.consume_front("struct.") && !n.consume_front("class."))
          continue;
        accessNames[n.str()].push_back(ST->getName().str());
        auto dot = n.rfind('.');
        if (dot != StringRef::npos && n.drop_front(dot + 1).find_if_not([](char c) { return c >= '0' && c <= '9'; }) == StringRef::npos)
          accessNames[n.substr(0, dot).str()].push_back(ST->getName().str());
      }
    }
  }

  Suffix suffixFromAccess(const StoreInst *S) const {
    const MDNode *TB = S->getMetadata(LLVMContext::MD_tbaa);
    if (!TB || TB->getNumOperands() < 3)
      return {};
    auto *Base = dyn_cast<MDNode>(TB->getOperand(0).get());
    auto *Off = dyn_cast<ConstantAsMetadata>(TB->getOperand(2).get());
    if (!Base || Base->getNumOperands() < 1 || !Off)
      return {};
    auto *Name = dyn_cast<MDString>(Base->getOperand(0).get());
    auto *CI = dyn_cast<ConstantInt>(Off->getValue());
    if (!Name || !CI)
      return {};
    ensureAccess();
    auto it = accessNames.find(Name->getString().str());
    if (it == accessNames.end() || it->second.empty())
      return {};
    return {Step{it->second.front(), CI->getSExtValue()}};
  }

  void indexFunctions() {
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *C = dyn_cast<Constant>(S->getValueOperand());
        if (!C)
          continue;
        Suffix suf = suffix(S->getPointerOperand());
        if (suf.empty())
          suf = suffixFromAccess(S);
        walkInit(C, C->getType(), suf, false);
      }
    });
    for (Module *M : {&down, &up})
      for (GlobalVariable &G : M->globals()) {
      if (!G.hasInitializer())
        continue;
      walkInit(G.getInitializer(), G.getValueType(), {}, true);
    }
    for (auto &kv : fnAt) {
      std::sort(kv.second.begin(), kv.second.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    }
    indexKeys();
  }

  // The bytes of a constant string argument.
  static std::string cstring(Value *V) {
    if (!V)
      return {};
    V = V->stripPointerCasts();
    if (auto *G = dyn_cast<GEPOperator>(V)) {
      if (G->hasAllZeroIndices())
        V = G->getPointerOperand()->stripPointerCasts();
    }
    auto *GV = dyn_cast<GlobalVariable>(V);
    if (!GV || !GV->hasInitializer())
      return {};
    auto *C = dyn_cast<ConstantDataSequential>(GV->getInitializer());
    if (!C || !C->isString())
      return {};
    StringRef s = C->getAsString();
    if (!s.empty() && s.back() == '\0')
      s = s.drop_back();
    if (s.empty() || s.find('\0') != StringRef::npos)
      return {};
    return s.str();
  }

  // Byte offset from the returned object at which the callee stores each argument.
  std::map<unsigned, int64_t> argOffsets(Function *F) {
    auto it = keyArgCache.find(F);
    if (it != keyArgCache.end())
      return it->second;
    std::map<unsigned, int64_t> args;
    std::unordered_set<const Value *> base;
    for (BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        break;
      }
      if (V)
        base.insert(V);
    }
    auto placed = [&](Value *P, int64_t &off) {
      off = 0;
      std::unordered_set<const Value *> seen;
      while (P && seen.insert(P).second) {
        if (auto *C = dyn_cast<CastInst>(P)) {
          P = C->getOperand(0);
          continue;
        }
        if (auto *G = dyn_cast<GEPOperator>(P)) {
          if (!G->hasAllConstantIndices())
            return false;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, delta))
            return false;
          off += delta.getSExtValue();
          P = G->getPointerOperand();
          continue;
        }
        break;
      }
      return P && base.count(P);
    };
    for (Instruction &I : instructions(*F)) {
      auto *S = dyn_cast<StoreInst>(&I);
      if (!S)
        continue;
      int64_t off = 0;
      if (!placed(S->getPointerOperand(), off))
        continue;
      Value *V = S->getValueOperand();
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(V)) {
          if (CB->arg_size() == 1) {
            V = CB->getArgOperand(0);
            continue;
          }
        }
        break;
      }
      if (auto *A = dyn_cast<Argument>(V))
        args[A->getArgNo()] = off;
    }
    keyArgCache[F] = args;
    return keyArgCache[F];
  }

  // A field is a key when a call loads it and passes that value together with
  // the object. The byte offsets of those fields, per struct.
  std::map<std::string, std::set<int64_t>> keyFields() {
    std::map<std::string, std::set<int64_t>> out;
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Op = CB->getArgOperand(i);
          while (auto *C = dyn_cast<CastInst>(Op))
            Op = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(Op);
          if (!L)
            continue;
          Value *Ptr = L->getPointerOperand();
          while (auto *C = dyn_cast<CastInst>(Ptr))
            Ptr = C->getOperand(0);
          auto *G = dyn_cast<GEPOperator>(Ptr);
          if (!G || !G->hasAllConstantIndices())
            continue;
          auto *ST = dyn_cast<StructType>(G->getSourceElementType());
          if (!ST || !ST->hasName())
            continue;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, delta))
            continue;
          Value *base = G->getPointerOperand()->stripPointerCasts();
          for (unsigned j = 0; j < CB->arg_size(); ++j) {
            if (i == j)
              continue;
            if (CB->getArgOperand(j)->stripPointerCasts() == base)
              out[ST->getName().str()].insert(delta.getSExtValue());
          }
        }
      }
    });
    return out;
  }

  static std::string bareType(StringRef n) {
    if (!n.consume_front("struct.") && !n.consume_front("class."))
      return n.str();
    auto dot = n.rfind('.');
    if (dot != StringRef::npos && n.drop_front(dot + 1).find_if_not([](char c) { return c >= '0' && c <= '9'; }) == StringRef::npos)
      return n.substr(0, dot).str();
    return n.str();
  }

  // A call returns an object, and a later store writes a function into that
  // object. The constant strings stored at the object's key field select it.
  void indexKeys() {
    auto fields = keyFields();
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts());
        if (!Fn)
          continue;
        Value *P = S->getPointerOperand();
        std::unordered_set<const Value *> seen;
        while (P && seen.insert(P).second) {
          if (auto *C = dyn_cast<CastInst>(P)) {
            P = C->getOperand(0);
            continue;
          }
          if (auto *G = dyn_cast<GEPOperator>(P)) {
            P = G->getPointerOperand();
            continue;
          }
          break;
        }
        auto *CB = dyn_cast<CallBase>(P);
        if (!CB)
          continue;
        if (Function *D = define(Fn->getName()))
          Fn = D;
        Function *Alloc = CB->getCalledFunction();
        if (Alloc)
          if (Function *AD = define(Alloc->getName()))
            Alloc = AD;
        if (!Alloc)
          continue;
        std::string structName;
        Suffix where = suffix(S->getPointerOperand());
        if (!where.empty())
          structName = bareType(where.front().type);
        std::set<int64_t> keys;
        for (const auto &kf : fields)
          if (bareType(kf.first) == structName)
            keys.insert(kf.second.begin(), kf.second.end());
        auto placed = argOffsets(Alloc);
        for (const auto &ao : placed) {
          if (!keys.empty() && !keys.count(ao.second))
            continue;
          if (keys.empty())
            continue;
          if (ao.first >= CB->arg_size())
            continue;
          std::string s = cstring(CB->getArgOperand(ao.first));
          if (!s.empty())
            regKeys[Fn].insert(std::move(s));
        }
      }
    });
    indexArgFns();
  }

  static void addUnique(std::vector<Function *> &v, Function *F) {
    if (F && std::find(v.begin(), v.end(), F) == v.end())
      v.push_back(F);
  }

  // An indirect call of a formal argument calls the functions its callers pass.
  void indexArgFns() {
    struct Site {
      Function *caller = nullptr;
      Function *callee = nullptr;
      unsigned index = 0;
      int from = -1;
    };
    std::vector<Site> sites;
    std::vector<std::pair<const CallBase *, unsigned>> indirect;
    struct Stored {
      Function *fn;
      unsigned arg;
      Suffix suf;
    };
    std::vector<Stored> stored;
    eachBody([&](Function &F) {
      Mem m;
      std::vector<std::optional<Loc>> roots(F.arg_size());
      for (unsigned i = 0; i < F.arg_size(); ++i)
        roots[i] = Loc{(int)i, {}};
      bindFormals(m, &F, roots);
      propagate(m, &F);
      auto argOf = [&](Value *V) -> int {
        Loc L;
        if (!locOf(m, V, L) || !L.suf.empty())
          return -1;
        return L.arg;
      };
      for (Instruction &I : instructions(F)) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          int arg = argOf(S->getValueOperand());
          if (arg < 0) {
            Value *Sv = S->getValueOperand()->stripPointerCasts();
            if (auto *Ld = dyn_cast<LoadInst>(Sv)) {
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              if (Al)
                for (Instruction &SI : instructions(F)) {
                  auto *St = dyn_cast<StoreInst>(&SI);
                  if (!St || St->getPointerOperand()->stripPointerCasts() != Al)
                    continue;
                  if (auto *A = dyn_cast<Argument>(St->getValueOperand()->stripPointerCasts()))
                    arg = (int)A->getArgNo();
                }
            }
          }
          Suffix suf = suffix(S->getPointerOperand());
          if (arg >= 0 && !suf.empty())
            stored.push_back(Stored{&F, (unsigned)arg, std::move(suf)});
        }
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *C = CB->getCalledFunction();
        if (C) {
          if (Function *D = define(C->getName()))
            C = D;
        }
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Op = CB->getArgOperand(i);
          if (auto *Fn = dyn_cast<Function>(Op->stripPointerCasts())) {
            if (Function *D = define(Fn->getName()))
              Fn = D;
            if (C)
              addUnique(argFn[std::make_pair(C, i)], Fn);
            continue;
          }
          int arg = argOf(Op);
          if (C && arg >= 0)
            sites.push_back(Site{&F, C, i, arg});
        }
        if (!C) {
          int arg = argOf(CB->getCalledOperand());
          if (arg >= 0)
            indirect.push_back({CB, (unsigned)arg});
        }
      }
    });
    bool grew = true;
    while (grew) {
      grew = false;
      for (const Site &s : sites) {
        if (s.from < 0 || !s.callee)
          continue;
        for (Function *Fn : argFn[std::make_pair(s.caller, (unsigned)s.from)]) {
          auto &dst = argFn[std::make_pair(s.callee, s.index)];
          if (std::find(dst.begin(), dst.end(), Fn) == dst.end()) {
            dst.push_back(Fn);
            grew = true;
          }
        }
      }
    }
    for (const auto &c : indirect)
      argCallTargets[c.first] = argFn[std::make_pair(const_cast<Function *>(c.first->getFunction()), c.second)];
    for (const Stored &s : stored) {
      for (Function *Fn : argFn[std::make_pair(s.fn, s.arg)])
        addFn(s.suf, Fn);
      argStored[s.fn].push_back({s.arg, s.suf});
    }
    for (const Stored &s : stored) {
      if (argFn[std::make_pair(s.fn, s.arg)].empty())
        continue;
      for (const Stored &o : stored) {
        if (o.fn != s.fn || o.arg == s.arg)
          continue;
        auto &v = besidePtr[s.suf];
        if (std::find(v.begin(), v.end(), o.suf) == v.end())
          v.push_back(o.suf);
      }
    }
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *C = CB->getCalledFunction();
        if (!C)
          continue;
        if (Function *D = define(C->getName()))
          C = D;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Act = CB->getArgOperand(i)->stripPointerCasts();
          if (auto *Ld = dyn_cast<LoadInst>(Act)) {
            auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
            if (Al)
              for (Instruction &SI : instructions(F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (S && S->getPointerOperand()->stripPointerCasts() == Al)
                  Act = S->getValueOperand()->stripPointerCasts();
              }
          }
          auto *Inner = dyn_cast<CallBase>(Act);
          if (!Inner)
            continue;
          Function *H = Inner->getCalledFunction();
          if (!H)
            continue;
          if (Function *HD = define(H->getName()))
            H = HD;
          for (const auto &st : argStored[C]) {
            if (st.first != i)
              continue;
            auto &v = builderOf[st.second];
            if (std::find(v.begin(), v.end(), H) == v.end())
              v.push_back(H);
          }
        }
      }
    });
  }

  Suffix returnsOf(const Function *F) const {
    if (!F || F->isDeclaration())
      return {};
    auto it = retCache.find(F);
    if (it != retCache.end())
      return it->second;
    bool saw = false;
    bool bad = false;
    Suffix s;
    for (const BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
        continue;
      Suffix t = suffix(V);
      if (t.empty()) {
        bad = true;
        break;
      }
      if (!saw) {
        s = std::move(t);
        saw = true;
      } else if (s != t) {
        bad = true;
        break;
      }
    }
    if (!saw || bad)
      s.clear();
    retCache[F] = s;
    return retCache[F];
  }

  // The function a global initializer places at a byte offset.
  Function *functionAt(Constant *C, uint64_t base, uint64_t want) const {
    if (!C)
      return nullptr;
    if (auto *CE = dyn_cast<ConstantExpr>(C)) {
      if (CE->isCast())
        return functionAt(CE->getOperand(0), base, want);
      return nullptr;
    }
    if (auto *F = dyn_cast<Function>(C)) {
      if (base != want)
        return nullptr;
      if (Function *D = define(F->getName()))
        return D;
      return F;
    }
    if (auto *CS = dyn_cast<ConstantStruct>(C)) {
      const StructLayout *SL = dl.getStructLayout(CS->getType());
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        if (Function *Fn = functionAt(CS->getOperand(i), base + SL->getElementOffset(i), want))
          return Fn;
      return nullptr;
    }
    if (auto *CA = dyn_cast<ConstantArray>(C)) {
      uint64_t es = dl.getTypeAllocSize(CA->getType()->getElementType()).getFixedValue();
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        if (Function *Fn = functionAt(CA->getOperand(i), base + (uint64_t)i * es, want))
          return Fn;
      return nullptr;
    }
    return nullptr;
  }

  // A constructor stores a vtable into the object it builds. The named struct
  // it writes through is the type a later virtual call sees.
  void indexVtables() const {
    if (vtReady)
      return;
    vtReady = true;
    eachBody([&](Function &F) {
      bool any = false;
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *VG = dyn_cast<GEPOperator>(S->getValueOperand()->stripPointerCasts());
        if (VG && dyn_cast<GlobalVariable>(VG->getPointerOperand()->stripPointerCasts()))
          any = true;
      }
      if (!any || F.arg_empty())
        return;
      std::unordered_set<const Value *> th{F.getArg(0)};
      std::unordered_set<const AllocaInst *> boxes;
      for (int pass = 0; pass < 3; ++pass) {
        for (Instruction &I : instructions(F)) {
          if (auto *C = dyn_cast<CastInst>(&I))
            if (th.count(C->getOperand(0)))
              th.insert(&I);
          if (auto *S = dyn_cast<StoreInst>(&I))
            if (th.count(S->getValueOperand()->stripPointerCasts()))
              if (auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
                boxes.insert(Al);
          if (auto *L = dyn_cast<LoadInst>(&I))
            if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
              if (boxes.count(Al))
                th.insert(&I);
        }
      }
      std::set<std::string> types;
      for (Instruction &I : instructions(F)) {
        auto *G = dyn_cast<GetElementPtrInst>(&I);
        if (!G || !th.count(G->getPointerOperand()->stripPointerCasts()))
          continue;
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName())
            types.insert(ST->getName().str());
      }
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        Value *Val = S->getValueOperand()->stripPointerCasts();
        auto *VG = dyn_cast<GEPOperator>(Val);
        if (!VG || !VG->hasAllConstantIndices())
          continue;
        APInt bo(dl.getIndexSizeInBits(VG->getPointerAddressSpace()), 0);
        if (!VG->accumulateConstantOffset(dl, bo))
          continue;
        auto *GV = dyn_cast<GlobalVariable>(VG->getPointerOperand()->stripPointerCasts());
        if (!GV || !GV->hasInitializer())
          continue;
        Value *P = S->getPointerOperand()->stripPointerCasts();
        int64_t field = 0;
        if (auto *G = dyn_cast<GEPOperator>(P)) {
          if (!G->hasAllConstantIndices())
            continue;
          APInt fo(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, fo))
            continue;
          field = fo.getSExtValue();
          P = G->getPointerOperand()->stripPointerCasts();
        }
        if (!th.count(P))
          continue;
        VTab vt{GV, (uint64_t)bo.getSExtValue(), field};
        vtAll.push_back(vt);
        for (const std::string &ty : types)
          vtOf[ty].push_back(vt);
      }
    });
  }

  struct VSlot {
    bool ok = false;
    Value *obj = nullptr;
    int64_t field = 0;
    uint64_t slot = 0;
  };

  VSlot vslot(CallBase *CB) const {
    VSlot s;
    auto *fnLoad = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
    if (!fnLoad)
      return s;
    auto *slotG = dyn_cast<GEPOperator>(fnLoad->getPointerOperand()->stripPointerCasts());
    if (!slotG || !slotG->hasAllConstantIndices())
      return s;
    APInt slot(dl.getIndexSizeInBits(slotG->getPointerAddressSpace()), 0);
    if (!slotG->accumulateConstantOffset(dl, slot))
      return s;
    auto *vLoad = dyn_cast<LoadInst>(slotG->getPointerOperand()->stripPointerCasts());
    if (!vLoad)
      return s;
    Value *obj = vLoad->getPointerOperand()->stripPointerCasts();
    int64_t field = 0;
    if (auto *OG = dyn_cast<GEPOperator>(obj)) {
      if (!OG->hasAllConstantIndices())
        return s;
      APInt fo(dl.getIndexSizeInBits(OG->getPointerAddressSpace()), 0);
      if (!OG->accumulateConstantOffset(dl, fo))
        return s;
      field = fo.getSExtValue();
      obj = OG->getPointerOperand()->stripPointerCasts();
    }
    s.ok = true;
    s.obj = obj;
    s.field = field;
    s.slot = (uint64_t)slot.getSExtValue();
    return s;
  }

  std::vector<Function *> fromVtabs(const std::vector<VTab> &tabs, int64_t field, uint64_t slot) const {
    std::vector<Function *> out;
    for (const VTab &vt : tabs) {
      if (vt.field != field)
        continue;
      if (Function *Fn = functionAt(vt.g->getInitializer(), 0, vt.base + slot))
        if (std::find(out.begin(), out.end(), Fn) == out.end())
          out.push_back(Fn);
    }
    return out;
  }

  bool containsRead(Function *F) const {
    auto it = readBody.find(F);
    if (it != readBody.end())
      return it->second;
    bool yes = false;
    if (F && !F->isDeclaration()) {
      for (Instruction &I : instructions(*F)) {
        auto *C = dyn_cast<CallBase>(&I);
        if (!C)
          continue;
        Function *Cal = C->getCalledFunction();
        if (!Cal || define(Cal->getName()))
          continue;
        if (asRead(*C).ok) {
          yes = true;
          break;
        }
      }
    }
    readBody[F] = yes;
    return yes;
  }

  // Functions reached from From by direct and indirect calls, including From.
  bool reachesFn(Function *From, Function *To) const {
    if (!From || !To)
      return false;
    Function *Dst = define(To->getName());
    if (!Dst)
      Dst = To;
    auto it = reachFrom.find(From);
    if (it == reachFrom.end()) {
      std::unordered_set<const Function *> seen;
      std::vector<Function *> work{From};
      seen.insert(From);
      for (size_t i = 0; i < work.size(); ++i) {
        if (work[i]->isDeclaration())
          continue;
        for (Instruction &I : instructions(*work[i])) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          for (Function *T : targetsOf(CB)) {
            if (!T)
              continue;
            Function *D = define(T->getName());
            if (!D)
              D = T;
            if (seen.insert(D).second)
              work.push_back(D);
          }
        }
      }
      it = reachFrom.emplace(From, std::move(seen)).first;
    }
    return it->second.count(Dst) != 0;
  }

  // Functions stored at this cell by a function that also stores Next.
  // The two stores are one fact: the initializer that installs the next call.
  std::set<std::string> storedBeside(const Suffix &cell, Function *Next) const {
    std::set<std::string> out;
    if (!Next || cell.empty())
      return out;
    auto key = std::make_pair(static_cast<const Function *>(Next), cell);
    if (auto it = besideCache.find(key); it != besideCache.end())
      return it->second;
    auto same = [&](const Suffix &s) {
      if (s.size() != cell.size())
        return false;
      for (size_t i = 0; i < s.size(); ++i)
        if (s[i].type != cell[i].type || s[i].off != cell[i].off)
          return false;
      return true;
    };
    eachBody([&](Function &F) {
      bool writes = false;
      std::vector<std::string> here;
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts());
        if (!Fn)
          continue;
        if (Function *D = define(Fn->getName()))
          Fn = D;
        if (Fn == Next)
          writes = true;
        if (same(suffix(S->getPointerOperand())))
          here.push_back(Fn->getName().str());
      }
      if (writes)
        out.insert(here.begin(), here.end());
    });
    besideCache[key] = out;
    return besideCache[key];
  }

  // An indirect call through a constant slot of a vtable. The vtable is the
  // constant stored into the object by the function that built it.
  std::vector<Function *> vtableTargets(CallBase *CB) const {
    auto hit = vtableCache.find(CB);
    if (hit != vtableCache.end())
      return hit->second;
    std::vector<Function *> out;
    VSlot s = vslot(CB);
    if (!s.ok) {
      vtableCache[CB] = out;
      return out;
    }
    indexVtables();
    std::unordered_set<const Value *> objs{s.obj};
    for (Instruction &I : instructions(*CB->getFunction()))
      if (auto *C = dyn_cast<CastInst>(&I))
        if (objs.count(C->getOperand(0)))
          objs.insert(&I);
    std::set<std::string> types;
    for (Instruction &I : instructions(*CB->getFunction())) {
      auto *G = dyn_cast<GetElementPtrInst>(&I);
      if (!G)
        continue;
      if (!objs.count(G->getPointerOperand()->stripPointerCasts()))
        continue;
      if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
        if (ST->hasName())
          types.insert(ST->getName().str());
    }
    for (const std::string &ty : types) {
      auto it = vtOf.find(ty);
      if (it == vtOf.end())
        continue;
      for (Function *Fn : fromVtabs(it->second, s.field, s.slot))
        if (std::find(out.begin(), out.end(), Fn) == out.end())
          out.push_back(Fn);
    }
    if (out.empty()) {
      uint64_t want = objectBytes(s.obj, CB->getFunction());
      std::vector<Function *> found;
      if (want)
        for (const auto &kv : vtOf) {
          if (typeBytes(kv.first) != want)
            continue;
          for (Function *Fn : fromVtabs(kv.second, s.field, s.slot))
            if (std::find(found.begin(), found.end(), Fn) == found.end())
              found.push_back(Fn);
        }
      // Several structs share the size. The slot names one function, or it
      // does not name the call.
      if (found.size() == 1)
        out.push_back(found[0]);
    }
    vtableCache[CB] = out;
    return out;
  }

  // The argument's dereferenceable size, through one local the function
  // reloads it from.
  uint64_t objectBytes(Value *O, Function *F) const {
    std::unordered_set<const Value *> seen;
    while (O && seen.insert(O).second) {
      if (auto *C = dyn_cast<CastInst>(O)) {
        O = C->getOperand(0);
        continue;
      }
      auto *L = dyn_cast<LoadInst>(O);
      if (!L || !F)
        break;
      auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      if (!Al)
        break;
      Value *stored = nullptr;
      for (Instruction &I : instructions(*F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
          continue;
        Value *sv = S->getValueOperand()->stripPointerCasts();
        if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
          continue;
        stored = sv;
      }
      if (!stored)
        return 0;
      O = stored;
    }
    if (!O)
      return 0;
    auto *A = dyn_cast<Argument>(O);
    if (!A || !A->hasAttribute(Attribute::Dereferenceable))
      return 0;
    return A->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
  }

  uint64_t typeBytes(const std::string &name) const {
    auto it = typeSize.find(name);
    if (it != typeSize.end())
      return it->second;
    uint64_t n = 0;
    for (Module *M : {&down, &up})
      for (StructType *ST : M->getIdentifiedStructTypes())
        if (ST->hasName() && ST->getName() == name && !ST->isOpaque() && ST->isSized()) {
          n = dl.getTypeAllocSize(ST).getFixedValue();
          break;
        }
    typeSize[name] = n;
    return n;
  }

  // The object's static type is not in the caller. Every vtable slot that
  // itself reads is a possible body of this call.
  std::vector<Function *> vtableReads(CallBase *CB) const {
    auto hit = readCache.find(CB);
    if (hit != readCache.end())
      return hit->second;
    std::vector<Function *> out;
    VSlot s = vslot(CB);
    if (!s.ok) {
      readCache[CB] = out;
      return out;
    }
    indexVtables();
    for (Function *Fn : fromVtabs(vtAll, s.field, s.slot))
      if (containsRead(Fn))
        out.push_back(Fn);
    readCache[CB] = out;
    return out;
  }

  std::vector<Function *> targetsOf(CallBase *CB) const {
    Value *Cal = CB->getCalledOperand()->stripPointerCasts();
    if (auto *A = dyn_cast<GlobalAlias>(Cal))
      if (Constant *Ali = A->getAliasee())
        Cal = Ali->stripPointerCasts();
    if (auto *F = dyn_cast<Function>(Cal)) {
      if (Function *D = define(F->getName()))
        return {D};
      return {};
    }
    Suffix s = suffix(CB->getCalledOperand());
    if (s.empty()) {
      Value *V = CB->getCalledOperand();
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
        if (auto *P = dyn_cast<PHINode>(V)) {
          Value *one = nullptr;
          bool bad = false;
          for (Value *in : P->incoming_values()) {
            if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
              continue;
            if (one && one != in) {
              bad = true;
              break;
            }
            one = in;
          }
          if (bad || !one)
            break;
          V = one;
          continue;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!A) {
            V = L->getPointerOperand();
            continue;
          }
          Value *stored = nullptr;
          for (Instruction &I : instructions(*CB->getFunction())) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || S->getPointerOperand()->stripPointerCasts() != A)
              continue;
            Value *W = S->getValueOperand();
            std::unordered_set<const Value *> walk;
            while (W && walk.insert(W).second) {
              if (auto *C = dyn_cast<CastInst>(W)) {
                W = C->getOperand(0);
                continue;
              }
              if (auto *GE = dyn_cast<GEPOperator>(W)) {
                W = GE->getPointerOperand();
                continue;
              }
              break;
            }
            if (isa<CallBase>(W))
              stored = W;
          }
          if (!stored)
            break;
          V = stored;
          continue;
        }
        if (auto *Call = dyn_cast<CallBase>(V)) {
          if (Function *C = Call->getCalledFunction())
            if (Function *D = define(C->getName()))
              s = returnsOf(D);
        }
        break;
      }
    }
    ensureSlots();
    auto it = slotAt.find(s);
    if (it != slotAt.end())
      return it->second;
    auto at = argCallTargets.find(CB);
    // A formal that callers pass a function through is that function.
    // An empty list is a call through the object, which a vtable may name.
    if (at != argCallTargets.end() && !at->second.empty())
      return at->second;
    return vtableTargets(CB);
  }

  static bool exported(const Function &F) {
    switch (F.getLinkage()) {
    case GlobalValue::ExternalLinkage:
    case GlobalValue::AvailableExternallyLinkage:
    case GlobalValue::WeakAnyLinkage:
    case GlobalValue::WeakODRLinkage:
    case GlobalValue::LinkOnceAnyLinkage:
    case GlobalValue::LinkOnceODRLinkage:
      return true;
    default:
      return false;
    }
  }

  // An export is a defined library function a caller outside the library can
  // name. The sink's own module is the callee of that library.
  std::vector<Function *> findExports() {
    std::vector<Function *> v;
    for (Function &F : down)
      if (!F.isDeclaration() && exported(F))
        v.push_back(&F);
    std::sort(v.begin(), v.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    return v;
  }

  void buildCallers() {
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (Function *T : targetsOf(CB))
          callersOf[T].push_back(&F);
      }
    });
  }

  std::unordered_set<Function *> reachSink() {
    std::unordered_set<Function *> can(sinks.begin(), sinks.end());
    std::vector<Function *> work = sinks;
    for (size_t i = 0; i < work.size(); ++i) {
      auto it = callersOf.find(work[i]);
      if (it == callersOf.end())
        continue;
      for (Function *C : it->second)
        if (can.insert(C).second)
          work.push_back(C);
    }
    return can;
  }

  std::vector<Function *> findStarts() {
    std::vector<Function *> v;
    for (Function *E : exports) {
      if (!cone.count(E))
        continue;
      bool inside = false;
      auto it = callersOf.find(E);
      if (it != callersOf.end())
        for (Function *C : it->second)
          if (cone.count(C))
            inside = true;
      if (!inside)
        v.push_back(E);
    }
    std::sort(v.begin(), v.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    return v;
  }

  struct Path {
    std::vector<Function *> fn;
    int indirect = 0;
  };

  std::vector<Path> sequences(int seqPick) {
    struct Item {
      int indirect = 0;
      size_t length = 0;
      uint64_t ord = 0;
      std::vector<Function *> fn;
      bool operator>(const Item &o) const {
        return std::tie(indirect, length, ord) > std::tie(o.indirect, o.length, o.ord);
      }
    };
    using Hop = std::pair<Function *, Function *>;
    std::set<Hop> banned;
    std::vector<Path> found;
    for (int n = 0; n <= seqPick; ++n) {
      uint64_t ticket = 0;
      std::priority_queue<Item, std::vector<Item>, std::greater<Item>> q;
      for (Function *E : starts)
        q.push(Item{0, 1, ticket++, {E}});
      std::unordered_set<Function *> expanded;
      Path best;
      bool got = false;
      while (!q.empty()) {
        Item cur = q.top();
        q.pop();
        Function *At = cur.fn.back();
        if (!expanded.insert(At).second)
          continue;
        if (std::find(sinks.begin(), sinks.end(), At) != sinks.end()) {
          best = Path{cur.fn, cur.indirect};
          got = true;
          break;
        }
        for (Instruction &I : instructions(*At)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          auto ts = targetsOf(CB);
          bool indirect = CB->getCalledFunction() == nullptr;
          for (Function *T : ts) {
            if (!cone.count(T) || T->isDeclaration())
              continue;
            if (banned.count({At, T}))
              continue;
            if (std::find(cur.fn.begin(), cur.fn.end(), T) != cur.fn.end())
              continue;
            Item nxt = cur;
            nxt.fn.push_back(T);
            nxt.length = nxt.fn.size();
            if (indirect)
              ++nxt.indirect;
            nxt.ord = ticket++;
            q.push(std::move(nxt));
          }
        }
      }
      if (!got)
        break;
      found.push_back(best);
      if (best.fn.size() >= 2)
        banned.insert({best.fn[best.fn.size() - 2], best.fn.back()});
    }
    return found;
  }

  struct Mem {
    std::unordered_map<const Value *, Loc> loc;
    std::unordered_map<const AllocaInst *, Loc> slot;
  };

  static Value *rootOf(Value *V) {
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

  // The pointer a function returns carries a formal when the return is that
  // formal, or the returned object is filled by constant-offset copies from it.
  std::optional<int> carryArg(Function *F) const {
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

  // The argument is the export object, or a constant-offset field of it.
  // A pointer loaded from that object is a different object.
  bool objectLoc(Mem &m, Value *V, Loc &out) const {
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

  // Bytes reached from Root by a constant offset. The end is the furthest
  // typed load or store, or the furthest constant-length copy, of that
  // pointer. A callee that receives the pointer contributes the same
  // accesses. A function already on the stack is a cycle. A variable index
  // covers one element. No other length is chosen.
  uint64_t pointedExtent(Function *F, Value *Root, std::unordered_set<const Function *> &stack, int depth) const {
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

  // A load yields the pointer that was stored. That pointer was taken out of a
  // field only when the stored value is itself a load. Reloading an argument
  // gives the same object back, so the next field stays in it.
  bool heldPointer(const LoadInst *L) const {
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

  // The export path of an address. A loaded pointer keeps the field it was
  // loaded from and later steps append. A variable array index stays on
  // that array. A variable struct field is not a cell.
  bool cellLoc(Mem &m, Value *V, Loc &out) const {
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

  bool locOf(Mem &m, Value *V, Loc &out) const {
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

  static bool sameSteps(const Suffix &a, const Suffix &b) {
    if (a.size() != b.size())
      return false;
    for (size_t i = 0; i < a.size(); ++i)
      if (a[i].type != b[i].type || a[i].off != b[i].off)
        return false;
    return true;
  }

  // The one pointer stored into this alloca, ignoring a null that a later
  // store replaces. Two different stores do not agree, so there is no value.
  Value *storedOnce(const AllocaInst *A) const {
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

  // The address V names: an argument or an alloca, plus the constant fields
  // walked to reach it. A load of an alloca forwards the address that was
  // saved there. A load of anything else is a pointer value, not an address.
  // A call forwards the address its summary says it returns.
  ArgRef addrIn(Function *F, Value *V) const {
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

  FnMove fnMove(Function *F) const {
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

  // The export object a pointer value names. An argument is the formal the
  // caller bound. A field address extends that formal. A load is the pointer
  // a put stored at that address. Two puts that name different objects do
  // not agree, so the load has no location.
  std::optional<Loc> valueAt(Function *F, Value *V, const Mem &m) const {
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

  void bindFormals(Mem &m, Function *F, const std::vector<std::optional<Loc>> &args) const {
    unsigned i = 0;
    for (Argument &A : F->args()) {
      if (i < args.size() && args[i])
        m.loc[&A] = *args[i];
      ++i;
    }
  }

  // Same as propagate, except a value returned by a call is a new object.
  void propagateObject(Mem &m, Function *F) const {
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

  void propagate(Mem &m, Function *F) const {
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

  bool fromFormal(Function *F, Value *V, std::unordered_map<Function *, bool> &pureCache, std::unordered_set<Function *> &stack, int &arg, Suffix &suf) const {
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

  // A function folds when every store into the export object is a constant
  // offset and every callee that receives the object is the same kind of
  // bundle. A call that does not receive the object is outside the memory.
  // edgeNext is the sequence successor: that call is the boundary, not a
  // callee to fold.
  bool summarizes(Function *F, const std::vector<std::optional<Loc>> &args, std::unordered_map<std::string, bool> &cache,
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

  // Blocks that reach the next sequence call or the sink. A callee is on
  // the slice where its blocks reach a return. A function that is not on
  // the sequence and has no return contributes no block.
  std::unordered_set<const BasicBlock *> sliceReach(Function *F, const std::vector<Function *> &seq) const {
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

  bool solve(const std::vector<Function *> &seq, raw_ostream &out) {
    solvedCells.clear();
    rels.clear();
    readBytes.clear();
    fileLen.clear();
    argFileLen.clear();
    argExtent.clear();
    pathSrc.clear();
    ptrSpan.clear();
    size_t residual = seq.size() - 1;
    std::vector<std::vector<std::optional<Loc>>> frames(seq.size());
    frames[0].resize(seq[0]->arg_size());
    for (unsigned i = 0; i < seq[0]->arg_size(); ++i)
      frames[0][i] = Loc{(int)i, {}};
    size_t mapped = 1;
    bool failed = false;
    std::set<int> files;
    std::map<Suffix, std::set<std::string>> need;
    std::map<std::pair<int, Suffix>, std::set<std::string>> keyCell;
    std::map<std::pair<int, Suffix>, std::set<std::string>> calleeAt;
    std::set<std::pair<int, Suffix>> indirectAt;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepEq;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepNe;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepStore;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepEdge;
    struct Ev {
      Instruction *at = nullptr;
      Instruction *anchor = nullptr;
      Function *fn = nullptr;
      char kind = 0;
      bool callMust = true;
      bool mustExit = true;
      std::pair<int, Suffix> cell;
      std::pair<int, Suffix> src;
      std::set<std::string> vals;
      int pred = 0;
      unsigned bits = 0;
    };
    std::map<size_t, std::vector<Ev>> stepEv;
    std::unordered_map<const Function *, std::unique_ptr<DominatorTree>> dts;
    Instruction *evAnchor = nullptr;
    bool evCallMust = true;
    std::vector<Instruction *> stepGoal(seq.size(), nullptr);
    size_t curStep = 0;
    auto domTree = [&](Function *F) -> DominatorTree & {
      auto &p = dts[F];
      if (!p)
        p = std::make_unique<DominatorTree>(*F);
      return *p;
    };
    auto dominatesBefore = [&](Instruction *I, Instruction *G) {
      if (!I || !G || I->getFunction() != G->getFunction())
        return false;
      if (I == G)
        return true;
      DominatorTree &DT = domTree(I->getFunction());
      if (!DT.dominates(I->getParent(), G->getParent()))
        return false;
      if (I->getParent() != G->getParent())
        return true;
      for (Instruction &J : *I->getParent()) {
        if (&J == G)
          return false;
        if (&J == I)
          return true;
      }
      return false;
    };
    auto dominatesReturns = [&](Instruction *I) {
      if (!I)
        return false;
      bool any = false;
      for (BasicBlock &BB : *I->getFunction()) {
        auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!R)
          continue;
        any = true;
        if (!dominatesBefore(I, R))
          return false;
      }
      return any;
    };
    std::vector<std::vector<Act>> atAct(seq.size());
    std::unordered_map<std::string, bool> sumCache;
    std::unordered_set<std::string> sumStack;

    for (size_t si = 0; si + 1 < seq.size(); ++si) {
      Function *F = seq[si];
      Function *Next = seq[si + 1];
      const std::vector<std::optional<Loc>> &at = frames[si];
      Mem m;
      bindFormals(m, F, at);
      propagate(m, F);
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        if (!noBody(CB))
          continue;
        Read rd = asRead(*CB);
        if (!rd.ok)
          continue;
        auto claim = [&](Value *V) {
          while (auto *Cast = dyn_cast<CastInst>(V))
            V = Cast->getOperand(0);
          if (auto *Open = dyn_cast<CallBase>(V)) {
            for (unsigned i = 0; i < Open->arg_size(); ++i) {
              Value *Op = Open->getArgOperand(i);
              if (!Op->getType()->isPointerTy())
                continue;
              Loc L;
              if (locOf(m, Op, L) && L.suf.empty()) {
                files.insert(L.arg);
                if (rd.len)
                  argFileLen[L.arg] = *rd.len;
              }
            }
            return;
          }
          Loc L;
          if (locOf(m, V, L) && L.suf.empty()) {
            files.insert(L.arg);
            if (rd.len)
              argFileLen[L.arg] = *rd.len;
          }
        };
        if (rd.file >= 0)
          claim(CB->getArgOperand((unsigned)rd.file));
        if (rd.handle >= 0)
          claim(CB->getArgOperand((unsigned)rd.handle));
      }
      CallBase *edge = nullptr;
      std::vector<std::optional<Loc>> nextArgs;
      std::vector<Act> nextActs;
      bool edgeLocated = false;
      bool edgeConcrete = false;
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto ts = targetsOf(CB);
        if (std::find(ts.begin(), ts.end(), Next) == ts.end())
          continue;
        if (!CB->getCalledFunction()) {
          Suffix s = suffix(CB->getCalledOperand());
          if (!s.empty())
            need[s].insert(Next->getName().str());
          Loc calleeLoc;
          if (locOf(m, CB->getCalledOperand(), calleeLoc) && !calleeLoc.suf.empty()) {
            calleeAt[{calleeLoc.arg, calleeLoc.suf}].insert(Next->getName().str());
            stepEdge[si][{calleeLoc.arg, calleeLoc.suf}].insert(Next->getName().str());
          }
          auto kit = regKeys.find(Next);
          if (kit != regKeys.end()) {
            std::vector<Value *> stack{CB->getCalledOperand()};
            std::unordered_set<Value *> seen;
            while (!stack.empty()) {
              Value *V = stack.back();
              stack.pop_back();
              if (!V || !seen.insert(V).second)
                continue;
              Loc L;
              if (locOf(m, V, L) && !L.suf.empty()) {
                keyCell[{L.arg, L.suf}].insert(kit->second.begin(), kit->second.end());
                if (kit->second.size() == 1)
                  stepEq[si][{L.arg, L.suf}].insert(*kit->second.begin());
                continue;
              }
              if (auto *C = dyn_cast<CastInst>(V)) {
                stack.push_back(C->getOperand(0));
                continue;
              }
              if (auto *P = dyn_cast<PHINode>(V)) {
                for (Value *in : P->incoming_values())
                  stack.push_back(in);
                continue;
              }
              if (auto *Ld = dyn_cast<LoadInst>(V)) {
                stack.push_back(Ld->getPointerOperand());
                continue;
              }
              if (auto *Call = dyn_cast<CallBase>(V))
                for (Value *Op : Call->args())
                  stack.push_back(Op);
            }
          }
        }
        std::vector<std::optional<Loc>> got;
        std::vector<Act> gotActs;
        bool any = false;
        bool concrete = true;
        for (Value *Op : CB->args()) {
          Act a;
          Value *bare = Op->stripPointerCasts();
          Loc L;
          if (auto *Fn = dyn_cast<Function>(bare)) {
            a.fn = Fn->getName().str();
            a.address = false;
            a.missing = false;
          } else if (auto *CI = dyn_cast<ConstantInt>(bare)) {
            if (CI->getBitWidth() <= 64) {
              a.haveInt = true;
              a.ival = CI->getSExtValue();
              a.ibits = CI->getBitWidth();
              a.address = false;
              a.missing = false;
            }
          } else if (isa<ConstantPointerNull>(bare)) {
            a.nullPtr = true;
            a.address = false;
            a.missing = false;
          } else if (locOf(m, Op, L)) {
            a.loc = L;
            auto *Ld = dyn_cast<LoadInst>(bare);
            a.address = !(Ld && Ld->getType()->isPointerTy());
            a.missing = false;
            any = true;
          }
          if (a.missing)
            concrete = false;
          got.push_back(a.loc);
          gotActs.push_back(std::move(a));
        }
        int rank = (concrete ? 2 : 0) + (any ? 1 : 0);
        int best = (edgeConcrete ? 2 : 0) + (edgeLocated ? 1 : 0);
        if (!edge || rank > best) {
          edge = CB;
          nextArgs = std::move(got);
          nextActs = std::move(gotActs);
          edgeLocated = any;
          edgeConcrete = concrete;
        }
        if (edgeConcrete && edgeLocated)
          break;
      }
      if (edge)
        stepGoal[si] = edge;
      // Fold only when the call into the next function passes cells or
      // constants and this function is a bundle of constant-offset stores.
      bool bundle = edge && edgeConcrete && summarizes(F, at, sumCache, sumStack, Next);
      if (!bundle && !failed) {
        residual = si;
        failed = true;
      }
      if (bundle && !failed) {
        out << "bundle " << F->getName() << " " << Next->getName() << "\n";
        residual = si + 1;
      }
      if (!edge)
        break;
      frames[si + 1].assign(Next->arg_size(), std::nullopt);
      for (size_t i = 0; i < nextArgs.size() && i < frames[si + 1].size(); ++i)
        frames[si + 1][i] = nextArgs[i];
      atAct[si + 1] = std::move(nextActs);
      if (atAct[si + 1].size() < Next->arg_size())
        atAct[si + 1].resize(Next->arg_size());
      mapped = si + 2;
    }
    entry = seq[residual];
    callActs.clear();
    if (residual == 0) {
      unsigned ai = 0;
      for (Argument &A : entry->args()) {
        Act a;
        if (A.getType()->isPointerTy()) {
          a.loc = Loc{(int)ai, {}};
          a.address = true;
          a.missing = false;
        } else if (A.getType()->isIntegerTy()) {
          a.address = false;
        } else {
          a.nullPtr = true;
          a.address = false;
          a.missing = false;
        }
        callActs.push_back(std::move(a));
        ++ai;
      }
    } else {
      callActs = atAct[residual];
      if (callActs.size() < entry->arg_size())
        callActs.resize(entry->arg_size());
    }
    if (residual < seq.size())
      out << "residual " << seq[residual]->getName() << " " << pretty(seq[residual]->getName()) << "\n";
    for (int a : files) {
      out << "file arg" << a;
      auto it = argFileLen.find(a);
      if (it != argFileLen.end())
        out << " " << it->second;
      out << "\n";
    }
    Mem top;
    bindFormals(top, seq[0], {});
    for (unsigned i = 0; i < seq[0]->arg_size(); ++i)
      top.loc[seq[0]->getArg(i)] = Loc{(int)i, {}};
    propagate(top, seq[0]);
    std::set<std::pair<int, Suffix>> cells;
    std::set<std::pair<int, Suffix>> pathCell;
    std::set<std::pair<int, Suffix>> ptrHold;
    std::set<std::pair<int, Suffix>> pathAt;
    std::set<std::pair<int, Suffix>> pathPtr;
    std::map<std::pair<int, Suffix>, unsigned> wide;
    std::map<std::pair<int, Suffix>, FunctionType *> fileCell;
    std::map<std::pair<int, Suffix>, std::set<std::string>> cmps;
    std::map<std::pair<int, Suffix>, std::set<std::string>> neq;
    std::map<std::pair<int, Suffix>, std::set<std::string>> seqStore;
    std::unordered_set<std::string> walked;
    std::function<void(Function *, const std::vector<std::optional<Loc>> &)> walk = [&](Function *F, const std::vector<std::optional<Loc>> &args) {
      Mem m;
      bindFormals(m, F, args);
      propagate(m, F);
      auto reach = sliceReach(F, seq);
      for (Instruction &I : instructions(*F)) {
        if (!reach.count(I.getParent()))
          continue;
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          Loc cell;
          if (locOf(m, S->getPointerOperand(), cell) && !cell.suf.empty()) {
            cells.insert({cell.arg, cell.suf});
            Ev ev;
            ev.at = S;
            ev.fn = F;
            ev.kind = 's';
            ev.cell = {cell.arg, cell.suf};
            if (auto *CI = dyn_cast<ConstantInt>(S->getValueOperand())) {
              seqStore[{cell.arg, cell.suf}].insert(dec(CI));
              stepStore[curStep][{cell.arg, cell.suf}].insert(dec(CI));
              ev.vals.insert(dec(CI));
              stepEv[curStep].push_back(std::move(ev));
            } else if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
              if (Function *D = define(Fn->getName()))
                Fn = D;
              if (!Fn->isDeclaration()) {
                stepStore[curStep][{cell.arg, cell.suf}].insert(Fn->getName().str());
                ev.vals.insert(Fn->getName().str());
                stepEv[curStep].push_back(std::move(ev));
              }
            } else if (auto *Ld = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts())) {
              Loc src;
              if (locOf(m, Ld->getPointerOperand(), src) && !src.suf.empty()) {
                cells.insert({src.arg, src.suf});
                ev.kind = 'c';
                ev.src = {src.arg, src.suf};
                stepEv[curStep].push_back(std::move(ev));
              }
            }
          }
        }
        if (auto *L = dyn_cast<LoadInst>(&I)) {
          Loc cell;
          if (locOf(m, L->getPointerOperand(), cell) && !cell.suf.empty() && cells.count({cell.arg, cell.suf}))
            wide[{cell.arg, cell.suf}] = (unsigned)dl.getTypeStoreSize(L->getType()).getFixedValue();
        }
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          Copy copied = fixedCopy(*CB);
          if (copied.ok && !CB->getType()->isIntegerTy() && copied.len > dl.getPointerSize(0) * 2) {
            Loc dst, src;
            if (locOf(m, CB->getArgOperand(copied.dst), dst) && locOf(m, CB->getArgOperand(copied.src), src) &&
                !dst.suf.empty() && !src.suf.empty()) {
              cells.insert({dst.arg, dst.suf});
              cells.insert({src.arg, src.suf});
              Ev ev;
              ev.at = CB;
              ev.fn = F;
              ev.kind = 'c';
              ev.cell = {dst.arg, dst.suf};
              ev.src = {src.arg, src.suf};
              stepEv[curStep].push_back(std::move(ev));
            }
          }
          Read rd = asRead(*CB);
          if (rd.ok && noBody(CB) && !CB->getCalledFunction()) {
            Loc cell;
            if (locOf(m, CB->getCalledOperand(), cell) && !cell.suf.empty() && cells.count({cell.arg, cell.suf})) {
              fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
              if (rd.len)
                fileLen[{cell.arg, cell.suf}] = *rd.len;
            }
          }
        }
      }
    };
    for (const auto &kv : keyCell)
      cells.insert(kv.first);
    for (const auto &kv : calleeAt)
      cells.insert(kv.first);
    std::vector<Mem> mems(seq.size());
    std::vector<char> memReady(seq.size(), 0);
    auto memAt = [&](size_t si) -> Mem & {
      if (!memReady[si]) {
        bindFormals(mems[si], seq[si], frames[si]);
        propagate(mems[si], seq[si]);
        memReady[si] = 1;
      }
      return mems[si];
    };
    std::set<std::pair<int, Suffix>> indexed;
    auto varIndex = [](Value *V) {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        auto *G = dyn_cast<GEPOperator>(V);
        if (!G) {
          if (auto *L = dyn_cast<LoadInst>(V)) {
            V = L->getPointerOperand();
            continue;
          }
          break;
        }
        if (!G->hasAllConstantIndices() && !isa<StructType>(G->getSourceElementType()))
          return true;
        V = G->getPointerOperand();
      }
      return false;
    };
    std::vector<std::unordered_set<const Value *>> seen(seq.size());
    std::function<void(size_t, Value *)> trace = [&](size_t si, Value *V) {
      if (!V || si >= seq.size() || !seen[si].insert(V).second)
        return;
      if (auto *G = dyn_cast<GEPOperator>(V))
        for (Value *Idx : G->indices())
          if (!isa<Constant>(Idx))
            trace(si, Idx);
      Loc cell;
      if (cellLoc(memAt(si), V, cell) && !cell.suf.empty()) {
        cells.insert({cell.arg, cell.suf});
        if (varIndex(V))
          indexed.insert({cell.arg, cell.suf});
        return;
      }
      if (auto *C = dyn_cast<CastInst>(V)) {
        trace(si, C->getOperand(0));
        return;
      }
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        trace(si, G->getPointerOperand());
        return;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        trace(si, L->getPointerOperand());
        return;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        for (Value *in : P->incoming_values())
          trace(si, in);
        return;
      }
      if (auto *A = dyn_cast<Argument>(V)) {
        unsigned ai = A->getArgNo();
        if (ai < frames[si].size() && frames[si][ai] && !frames[si][ai]->suf.empty()) {
          cells.insert({frames[si][ai]->arg, frames[si][ai]->suf});
          if (varIndex(V))
            indexed.insert({frames[si][ai]->arg, frames[si][ai]->suf});
          return;
        }
        if (si == 0)
          return;
        for (Instruction &I : instructions(*seq[si - 1])) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          auto ts = targetsOf(CB);
          if (std::find(ts.begin(), ts.end(), seq[si]) == ts.end())
            continue;
          if (ai < CB->arg_size())
            trace(si - 1, CB->getArgOperand(ai));
        }
        return;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        if (noBody(CB)) {
          Read rd = asRead(*CB);
          if (rd.ok && rd.file >= 0) {
            Loc L;
            if (cellLoc(memAt(si), CB->getArgOperand((unsigned)rd.file), L) && L.suf.empty())
              files.insert(L.arg);
          }
        }
        Function *C = CB->getCalledFunction();
        if (C) {
          if (Function *D = define(C->getName())) {
            auto a = carryArg(D);
            if (a && *a >= 0 && *a < (int)CB->arg_size())
              trace(si, CB->getArgOperand((unsigned)*a));
          }
        }
        for (Value *Op : CB->args())
          if (Op->getType()->isPointerTy())
            trace(si, Op);
      }
    };
    for (size_t si = 0; si < seq.size(); ++si) {
      bool hasSink = false;
      for (Instruction &I : instructions(*seq[si]))
        if (sinkHere(I, sinkFile, sinkLine))
          hasSink = true;
      if (!hasSink)
        continue;
      for (Instruction &I : instructions(*seq[si])) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        for (Value *Op : I.operands())
          trace(si, Op);
      }
    }
    // The sink address may be a buffer filled by a read on the sequence.
    // That read's bytes are this cell. The file argument, or the callee of
    // an indirect read, is the input.
    std::set<std::pair<size_t, const Value *>> bufs;
    std::vector<std::unordered_set<const Value *>> bufSeen(seq.size());
    auto putCell = [&](int arg, Suffix suf, const std::vector<Step> &towardUse, Value *from) {
      suf.insert(suf.end(), towardUse.begin(), towardUse.end());
      if (suf.empty())
        return;
      cells.insert({arg, suf});
      if (varIndex(from))
        indexed.insert({arg, suf});
    };
    bool holdPtr = false;
    std::function<void(size_t, Value *, std::vector<Step>)> buffers =
        [&](size_t si, Value *V, std::vector<Step> towardUse) {
          if (!V || si >= seq.size() || !bufSeen[si].insert(V).second)
            return;
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            Loc cell;
            if (cellLoc(memAt(si), V, cell) && !cell.suf.empty()) {
              if (holdPtr)
                ptrHold.insert({cell.arg, cell.suf});
              putCell(cell.arg, cell.suf, towardUse, V);
              return;
            }
            std::vector<Step> next = towardUse;
            if (G->hasAllConstantIndices()) {
              APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
              if (G->accumulateConstantOffset(dl, off))
                if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
                  if (ST->hasName())
                    next.insert(next.begin(), Step{ST->getName().str(), off.getSExtValue(), false});
            } else if (isa<StructType>(G->getSourceElementType())) {
              return;
            }
            buffers(si, G->getPointerOperand(), next);
            return;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            std::vector<Step> next = towardUse;
            if (L->getType()->isPointerTy() && !next.empty())
              next[0].deref = true;
            Loc cell;
            if (cellLoc(memAt(si), L->getPointerOperand(), cell) && !cell.suf.empty()) {
              if (L->getType()->isPointerTy() && next.empty())
                ptrHold.insert({cell.arg, cell.suf});
              putCell(cell.arg, cell.suf, next, V);
              return;
            }
            bool prevHold = holdPtr;
            if (L->getType()->isPointerTy() && next.empty())
              holdPtr = true;
            buffers(si, L->getPointerOperand(), next);
            holdPtr = prevHold;
            return;
          }
          if (auto *P = dyn_cast<PHINode>(V)) {
            for (Value *in : P->incoming_values())
              buffers(si, in, towardUse);
            return;
          }
          if (auto *Al = dyn_cast<AllocaInst>(V)) {
            bufs.insert({si, Al});
            bool stored = false;
            for (Instruction &SI : instructions(*seq[si])) {
              auto *S = dyn_cast<StoreInst>(&SI);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              stored = true;
              buffers(si, sv, towardUse);
            }
            if (stored)
              return;
            // The call wrote the object through this pointer. The object's
            // bytes are the call's other pointer arguments, at their own address.
            for (Instruction &SI : instructions(*seq[si])) {
              auto *CB = dyn_cast<CallBase>(&SI);
              if (!CB)
                continue;
              bool outp = false;
              for (Value *Op : CB->args())
                if (Op->stripPointerCasts() == Al)
                  outp = true;
              if (!outp)
                continue;
              for (Value *Op : CB->args()) {
                if (!Op->getType()->isPointerTy() || Op->stripPointerCasts() == Al)
                  continue;
                buffers(si, Op, {});
              }
            }
            return;
          }
          if (auto *A = dyn_cast<Argument>(V)) {
            bufs.insert({si, A});
            if (si == 0) {
              putCell((int)A->getArgNo(), {}, towardUse, V);
              return;
            }
            if (A->getArgNo() < frames[si].size() && frames[si][A->getArgNo()]) {
              const Loc &base = *frames[si][A->getArgNo()];
              putCell(base.arg, base.suf, towardUse, V);
              return;
            }
            for (Instruction &I : instructions(*seq[si - 1])) {
              auto *CB = dyn_cast<CallBase>(&I);
              if (!CB)
                continue;
              auto ts = targetsOf(CB);
              if (std::find(ts.begin(), ts.end(), seq[si]) == ts.end())
                continue;
              if (A->getArgNo() < CB->arg_size())
                buffers(si - 1, CB->getArgOperand(A->getArgNo()), towardUse);
            }
            return;
          }
          if (auto *CB = dyn_cast<CallBase>(V)) {
            for (Value *Op : CB->args())
              if (Op->getType()->isPointerTy())
                buffers(si, Op, {});
            return;
          }
          bufs.insert({si, V});
        };
    for (size_t si = 0; si < seq.size(); ++si) {
      for (Instruction &I : instructions(*seq[si])) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        for (Value *Op : I.operands())
          buffers(si, Op, {});
      }
    }
    auto bare = [](Value *V) {
      while (V) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        auto *G = dyn_cast<GEPOperator>(V);
        if (!G)
          break;
        V = G->getPointerOperand();
      }
      return V;
    };
    for (size_t si = 0; si < seq.size(); ++si) {
      for (Instruction &I : instructions(*seq[si])) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto hit = [&](unsigned arg) {
          if (arg >= CB->arg_size() || !CB->getArgOperand(arg)->getType()->isPointerTy())
            return false;
          const Value *B = bare(CB->getArgOperand(arg));
          return B && bufs.count({si, B});
        };
        Copy copied = fixedCopy(*CB);
        if (copied.ok) {
          if (hit(copied.dst))
            buffers(si, CB->getArgOperand(copied.src), {});
          continue;
        }
        if (!noBody(CB))
          continue;
        Read rd = asRead(*CB);
        if (!rd.ok || !hit(rd.buf))
          continue;
        auto keepLen = [&](const std::pair<int, Suffix> &key) {
          if (!rd.len)
            return;
          auto it = fileLen.find(key);
          if (it != fileLen.end() && it->second != *rd.len)
            fileLen.erase(it);
          else
            fileLen[key] = *rd.len;
        };
        if (!CB->getCalledFunction()) {
          Loc cell;
          if (!cellLoc(memAt(si), CB->getCalledOperand(), cell) || cell.suf.empty())
            continue;
          cells.insert({cell.arg, cell.suf});
          fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
          keepLen({cell.arg, cell.suf});
          continue;
        }
        if (rd.file >= 0) {
          Loc L;
          if (cellLoc(memAt(si), CB->getArgOperand((unsigned)rd.file), L)) {
            if (L.suf.empty()) {
              files.insert(L.arg);
              if (rd.len)
                argFileLen[L.arg] = *rd.len;
            } else {
              cells.insert({L.arg, L.suf});
              keepLen({L.arg, L.suf});
            }
          }
        }
      }
    }
    // The path condition of this sequence. A branch outcome is required when
    // it is the only successor that reaches the next call, or the sink. The
    // equality of a constant-offset load and a constant is that cell's
    // equation. A direct callee reached with the export object contributes
    // the outcomes that are the only successor of a return. A pointer the
    // path dereferences is a cell; its pointee stays symbolic.
    {
      std::unordered_set<const Function *> didCallee;
      std::function<void(Function *, const std::vector<std::optional<Loc>> &, const std::unordered_set<Instruction *> &, bool, Function *)>
          pathFacts;
      pathFacts = [&](Function *F, const std::vector<std::optional<Loc>> &args, const std::unordered_set<Instruction *> &goals,
                      bool enterCallee, Function *reachTo) {
        if (!F || F->isDeclaration() || goals.empty())
          return;
        std::unordered_set<const BasicBlock *> reach;
        std::vector<const BasicBlock *> stack;
        for (Instruction *g : goals)
          if (g)
            stack.push_back(g->getParent());
        while (!stack.empty()) {
          const BasicBlock *BB = stack.back();
          stack.pop_back();
          if (!BB || !reach.insert(BB).second)
            continue;
          for (const BasicBlock *P : predecessors(BB))
            stack.push_back(P);
        }
        Mem m;
        bindFormals(m, F, args);
        propagateObject(m, F);
        auto locate = [&](Value *V, Loc &cell) -> bool {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(V);
          if (!L)
            return false;
          return objectLoc(m, L->getPointerOperand(), cell) && !cell.suf.empty();
        };
        auto keep = [&](const Loc &cell) { pathCell.insert({cell.arg, cell.suf}); cells.insert({cell.arg, cell.suf}); };
        Instruction *factAt = nullptr;
        Instruction *myAnchor = evAnchor;
        bool myMust = evCallMust;
        auto noteFact = [&](const Loc &cell, char kind, const std::string &v) {
          if (!factAt)
            return;
          Ev ev;
          ev.at = factAt;
          ev.fn = F;
          ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
          ev.callMust = myMust;
          ev.mustExit = F == seq[curStep] || dominatesReturns(factAt);
          ev.kind = kind;
          ev.cell = {cell.arg, cell.suf};
          ev.vals.insert(v);
          stepEv[curStep].push_back(std::move(ev));
        };
        auto equation = [&](const Loc &cell, std::string v) {
          keep(cell);
          noteFact(cell, 'e', v);
          stepEq[curStep][{cell.arg, cell.suf}].insert(v);
          cmps[{cell.arg, cell.suf}].insert(std::move(v));
        };
        auto pointee = [&](const Loc &cell) {
          auto it = cmps.find({cell.arg, cell.suf});
          if (it != cmps.end() && it->second.size() == 1 && it->second.count("0"))
            return;
          keep(cell);
          Loc child = cell;
          child.suf.push_back(Step{"", 0, true});
          keep(child);
        };
        auto onCmp = [&](ICmpInst *Cmp, ICmpInst::Predicate pred) {
          Value *lhs = Cmp->getOperand(0);
          Value *rhs = Cmp->getOperand(1);
          while (auto *C = dyn_cast<CastInst>(lhs))
            lhs = C->getOperand(0);
          while (auto *C = dyn_cast<CastInst>(rhs))
            rhs = C->getOperand(0);
          Loc L, R;
          bool lc = locate(lhs, L);
          bool rc = locate(rhs, R);
          Constant *CL = nullptr;
          Constant *CR = nullptr;
          if (isa<ConstantInt>(lhs) || isa<ConstantPointerNull>(lhs))
            CL = cast<Constant>(lhs);
          if (isa<ConstantInt>(rhs) || isa<ConstantPointerNull>(rhs))
            CR = cast<Constant>(rhs);
          unsigned bits = 64;
          if (auto *IT = dyn_cast<IntegerType>(Cmp->getOperand(0)->getType()))
            bits = IT->getBitWidth();
          auto push = [&](const Loc &cell, char kind, ICmpInst::Predicate p, const std::string &k, const Loc *other) {
            if (!factAt)
              return;
            keep(cell);
            if (other)
              keep(*other);
            Ev ev;
            ev.at = factAt;
            ev.fn = F;
            ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
            ev.callMust = myMust;
            ev.mustExit = F == seq[curStep] || dominatesReturns(factAt);
            ev.kind = kind;
            ev.pred = (int)p;
            ev.bits = bits;
            ev.cell = {cell.arg, cell.suf};
            if (other)
              ev.src = {other->arg, other->suf};
            else if (!k.empty())
              ev.vals.insert(k);
            stepEv[curStep].push_back(std::move(ev));
          };
          if (lc && rc && !CL && !CR) {
            push(L, 'p', pred, "", &R);
            return;
          }
          Loc cell;
          Constant *C = nullptr;
          ICmpInst::Predicate use = pred;
          if (CR && lc) {
            cell = L;
            C = CR;
          } else if (CL && rc) {
            cell = R;
            C = CL;
            use = ICmpInst::getSwappedPredicate(pred);
          } else
            return;
          if (isa<ConstantPointerNull>(C)) {
            if (use == ICmpInst::ICMP_EQ)
              equation(cell, "0");
            else if (use == ICmpInst::ICMP_NE)
              pointee(cell);
            else
              push(cell, 'r', use, "0", nullptr);
            return;
          }
          std::string k = dec(cast<ConstantInt>(C));
          if (use == ICmpInst::ICMP_EQ)
            equation(cell, k);
          else if (use == ICmpInst::ICMP_NE) {
            keep(cell);
            noteFact(cell, 'n', k);
            stepNe[curStep][{cell.arg, cell.suf}].insert(k);
            neq[{cell.arg, cell.suf}].insert(k);
          } else
            push(cell, 'r', use, k, nullptr);
        };
        for (const BasicBlock *CBB : reach) {
          BasicBlock *BB = const_cast<BasicBlock *>(CBB);
          Instruction *Term = BB->getTerminator();
          auto *BR = dyn_cast<BranchInst>(Term);
          if (BR && BR->isConditional()) {
            BasicBlock *only = nullptr;
            int n = 0;
            for (BasicBlock *S : successors(BR))
              if (reach.count(S)) {
                ++n;
                only = S;
              }
            if (n == 1) {
              factAt = BR;
              bool takenTrue = only == BR->getSuccessor(0);
              std::function<void(Value *, bool)> req = [&](Value *V, bool need) {
                while (auto *C = dyn_cast<CastInst>(V))
                  V = C->getOperand(0);
                if (auto *BO = dyn_cast<BinaryOperator>(V)) {
                  if (BO->getOpcode() == Instruction::Xor)
                    if (auto *One = dyn_cast<ConstantInt>(BO->getOperand(1)))
                      if (One->isOne()) {
                        req(BO->getOperand(0), !need);
                        return;
                      }
                  if (need && BO->getOpcode() == Instruction::And) {
                    req(BO->getOperand(0), true);
                    req(BO->getOperand(1), true);
                    return;
                  }
                  if (!need && BO->getOpcode() == Instruction::Or) {
                    req(BO->getOperand(0), false);
                    req(BO->getOperand(1), false);
                    return;
                  }
                }
                if (auto *Cmp = dyn_cast<ICmpInst>(V)) {
                  auto pred = Cmp->getPredicate();
                  if (!need)
                    pred = Cmp->getInversePredicate();
                  onCmp(Cmp, pred);
                }
              };
              req(BR->getCondition(), takenTrue);
            }
          }
          if (auto *SW = dyn_cast<SwitchInst>(Term)) {
            ConstantInt *onlyV = nullptr;
            int n = 0;
            bool def = reach.count(SW->getDefaultDest());
            if (def)
              ++n;
            for (auto &Case : SW->cases())
              if (reach.count(Case.getCaseSuccessor())) {
                ++n;
                onlyV = Case.getCaseValue();
              }
            Loc cell;
            if (n == 1 && onlyV && !def && locate(SW->getCondition(), cell)) {
              factAt = SW;
              equation(cell, dec(onlyV));
            }
          }
        }
        // An indirect call on the slice reads one cell. The value is the one
        // function that call can reach the next sequence function through.
        // A vtable call is the vtable, recorded where the object is loaded.
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB || CB->getCalledFunction() || !vtableTargets(CB).empty())
              continue;
            Loc cell;
            if (!cellLoc(m, CB->getCalledOperand(), cell) || cell.suf.empty())
              continue;
            keep(cell);
            indirectAt.insert({cell.arg, cell.suf});
            auto &slot = calleeAt[{cell.arg, cell.suf}];
            bool edge = false;
            std::vector<Function *> reachHits;
            for (Function *T : targetsOf(CB)) {
              if (!T || T->isDeclaration())
                continue;
              if (reachTo && T == reachTo)
                edge = true;
              else if (reachTo && reachesFn(T, reachTo))
                reachHits.push_back(T);
            }
            if (edge && reachTo)
              slot.insert(reachTo->getName().str());
            else if (!reachHits.empty()) {
              for (Function *T : reachHits)
                slot.insert(T->getName().str());
            }
            if (!slot.empty()) {
              stepEdge[curStep][{cell.arg, cell.suf}] = slot;
              Ev ev;
              ev.at = CB;
              ev.fn = F;
              ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
              ev.callMust = myMust;
              ev.mustExit = F == seq[curStep] || dominatesReturns(CB);
              ev.kind = 'g';
              ev.cell = {cell.arg, cell.suf};
              ev.vals = slot;
              stepEv[curStep].push_back(std::move(ev));
            }
          }
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *L = dyn_cast<LoadInst>(&I);
            if (!L || !L->getType()->isPointerTy())
              continue;
            auto asAddr = [](const User *U, const Value *P) {
              if (auto *Ld = dyn_cast<LoadInst>(U))
                return Ld->getPointerOperand() == P;
              if (auto *S = dyn_cast<StoreInst>(U))
                return S->getPointerOperand() == P;
              if (auto *G = dyn_cast<GetElementPtrInst>(U))
                return G->getPointerOperand() == P;
              return false;
            };
            bool used = false;
            bool passed = false;
            for (const User *U : L->users()) {
              if (asAddr(U, L))
                used = true;
              if (isa<CallBase>(U))
                passed = true;
              if (auto *C = dyn_cast<CastInst>(U))
                for (const User *U2 : C->users()) {
                  if (asAddr(U2, C))
                    used = true;
                  if (isa<CallBase>(U2))
                    passed = true;
                }
            }
            if (!used && !passed)
              continue;
            Loc cell;
            if (!cellLoc(m, L, cell) || cell.suf.empty())
              continue;
            std::unordered_set<const Function *> seenF;
            uint64_t n = pointedExtent(F, L, seenF, 0);
            if (!used && n == 0)
              continue;
            pointee(cell);
            if (n == 0)
              continue;
            Loc child = cell;
            child.suf.push_back(Step{"", 0, true});
            auto key = std::make_pair(child.arg, child.suf);
            auto it = readBytes.find(key);
            if (it == readBytes.end() || it->second < n)
              readBytes[key] = n;
          }
        if (!enterCallee)
          return;
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            if (!Cal || ignorable(Cal))
              continue;
            Function *D = define(Cal->getName());
            if (!D || D->isDeclaration())
              continue;
            std::vector<std::optional<Loc>> down;
            bool touch = false;
            for (Value *Op : CB->args()) {
              Loc L;
              if (objectLoc(m, Op, L)) {
                down.push_back(L);
                touch = true;
              } else
                down.push_back(std::nullopt);
            }
            if (!touch || !didCallee.insert(D).second)
              continue;
            std::unordered_set<Instruction *> rets;
            for (BasicBlock &RBB : *D)
              if (auto *R = dyn_cast<ReturnInst>(RBB.getTerminator()))
                rets.insert(R);
            Instruction *savedA = evAnchor;
            bool savedM = evCallMust;
            if (F == seq[curStep]) {
              evAnchor = CB;
              evCallMust = true;
            } else
              evCallMust = myMust && dominatesReturns(CB);
            pathFacts(D, down, rets, true, reachTo);
            evAnchor = savedA;
            evCallMust = savedM;
          }
      };
      for (size_t si = 0; si < mapped && si < seq.size(); ++si) {
        std::unordered_set<Instruction *> goals;
        if (si + 1 < seq.size())
          for (Instruction &I : instructions(*seq[si])) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            auto ts = targetsOf(CB);
            if (std::find(ts.begin(), ts.end(), seq[si + 1]) != ts.end())
              goals.insert(&I);
          }
        for (Instruction &I : instructions(*seq[si]))
          if (sinkHere(I, sinkFile, sinkLine))
            goals.insert(&I);
        curStep = si;
        evAnchor = nullptr;
        evCallMust = true;
        Function *reachTo = si + 1 < seq.size() ? seq[si + 1] : seq[si];
        pathFacts(seq[si], frames[si], goals, true, reachTo);
      }
    }
    for (size_t i = 0; i < mapped && i < seq.size(); ++i) {
      curStep = i;
      walk(seq[i], frames[i]);
    }
    // A direct callee reached with the export object contributes its
    // constant stores. Its constant-offset reads set the object size.
    // A store through a loaded pointer writes the cell those bytes belong to.
    // The bundle still folds only constant-offset stores of the export object.
    std::function<void(Function *, const std::vector<std::optional<Loc>> &, Instruction *, bool)> noteCallee =
        [&](Function *F, const std::vector<std::optional<Loc>> &args, Instruction *anchor, bool callMust) {
          Mem m;
          bindFormals(m, F, args);
          propagateObject(m, F);
          auto located = [&](Value *Ptr, Loc &cell) {
            return objectLoc(m, Ptr, cell) && !cell.suf.empty();
          };
          auto grow = [&](Value *Ptr, uint64_t n) {
            Loc cell;
            if (!located(Ptr, cell) || n == 0)
              return;
            auto it = readBytes.find({cell.arg, cell.suf});
            if (it == readBytes.end() || it->second < n)
              readBytes[{cell.arg, cell.suf}] = n;
            if (cell.suf.size() == 1) {
              uint64_t end = (uint64_t)cell.suf[0].off + n;
              auto at = argExtent.find(cell.arg);
              if (at == argExtent.end() || at->second < end)
                argExtent[cell.arg] = end;
            }
          };
          auto reach = sliceReach(F, seq);
          for (Instruction &I : instructions(*F)) {
            if (!reach.count(I.getParent()))
              continue;
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              grow(S->getPointerOperand(), dl.getTypeStoreSize(S->getValueOperand()->getType()).getFixedValue());
              Loc cell;
              if (located(S->getPointerOperand(), cell)) {
                cells.insert({cell.arg, cell.suf});
                Ev ev;
                ev.at = S;
                ev.fn = F;
                ev.anchor = F == seq[curStep] ? nullptr : anchor;
                ev.callMust = callMust;
                ev.mustExit = F == seq[curStep] || dominatesReturns(S);
                ev.cell = {cell.arg, cell.suf};
                ev.kind = 's';
                if (auto *CI = dyn_cast<ConstantInt>(S->getValueOperand())) {
                  seqStore[{cell.arg, cell.suf}].insert(dec(CI));
                  stepStore[curStep][{cell.arg, cell.suf}].insert(dec(CI));
                  ev.vals.insert(dec(CI));
                  if (F != seq[curStep])
                    stepEv[curStep].push_back(std::move(ev));
                } else if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
                  if (Function *D = define(Fn->getName()))
                    Fn = D;
                  if (!Fn->isDeclaration()) {
                    stepStore[curStep][{cell.arg, cell.suf}].insert(Fn->getName().str());
                    ev.vals.insert(Fn->getName().str());
                    if (F != seq[curStep])
                      stepEv[curStep].push_back(std::move(ev));
                  }
                } else if (auto *Ld = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts())) {
                  Loc src;
                  if (located(Ld->getPointerOperand(), src)) {
                    cells.insert({src.arg, src.suf});
                    ev.kind = 'c';
                    ev.src = {src.arg, src.suf};
                    if (F != seq[curStep])
                      stepEv[curStep].push_back(std::move(ev));
                  }
                }
              }
            }
            if (auto *L = dyn_cast<LoadInst>(&I))
              grow(L->getPointerOperand(), dl.getTypeStoreSize(L->getType()).getFixedValue());
            if (auto *CB = dyn_cast<CallBase>(&I)) {
              Copy copied = fixedCopy(*CB);
              // An integer result is computed from the arguments. It is not
              // a copy of copied.len bytes, so it does not size the object.
              if (copied.ok && !CB->getType()->isIntegerTy()) {
                grow(CB->getArgOperand(copied.src), copied.len);
                grow(CB->getArgOperand(copied.dst), copied.len);
                if (copied.len > dl.getPointerSize(0) * 2) {
                  Loc dst, src;
                  if (located(CB->getArgOperand(copied.dst), dst) && located(CB->getArgOperand(copied.src), src)) {
                    cells.insert({dst.arg, dst.suf});
                    cells.insert({src.arg, src.suf});
                    Ev ev;
                    ev.at = CB;
                    ev.fn = F;
                    ev.anchor = F == seq[curStep] ? nullptr : anchor;
                    ev.callMust = callMust;
                    ev.mustExit = F == seq[curStep] || dominatesReturns(CB);
                    ev.kind = 'c';
                    ev.cell = {dst.arg, dst.suf};
                    ev.src = {src.arg, src.suf};
                    if (F != seq[curStep])
                      stepEv[curStep].push_back(std::move(ev));
                  }
                }
              }
              Function *C = CB->getCalledFunction();
              if (C && !C->isDeclaration()) {
                std::vector<std::optional<Loc>> downArgs;
                bool touch = false;
                for (Value *Op : CB->args()) {
                  Loc L;
                  if (objectLoc(m, Op, L)) {
                    downArgs.push_back(L);
                    touch = true;
                  } else
                    downArgs.push_back(std::nullopt);
                }
                if (touch) {
                  std::string sg = C->getName().str();
                  for (const auto &a : downArgs) {
                    sg.push_back('|');
                    if (!a) {
                      sg.push_back('-');
                      continue;
                    }
                    sg += std::to_string(a->arg);
                    for (const Step &st : a->suf)
                      sg += ":" + st.type + "+" + std::to_string(st.off);
                  }
                  if (walked.insert(sg).second) {
                    Instruction *childAnchor = F == seq[curStep] ? CB : anchor;
                    bool childMust = F == seq[curStep] || (callMust && dominatesReturns(CB));
                    noteCallee(C, downArgs, childAnchor, childMust);
                  }
                }
              }
              if (!C) {
                Read rd = asRead(*CB);
                Loc cell;
                if (rd.ok && noBody(CB) && located(CB->getCalledOperand(), cell) && cells.count({cell.arg, cell.suf})) {
                  fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
                  if (rd.len)
                    fileLen[{cell.arg, cell.suf}] = *rd.len;
                }
              }
            }
          }
        };
    for (size_t i = 0; i < mapped && i < seq.size(); ++i) {
      curStep = i;
      noteCallee(seq[i], frames[i], nullptr, true);
    }
    // open produced the read's handle. The pointer it passes is the file
    // path when those bytes are a cell, including through a fixed copy and
    // the object a call returns.
    {
      struct Site {
        Function *caller = nullptr;
        CallBase *cb = nullptr;
      };
      std::map<Function *, std::vector<Site>> sites;
      std::map<Function *, const std::vector<std::optional<Loc>> *> frameOf;
      for (size_t i = 0; i < mapped && i < seq.size(); ++i)
        frameOf[seq[i]] = &frames[i];
      std::vector<std::pair<Function *, int>> q;
      std::unordered_set<Function *> seenFn;
      for (size_t i = 0; i < mapped && i < seq.size(); ++i)
        q.push_back({seq[i], 0});
      for (size_t qi = 0; qi < q.size(); ++qi) {
        Function *F = q[qi].first;
        if (!F || !seenFn.insert(F).second)
          continue;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          std::vector<Function *> ts = targetsOf(CB);
          if (ts.empty())
            ts = vtableReads(CB);
          for (Function *T : ts) {
            if (T->isDeclaration())
              continue;
            sites[T].push_back(Site{F, CB});
            q.push_back({T, 0});
          }
        }
      }
      auto baseOff = [&](Value *V, Value *&base, int64_t &off) {
        base = V;
        off = 0;
        std::unordered_set<const Value *> seen;
        while (base && seen.insert(base).second) {
          if (auto *C = dyn_cast<CastInst>(base)) {
            base = C->getOperand(0);
            continue;
          }
          auto *G = dyn_cast<GEPOperator>(base);
          if (!G)
            break;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta))
            break;
          off += delta.getSExtValue();
          base = G->getPointerOperand();
        }
        if (base)
          base = base->stripPointerCasts();
      };
      std::set<std::pair<Function *, const Value *>> stack;
      std::map<std::pair<const Function *, const Value *>, std::optional<Loc>> known;
      std::function<std::optional<Loc>(Function *, Value *, int)> find;
      std::function<std::optional<Loc>(Function *, int64_t, CallBase *, int)> fieldIn;
      find = [&](Function *F, Value *V, int depth) -> std::optional<Loc> {
        if (!F || !V)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (auto it = known.find({F, V}); it != known.end())
          return it->second;
        if (!stack.insert({F, V}).second)
          return std::nullopt;
        struct Pop {
          std::set<std::pair<Function *, const Value *>> &s;
          Function *F;
          const Value *V;
          ~Pop() { s.erase({F, V}); }
        } pop{stack, F, V};
        Value *base = nullptr;
        int64_t off = 0;
        baseOff(V, base, off);
        if (off == 0)
          if (auto *Ld = dyn_cast<LoadInst>(base)) {
            if (Ld->getType()->isPointerTy()) {
              if (auto L = find(F, Ld->getPointerOperand(), depth + 1)) {
                pathPtr.insert({L->arg, L->suf});
                return L;
              }
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              auto fr0 = frameOf.find(F);
              if (Al && fr0 != frameOf.end()) {
                for (Instruction &SI : instructions(*F)) {
                  auto *S = dyn_cast<StoreInst>(&SI);
                  if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                    continue;
                  auto *Arg = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
                  if (!Arg || Arg->getArgNo() >= fr0->second->size() || !(*fr0->second)[Arg->getArgNo()])
                    continue;
                  Loc L = *(*fr0->second)[Arg->getArgNo()];
                  if (L.suf.empty())
                    continue;
                  return L;
                }
              }
            }
          }
        auto fr = frameOf.find(F);
        if (fr != frameOf.end()) {
          Mem m;
          bindFormals(m, F, *fr->second);
          Loc L;
          if (locOf(m, V, L) && !L.suf.empty())
            return L;
        }
        if (auto *A = dyn_cast<Argument>(base)) {
          Suffix field = suffix(V);
          if (field.empty() && off != 0)
            field.push_back(Step{"", off});
          if (fr != frameOf.end() && A->getArgNo() < fr->second->size() && (*fr->second)[A->getArgNo()]) {
            Loc L = *(*fr->second)[A->getArgNo()];
            L.suf.insert(L.suf.end(), field.begin(), field.end());
            if (!L.suf.empty())
              return L;
          }
          auto sit = sites.find(F);
          if (sit != sites.end()) {
            for (const Site &s : sit->second) {
              if (A->getArgNo() >= s.cb->arg_size())
                continue;
              Value *act = s.cb->getArgOperand(A->getArgNo())->stripPointerCasts();
              if (field.empty()) {
                if (auto L = find(s.caller, act, depth + 1))
                  return L;
                continue;
              }
              if (auto *CB = dyn_cast<CallBase>(act)) {
                if (Function *D = CB->getCalledFunction())
                  if (Function *B = define(D->getName()))
                    if (auto L = fieldIn(B, off, CB, depth + 1))
                      return L;
              }
              if (auto *Arg = dyn_cast<Argument>(act)) {
                auto cfr = frameOf.find(s.caller);
                if (cfr != frameOf.end() && Arg->getArgNo() < cfr->second->size() && (*cfr->second)[Arg->getArgNo()]) {
                  Loc L = *(*cfr->second)[Arg->getArgNo()];
                  L.suf.insert(L.suf.end(), field.begin(), field.end());
                  if (!L.suf.empty())
                    return L;
                }
              }
            }
          }
        }
        if (auto *Al = dyn_cast<AllocaInst>(base)) {
          for (Instruction &I : instructions(*F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Copy copied = fixedCopy(*CB);
            if (!copied.ok)
              continue;
            Value *db = nullptr;
            int64_t doff = 0;
            baseOff(CB->getArgOperand(copied.dst), db, doff);
            if (db != Al || doff != off)
              continue;
            if (auto L = find(F, CB->getArgOperand(copied.src), depth + 1))
              return L;
          }
        }
        if (auto *CB = dyn_cast<CallBase>(base)) {
          if (Function *D = CB->getCalledFunction())
            if (Function *B = define(D->getName()))
              if (auto L = fieldIn(B, off, CB, depth + 1))
                return L;
          // A call with no body that returns a pointer yields the bytes of
          // the object it was given. That pointer is the cell.
          if (noBody(CB) && CB->getType()->isPointerTy()) {
            for (Value *Op : CB->args()) {
              if (!Op->getType()->isPointerTy())
                continue;
              if (auto L = find(F, Op, depth + 1)) {
                // Offset 0 of the object is its data pointer. A field that
                // already names the bytes stays the bytes.
                if (L->suf.size() == 1 && L->suf[0].type.empty() && L->suf[0].off == 0)
                  pathPtr.insert({L->arg, L->suf});
                return L;
              }
              auto *Arg = dyn_cast<Argument>(Op->stripPointerCasts());
              auto fr2 = frameOf.find(F);
              if (!Arg || fr2 == frameOf.end() || Arg->getArgNo() >= fr2->second->size() || !(*fr2->second)[Arg->getArgNo()])
                continue;
              Loc L = *(*fr2->second)[Arg->getArgNo()];
              if (L.suf.empty())
                continue;
              pathPtr.insert({L.arg, L.suf});
              return L;
            }
          }
        }
        if (auto *Ld = dyn_cast<LoadInst>(base)) {
          auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
          if (Al) {
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              if (auto L = find(F, S->getValueOperand(), depth + 1)) {
                known[{F, V}] = L;
                return L;
              }
            }
          }
        }
        known[{F, V}] = std::nullopt;
        return std::nullopt;
      };
      fieldIn = [&](Function *D, int64_t want, CallBase *CB, int depth) -> std::optional<Loc> {
        if (!D)
          return std::nullopt;
        std::vector<Value *> roots;
        for (BasicBlock &BB : *D) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue())
            continue;
          Value *base = nullptr;
          int64_t o = 0;
          baseOff(R->getReturnValue(), base, o);
          if (base && o == 0)
            roots.push_back(base);
        }
        for (Instruction &I : instructions(*D)) {
          auto *Call = dyn_cast<CallBase>(&I);
          if (!Call)
            continue;
          Copy copied = fixedCopy(*Call);
          if (!copied.ok)
            continue;
          Value *db = nullptr;
          int64_t doff = 0;
          baseOff(Call->getArgOperand(copied.dst), db, doff);
          if (!db || doff != want)
            continue;
          bool retObj = false;
          for (Value *r : roots)
            if (r == db)
              retObj = true;
          if (!retObj)
            continue;
          Value *src = Call->getArgOperand(copied.src);
          if (auto L = find(D, src, depth + 1))
            return L;
          Value *sb = nullptr;
          int64_t soff = 0;
          baseOff(src, sb, soff);
          auto *Arg = dyn_cast<Argument>(sb);
          if (!Arg || Arg->getArgNo() >= CB->arg_size())
            continue;
          Value *act = CB->getArgOperand(Arg->getArgNo())->stripPointerCasts();
          Suffix field = suffix(src);
          if (field.empty() && soff != 0)
            field.push_back(Step{"", soff});
          if (auto *ActArg = dyn_cast<Argument>(act)) {
            auto cfr = frameOf.find(CB->getFunction());
            if (cfr != frameOf.end() && ActArg->getArgNo() < cfr->second->size() && (*cfr->second)[ActArg->getArgNo()]) {
              Loc L = *(*cfr->second)[ActArg->getArgNo()];
              L.suf.insert(L.suf.end(), field.begin(), field.end());
              if (!L.suf.empty())
                return L;
            }
          }
          if (auto *Inner = dyn_cast<CallBase>(act)) {
            if (Function *ID = Inner->getCalledFunction())
              if (Function *IB = define(ID->getName()))
                if (auto L = fieldIn(IB, soff, Inner, depth + 1))
                  return L;
          }
        }
        return std::nullopt;
      };
      std::vector<std::pair<CallBase *, CallBase *>> opens;
      for (Function *F : seenFn) {
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || !noBody(CB))
            continue;
          Read rd = asRead(*CB);
          if (!rd.ok)
            continue;
          int slot = -1;
          if (rd.file >= 0)
            slot = (int)rd.file;
          else if (rd.handle >= 0)
            slot = (int)rd.handle;
          if (slot < 0 || (unsigned)slot >= CB->arg_size())
            continue;
          Value *H = CB->getArgOperand((unsigned)slot);
          while (auto *C = dyn_cast<CastInst>(H))
            H = C->getOperand(0);
          if (auto *Ld = dyn_cast<LoadInst>(H)) {
            auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
            if (Al) {
              for (Instruction &S : instructions(*F)) {
                auto *St = dyn_cast<StoreInst>(&S);
                if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                  H = St->getValueOperand();
              }
              while (auto *C = dyn_cast<CastInst>(H))
                H = C->getOperand(0);
            }
          }
          if (auto *P = dyn_cast<CallBase>(H->stripPointerCasts())) {
            if (noBody(P))
              opens.push_back({P, CB});
            continue;
          }
          Suffix hs = suffix(H);
          if (hs.empty())
            continue;
          for (Function *G : seenFn) {
            for (Instruction &S : instructions(*G)) {
              auto *St = dyn_cast<StoreInst>(&S);
              if (!St || suffix(St->getPointerOperand()) != hs)
                continue;
              auto *P = dyn_cast<CallBase>(St->getValueOperand()->stripPointerCasts());
              if (P && noBody(P))
                opens.push_back({P, CB});
            }
          }
        }
      }
      std::set<std::pair<Function *, const Value *>> pret;
      std::function<bool(Function *, Value *, int)> ptrRet;
      ptrRet = [&](Function *F, Value *V, int depth) -> bool {
        if (!F || !V)
          return false;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (!pret.insert({F, V}).second)
          return false;
        if (auto *CB = dyn_cast<CallBase>(V)) {
          if (!noBody(CB) || !CB->getType()->isPointerTy())
            return false;
          // The call returns a pointer into an object. A pointer into a
          // byte array is the bytes themselves.
          auto intoObject = [&](Function *Fn, Value *A) {
            while (auto *C = dyn_cast<CastInst>(A))
              A = C->getOperand(0);
            if (auto *Ld = dyn_cast<LoadInst>(A)) {
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              if (Al)
                for (Instruction &I : instructions(*Fn)) {
                  auto *S = dyn_cast<StoreInst>(&I);
                  if (S && S->getPointerOperand()->stripPointerCasts() == Al)
                    A = S->getValueOperand()->stripPointerCasts();
                }
            }
            if (auto *G = dyn_cast<GEPOperator>(A))
              return G->getResultElementType()->isStructTy();
            auto *Arg = dyn_cast<Argument>(A);
            if (!Arg)
              return false;
            auto sit = sites.find(Fn);
            if (sit == sites.end())
              return false;
            for (const Site &s : sit->second) {
              if (Arg->getArgNo() >= s.cb->arg_size())
                continue;
              Value *act = s.cb->getArgOperand(Arg->getArgNo())->stripPointerCasts();
              if (auto *G = dyn_cast<GEPOperator>(act))
                if (G->getResultElementType()->isStructTy())
                  return true;
            }
            return false;
          };
          for (Value *Op : CB->args()) {
            if (!Op->getType()->isPointerTy())
              continue;
            return intoObject(CB->getFunction(), Op);
          }
          return false;
        }
        if (auto *Ld = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
          if (!Al)
            return false;
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (S && S->getPointerOperand()->stripPointerCasts() == Al && ptrRet(F, S->getValueOperand(), depth + 1))
              return true;
          }
          return false;
        }
        auto *A = dyn_cast<Argument>(V);
        if (!A)
          return false;
        auto sit = sites.find(F);
        if (sit == sites.end())
          return false;
        for (const Site &s : sit->second) {
          if (A->getArgNo() >= s.cb->arg_size())
            continue;
          if (ptrRet(s.caller, s.cb->getArgOperand(A->getArgNo()), depth + 1))
            return true;
        }
        return false;
      };
      auto remember = [&](const FileIO &io) {
        for (const FileIO &e : fileIO)
          if (e.name == io.name && e.opener == io.opener)
            return;
        fileIO.push_back(io);
      };
      for (auto [P, R] : opens) {
        bool got = false;
        int pathArg = 0;
        for (unsigned i = 0; i < P->arg_size(); ++i) {
          Value *Op = P->getArgOperand(i);
          if (!Op->getType()->isPointerTy())
            continue;
          if (auto L = find(P->getFunction(), Op, 0)) {
            pathAt.insert({L->arg, L->suf});
            if (ptrRet(P->getFunction(), Op, 0))
              pathPtr.insert({L->arg, L->suf});
            got = true;
            pathArg = (int)i;
          }
        }
        if (!got)
          continue;
        if (Function *C = P->getCalledFunction()) {
          FileIO io;
          io.name = C->getName().str();
          io.opener = true;
          io.retPtr = P->getType()->isPointerTy();
          io.pathArg = pathArg;
          remember(io);
        }
        Read rd = asRead(*R);
        if (rd.ok)
          if (Function *C = R->getCalledFunction()) {
            FileIO io;
            io.name = C->getName().str();
            io.bufArg = (int)rd.buf;
            io.countArg = (int)rd.count;
            if (rd.file >= 0)
              for (int i = (int)rd.count + 1; i < rd.file; ++i)
                if ((unsigned)i < R->arg_size() &&
                    R->getArgOperand((unsigned)i)->getType()->isIntegerTy())
                  io.count2 = i;
            remember(io);
          }
      }
      for (const auto &c : pathAt)
        cells.insert(c);
    }
    auto tail = [](const Suffix &cell, const Suffix &store) {
      if (cell.size() != store.size())
        return false;
      for (size_t i = 0; i < cell.size(); ++i)
        if (cell[i].type != store[i].type || cell[i].off != store[i].off)
          return false;
      return true;
    };
    // A pointer loaded from a cell is an object. The function stored in a
    // slot of that object, and the pointer stored beside it, are cells.
    // A function that returns one field of the object and writes another
    // through an argument names the bytes and their length.
    {
      auto sameSuf = [](const Suffix &a, const Suffix &b) {
        if (a.size() != b.size())
          return false;
        for (size_t i = 0; i < a.size(); ++i)
          if (a[i].type != b[i].type || a[i].off != b[i].off)
            return false;
        return true;
      };
      struct Bytes {
        Suffix data;
        Suffix len;
        bool hasLen = false;
        bool ok = false;
      };
      std::unordered_map<const Function *, Bytes> byteOf;
      auto fieldsOf = [&](Function *F) -> Bytes {
        auto it = byteOf.find(F);
        if (it != byteOf.end())
          return it->second;
        Bytes b;
        if (!F || F->isDeclaration() || F->arg_empty()) {
          byteOf[F] = b;
          return b;
        }
        std::unordered_set<const Value *> th{F->getArg(0)};
        std::unordered_set<const AllocaInst *> boxes;
        for (int pass = 0; pass < 3; ++pass)
          for (Instruction &I : instructions(*F)) {
            if (auto *C = dyn_cast<CastInst>(&I))
              if (th.count(C->getOperand(0)))
                th.insert(&I);
            if (auto *S = dyn_cast<StoreInst>(&I))
              if (th.count(S->getValueOperand()->stripPointerCasts()))
                if (auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
                  boxes.insert(Al);
            if (auto *L = dyn_cast<LoadInst>(&I))
              if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
                if (boxes.count(Al))
                  th.insert(&I);
          }
        auto fieldOf = [&](Value *V) -> Suffix {
          auto *L = dyn_cast<LoadInst>(V->stripPointerCasts());
          if (!L)
            return {};
          Value *P = L->getPointerOperand()->stripPointerCasts();
          Value *base = P;
          if (auto *G = dyn_cast<GEPOperator>(base))
            base = G->getPointerOperand()->stripPointerCasts();
          if (!th.count(base))
            return {};
          return suffix(P);
        };
        for (const BasicBlock &BB : *F) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
            continue;
          Suffix d = fieldOf(R->getReturnValue());
          if (!d.empty())
            b.data = d;
        }
        if (!b.data.empty()) {
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || !S->getValueOperand()->getType()->isIntegerTy())
              continue;
            Suffix n = fieldOf(S->getValueOperand());
            if (!n.empty()) {
              b.len = n;
              b.hasLen = true;
            }
          }
          b.ok = true;
        }
        byteOf[F] = b;
        return b;
      };
      ensureSlots();
      auto addFns = [&](int arg, Suffix full, const std::vector<Function *> &fns) {
        if (fns.empty() || full.empty())
          return;
        cells.insert({arg, full});
        auto &names = calleeAt[{arg, full}];
        for (Function *Fn : fns)
          names.insert(Fn->getName().str());
      };
      for (const auto &hold : ptrHold) {
        if (pathAt.count(hold) || pathPtr.count(hold))
          continue;
        std::vector<Suffix> blobs;
        for (size_t si = 0; si < seq.size(); ++si) {
          Mem &m = memAt(si);
          for (Instruction &I : instructions(*seq[si])) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            for (unsigned i = 0; i < CB->arg_size(); ++i) {
              if (!CB->getArgOperand(i)->getType()->isPointerTy())
                continue;
              Loc L;
              if (!cellLoc(m, CB->getArgOperand(i), L) || L.arg != hold.first || !sameSuf(L.suf, hold.second))
                continue;
              Function *Cal = CB->getCalledFunction();
              if (!Cal)
                continue;
              Function *D = define(Cal->getName());
              if (!D)
                continue;
              std::vector<std::pair<Function *, unsigned>> work{{D, i}};
              std::unordered_set<Function *> seenD;
              for (size_t wi = 0; wi < work.size(); ++wi) {
                Function *Dw = work[wi].first;
                unsigned argNo = work[wi].second;
                if (!Dw || !seenD.insert(Dw).second)
                  continue;
              for (Instruction &J : instructions(*Dw)) {
                auto *IC = dyn_cast<CallBase>(&J);
                if (!IC)
                  continue;
                if (Function *N0 = IC->getCalledFunction()) {
                  Function *ND = define(N0->getName());
                  if (!ND)
                    continue;
                  for (unsigned k = 0; k < IC->arg_size() && k < ND->arg_size(); ++k) {
                    Value *Op = IC->getArgOperand(k);
                    while (auto *C = dyn_cast<CastInst>(Op))
                      Op = C->getOperand(0);
                    if (auto *Ld = dyn_cast<LoadInst>(Op)) {
                      auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                      if (Al)
                        for (Instruction &SI : instructions(*Dw)) {
                          auto *St = dyn_cast<StoreInst>(&SI);
                          if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                            Op = St->getValueOperand()->stripPointerCasts();
                        }
                    }
                    if (auto *A2 = dyn_cast<Argument>(Op))
                      if (A2->getArgNo() == argNo)
                        work.push_back({ND, k});
                  }
                  continue;
                }
                Value *base = IC->getCalledOperand();
                std::unordered_set<const Value *> seen;
                bool mine = false;
                while (base && seen.insert(base).second) {
                  if (auto *C = dyn_cast<CastInst>(base)) {
                    base = C->getOperand(0);
                    continue;
                  }
                  if (auto *G = dyn_cast<GEPOperator>(base)) {
                    base = G->getPointerOperand();
                    continue;
                  }
                  if (auto *Ld = dyn_cast<LoadInst>(base)) {
                    base = Ld->getPointerOperand();
                    continue;
                  }
                  if (auto *Al = dyn_cast<AllocaInst>(base)) {
                    Value *stored = nullptr;
                    for (Instruction &SI : instructions(*Dw)) {
                      auto *St = dyn_cast<StoreInst>(&SI);
                      if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                        stored = St->getValueOperand();
                    }
                    base = stored;
                    continue;
                  }
                  break;
                }
                if (auto *A = dyn_cast<Argument>(base ? base->stripPointerCasts() : nullptr))
                  mine = A->getArgNo() == argNo;
                if (!mine) {
                  Function *N = IC->getCalledFunction();
                  if (N) {
                    if (Function *ND = define(N->getName()))
                      N = ND;
                    for (unsigned k = 0; k < IC->arg_size() && k < N->arg_size(); ++k) {
                      Value *Op = IC->getArgOperand(k);
                      while (auto *C = dyn_cast<CastInst>(Op))
                        Op = C->getOperand(0);
                      if (auto *Ld = dyn_cast<LoadInst>(Op)) {
                        auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                        if (Al)
                          for (Instruction &SI : instructions(*Dw)) {
                            auto *St = dyn_cast<StoreInst>(&SI);
                            if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                              Op = St->getValueOperand()->stripPointerCasts();
                          }
                      }
                      if (auto *A2 = dyn_cast<Argument>(Op))
                        if (A2->getArgNo() == argNo)
                          work.push_back({N, k});
                    }
                  }
                  continue;
                }
                Suffix slot = suffix(IC->getCalledOperand());
                std::vector<Function *> fns;
                auto sit = slotAt.find(slot);
                if (sit != slotAt.end())
                  fns = sit->second;
                if (fns.empty()) {
                  auto fit = fnAt.find(slot);
                  if (fit != fnAt.end())
                    fns = fit->second;
                }
                Suffix full = hold.second;
                full.insert(full.end(), slot.begin(), slot.end());
                addFns(hold.first, full, fns);
                for (const Suffix &side : besidePtr[slot]) {
                  Suffix comp = hold.second;
                  comp.insert(comp.end(), side.begin(), side.end());
                  cells.insert({hold.first, comp});
                  for (Function *H : builderOf[side]) {
                    for (const auto &st : argStored[H]) {
                      if (st.first >= H->arg_size() || !H->getArg(st.first)->getType()->isPointerTy())
                        continue;
                      Suffix inner = comp;
                      inner.insert(inner.end(), st.second.begin(), st.second.end());
                      cells.insert({hold.first, inner});
                      blobs.push_back(inner);
                    }
                  }
                }
              }
              }
              Bytes fb = fieldsOf(D);
              if (fb.ok) {
                Suffix data = hold.second;
                data.insert(data.end(), fb.data.begin(), fb.data.end());
                data.push_back(Step{"", 0});
                cells.insert({hold.first, data});
                if (fb.hasLen) {
                  Suffix ln = hold.second;
                  ln.insert(ln.end(), fb.len.begin(), fb.len.end());
                  cells.insert({hold.first, ln});
                }
              }
            }
          }
        }
        for (const Suffix &blob : blobs) {
          for (size_t si = 0; si < seq.size(); ++si)
            for (Instruction &I : instructions(*seq[si])) {
              auto *CB = dyn_cast<CallBase>(&I);
              if (!CB)
                continue;
              Function *Cal = CB->getCalledFunction();
              if (!Cal)
                continue;
              Function *D = define(Cal->getName());
              Bytes fb = fieldsOf(D);
              if (!fb.ok)
                continue;
              bool touch = false;
              for (Value *Op : CB->args()) {
                if (!Op->getType()->isPointerTy())
                  continue;
                Value *Act = Op->stripPointerCasts();
                if (auto *Ld = dyn_cast<LoadInst>(Act)) {
                  auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                  if (Al)
                    for (Instruction &SI : instructions(*seq[si])) {
                      auto *St = dyn_cast<StoreInst>(&SI);
                      if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                        Act = St->getValueOperand()->stripPointerCasts();
                    }
                }
                auto *Inner = dyn_cast<CallBase>(Act);
                if (!Inner)
                  continue;
                for (Value *In : Inner->args()) {
                  Loc L;
                  if (cellLoc(memAt(si), In, L) && L.arg == hold.first && sameSuf(L.suf, hold.second))
                    touch = true;
                }
              }
              if (!touch)
                continue;
              Suffix data = blob;
              data.insert(data.end(), fb.data.begin(), fb.data.end());
              data.push_back(Step{"", 0});
              cells.insert({hold.first, data});
              if (fb.hasLen) {
                Suffix ln = blob;
                ln.insert(ln.end(), fb.len.begin(), fb.len.end());
                cells.insert({hold.first, ln});
              }
            }
        }
      }
    }
    // A function that returns a pointer loaded from a field of an argument
    // returns that field. The caller's actual argument is the object.
    struct RetF {
      unsigned arg = 0;
      Suffix suf;
      bool pointer = false;
    };
    std::unordered_map<const Function *, std::optional<RetF>> retMemo;
    std::unordered_set<const Function *> retSeen;
    std::function<std::optional<RetF>(Function *, Value *)> asField;
    std::function<std::optional<RetF>(Function *)> retField;
    asField = [&](Function *F, Value *V) -> std::optional<RetF> {
      std::unordered_set<const Value *> seen;
      std::function<std::optional<RetF>(Value *)> go = [&](Value *V) -> std::optional<RetF> {
        while (V) {
          if (auto *C = dyn_cast<CastInst>(V)) {
            V = C->getOperand(0);
            continue;
          }
          break;
        }
        if (!V || !seen.insert(V).second)
          return std::nullopt;
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (Al) {
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              if (auto got = go(sv))
                return got;
            }
            return std::nullopt;
          }
          auto *A = dyn_cast<Argument>(rootOf(L->getPointerOperand()));
          if (!A)
            return std::nullopt;
          RetF r;
          r.arg = A->getArgNo();
          r.suf = suffix(L->getPointerOperand());
          r.pointer = L->getType()->isPointerTy();
          return r;
        }
        if (auto *A = dyn_cast<Argument>(V)) {
          RetF r;
          r.arg = A->getArgNo();
          return r;
        }
        auto *Call = dyn_cast<CallBase>(V);
        if (!Call)
          return std::nullopt;
        Function *Cal = Call->getCalledFunction();
        if (!Cal)
          return std::nullopt;
        Function *D = define(Cal->getName());
        if (!D)
          return std::nullopt;
        auto inner = retField(D);
        if (!inner || inner->arg >= Call->arg_size())
          return std::nullopt;
        auto sub = go(Call->getArgOperand(inner->arg));
        if (!sub)
          return std::nullopt;
        sub->suf.insert(sub->suf.end(), inner->suf.begin(), inner->suf.end());
        sub->pointer = sub->pointer || inner->pointer;
        return sub;
      };
      return go(V);
    };
    retField = [&](Function *F) -> std::optional<RetF> {
      if (!F || F->isDeclaration())
        return std::nullopt;
      if (auto it = retMemo.find(F); it != retMemo.end())
        return it->second;
      if (!retSeen.insert(F).second)
        return std::nullopt;
      std::optional<RetF> got;
      bool bad = false;
      for (const BasicBlock &BB : *F) {
        auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue())
          continue;
        Value *rv = R->getReturnValue();
        if (isa<ConstantPointerNull>(rv) || isa<UndefValue>(rv))
          continue;
        auto one = asField(F, rv);
        if (!one) {
          bad = true;
          break;
        }
        if (!got)
          got = one;
        else if (got->arg != one->arg || got->suf != one->suf || got->pointer != one->pointer) {
          bad = true;
          break;
        }
      }
      retSeen.erase(F);
      if (bad)
        got.reset();
      retMemo[F] = got;
      return got;
    };
    auto flatten = [](const Suffix &in, bool pointee) {
      Suffix flat;
      int64_t acc = 0;
      std::string ty;
      bool any = false;
      auto flush = [&]() {
        if (!any)
          return;
        flat.push_back(Step{ty, acc, false});
        acc = 0;
        ty.clear();
        any = false;
      };
      for (const Step &s : in) {
        if (s.deref) {
          flush();
          flat.push_back(s);
          continue;
        }
        if (!any && !s.type.empty())
          ty = s.type;
        acc += s.off;
        any = true;
      }
      flush();
      if (pointee)
        flat.push_back(Step{"", 0, true});
      return flat;
    };
    std::map<std::pair<int, Suffix>, std::pair<std::string, uint64_t>> vptrAt;
    for (size_t si = 0; si < seq.size(); ++si) {
      Mem &m = memAt(si);
      auto reach = sliceReach(seq[si], seq);
      for (Instruction &I : instructions(*seq[si])) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        bool held = false;
        for (Value *Op : CB->args()) {
          if (!Op->getType()->isPointerTy())
            continue;
          Loc L;
          if (cellLoc(m, Op, L) && !L.suf.empty() && cells.count({L.arg, L.suf}))
            held = true;
        }
        if (held)
          for (unsigned i = 0; i + 1 < CB->arg_size(); ++i) {
            Value *Buf = CB->getArgOperand(i);
            Value *Cnt = CB->getArgOperand(i + 1);
            if (!Buf->getType()->isPointerTy() || !Cnt->getType()->isIntegerTy())
              continue;
            auto *Call = dyn_cast<CallBase>(Buf->stripPointerCasts());
            if (!Call || !Call->getCalledFunction())
              continue;
            Function *D = define(Call->getCalledFunction()->getName());
            auto rf = retField(D);
            if (!rf || !rf->pointer || rf->arg >= Call->arg_size())
              continue;
            Loc base;
            if (!cellLoc(m, Call->getArgOperand(rf->arg), base) || base.suf.empty())
              continue;
            Suffix both = base.suf;
            both.insert(both.end(), rf->suf.begin(), rf->suf.end());
            Suffix flat = flatten(both, true);
            if (flat.empty())
              continue;
            cells.insert({base.arg, flat});
            if (auto *CI = dyn_cast<ConstantInt>(Cnt))
              if (CI->getBitWidth() <= 64 && !CI->isNegative() && CI->getZExtValue())
                readBytes[{base.arg, flat}] = CI->getZExtValue();
          }
        if (CB->getCalledFunction())
          continue;
        if (!reach.count(CB->getParent()))
          continue;
        VSlot vs = vslot(CB);
        if (!vs.ok)
          continue;
        Loc objL;
        if (!cellLoc(m, vs.obj, objL))
          continue;
        auto ts = targetsOf(CB);
        Function *want = nullptr;
        Function *next = si + 1 < seq.size() ? seq[si + 1] : nullptr;
        if (next && std::find(ts.begin(), ts.end(), next) != ts.end())
          want = next;
        else if (ts.size() == 1)
          want = ts[0];
        indexVtables();
        std::unordered_set<const Value *> objs{vs.obj};
        for (Instruction &GI : instructions(*seq[si]))
          if (auto *C = dyn_cast<CastInst>(&GI))
            if (objs.count(C->getOperand(0)))
              objs.insert(&GI);
        std::set<std::string> types;
        for (Instruction &GI : instructions(*seq[si])) {
          auto *G = dyn_cast<GetElementPtrInst>(&GI);
          if (!G || !objs.count(G->getPointerOperand()->stripPointerCasts()))
            continue;
          if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
            if (ST->hasName())
              types.insert(ST->getName().str());
        }
        std::vector<const VTab *> hits;
        std::set<std::tuple<GlobalVariable *, uint64_t, int64_t>> seenVt;
        auto consider = [&](const VTab &vt) {
          if (vt.field != vs.field || !vt.g || !vt.g->hasInitializer())
            return;
          if (!seenVt.insert({vt.g, vt.base, vt.field}).second)
            return;
          hits.push_back(&vt);
        };
        if (want) {
          for (const VTab &vt : vtAll)
            if (vt.g && vt.g->hasInitializer() &&
                functionAt(vt.g->getInitializer(), 0, vt.base + vs.slot) == want)
              consider(vt);
        }
        if (hits.empty())
          for (const std::string &ty : types) {
            auto it = vtOf.find(ty);
            if (it == vtOf.end())
              continue;
            for (const VTab &vt : it->second)
              consider(vt);
          }
        if (hits.empty() && next)
          for (const VTab &vt : vtAll) {
            if (!vt.g || !vt.g->hasInitializer())
              continue;
            Function *slotFn = functionAt(vt.g->getInitializer(), 0, vt.base + vs.slot);
            if (slotFn && reachesFn(slotFn, next))
              consider(vt);
          }
        // Every slot this slice calls through the same object is a defined
        // function. A declaration in one slot is not that vtable.
        std::vector<uint64_t> needSlots{vs.slot};
        {
          std::unordered_set<const Function *> seenFn;
          std::function<void(Function *, const std::vector<std::optional<Loc>> &)> slotsOf;
          slotsOf = [&](Function *SF, const std::vector<std::optional<Loc>> &sargs) {
            if (!SF || SF->isDeclaration() || !seenFn.insert(SF).second)
              return;
            Mem mm;
            bindFormals(mm, SF, sargs);
            propagateObject(mm, SF);
            auto sreach = sliceReach(SF, seq);
            for (const BasicBlock *BB : sreach)
              for (Instruction &JI : *const_cast<BasicBlock *>(BB)) {
                auto *O = dyn_cast<CallBase>(&JI);
                if (!O)
                  continue;
                if (!O->getCalledFunction()) {
                  VSlot os = vslot(O);
                  if (os.ok) {
                    Loc oL;
                    if (cellLoc(mm, os.obj, oL) && oL.arg == objL.arg && oL.suf == objL.suf)
                      needSlots.push_back(os.slot);
                  }
                  continue;
                }
                Function *D = define(O->getCalledFunction()->getName());
                if (!D || D->isDeclaration() || ignorable(O->getCalledFunction()))
                  continue;
                std::vector<std::optional<Loc>> down;
                bool touch = false;
                for (Value *Op : O->args()) {
                  Loc L;
                  if (objectLoc(mm, Op, L)) {
                    down.push_back(L);
                    touch = true;
                  } else
                    down.push_back(std::nullopt);
                }
                if (touch)
                  slotsOf(D, down);
              }
          };
          std::vector<std::optional<Loc>> top(seq[si]->arg_size());
          for (unsigned a = 0; a < top.size(); ++a)
            top[a] = Loc{(int)a, {}};
          if (si < frames.size())
            top = frames[si];
          slotsOf(seq[si], top);
        }
        auto definedAt = [&](const VTab *vt, uint64_t slot) {
          if (!vt->g || !vt->g->hasInitializer())
            return false;
          Function *Fn = functionAt(vt->g->getInitializer(), 0, vt->base + slot);
          return Fn && !Fn->isDeclaration();
        };
        std::vector<const VTab *> covered;
        for (const VTab *vt : hits) {
          bool ok = true;
          for (uint64_t slot : needSlots)
            if (!definedAt(vt, slot)) {
              ok = false;
              break;
            }
          if (ok)
            covered.push_back(vt);
        }
        hits.swap(covered);
        const VTab *hit = nullptr;
        if (hits.size() == 1)
          hit = hits[0];
        else if (!hits.empty()) {
          uint64_t wantN = objectBytes(vs.obj, seq[si]);
          std::vector<const VTab *> sized;
          for (const VTab *vt : hits)
            for (const auto &kv : vtOf) {
              if (!wantN || typeBytes(kv.first) != wantN)
                continue;
              for (const VTab &x : kv.second)
                if (x.g == vt->g && x.base == vt->base && x.field == vt->field)
                  sized.push_back(vt);
            }
          std::set<const VTab *> one(sized.begin(), sized.end());
          if (one.size() == 1)
            hit = *one.begin();
        }
        if (!hit)
          continue;
        std::string ty;
        for (const auto &kv : vtOf)
          for (const VTab &x : kv.second)
            if (x.g == hit->g && x.base == hit->base && x.field == hit->field)
              ty = kv.first;
        Suffix suf = objL.suf;
        suf.push_back(Step{ty, vs.field, false});
        vptrAt[{objL.arg, suf}] = {hit->g->getName().str(), hit->base};
        cells.insert({objL.arg, suf});
      }
    }
    // The value of a load is the store to that address. The value of a call
    // is what it returns, or the pointer it stores into an object it was
    // given. A value already followed is a cycle.
    {
      struct Frame {
        Function *fn = nullptr;
        std::vector<std::optional<Loc>> args;
      };
      std::map<std::string, std::optional<Loc>> knownV;
      std::set<std::string> stackV;
      auto argKey = [](const std::vector<std::optional<Loc>> &args) {
        std::string k;
        for (const auto &a : args) {
          if (!a) {
            k += "-;";
            continue;
          }
          k += std::to_string(a->arg);
          for (const Step &s : a->suf) {
            k.push_back('|');
            k += s.type;
            k.push_back('@');
            k += std::to_string(s.off);
            k.push_back(s.deref ? 'd' : 'n');
          }
          k.push_back(';');
        }
        return k;
      };
      std::function<std::optional<Loc>(Function *, Value *, const std::vector<std::optional<Loc>> &, bool)> origin;
      auto locate = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args, bool &loaded) -> std::optional<Loc> {
        loaded = false;
        Suffix pre;
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            if (!G->hasAllConstantIndices()) {
              if (isa<StructType>(G->getSourceElementType()))
                return std::nullopt;
              V = G->getPointerOperand();
              continue;
            }
            APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(dl, off))
              return std::nullopt;
            if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
              if (ST->hasName())
                pre.insert(pre.begin(), Step{ST->getName().str(), off.getSExtValue(), false});
            V = G->getPointerOperand();
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!Al) {
              if (!L->getType()->isPointerTy())
                return std::nullopt;
              loaded = true;
              if (!pre.empty())
                pre.back().deref = true;
              V = L->getPointerOperand();
              continue;
            }
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            if (!st)
              return std::nullopt;
            V = st;
            continue;
          }
          auto *A = dyn_cast<Argument>(V);
          if (!A || A->getArgNo() >= args.size() || !args[A->getArgNo()])
            return std::nullopt;
          Loc out = *args[A->getArgNo()];
          out.suf.insert(out.suf.end(), pre.begin(), pre.end());
          return out;
        }
        return std::nullopt;
      };
      origin = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args, bool asPtr) -> std::optional<Loc> {
        if (!F || !V)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        std::string key = std::to_string(reinterpret_cast<uintptr_t>(F)) + ":" + std::to_string(reinterpret_cast<uintptr_t>(V)) +
                          ":" + (asPtr ? "1:" : "0:") + argKey(args);
        if (auto it = knownV.find(key); it != knownV.end())
          return it->second;
        if (!stackV.insert(key).second)
          return std::nullopt;
        struct Leave {
          std::set<std::string> &stack;
          std::map<std::string, std::optional<Loc>> &known;
          std::string key;
          std::optional<Loc> result;
          ~Leave() {
            stack.erase(key);
            known.emplace(key, result);
          }
        } leave{stackV, knownV, key, {}};
        bool loaded = false;
        if (auto L = locate(F, V, args, loaded)) {
          if (!L->suf.empty() && (asPtr || loaded))
            L->suf.push_back(Step{"", 0, true});
          leave.result = L;
          return L;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || S->getPointerOperand()->stripPointerCasts() != L->getPointerOperand()->stripPointerCasts())
              continue;
            if (isa<ConstantPointerNull>(S->getValueOperand()) || isa<UndefValue>(S->getValueOperand()))
              continue;
            if (auto got = origin(F, S->getValueOperand(), args, L->getType()->isPointerTy())) {
              leave.result = got;
              return got;
            }
          }
          leave.result = origin(F, L->getPointerOperand(), args, false);
          return leave.result;
        }
        if (auto *P = dyn_cast<PHINode>(V)) {
          for (Value *in : P->incoming_values())
            if (auto got = origin(F, in, args, asPtr)) {
              leave.result = got;
              return got;
            }
          return std::nullopt;
        }
        auto *CB = dyn_cast<CallBase>(V);
        if (!CB)
          return std::nullopt;
        Function *Cal = CB->getCalledFunction();
        if (!Cal)
          return std::nullopt;
        Function *D = define(Cal->getName());
        if (!D || D->isDeclaration())
          return std::nullopt;
        std::vector<std::optional<Loc>> inner(D->arg_size());
        unsigned n = 0;
        for (Value *Op : CB->args()) {
          if (n >= inner.size())
            break;
          bool ld = false;
          if (auto L = locate(F, Op, args, ld))
            inner[n] = L;
          else if (Op->getType()->isPointerTy())
            inner[n] = origin(F, Op, args, false);
          ++n;
        }
        std::optional<Loc> ret;
        for (const BasicBlock &BB : *D) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue())
            continue;
          if (isa<ConstantPointerNull>(R->getReturnValue()) || isa<UndefValue>(R->getReturnValue()))
            continue;
          if (auto got = origin(D, R->getReturnValue(), inner, asPtr))
            ret = got;
        }
        for (Instruction &I : instructions(*D)) {
          auto *S = dyn_cast<StoreInst>(&I);
          if (!S || !S->getValueOperand()->getType()->isPointerTy())
            continue;
          bool ld = false;
          if (!locate(D, S->getPointerOperand(), inner, ld))
            continue;
          if (auto got = origin(D, S->getValueOperand(), inner, true))
            ret = got;
        }
        leave.result = ret;
        return ret;
      };
      auto rooted = [&](Function *F, Value *V, unsigned arg) {
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            V = G->getPointerOperand();
            continue;
          }
          if (auto *Al = dyn_cast<AllocaInst>(V)) {
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            V = st;
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!Al)
              return false;
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            V = st;
            continue;
          }
          auto *A = dyn_cast<Argument>(V);
          return A && A->getArgNo() == arg;
        }
        return false;
      };
      std::function<bool(Function *, unsigned, std::unordered_set<const Function *> &)> copied;
      copied = [&](Function *F, unsigned src, std::unordered_set<const Function *> &seen) -> bool {
        if (!F || F->isDeclaration() || !seen.insert(F).second)
          return false;
        auto samePtr = [&](Value *V) {
          std::unordered_set<const Value *> local;
          while (V && local.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            if (auto *Al = dyn_cast<AllocaInst>(V)) {
              Value *st = nullptr;
              for (Instruction &SI : instructions(*F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                  continue;
                Value *sv = S->getValueOperand();
                if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                  continue;
                st = sv;
              }
              V = st;
              continue;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (!Al)
                return false;
              Value *st = nullptr;
              for (Instruction &SI : instructions(*F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                  continue;
                Value *sv = S->getValueOperand();
                if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                  continue;
                st = sv;
              }
              V = st;
              continue;
            }
            auto *A = dyn_cast<Argument>(V);
            return A && A->getArgNo() == src;
          }
          return false;
        };
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          Copy cp = fixedCopy(*CB);
          auto pointerMove = [&](const CallBase &Call) {
            if (Call.arg_size() < 3 || !Call.getArgOperand(2)->getType()->isIntegerTy())
              return false;
            auto *N = dyn_cast<ConstantInt>(Call.getArgOperand(2));
            return N && N->getZExtValue() <= dl.getPointerSize(0) * 2;
          };
          auto restInt = [&](const CallBase &Call) {
            for (unsigned k = 3; k < Call.arg_size(); ++k)
              if (!Call.getArgOperand(k)->getType()->isIntegerTy())
                return false;
            return true;
          };
          if (cp.ok && !pointerMove(*CB) && restInt(*CB) && samePtr(CB->getArgOperand(cp.src)))
            return true;
          if (CB->arg_size() >= 3 && CB->getArgOperand(0)->getType()->isPointerTy() &&
              CB->getArgOperand(1)->getType()->isPointerTy() && CB->getArgOperand(2)->getType()->isIntegerTy() &&
              restInt(*CB) && !pointerMove(*CB) && samePtr(CB->getArgOperand(1)))
            return true;
          Function *Cal = CB->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D && !Cal)
            for (Function *T : targetsOf(CB))
              if (T && !T->isDeclaration()) {
                D = T;
                break;
              }
          if (!D || D->isDeclaration())
            continue;
          for (unsigned i = 0; i < CB->arg_size() && i < D->arg_size(); ++i)
            if (CB->getArgOperand(i)->getType()->isPointerTy() && samePtr(CB->getArgOperand(i)))
              if (copied(D, i, seen))
                return true;
        }
        return false;
      };
      std::function<std::optional<Loc>(Function *, Value *, const std::vector<std::optional<Loc>> &,
                                       std::unordered_set<const Value *> &)>
          filled;
      filled = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args,
                   std::unordered_set<const Value *> &seen) -> std::optional<Loc> {
        if (!F || !V || !seen.insert(V).second)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (auto *L = dyn_cast<LoadInst>(V))
          return filled(F, L->getPointerOperand(), args, seen);
        if (auto *CB = dyn_cast<CallBase>(V)) {
          for (Value *Op : CB->args())
            if (Op->getType()->isPointerTy())
              if (auto got = filled(F, Op, args, seen))
                return got;
          return std::nullopt;
        }
        auto *Al = dyn_cast<AllocaInst>(V);
        if (!Al)
          return std::nullopt;
        for (Instruction &I : instructions(*F)) {
          auto *Call = dyn_cast<CallBase>(&I);
          if (!Call)
            continue;
          int slot = -1;
          for (unsigned i = 0; i < Call->arg_size(); ++i)
            if (Call->getArgOperand(i)->stripPointerCasts() == Al)
              slot = (int)i;
          if (slot < 0)
            continue;
          Function *Cal = Call->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D || D->isDeclaration())
            continue;
          std::vector<std::optional<Loc>> inner(D->arg_size());
          unsigned n = 0;
          for (Value *Op : Call->args()) {
            if (n >= inner.size())
              break;
            bool ld = false;
            if (auto loc = locate(F, Op, args, ld))
              inner[n] = loc;
            ++n;
          }
          for (Instruction &SI : instructions(*D)) {
            auto *S = dyn_cast<StoreInst>(&SI);
            if (!S || !S->getValueOperand()->getType()->isPointerTy())
              continue;
            if (!rooted(D, S->getPointerOperand(), (unsigned)slot))
              continue;
            if (auto got = origin(D, S->getValueOperand(), inner, true))
              return got;
          }
          for (Instruction &SI : instructions(*D)) {
            auto *Sub = dyn_cast<CallBase>(&SI);
            if (!Sub)
              continue;
            for (unsigned i = 0; i < Sub->arg_size(); ++i)
              if (rooted(D, Sub->getArgOperand(i), (unsigned)slot))
                if (auto got = filled(D, Sub->getArgOperand(i), inner, seen))
                  return got;
          }
        }
        return std::nullopt;
      };
      const auto roots = cells;
      auto sameStep = [](const Step &a, const Step &b) { return a.type == b.type && a.off == b.off; };
      auto insideRoot = [&](const Loc &L) {
        for (const auto &c : roots)
          if (c.first == L.arg && !c.second.empty() && L.suf.size() >= c.second.size() &&
              std::equal(c.second.begin(), c.second.end(), L.suf.begin(), sameStep))
            return true;
        return false;
      };
      auto keep = [&](const Loc &L) {
        if (L.suf.empty() || insideRoot(L))
          return;
        if (L.suf.size() == 1 && L.suf[0].type.empty())
          return;
        cells.insert({L.arg, L.suf});
      };
      std::vector<Frame> work;
      std::unordered_set<Function *> seenF;
      for (size_t si = 0; si < seq.size(); ++si) {
        Frame fr;
        fr.fn = seq[si];
        fr.args = frames[si];
        if (fr.args.size() < seq[si]->arg_size())
          fr.args.resize(seq[si]->arg_size());
        if (si == 0)
          for (unsigned i = 0; i < seq[si]->arg_size(); ++i)
            if (!fr.args[i])
              fr.args[i] = Loc{(int)i, {}};
        seenF.insert(seq[si]);
        work.push_back(std::move(fr));
      }
      for (size_t wi = 0; wi < work.size(); ++wi) {
        Function *F = work[wi].fn;
        std::vector<std::optional<Loc>> args = work[wi].args;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          std::vector<std::optional<Loc>> at(CB->arg_size());
          bool fromExport = false;
          std::vector<unsigned> fresh;
          for (unsigned i = 0; i < CB->arg_size(); ++i) {
            bool ld = false;
            auto L = locate(F, CB->getArgOperand(i), args, ld);
            if (!L)
              continue;
            at[i] = L;
            fromExport = true;
          }
          if (fromExport)
            for (unsigned i = 0; i < CB->arg_size(); ++i) {
              if (at[i] || !CB->getArgOperand(i)->getType()->isPointerTy())
                continue;
              at[i] = origin(F, CB->getArgOperand(i), args, true);
              if (!at[i]) {
                std::unordered_set<const Value *> seen;
                at[i] = filled(F, CB->getArgOperand(i), args, seen);
              }
              if (at[i])
                fresh.push_back(i);
            }
          Function *Cal = CB->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D && !Cal)
            for (Function *T : targetsOf(CB))
              if (T && !T->isDeclaration()) {
                D = T;
                break;
              }
          if (D && !D->isDeclaration() && fromExport)
            for (unsigned i : fresh) {
              if (i >= D->arg_size())
                continue;
              std::unordered_set<const Function *> copiedSeen;
              if (!copied(D, i, copiedSeen))
                continue;
              keep(*at[i]);
            }
          if (D && !D->isDeclaration() && fromExport && seenF.insert(D).second) {
            Frame fr;
            fr.fn = D;
            fr.args.resize(D->arg_size());
            for (unsigned i = 0; i < at.size() && i < fr.args.size(); ++i)
              fr.args[i] = at[i];
            work.push_back(std::move(fr));
          }
        }
      }
      std::vector<std::pair<int, Suffix>> drop;
      for (const auto &c : cells) {
        if (!indexed.count(c))
          continue;
        bool named = false;
        for (const auto &kv : facts)
          if (tail(c.second, kv.first) && !kv.second.empty())
            named = true;
        if (named)
          continue;
        auto fieldOf = [&](Function *F, Value *V) {
          Suffix s;
          std::unordered_set<const Value *> seen;
          while (V && seen.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            auto *G = dyn_cast<GEPOperator>(V);
            if (!G)
              break;
            if (!G->hasAllConstantIndices()) {
              if (isa<StructType>(G->getSourceElementType()))
                return Suffix{};
              V = G->getPointerOperand();
              continue;
            }
            APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(dl, off))
              return Suffix{};
            if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
              if (ST->hasName())
                s.insert(s.begin(), Step{ST->getName().str(), off.getSExtValue(), false});
            V = G->getPointerOperand();
          }
          return s;
        };
        std::function<bool(Function *, std::unordered_set<Function *> &)> written;
        written = [&](Function *F, std::unordered_set<Function *> &seen) {
          if (!F || F->isDeclaration() || !seen.insert(F).second)
            return false;
          for (Instruction &I : instructions(*F)) {
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              if (isa<Constant>(S->getValueOperand()))
                continue;
              Suffix got = fieldOf(F, S->getPointerOperand());
              if (!got.empty() && c.second.size() >= got.size() &&
                  std::equal(got.begin(), got.end(), c.second.end() - (long)got.size(), sameStep))
                return true;
              continue;
            }
            auto *CB = dyn_cast<CallBase>(&I);
            if (CB) {
              Function *Cal = CB->getCalledFunction();
              Function *Callee = Cal ? define(Cal->getName()) : nullptr;
              for (unsigned a = 0; Callee && a < CB->arg_size() && a < Callee->arg_size(); ++a) {
                if (!CB->getArgOperand(a)->getType()->isPointerTy())
                  continue;
                Suffix at = fieldOf(F, CB->getArgOperand(a));
                if (at.empty() || c.second.size() < at.size() ||
                    !std::equal(at.begin(), at.end(), c.second.end() - (long)at.size(), sameStep))
                  continue;
                for (Instruction &SI : instructions(*Callee)) {
                  auto *St = dyn_cast<StoreInst>(&SI);
                  if (!St || isa<Constant>(St->getValueOperand()))
                    continue;
                  Value *P = St->getPointerOperand();
                  std::unordered_set<const Value *> local;
                  while (P && local.insert(P).second) {
                    while (auto *C = dyn_cast<CastInst>(P))
                      P = C->getOperand(0);
                    if (auto *G = dyn_cast<GEPOperator>(P)) {
                      P = G->getPointerOperand();
                      continue;
                    }
                    auto *Al = dyn_cast<AllocaInst>(P->stripPointerCasts());
                    if (!Al && isa<LoadInst>(P))
                      Al = dyn_cast<AllocaInst>(cast<LoadInst>(P)->getPointerOperand()->stripPointerCasts());
                    if (Al) {
                      Value *st = nullptr;
                      for (Instruction &AI : instructions(*Callee)) {
                        auto *WS = dyn_cast<StoreInst>(&AI);
                        if (!WS || WS->getPointerOperand()->stripPointerCasts() != Al)
                          continue;
                        if (isa<ConstantPointerNull>(WS->getValueOperand()) || isa<UndefValue>(WS->getValueOperand()))
                          continue;
                        st = WS->getValueOperand();
                      }
                      P = st;
                      continue;
                    }
                    break;
                  }
                  auto *Arg = dyn_cast<Argument>(P);
                  if (Arg && Arg->getArgNo() == a)
                    return true;
                }
              }
            }
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            Function *D = Cal ? define(Cal->getName()) : nullptr;
            if (written(D, seen))
              return true;
          }
          return false;
        };
        bool hit = false;
        std::unordered_set<Function *> seenFn;
        for (Function *F : seq)
          if (written(F, seenFn)) {
            hit = true;
            break;
          }
        if (hit)
          drop.push_back(c);
      }
      for (const auto &c : drop)
        cells.erase(c);
      // A call that stores a fresh pointer into a slot, and does not copy
      // the bytes that pointer used to address, replaces the slot. The
      // caller's pointer is not the object the sink reads.
      auto freshPtr = [&](Value *V) {
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *CB = dyn_cast<CallBase>(V);
          if (!CB || !CB->getType()->isPointerTy())
            return false;
          for (Value *Op : CB->args())
            if (!Op->getType()->isIntegerTy())
              return false;
          Function *Cal = CB->getCalledFunction();
          if (!Cal)
            return false;
          Function *D = define(Cal->getName());
          return !D || D->isDeclaration();
        }
        return false;
      };
      auto slotOf = [&](Function *F, Value *V) {
        Suffix s;
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *G = dyn_cast<GEPOperator>(V);
          if (!G)
            break;
          if (!G->hasAllConstantIndices()) {
            if (isa<StructType>(G->getSourceElementType()))
              return Suffix{};
            V = G->getPointerOperand();
            continue;
          }
          APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, off))
            return Suffix{};
          if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
            if (ST->hasName())
              s.insert(s.begin(), Step{ST->getName().str(), off.getSExtValue(), false});
          V = G->getPointerOperand();
        }
        return s;
      };
      // A value comes from an argument when casts, field addresses, the
      // alloca the argument was saved in, or a call that returns an address
      // inside that argument, lead back to it.
      auto fromArg = [](Function *Callee, Value *P, int argNo) {
        std::function<bool(Value *, std::unordered_set<const Value *> &)> go;
        go = [&](Value *V, std::unordered_set<const Value *> &local) -> bool {
          while (V && local.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            if (auto *G = dyn_cast<GEPOperator>(V)) {
              V = G->getPointerOperand();
              continue;
            }
            if (auto *CB = dyn_cast<CallBase>(V)) {
              if (!CB->getType()->isPointerTy())
                return false;
              for (Value *Op : CB->args())
                if (Op->getType()->isPointerTy() && go(Op, local))
                  return true;
              return false;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              V = L->getPointerOperand();
              continue;
            }
            auto *Al = dyn_cast<AllocaInst>(V->stripPointerCasts());
            if (!Al)
              break;
            Value *st = nullptr;
            for (Instruction &AI : instructions(*Callee)) {
              auto *WS = dyn_cast<StoreInst>(&AI);
              if (!WS || WS->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              if (isa<ConstantPointerNull>(WS->getValueOperand()) || isa<UndefValue>(WS->getValueOperand()))
                continue;
              st = WS->getValueOperand();
            }
            V = st;
          }
          auto *Arg = dyn_cast<Argument>(V);
          return Arg && (int)Arg->getArgNo() == argNo;
        };
        std::unordered_set<const Value *> local;
        return go(P, local);
      };
      std::function<bool(Function *, int, int, std::unordered_set<Function *> &)> replaced;
      replaced = [&](Function *Callee, int slotArg, int freshArg, std::unordered_set<Function *> &seen) -> bool {
        if (!Callee || Callee->isDeclaration() || !seen.insert(Callee).second)
          return false;
        bool storesFresh = false;
        bool copies = false;
        bool deeper = false;
        for (Instruction &SI : instructions(*Callee)) {
          if (auto *St = dyn_cast<StoreInst>(&SI)) {
            if (!isa<Constant>(St->getValueOperand()) &&
                fromArg(Callee, St->getValueOperand(), freshArg) &&
                fromArg(Callee, St->getPointerOperand(), slotArg))
              storesFresh = true;
          }
          auto *Call = dyn_cast<CallBase>(&SI);
          if (!Call)
            continue;
          if (Call->arg_size() >= 3 && Call->getArgOperand(0)->getType()->isPointerTy() &&
              Call->getArgOperand(1)->getType()->isPointerTy() &&
              Call->getArgOperand(2)->getType()->isIntegerTy() &&
              (fromArg(Callee, Call->getArgOperand(0), slotArg) ||
               fromArg(Callee, Call->getArgOperand(1), slotArg)))
            copies = true;
          Function *InnerCal = Call->getCalledFunction();
          Function *Inner = InnerCal ? define(InnerCal->getName()) : nullptr;
          if (!Inner || Inner->isDeclaration())
            continue;
          int slot2 = -1;
          int made2 = -1;
          for (unsigned a = 0; a < Call->arg_size() && a < Inner->arg_size(); ++a) {
            Value *Op = Call->getArgOperand(a);
            if (!Op->getType()->isPointerTy())
              continue;
            if (fromArg(Callee, Op, slotArg))
              slot2 = (int)a;
            if (fromArg(Callee, Op, freshArg))
              made2 = (int)a;
          }
          if (slot2 >= 0 && made2 >= 0 && slot2 != made2 && replaced(Inner, slot2, made2, seen))
            deeper = true;
        }
        return !copies && (storesFresh || deeper);
      };
      drop.clear();
      for (const auto &c : cells) {
        if (calleeAt.count(c) || pathAt.count(c) || keyCell.count(c) || pathCell.count(c))
          continue;
        bool named = false;
        for (const auto &kv : facts)
          if (tail(c.second, kv.first) && !kv.second.empty())
            named = true;
        if (named)
          continue;
        bool parent = false;
        for (const auto &o : cells)
          if (o.first == c.first && o.second.size() > c.second.size() &&
              std::equal(c.second.begin(), c.second.end(), o.second.begin(), sameStep))
            parent = true;
        if (parent)
          continue;
        bool hit = false;
        for (Function *F : seq) {
          if (hit)
            break;
          if (!F || F->isDeclaration())
            continue;
          for (Instruction &I : instructions(*F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            Function *Callee = Cal ? define(Cal->getName()) : nullptr;
            if (!Callee || Callee->isDeclaration())
              continue;
            int slotArg = -1;
            int made = -1;
            for (unsigned a = 0; a < CB->arg_size() && a < Callee->arg_size(); ++a) {
              Value *Op = CB->getArgOperand(a);
              if (!Op->getType()->isPointerTy())
                continue;
              Suffix at = slotOf(F, Op);
              if (!at.empty() && c.second.size() >= at.size() &&
                  std::equal(at.begin(), at.end(), c.second.end() - (long)at.size(), sameStep))
                slotArg = (int)a;
              if (freshPtr(Op))
                made = (int)a;
            }
            if (slotArg < 0 || made < 0 || slotArg == made)
              continue;
            std::unordered_set<Function *> seenFn;
            if (replaced(Callee, slotArg, made, seenFn))
              hit = true;
          }
        }
        if (hit)
          drop.push_back(c);
      }
      for (const auto &c : drop)
        cells.erase(c);
    }
    // A call that returns its first pointer and takes the cell plus another
    // object assigns that object into the cell. The sink reads the object.
    auto sameSuf = [](const Suffix &a, const Suffix &b) {
      if (a.size() != b.size())
        return false;
      for (size_t i = 0; i < a.size(); ++i)
        if (a[i].type != b[i].type || a[i].off != b[i].off)
          return false;
      return true;
    };
    auto loadedPtr = [](Value *V) -> Value * {
      while (auto *C = dyn_cast<CastInst>(V))
        V = C->getOperand(0);
      auto *L = dyn_cast<LoadInst>(V);
      if (!L || !L->getType()->isPointerTy())
        return nullptr;
      return L->getPointerOperand();
    };
    for (const auto &c : pathAt) {
      if (!pathPtr.count(c))
        continue;
      for (size_t si = 0; si < seq.size(); ++si) {
        Function *F = seq[si];
        if (!F || F->isDeclaration())
          continue;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->arg_size() != 2 || !CB->getType()->isPointerTy())
            continue;
          if (!CB->getArgOperand(0)->getType()->isPointerTy() || !CB->getArgOperand(1)->getType()->isPointerTy())
            continue;
          Loc dest, src;
          if (!cellLoc(memAt(si), CB->getArgOperand(0), dest))
            continue;
          if (dest.arg != c.first || !sameSuf(dest.suf, c.second))
            continue;
          if (!cellLoc(memAt(si), CB->getArgOperand(1), src) || src.arg < 0)
            continue;
          if (src.arg == dest.arg && sameSuf(src.suf, dest.suf))
            continue;
          if (!src.suf.empty())
            continue;
          std::string ty;
          if (!c.second.empty())
            if (StructType *ST = structNamed(c.second.back().type))
              if (Type *E = [&]() -> Type * {
                    if (!ST->isSized())
                      return nullptr;
                    const StructLayout *SL = dl.getStructLayout(ST);
                    for (unsigned i = 0; i < ST->getNumElements(); ++i)
                      if ((int64_t)SL->getElementOffset(i) == c.second.back().off)
                        return ST->getElementType(i);
                    return nullptr;
                  }())
                if (auto *FT = dyn_cast<StructType>(E))
                  if (FT->hasName())
                    ty = FT->getName().str();
          pathSrc.push_back(PathSrc{src.arg, ty});
        }
      }
    }
    auto underByte = [&](const Loc &L) {
      for (const auto &c : cells) {
        if (c.first != L.arg || c.second.empty() || !c.second.back().type.empty())
          continue;
        if (c.second.size() < L.suf.size())
          continue;
        bool pre = true;
        for (size_t i = 0; i < L.suf.size(); ++i)
          if (c.second[i].type != L.suf[i].type || c.second[i].off != L.suf[i].off)
            pre = false;
        if (pre)
          return true;
      }
      return false;
    };
    std::deque<Mem> owned;
    struct Job {
      Function *F = nullptr;
      Mem *m = nullptr;
    };
    std::vector<Job> jobs;
    std::set<Function *> seqFn(seq.begin(), seq.end());
    std::set<std::string> seenCallee;
    for (size_t si = 0; si < seq.size(); ++si) {
      Function *F = seq[si];
      if (!F || F->isDeclaration())
        continue;
      jobs.push_back(Job{F, &memAt(si)});
    }
    for (size_t qi = 0; qi < jobs.size(); ++qi) {
      Function *F = jobs[qi].F;
      Mem &m = *jobs[qi].m;
      for (Instruction &I : instructions(*F)) {
        Value *lhs = nullptr;
        Value *rhs = nullptr;
        if (auto *Sub = dyn_cast<BinaryOperator>(&I)) {
          if (Sub->getOpcode() == Instruction::Sub) {
            lhs = loadedPtr(Sub->getOperand(0));
            rhs = loadedPtr(Sub->getOperand(1));
          }
        } else if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
          lhs = loadedPtr(Cmp->getOperand(0));
          rhs = loadedPtr(Cmp->getOperand(1));
        }
        auto locate = [&](Value *P, Loc &L) {
          Loc c;
          if (cellLoc(m, P, c) && !c.suf.empty()) {
            L = c;
            return true;
          }
          if (auto v = valueAt(F, P, m))
            if (!v->suf.empty()) {
              L = *v;
              return true;
            }
          return false;
        };
        if (lhs && rhs) {
          Loc a, b;
          if (locate(lhs, a) && locate(rhs, b) && a.arg == b.arg && a.suf.size() == b.suf.size()) {
            bool prefix = true;
            for (size_t i = 0; i + 1 < a.suf.size(); ++i)
              if (a.suf[i].type != b.suf[i].type || a.suf[i].off != b.suf[i].off)
                prefix = false;
            if (prefix && a.suf.back().off != b.suf.back().off && fieldIsPointer(a.suf.back().type, a.suf.back().off) &&
                fieldIsPointer(b.suf.back().type, b.suf.back().off)) {
              if (a.suf.back().off < b.suf.back().off)
                ptrSpan.push_back(PtrSpan{a.arg, a.suf, b.suf});
              else
                ptrSpan.push_back(PtrSpan{a.arg, b.suf, a.suf});
            }
          }
        }
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (Function *Callee : targetsOf(CB)) {
          if (!Callee || Callee->isDeclaration() || seqFn.count(Callee))
            continue;
          std::vector<std::optional<Loc>> args(Callee->arg_size());
          bool hit = false;
          for (unsigned i = 0; i < CB->arg_size() && i < Callee->arg_size(); ++i) {
            if (!CB->getArgOperand(i)->getType()->isPointerTy())
              continue;
            Loc L;
            bool got = cellLoc(m, CB->getArgOperand(i), L);
            if (!got || L.suf.empty()) {
              if (auto v = valueAt(F, CB->getArgOperand(i), m)) {
                L = *v;
                got = true;
              }
            }
            if (!got || !underByte(L))
              continue;
            args[i] = L;
            hit = true;
          }
          if (!hit)
            continue;
          std::string key = Callee->getName().str();
          for (const auto &L : args) {
            key.push_back('|');
            if (!L)
              continue;
            key += std::to_string(L->arg);
            for (const Step &s : L->suf)
              key += ":" + s.type + "@" + std::to_string(s.off);
          }
          if (!seenCallee.insert(key).second)
            continue;
          owned.emplace_back();
          bindFormals(owned.back(), Callee, args);
          propagate(owned.back(), Callee);
          jobs.push_back(Job{Callee, &owned.back()});
        }
      }
    }
    for (const auto &c : cells) {
      out << "cell arg" << c.first;
      for (const Step &s : c.second)
        out << " " << s.type << "+" << s.off;
      std::set<std::string> vals;
      size_t best = 0;
      for (const auto &kv : facts) {
        if (!tail(c.second, kv.first) || kv.first.size() < best)
          continue;
        best = kv.first.size();
        vals = kv.second;
      }
      auto narrow = [&](const std::set<std::string> &keep) {
        if (keep.empty())
          return;
        if (vals.empty()) {
          vals = keep;
          return;
        }
        std::set<std::string> both;
        std::set_intersection(keep.begin(), keep.end(), vals.begin(), vals.end(), std::inserter(both, both.end()));
        vals.swap(both);
      };
      std::set<std::string> must;
      size_t bestNeed = 0;
      for (const auto &kv : need) {
        if (!tail(c.second, kv.first) || kv.first.size() < bestNeed)
          continue;
        bestNeed = kv.first.size();
        must = kv.second;
      }
      if (indirectAt.count(c)) {
        vals.clear();
        if (auto callIt = calleeAt.find(c); callIt != calleeAt.end())
          vals = callIt->second;
      } else {
        narrow(must);
        auto callIt = calleeAt.find(c);
        if (callIt != calleeAt.end())
          narrow(callIt->second);
      }
      auto sit = seqStore.find(c);
      if (sit != seqStore.end() && !sit->second.empty()) {
        bool numeric = true;
        for (const std::string &v : vals) {
          size_t i = !v.empty() && v[0] == '-' ? 1 : 0;
          if (i >= v.size())
            numeric = false;
          for (; numeric && i < v.size(); ++i)
            if (v[i] < '0' || v[i] > '9')
              numeric = false;
        }
        if (numeric)
          vals = sit->second;
      }
      auto cit = cmps.find(c);
      if (cit != cmps.end())
        narrow(cit->second);
      std::set<std::string> text;
      bool path = pathAt.count(c) != 0;
      bool asPtr = pathPtr.count(c) != 0;
      if (path && !asPtr && text.empty() && vals.empty())
        text.insert("f");
      bool hasChild = false;
      for (const auto &o : cells) {
        if (o.first == c.first && o.second.size() > c.second.size() &&
            std::equal(c.second.begin(), c.second.end(), o.second.begin()))
          hasChild = true;
      }
      if (hasChild && vals.size() == 1 && *vals.begin() == "0")
        vals.clear();
      auto fit = fileCell.find(c);
      bool nullOnly = vals.size() == 1 && *vals.begin() == "0";
      bool asFile = fit != fileCell.end() && text.empty() && (vals.empty() || nullOnly);
      if (asFile)
        vals.clear();
      std::optional<uint64_t> flen;
      if (asFile) {
        auto lit = fileLen.find(c);
        if (lit != fileLen.end())
          flen = lit->second;
      }
      auto vit = vptrAt.find(c);
      if (vit != vptrAt.end() && text.empty()) {
        out << " = " << vit->second.first << "+" << vit->second.second;
        vals.clear();
      } else if (!text.empty()) {
        out << " =";
        for (const std::string &t : text)
          out << " \"" << t << "\"";
      } else if (!vals.empty()) {
        out << " =";
        for (const std::string &v : vals)
          out << " " << v;
      } else if (neq.count(c)) {
        out << " !=";
        for (const std::string &v : neq[c])
          out << " " << v;
      }
      if (asFile || path) {
        out << " file";
        if (flen)
          out << " " << *flen;
      }
      out << "\n";
      Solved s;
      s.arg = c.first;
      s.suf = c.second;
      s.vals = std::move(vals);
      if (s.vals.empty())
        if (auto nit = neq.find(c); nit != neq.end())
          s.ban = nit->second;
      s.text = std::move(text);
      s.file = asFile || (path && asPtr);
      s.pathPtr = path && asPtr;
      if (vit != vptrAt.end()) {
        s.glob = vit->second.first;
        s.gbyte = vit->second.second;
        s.vals.clear();
      }
      s.len = flen;
      if (asFile)
        s.fty = fit->second;
      auto w = wide.find(c);
      if (w != wide.end() && w->second)
        s.width = w->second;
      solvedCells.push_back(std::move(s));
    }
    Transition tr;
    using Cell = std::pair<int, Suffix>;
    std::map<Cell, SlotVal> mem;
    auto writeCell = [&](const Cell &c) {
      out << " arg" << c.first;
      for (const Step &st : c.second)
        out << " " << st.type << "+" << st.off;
    };
    auto rankOf = [&](Instruction *I) {
      int level = 0;
      int idx = 0;
      if (I) {
        if (auto *N = domTree(I->getFunction()).getNode(I->getParent()))
          level = (int)N->getLevel();
        for (Instruction &J : *I->getParent()) {
          if (&J == I)
            break;
          ++idx;
        }
      }
      return std::make_pair(level, idx);
    };
    auto readNode = [](auto &nodes, auto &find, int id) {
      id = find(id);
      SlotVal s;
      s.known = nodes[id].has;
      s.val = nodes[id].val;
      s.any = nodes[id].any;
      s.ban = nodes[id].ban;
      s.slo = nodes[id].slo;
      s.shi = nodes[id].shi;
      s.ulo = nodes[id].ulo;
      s.uhi = nodes[id].uhi;
      s.sloV = nodes[id].sloV;
      s.shiV = nodes[id].shiV;
      s.uloV = nodes[id].uloV;
      s.uhiV = nodes[id].uhiV;
      s.ordBytes = nodes[id].ordBytes;
      return s;
    };
    struct Node {
      int parent = 0;
      bool has = false;
      std::string val;
      std::set<std::string> any;
      std::set<std::string> ban;
      bool slo = false, shi = false, ulo = false, uhi = false;
      int64_t sloV = 0, shiV = 0;
      uint64_t uloV = 0, uhiV = 0;
      unsigned ordBytes = 0;
    };
    std::vector<Node> nodes;
    auto make = [&]() {
      int id = (int)nodes.size();
      nodes.push_back(Node{id, false, {}, {}, {}});
      return id;
    };
    std::function<int(int)> find = [&](int x) {
      if (nodes[x].parent != x)
        nodes[x].parent = find(nodes[x].parent);
      return nodes[x].parent;
    };
    std::function<void(int)> violate;
    auto pin = [&](int x, const std::string &v) {
      x = find(x);
      if (nodes[x].has && nodes[x].val != v)
        tr.conflict = true;
      if (nodes[x].ban.count(v))
        tr.conflict = true;
      if (!nodes[x].any.empty() && !nodes[x].any.count(v))
        tr.conflict = true;
      nodes[x].has = true;
      nodes[x].val = v;
      nodes[x].any.clear();
      if (violate)
        violate(x);
    };
    auto forbid = [&](int x, const std::set<std::string> &vs) {
      x = find(x);
      nodes[x].ban.insert(vs.begin(), vs.end());
      if (nodes[x].has && nodes[x].ban.count(nodes[x].val))
        tr.conflict = true;
    };
    auto allow = [&](int x, const std::set<std::string> &vs) {
      if (vs.empty())
        return;
      if (vs.size() == 1) {
        pin(x, *vs.begin());
        return;
      }
      x = find(x);
      if (nodes[x].has) {
        if (!vs.count(nodes[x].val))
          tr.conflict = true;
        return;
      }
      if (nodes[x].any.empty())
        nodes[x].any = vs;
      else {
        std::set<std::string> both;
        std::set_intersection(nodes[x].any.begin(), nodes[x].any.end(), vs.begin(), vs.end(), std::inserter(both, both.end()));
        if (both.empty())
          tr.conflict = true;
        nodes[x].any.swap(both);
      }
    };
    violate = [&](int x) {
      x = find(x);
      Node &n = nodes[x];
      if (n.slo && n.shi && n.sloV > n.shiV)
        tr.conflict = true;
      if (n.ulo && n.uhi && n.uloV > n.uhiV)
        tr.conflict = true;
      if (!n.has)
        return;
      if (n.slo || n.shi) {
        auto s = asI64(n.val);
        if (!s || (n.slo && *s < n.sloV) || (n.shi && *s > n.shiV))
          tr.conflict = true;
      }
      if (n.ulo || n.uhi) {
        auto u = asU64(n.val);
        if (!u || (n.ulo && *u < n.uloV) || (n.uhi && *u > n.uhiV))
          tr.conflict = true;
      }
    };
    auto loS = [&](int x, int64_t v) {
      x = find(x);
      if (!nodes[x].slo || v > nodes[x].sloV) {
        nodes[x].slo = true;
        nodes[x].sloV = v;
      }
      violate(x);
    };
    auto hiS = [&](int x, int64_t v) {
      x = find(x);
      if (!nodes[x].shi || v < nodes[x].shiV) {
        nodes[x].shi = true;
        nodes[x].shiV = v;
      }
      violate(x);
    };
    auto loU = [&](int x, uint64_t v) {
      x = find(x);
      if (!nodes[x].ulo || v > nodes[x].uloV) {
        nodes[x].ulo = true;
        nodes[x].uloV = v;
      }
      violate(x);
    };
    auto hiU = [&](int x, uint64_t v) {
      x = find(x);
      if (!nodes[x].uhi || v < nodes[x].uhiV) {
        nodes[x].uhi = true;
        nodes[x].uhiV = v;
      }
      violate(x);
    };
    auto boundConst = [&](int x, unsigned pred, const std::string &k, unsigned bytes) {
      x = find(x);
      if (bytes == 1 || bytes == 2 || bytes == 4 || bytes == 8)
        nodes[x].ordBytes = bytes;
      auto fail = [&] { tr.conflict = true; };
      switch (pred) {
      case ICmpInst::ICMP_SLT: {
        auto s = asI64(k);
        if (!s || *s == std::numeric_limits<int64_t>::min())
          return fail();
        hiS(x, *s - 1);
        break;
      }
      case ICmpInst::ICMP_SLE: {
        auto s = asI64(k);
        if (!s)
          return fail();
        hiS(x, *s);
        break;
      }
      case ICmpInst::ICMP_SGT: {
        auto s = asI64(k);
        if (!s || *s == std::numeric_limits<int64_t>::max())
          return fail();
        loS(x, *s + 1);
        break;
      }
      case ICmpInst::ICMP_SGE: {
        auto s = asI64(k);
        if (!s)
          return fail();
        loS(x, *s);
        break;
      }
      case ICmpInst::ICMP_ULT: {
        auto u = asU64(k);
        if (!u || *u == 0)
          return fail();
        hiU(x, *u - 1);
        break;
      }
      case ICmpInst::ICMP_ULE: {
        auto u = asU64(k);
        if (!u)
          return fail();
        hiU(x, *u);
        break;
      }
      case ICmpInst::ICMP_UGT: {
        auto u = asU64(k);
        if (!u || *u == std::numeric_limits<uint64_t>::max())
          return fail();
        loU(x, *u + 1);
        break;
      }
      case ICmpInst::ICMP_UGE: {
        auto u = asU64(k);
        if (!u)
          return fail();
        loU(x, *u);
        break;
      }
      default:
        break;
      }
    };
    auto holds = [&](unsigned pred, const std::string &a, const std::string &b) {
      if (pred == ICmpInst::ICMP_EQ)
        return a == b;
      if (pred == ICmpInst::ICMP_NE)
        return a != b;
      auto sa = asI64(a);
      auto sb = asI64(b);
      auto ua = asU64(a);
      auto ub = asU64(b);
      switch (pred) {
      case ICmpInst::ICMP_SLT:
        return sa && sb && *sa < *sb;
      case ICmpInst::ICMP_SLE:
        return sa && sb && *sa <= *sb;
      case ICmpInst::ICMP_SGT:
        return sa && sb && *sa > *sb;
      case ICmpInst::ICMP_SGE:
        return sa && sb && *sa >= *sb;
      case ICmpInst::ICMP_ULT:
        return ua && ub && *ua < *ub;
      case ICmpInst::ICMP_ULE:
        return ua && ub && *ua <= *ub;
      case ICmpInst::ICMP_UGT:
        return ua && ub && *ua > *ub;
      case ICmpInst::ICMP_UGE:
        return ua && ub && *ua >= *ub;
      default:
        return true;
      }
    };
    struct Live {
      unsigned pred = 0;
      int na = 0;
      int nb = 0;
      Cell a;
      Cell b;
      unsigned bytes = 8;
    };
    std::vector<Live> live;
    std::map<Cell, int> cur;
    std::map<Cell, int> entry;
    std::map<Cell, int> residNode;
    bool sawResidual = false;
    auto ensure = [&](const Cell &c) {
      if (cur.count(c))
        return;
      int id = make();
      cur[c] = entry[c] = id;
      if (sawResidual)
        residNode.emplace(c, id);
    };
    auto unite = [&](const Cell &dst, const Cell &src) {
      ensure(dst);
      ensure(src);
      int a = find(cur[dst]);
      int b = find(cur[src]);
      if (a == b)
        return;
      if (nodes[b].has)
        pin(a, nodes[b].val);
      else if (!nodes[b].any.empty())
        allow(a, nodes[b].any);
      forbid(a, nodes[b].ban);
      if (nodes[b].slo)
        loS(a, nodes[b].sloV);
      if (nodes[b].shi)
        hiS(a, nodes[b].shiV);
      if (nodes[b].ulo)
        loU(a, nodes[b].uloV);
      if (nodes[b].uhi)
        hiU(a, nodes[b].uhiV);
      if (nodes[b].ordBytes && !nodes[a].ordBytes)
        nodes[a].ordBytes = nodes[b].ordBytes;
      auto retarget = [&](int &id) {
        if (id == b)
          id = a;
      };
      for (auto &kv : cur)
        retarget(kv.second);
      for (auto &kv : entry)
        retarget(kv.second);
      for (auto &kv : residNode)
        retarget(kv.second);
      for (Live &L : live) {
        retarget(L.na);
        retarget(L.nb);
      }
    };
    auto cmpBytes = [](unsigned bits) {
      unsigned bytes = bits >= 8 ? bits / 8 : 8;
      if (bytes != 1 && bytes != 2 && bytes != 4 && bytes != 8)
        bytes = 8;
      return bytes;
    };
    auto strict = [](unsigned p) {
      return p == ICmpInst::ICMP_NE || p == ICmpInst::ICMP_SLT || p == ICmpInst::ICMP_SGT ||
             p == ICmpInst::ICMP_ULT || p == ICmpInst::ICMP_UGT;
    };
    for (size_t si = 0; si < mapped && si < seq.size(); ++si) {
      Function *SF = seq[si];
      std::vector<Instruction *> goals;
      if (si < stepGoal.size() && stepGoal[si])
        goals.push_back(stepGoal[si]);
      else {
        for (Instruction &I : instructions(*SF))
          if (sinkHere(I, sinkFile, sinkLine))
            goals.push_back(&I);
        if (goals.empty())
          for (BasicBlock &BB : *SF)
            if (auto *R = dyn_cast<ReturnInst>(BB.getTerminator()))
              goals.push_back(R);
      }
      if (si == residual) {
        sawResidual = true;
        for (const auto &kv : cur)
          residNode.emplace(kv.first, kv.second);
      }
      if (goals.empty())
        continue;
      std::vector<const Ev *> kept;
      for (const Ev &e : stepEv[si]) {
        if (!e.at)
          continue;
        bool all = true;
        for (Instruction *goal : goals) {
          if (e.anchor == goal) {
            all = false;
            break;
          }
          bool seqEv = e.fn == SF || !e.anchor;
          if (seqEv) {
            if (!dominatesBefore(e.at, goal))
              all = false;
          } else if (!(e.callMust && e.mustExit && dominatesBefore(e.anchor, goal)))
            all = false;
          if (!all)
            break;
        }
        if (all)
          kept.push_back(&e);
      }
      std::sort(kept.begin(), kept.end(), [&](const Ev *a, const Ev *b) {
        auto left = a->anchor ? rankOf(a->anchor) : rankOf(a->at);
        auto right = b->anchor ? rankOf(b->anchor) : rankOf(b->at);
        if (left != right)
          return left < right;
        int nestA = a->anchor ? 1 : 0;
        int nestB = b->anchor ? 1 : 0;
        if (nestA != nestB)
          return nestA < nestB;
        return rankOf(a->at) < rankOf(b->at);
      });
      for (const Ev *e : kept) {
        if (e->kind == 'c') {
          out << "copy " << si;
          writeCell(e->src);
          out << " ->";
          writeCell(e->cell);
          out << "\n";
          ensure(e->src);
          ensure(e->cell);
          cur[e->cell] = find(cur[e->src]);
        } else if (e->kind == 's') {
          out << "store " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          int id = make();
          cur[e->cell] = id;
          allow(id, e->vals);
        } else if (e->kind == 'e') {
          out << "pre " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          for (const std::string &v : e->vals)
            pin(cur[e->cell], v);
        } else if (e->kind == 'n') {
          out << "pre " << si;
          writeCell(e->cell);
          out << " !=";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          forbid(cur[e->cell], e->vals);
        } else if (e->kind == 'g') {
          out << "edge " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          allow(cur[e->cell], e->vals);
        } else if (e->kind == 'r') {
          out << "bound " << si;
          writeCell(e->cell);
          out << " " << icmpName((unsigned)e->pred);
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          unsigned bytes = cmpBytes(e->bits);
          for (const std::string &v : e->vals)
            boundConst(cur[e->cell], (unsigned)e->pred, v, bytes);
        } else if (e->kind == 'p') {
          out << "rel " << si;
          writeCell(e->cell);
          out << " " << icmpName((unsigned)e->pred);
          writeCell(e->src);
          out << "\n";
          unsigned pred = (unsigned)e->pred;
          if (e->cell == e->src) {
            if (strict(pred))
              tr.conflict = true;
            continue;
          }
          ensure(e->cell);
          ensure(e->src);
          unsigned bytes = cmpBytes(e->bits);
          if (pred == ICmpInst::ICMP_EQ) {
            unite(e->cell, e->src);
            continue;
          }
          int na = find(cur[e->cell]);
          int nb = find(cur[e->src]);
          if (pred == ICmpInst::ICMP_NE) {
            if (nodes[na].has && nodes[nb].has) {
              if (nodes[na].val == nodes[nb].val)
                tr.conflict = true;
            } else if (nodes[na].has)
              forbid(nb, {nodes[na].val});
            else if (nodes[nb].has)
              forbid(na, {nodes[nb].val});
            else
              live.push_back(Live{pred, na, nb, e->cell, e->src, bytes});
            continue;
          }
          if (nodes[na].has && nodes[nb].has) {
            if (!holds(pred, nodes[na].val, nodes[nb].val))
              tr.conflict = true;
          } else if (nodes[na].has)
            boundConst(nb, (unsigned)ICmpInst::getSwappedPredicate((ICmpInst::Predicate)pred), nodes[na].val, bytes);
          else if (nodes[nb].has)
            boundConst(na, pred, nodes[nb].val, bytes);
          else
            live.push_back(Live{pred, na, nb, e->cell, e->src, bytes});
        }
      }
    }
    for (const Live &L : live) {
      if (L.na < 0 || L.nb < 0 || L.na >= (int)nodes.size() || L.nb >= (int)nodes.size())
        continue;
      Node &na = nodes[L.na];
      Node &nb = nodes[L.nb];
      if (L.na == L.nb) {
        if (strict(L.pred))
          tr.conflict = true;
        continue;
      }
      if (na.has && nb.has) {
        if (!holds(L.pred, na.val, nb.val))
          tr.conflict = true;
        continue;
      }
      if (na.has && !nb.has) {
        boundConst(L.nb, (unsigned)ICmpInst::getSwappedPredicate((ICmpInst::Predicate)L.pred), na.val, L.bytes);
        continue;
      }
      if (!na.has && nb.has) {
        boundConst(L.na, L.pred, nb.val, L.bytes);
        continue;
      }
      auto onEntry = [&](const Cell &c, int id) {
        auto it = residNode.find(c);
        return it != residNode.end() && it->second == id;
      };
      if (!onEntry(L.a, L.na) || !onEntry(L.b, L.nb))
        continue;
      Rel r;
      r.pred = L.pred;
      r.a = L.a.first;
      r.asuf = L.a.second;
      r.b = L.b.first;
      r.bsuf = L.b.second;
      r.bytes = L.bytes ? L.bytes : 8;
      rels.push_back(r);
      out << "model";
      writeCell(L.a);
      out << " " << icmpName(L.pred);
      writeCell(L.b);
      out << "\n";
    }
    for (const auto &kv : entry) {
      int id = kv.second;
      if (auto it = residNode.find(kv.first); it != residNode.end())
        id = it->second;
      mem[kv.first] = readNode(nodes, find, id);
    }
    for (Solved &s : solvedCells) {
      auto it = mem.find({s.arg, s.suf});
      if (it == mem.end()) {
        if (s.glob.empty())
          s.vals.clear();
        s.ban.clear();
        continue;
      }
      s.slo = it->second.slo;
      s.shi = it->second.shi;
      s.ulo = it->second.ulo;
      s.uhi = it->second.uhi;
      s.sloV = it->second.sloV;
      s.shiV = it->second.shiV;
      s.uloV = it->second.uloV;
      s.uhiV = it->second.uhiV;
      s.ordBytes = it->second.ordBytes;
      if (!s.glob.empty())
        continue;
      if (it->second.known) {
        s.vals = {it->second.val};
        s.ban.clear();
        s.text.clear();
      } else if (!it->second.any.empty()) {
        s.vals = it->second.any;
        s.ban = it->second.ban;
        s.text.clear();
      } else {
        s.vals.clear();
        s.ban = it->second.ban;
      }
    }
    auto bounded = [](const SlotVal &s) { return s.slo || s.shi || s.ulo || s.uhi; };
    auto writeOrd = [&](const SlotVal &s) {
      if (s.slo)
        out << " sge " << s.sloV;
      if (s.shi)
        out << " sle " << s.shiV;
      if (s.ulo)
        out << " uge " << s.uloV;
      if (s.uhi)
        out << " ule " << s.uhiV;
    };
    auto inRel = [&](const Cell &c) {
      for (const Rel &r : rels)
        if ((r.a == c.first && r.asuf == c.second) || (r.b == c.first && r.bsuf == c.second))
          return true;
      return false;
    };
    for (const auto &kv : mem) {
      if (!kv.second.known && kv.second.any.empty() && kv.second.ban.empty() && !bounded(kv.second))
        continue;
      out << "model";
      writeCell(kv.first);
      if (kv.second.known) {
        out << " = " << kv.second.val;
      } else if (!kv.second.any.empty()) {
        out << " =";
        for (const std::string &v : kv.second.any)
          out << " " << v;
      }
      if (!kv.second.ban.empty() && !kv.second.known) {
        out << " !=";
        for (const std::string &v : kv.second.ban)
          out << " " << v;
      }
      writeOrd(kv.second);
      out << "\n";
    }
    for (const auto &c : cells) {
      auto it = mem.find(c);
      if (it != mem.end() && (it->second.known || !it->second.any.empty() || !it->second.ban.empty() || bounded(it->second)))
        continue;
      if (inRel(c))
        continue;
      out << "model";
      writeCell(c);
      out << " unknown\n";
    }
    out << (tr.conflict ? "unsat\n" : "sat\n");
    return !tr.conflict;
  }

 public:
  Function *exportFn() const { return entry; }

  StructType *structNamed(StringRef n) const {
    if (n.empty())
      return nullptr;
    for (StructType *S : down.getIdentifiedStructTypes())
      if (S->getName() == n)
        return S;
    for (StructType *S : up.getIdentifiedStructTypes())
      if (S->getName() == n)
        return S;
    return nullptr;
  }

  // The field of this struct at this byte offset is a pointer the program loads.
  bool fieldIsPointer(StringRef type, int64_t off) const {
    StructType *ST = structNamed(type);
    if (!ST || ST->isOpaque() || !ST->isSized() || off < 0)
      return false;
    const StructLayout *SL = dl.getStructLayout(ST);
    for (unsigned i = 0; i < ST->getNumElements(); ++i)
      if ((int64_t)SL->getElementOffset(i) == off)
        return ST->getElementType(i)->isPointerTy();
    return false;
  }

  // The harness calls the residual once. Solved cells are the initial memory
  // of the export arguments. The call receives the cells and constants that
  // enter the residual. Bytes no equation names stay symbolic.
  void emit(Module &H) const {
    if (!entry)
      return;
    LLVMContext &ctx = H.getContext();
    H.setDataLayout(down.getDataLayout());
    H.setTargetTriple(down.getTargetTriple());
    Type *i8 = Type::getInt8Ty(ctx);
    Type *i32 = Type::getInt32Ty(ctx);
    Type *i64 = Type::getInt64Ty(ctx);
    auto *ptrTy = PointerType::get(ctx, 0);
    auto *symTy = FunctionType::get(Type::getVoidTy(ctx), {ptrTy, i64, ptrTy}, false);
    auto *assumeTy = FunctionType::get(Type::getVoidTy(ctx), {i64}, false);
    auto *sym = Function::Create(symTy, Function::ExternalLinkage, "klee_make_symbolic", &H);
    auto *assume = Function::Create(assumeTy, Function::ExternalLinkage, "klee_assume", &H);
    auto declare = [&](Function *F) -> Function * {
      if (!F)
        return nullptr;
      if (Function *E = H.getFunction(F->getName()))
        return E;
      return Function::Create(F->getFunctionType(), Function::ExternalLinkage, F->getName(), &H);
    };
    auto fnNamed = [&](StringRef n) -> Function * {
      if (Function *F = down.getFunction(n))
        return F;
      return up.getFunction(n);
    };
    struct Piece {
      std::map<int64_t, Piece> child;
      std::map<int64_t, std::set<std::string>> word;
      std::map<int64_t, unsigned> width;
      std::map<int64_t, FunctionType *> fileAt;
      std::map<int64_t, uint64_t> fileLenAt;
      std::set<int64_t> pathPtrAt;
      std::map<int64_t, std::set<std::string>> text;
      std::map<int64_t, std::pair<std::string, uint64_t>> globAt;
      std::map<int64_t, uint64_t> symAt;
      std::map<int64_t, std::set<std::string>> ban;
      struct Ord {
        bool slo = false, shi = false, ulo = false, uhi = false;
        int64_t sloV = 0, shiV = 0;
        uint64_t uloV = 0, uhiV = 0;
      };
      std::map<int64_t, Ord> ordAt;
      // end-pointer offset -> offset of the pointer that begins the byte region
      std::map<int64_t, int64_t> boundAt;
      uint64_t size = 8;
    };
    std::map<int, Piece> args;
    auto declared = [&](int arg) -> uint64_t {
      if (!entry || arg < 0 || (unsigned)arg >= entry->arg_size())
        return 0;
      Argument *A = entry->getArg((unsigned)arg);
      if (!A->hasAttribute(Attribute::Dereferenceable))
        return 0;
      return A->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
    };
    for (const auto &ex : argExtent) {
      uint64_t n = std::max(ex.second, declared(ex.first));
      args[ex.first].size = std::max(args[ex.first].size, n);
    }
    for (const Solved &s : solvedCells) {
      Piece *p = &args[s.arg];
      Suffix walked;
      int64_t acc = 0;
      bool openPtr = false;
      for (size_t i = 0; i < s.suf.size(); ++i) {
        // A pointer field holds the next object. The step's own deref bit
        // records the same fact when the load was seen directly.
        bool into = s.suf[i].deref || openPtr;
        if (into) {
          p->size = std::max(p->size, (uint64_t)acc + 8);
          p = &p->child[acc];
          acc = 0;
        }
        int64_t off = s.suf[i].off < 0 ? 0 : s.suf[i].off;
        acc += off;
        walked.push_back(s.suf[i]);
        auto rb = readBytes.find({s.arg, walked});
        bool haveLen = rb != readBytes.end() && rb->second != 0;
        uint64_t span = 8;
        if (haveLen)
          span = std::max(span, rb->second);
        p->size = std::max(p->size, (uint64_t)acc + span);
        openPtr = fieldIsPointer(s.suf[i].type, off) && i + 1 < s.suf.size();
        if (i + 1 != s.suf.size())
          continue;
        if (s.file && s.fty) {
          p->fileAt[acc] = s.fty;
          if (s.len)
            p->fileLenAt[acc] = *s.len;
        } else if (s.pathPtr) {
          p->pathPtrAt.insert(acc);
          p->size = std::max(p->size, (uint64_t)acc + 8);
        } else if (!s.text.empty()) {
          p->text[acc] = s.text;
          uint64_t n = 1;
          for (const std::string &t : s.text)
            n = std::max(n, (uint64_t)t.size() + 1);
          p->size = std::max(p->size, (uint64_t)acc + n);
        } else if (!s.glob.empty()) {
          p->globAt[acc] = {s.glob, s.gbyte};
        } else if (!s.vals.empty()) {
          p->word[acc] = s.vals;
          p->width[acc] = s.width ? s.width : 8;
        } else if (!p->child.count(acc)) {
          p->symAt[acc] = span;
          if (!s.ban.empty()) {
            p->ban[acc] = s.ban;
            if (!p->width.count(acc))
              p->width[acc] = s.width ? s.width : (unsigned)span;
          }
        }
        if (s.slo || s.shi || s.ulo || s.uhi) {
          Piece::Ord o;
          o.slo = s.slo;
          o.shi = s.shi;
          o.ulo = s.ulo;
          o.uhi = s.uhi;
          o.sloV = s.sloV;
          o.shiV = s.shiV;
          o.uloV = s.uloV;
          o.uhiV = s.uhiV;
          p->ordAt[acc] = o;
          unsigned wd = s.ordBytes ? s.ordBytes : (s.width ? s.width : 8);
          if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
            wd = 8;
          if (!p->width.count(acc))
            p->width[acc] = wd;
          if (!p->word.count(acc) && !p->child.count(acc) && !p->symAt.count(acc) && !p->text.count(acc) &&
              !p->globAt.count(acc) && !p->fileAt.count(acc) && !p->pathPtrAt.count(acc))
            p->symAt[acc] = std::max<uint64_t>(span, wd);
        }
      }
    }
    for (const PathSrc &ps : pathSrc) {
      Piece &p = args[ps.arg];
      int64_t ptrOff = 0;
      int64_t intOff = -1;
      unsigned intW = 8;
      if (StructType *ST = structNamed(ps.fieldType))
        if (ST->isSized()) {
          const StructLayout *SL = dl.getStructLayout(ST);
          int64_t found = -1;
          for (unsigned i = 0; i < ST->getNumElements() && found < 0; ++i) {
            Type *E = ST->getElementType(i);
            int64_t o = (int64_t)SL->getElementOffset(i);
            if (E->isPointerTy())
              found = o;
            else if (auto *N = dyn_cast<StructType>(E))
              if (N->isSized() && N->getNumElements() && N->getElementType(0)->isPointerTy())
                found = o + (int64_t)dl.getStructLayout(N)->getElementOffset(0);
          }
          if (found >= 0)
            ptrOff = found;
          for (unsigned i = 0; i < ST->getNumElements(); ++i) {
            Type *E = ST->getElementType(i);
            int64_t o = (int64_t)SL->getElementOffset(i);
            if (o <= ptrOff || !E->isIntegerTy())
              continue;
            intOff = o;
            intW = std::max<unsigned>(1, E->getIntegerBitWidth() / 8);
            break;
          }
        }
      p.pathPtrAt.insert(ptrOff);
      p.size = std::max(p.size, (uint64_t)ptrOff + 8);
      if (intOff > ptrOff) {
        p.word[intOff] = {"1"};
        p.width[intOff] = intW;
        p.symAt.erase(intOff);
        p.size = std::max(p.size, (uint64_t)intOff + intW);
      }
    }
    auto placeIn = [&](int arg, const Suffix &suf) -> std::pair<Piece *, int64_t> {
      auto it = args.find(arg);
      if (it == args.end())
        return {nullptr, 0};
      Piece *p = &it->second;
      int64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        bool into = suf[i].deref || open;
        if (into) {
          auto ch = p->child.find(acc);
          if (ch == p->child.end())
            return {nullptr, 0};
          p = &ch->second;
          acc = 0;
        }
        acc += suf[i].off < 0 ? 0 : suf[i].off;
        open = fieldIsPointer(suf[i].type, suf[i].off) && i + 1 < suf.size();
      }
      return {p, acc};
    };
    for (const PtrSpan &sp : ptrSpan) {
      auto b = placeIn(sp.arg, sp.begin);
      auto e = placeIn(sp.arg, sp.end);
      if (!b.first || b.first != e.first || b.second == e.second)
        continue;
      if (!b.first->child.count(b.second))
        continue;
      b.first->boundAt[e.second] = b.second;
    }
    std::function<void(Piece &)> tieLen = [&](Piece &p) {
      for (auto &ch : p.child) {
        bool bytes = ch.second.child.empty() && ch.second.symAt.count(0) && ch.second.symAt.at(0) > dl.getPointerSize(0);
        int64_t lenOff = ch.first + (int64_t)dl.getPointerSize(0);
        auto sm = p.symAt.find(lenOff);
        if (bytes && sm != p.symAt.end() && !p.word.count(lenOff) && !p.child.count(lenOff)) {
          unsigned wd = (unsigned)sm->second;
          if (wd == 4 || wd == 8) {
            p.word[lenOff] = {std::to_string(ch.second.size)};
            p.width[lenOff] = wd;
            p.symAt.erase(sm);
          }
        }
        tieLen(ch.second);
      }
    };
    for (auto &kv : args)
      tieLen(kv.second);
    std::map<int, uint64_t> tiedCount;
    auto namesArg = [&](Value *V, unsigned argNo) {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *A = dyn_cast<Argument>(V))
          return A->getParent() == entry && A->getArgNo() == argNo;
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!Al)
            return false;
          Value *st = storedOnce(Al);
          if (!st)
            return false;
          V = st;
          continue;
        }
        return false;
      }
      return false;
    };
    // The integer is the buffer's length when a write in the entry passes
    // that pointer and, immediately after it, that integer.
    auto usedAsCount = [&](unsigned ptrArg, unsigned intArg) {
      if (!entry || entry->isDeclaration())
        return false;
      for (Instruction &I : instructions(*entry)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->onlyReadsMemory())
          continue;
        if (Function *C = CB->getCalledFunction()) {
          StringRef n = C->getName();
          if (n.starts_with("llvm.dbg.") || n.starts_with("llvm.lifetime.") || n.starts_with("llvm.experimental."))
            continue;
        }
        for (unsigned k = 0; k + 1 < CB->arg_size(); ++k) {
          if (!CB->getArgOperand(k)->getType()->isPointerTy() || !CB->getArgOperand(k + 1)->getType()->isIntegerTy())
            continue;
          if (CB->onlyReadsMemory(k))
            continue;
          if (namesArg(CB->getArgOperand(k), ptrArg) && namesArg(CB->getArgOperand(k + 1), intArg))
            return true;
        }
      }
      return false;
    };
    if (entry) {
      for (unsigned i = 0; i + 1 < entry->arg_size(); ++i) {
        Argument *P = entry->getArg(i);
        Argument *N = entry->getArg(i + 1);
        if (!P->getType()->isPointerTy() || !N->getType()->isIntegerTy())
          continue;
        if (!usedAsCount(i, i + 1))
          continue;
        Piece &p = args[(int)i];
        bool bare = p.child.empty() && p.symAt.empty() && p.text.empty() && p.word.empty() && p.pathPtrAt.empty() &&
                    p.fileAt.empty() && p.globAt.empty();
        if (!bare)
          continue;
        std::unordered_set<const Function *> seenF;
        uint64_t n = pointedExtent(entry, P, seenF, 0);
        if (P->hasAttribute(Attribute::Dereferenceable))
          n = std::max(n, P->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes());
        if (n == 0)
          continue;
        p.size = std::max(p.size, n);
        p.symAt[0] = n;
      }
    }
    Function *exp = declare(entry);
    auto *mainTy = FunctionType::get(i32, false);
    auto *mainF = Function::Create(mainTy, Function::ExternalLinkage, "main", &H);
    auto *BB = BasicBlock::Create(ctx, "entry", mainF);
    IRBuilder<> B(BB);
    auto *fdg = new GlobalVariable(H, i32, false, GlobalValue::PrivateLinkage, ConstantInt::get(i32, -1), "filefd");
    auto *openTy = FunctionType::get(i32, {ptrTy, i32}, true);
    auto *readTy = FunctionType::get(i64, {i32, ptrTy, i64}, false);
    auto *openF = Function::Create(openTy, Function::ExternalLinkage, "open", &H);
    auto *readF = Function::Create(readTy, Function::ExternalLinkage, "read", &H);
    auto *fileObj = new GlobalVariable(H, i8, false, GlobalValue::PrivateLinkage, ConstantInt::get(i8, 0), "fileobj");
    for (const FileIO &io : fileIO) {
      if (H.getFunction(io.name))
        continue;
      Function *Src = down.getFunction(io.name);
      if (!Src)
        Src = up.getFunction(io.name);
      if (!Src || !Src->isDeclaration())
        continue;
      FunctionType *FT = Src->getFunctionType();
      unsigned nArg = FT->getNumParams();
      auto inRange = [&](int i) { return i >= 0 && (unsigned)i < nArg; };
      if (io.opener && !inRange(io.pathArg))
        continue;
      if (!io.opener && (!inRange(io.bufArg) || !inRange(io.countArg)))
        continue;
      Function *F = Function::Create(FT, Function::ExternalLinkage, io.name, &H);
      auto *e = BasicBlock::Create(ctx, "e", F);
      IRBuilder<> IB(e);
      auto pathIsF = [&](Value *path) -> Value * {
        Value *c0 = IB.CreateLoad(i8, path);
        Value *c1 = IB.CreateLoad(i8, IB.CreateGEP(i8, path, {ConstantInt::get(i64, 1)}));
        return IB.CreateAnd(IB.CreateICmpEQ(c0, ConstantInt::get(i8, 'f')),
                             IB.CreateICmpEQ(c1, ConstantInt::get(i8, 0)));
      };
      if (io.opener) {
        Value *ok = pathIsF(F->getArg((unsigned)io.pathArg));
        if (io.retPtr)
          IB.CreateRet(IB.CreateSelect(ok, fileObj, Constant::getNullValue(ptrTy)));
        else if (F->getReturnType()->isIntegerTy())
          IB.CreateRet(IB.CreateSelect(ok, ConstantInt::get(F->getReturnType(), 3),
                                        ConstantInt::getSigned(F->getReturnType(), -1)));
        else
          IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      if (io.bufArg < 0 || io.countArg < 0 || (unsigned)io.bufArg >= F->arg_size() ||
          (unsigned)io.countArg >= F->arg_size()) {
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      Value *n = F->getArg((unsigned)io.countArg);
      if (!n->getType()->isIntegerTy()) {
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      if (n->getType() != i64)
        n = IB.CreateZExt(n, i64);
      if (io.count2 >= 0 && (unsigned)io.count2 < F->arg_size() &&
          F->getArg((unsigned)io.count2)->getType()->isIntegerTy()) {
        Value *m = F->getArg((unsigned)io.count2);
        if (m->getType() != i64)
          m = IB.CreateZExt(m, i64);
        n = IB.CreateMul(n, m);
      }
      auto *nm = IB.CreateGlobalString("f");
      IB.CreateCall(sym, {F->getArg((unsigned)io.bufArg), n, nm});
      Value *ret = io.count2 >= 0 ? F->getArg((unsigned)io.count2) : F->getArg((unsigned)io.countArg);
      if (!F->getReturnType()->isIntegerTy())
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
      else if (ret->getType() == F->getReturnType())
        IB.CreateRet(ret);
      else
        IB.CreateRet(IB.CreateZExtOrTrunc(ret, F->getReturnType()));
    }
    {
      auto *e = BasicBlock::Create(ctx, "e", openF);
      IRBuilder<> IB(e);
      Value *path = openF->getArg(0);
      Value *c0 = IB.CreateLoad(i8, path);
      Value *c1 = IB.CreateLoad(i8, IB.CreateGEP(i8, path, {ConstantInt::get(i64, 1)}));
      Value *ok = IB.CreateAnd(IB.CreateICmpEQ(c0, ConstantInt::get(i8, 'f')),
                                IB.CreateICmpEQ(c1, ConstantInt::get(i8, 0)));
      IB.CreateRet(IB.CreateSelect(ok, ConstantInt::get(i32, 3), ConstantInt::get(i32, -1)));
    }
    {
      auto *e = BasicBlock::Create(ctx, "e", readF);
      auto *yes = BasicBlock::Create(ctx, "file", readF);
      auto *no = BasicBlock::Create(ctx, "other", readF);
      IRBuilder<> IB(e);
      IB.CreateCondBr(IB.CreateICmpEQ(readF->getArg(0), ConstantInt::get(i32, 3)), yes, no);
      IB.SetInsertPoint(yes);
      auto *nm = IB.CreateGlobalString("f");
      IB.CreateCall(sym, {readF->getArg(1), readF->getArg(2), nm});
      IB.CreateRet(readF->getArg(2));
      IB.SetInsertPoint(no);
      IB.CreateRet(ConstantInt::get(i64, (uint64_t)-1));
    }
    std::map<std::pair<FunctionType *, uint64_t>, Function *> readers;
    auto readerFor = [&](FunctionType *FT, uint64_t len) -> Function * {
      auto it = readers.find({FT, len});
      if (it != readers.end())
        return it->second;
      auto *F = Function::Create(FT, Function::ExternalLinkage, "fileread", &H);
      auto *e = BasicBlock::Create(ctx, "e", F);
      auto *op = BasicBlock::Create(ctx, "op", F);
      auto *rd = BasicBlock::Create(ctx, "rd", F);
      IRBuilder<> IB(e);
      Value *buf = nullptr;
      Value *n = nullptr;
      for (Argument &A : F->args()) {
        if (!buf && A.getType()->isPointerTy())
          buf = &A;
        if (!n && A.getType()->isIntegerTy())
          n = &A;
      }
      if (!buf || !n) {
        IB.CreateRet(Constant::getNullValue(FT->getReturnType()));
        readers[{FT, len}] = F;
        return F;
      }
      auto *path = IB.CreateGlobalString("f");
      Value *cur = IB.CreateLoad(i32, fdg);
      IB.CreateCondBr(IB.CreateICmpSLT(cur, ConstantInt::get(i32, 0)), op, rd);
      IB.SetInsertPoint(op);
      Value *opened = IB.CreateCall(openF, {path, ConstantInt::get(i32, 0)});
      IB.CreateStore(opened, fdg);
      IB.CreateBr(rd);
      IB.SetInsertPoint(rd);
      auto *phi = IB.CreatePHI(i32, 2);
      phi->addIncoming(cur, e);
      phi->addIncoming(opened, op);
      Value *count = n;
      if (n->getType() != i64)
        count = IB.CreateZExtOrTrunc(n, i64);
      if (len != ~uint64_t{0}) {
        Value *eq = IB.CreateICmpEQ(count, ConstantInt::get(i64, len));
        IB.CreateCall(assume, {IB.CreateZExt(eq, i64)});
      }
      Value *got = IB.CreateCall(readF, {phi, buf, count});
      if (FT->getReturnType()->isVoidTy())
        IB.CreateRetVoid();
      else if (FT->getReturnType() == i64)
        IB.CreateRet(got);
      else if (FT->getReturnType()->isIntegerTy())
        IB.CreateRet(IB.CreateZExtOrTrunc(got, FT->getReturnType()));
      else
        IB.CreateRet(Constant::getNullValue(FT->getReturnType()));
      readers[{FT, len}] = F;
      return F;
    };
    unsigned ai = 0;
    for (Argument &A : entry->args()) {
      if (ai < callActs.size()) {
        const Act &a = callActs[ai];
        if (A.getType()->isPointerTy() && a.loc && a.address && a.loc->suf.empty()) {
          Piece &p = args[a.loc->arg];
          uint64_t n = 0;
          if (A.hasAttribute(Attribute::Dereferenceable))
            n = A.getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
          if (A.hasStructRetAttr()) {
            Type *T = A.getAttribute(Attribute::StructRet).getValueAsType();
            if (T && T->isSized())
              n = std::max(n, (uint64_t)dl.getTypeAllocSize(T).getFixedValue());
          }
          p.size = std::max(p.size, std::max<uint64_t>(n, 8));
        }
      }
      ++ai;
    }
    struct Built {
      Value *base = nullptr;
      std::map<int64_t, Built> child;
    };
    int nameN = 0;
    std::function<Built(const Piece &)> mat = [&](const Piece &p) -> Built {
      uint64_t nbytes = p.size ? p.size : 8;
      auto *arr = ArrayType::get(i8, nbytes);
      Value *base = B.CreateAlloca(arr);
      B.CreateMemSet(base, ConstantInt::get(i8, 0), nbytes, MaybeAlign(1));
      Built built;
      built.base = base;
      for (const auto &sm : p.symAt) {
        if (p.child.count(sm.first) || p.word.count(sm.first) || p.text.count(sm.first) ||
            p.pathPtrAt.count(sm.first) || p.fileAt.count(sm.first) || p.globAt.count(sm.first))
          continue;
        if ((uint64_t)sm.first >= nbytes)
          continue;
        uint64_t n = sm.second;
        if ((uint64_t)sm.first + n > nbytes)
          n = nbytes - (uint64_t)sm.first;
        if (n == 0)
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)sm.first)});
        // klee_make_symbolic names one whole object. These bytes are a range
        // of the cell, so they are a separate object copied into that range.
        Value *tmp = B.CreateAlloca(ArrayType::get(i8, n));
        auto *nm = B.CreateGlobalString("a" + std::to_string(nameN++));
        B.CreateCall(sym, {tmp, ConstantInt::get(i64, n), nm});
        B.CreateMemCpy(slot, MaybeAlign(1), tmp, MaybeAlign(1), ConstantInt::get(i64, n));
      }
      for (const auto &b : p.ban) {
        auto sit = p.symAt.find(b.first);
        if (sit == p.symAt.end() || b.second.empty())
          continue;
        unsigned wd = p.width.count(b.first) ? p.width.at(b.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        if (sit->second < wd)
          continue;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)b.first)});
        Value *got = B.CreateLoad(ty, slot);
        Value *ok = ConstantInt::getTrue(ctx);
        for (const std::string &v : b.second)
          ok = B.CreateAnd(ok, B.CreateICmpNE(got, ConstantInt::get(ty, (uint64_t)std::stoll(v), true)));
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      for (const auto &o : p.ordAt) {
        auto sit = p.symAt.find(o.first);
        if (sit == p.symAt.end())
          continue;
        unsigned wd = p.width.count(o.first) ? p.width.at(o.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        if (sit->second < wd)
          continue;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)o.first)});
        Value *got = B.CreateLoad(ty, slot);
        Value *ok = ConstantInt::getTrue(ctx);
        const Piece::Ord &b = o.second;
        if (b.slo)
          ok = B.CreateAnd(ok, B.CreateICmpSGE(got, ConstantInt::get(ty, (uint64_t)b.sloV, true)));
        if (b.shi)
          ok = B.CreateAnd(ok, B.CreateICmpSLE(got, ConstantInt::get(ty, (uint64_t)b.shiV, true)));
        if (b.ulo)
          ok = B.CreateAnd(ok, B.CreateICmpUGE(got, ConstantInt::get(ty, b.uloV, false)));
        if (b.uhi)
          ok = B.CreateAnd(ok, B.CreateICmpULE(got, ConstantInt::get(ty, b.uhiV, false)));
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      for (const auto &f : p.fileAt) {
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)f.first)});
        uint64_t len = ~uint64_t{0};
        auto lit = p.fileLenAt.find(f.first);
        if (lit != p.fileLenAt.end())
          len = lit->second;
        B.CreateStore(readerFor(f.second, len), slot);
      }
      for (const auto &g : p.globAt) {
        GlobalVariable *src = down.getNamedGlobal(g.second.first);
        if (!src)
          src = up.getNamedGlobal(g.second.first);
        if (src && !p.child.count(g.first)) {
          GlobalVariable *gv = H.getNamedGlobal(src->getName());
          if (!gv)
            gv = new GlobalVariable(H, src->getValueType(), false, GlobalValue::ExternalLinkage, nullptr, src->getName());
          Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)g.first)});
          Value *addr = B.CreateGEP(i8, gv, {ConstantInt::get(i64, g.second.second)});
          B.CreateStore(addr, slot);
        }
      }
      for (int64_t off : p.pathPtrAt) {
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)off)});
        auto *bytes = B.CreateGlobalString("f");
        B.CreateStore(bytes, slot);
      }
      for (const auto &t : p.text) {
        if (p.child.count(t.first) || t.second.empty())
          continue;
        std::vector<std::string> opts(t.second.begin(), t.second.end());
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)t.first)});
        auto *kmem = B.CreateAlloca(i32);
        auto *kn = B.CreateGlobalString("k" + std::to_string(nameN++));
        B.CreateCall(sym, {kmem, ConstantInt::get(i64, 4), kn});
        Value *k = B.CreateLoad(i32, kmem);
        Value *inRange = B.CreateICmpULT(k, ConstantInt::get(i32, opts.size()));
        B.CreateCall(assume, {B.CreateZExt(inRange, i64)});
        Function *mf = B.GetInsertBlock()->getParent();
        auto *cont = BasicBlock::Create(ctx, "kcont", mf);
        auto *def = BasicBlock::Create(ctx, "kdef", mf);
        auto *sw = B.CreateSwitch(k, def, opts.size());
        auto storeText = [&](BasicBlock *bb, const std::string &str) {
          IRBuilder<> IB(bb);
          for (size_t i = 0; i <= str.size(); ++i) {
            Value *at = IB.CreateGEP(i8, slot, {ConstantInt::get(i64, i)});
            IB.CreateStore(ConstantInt::get(i8, i == str.size() ? 0 : (unsigned char)str[i]), at);
          }
          IB.CreateBr(cont);
        };
        for (unsigned i = 0; i < opts.size(); ++i) {
          BasicBlock *bb = i == 0 ? def : BasicBlock::Create(ctx, "kcase", mf);
          if (i != 0)
            sw->addCase(cast<ConstantInt>(ConstantInt::get(i32, i)), bb);
          storeText(bb, opts[i]);
        }
        B.SetInsertPoint(cont);
      }
      for (const auto &ch : p.child) {
        Built inner = mat(ch.second);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)ch.first)});
        B.CreateStore(inner.base, slot);
        built.child.emplace(ch.first, std::move(inner));
      }
      for (const auto &bd : p.boundAt) {
        auto cit = built.child.find(bd.second);
        auto pit = p.child.find(bd.second);
        if (cit == built.child.end() || pit == p.child.end())
          continue;
        Value *end = B.CreateGEP(i8, cit->second.base, {ConstantInt::get(i64, pit->second.size)});
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)bd.first)});
        B.CreateStore(end, slot);
      }
      for (const auto &w : p.word) {
        if (p.child.count(w.first))
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)w.first)});
        unsigned wd = p.width.count(w.first) ? p.width.at(w.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        bool allFn = true;
        for (const std::string &v : w.second)
          if (!fnNamed(v))
            allFn = false;
        if (w.second.size() == 1) {
          if (allFn)
            B.CreateStore(declare(fnNamed(*w.second.begin())), slot);
          else
            B.CreateStore(ConstantInt::get(ty, (uint64_t)std::stoll(*w.second.begin()), true), slot);
          continue;
        }
        auto *nm = B.CreateGlobalString("c" + std::to_string(nameN++));
        Value *tmp = B.CreateAlloca(ArrayType::get(i8, wd));
        B.CreateCall(sym, {tmp, ConstantInt::get(i64, wd), nm});
        B.CreateMemCpy(slot, MaybeAlign(1), tmp, MaybeAlign(1), ConstantInt::get(i64, wd));
        Value *got = B.CreateLoad(allFn ? ptrTy : ty, slot);
        Value *ok = ConstantInt::get(Type::getInt1Ty(ctx), 0);
        for (const std::string &v : w.second) {
          Value *want = nullptr;
          if (Function *F = fnNamed(v))
            want = declare(F);
          else
            want = ConstantInt::get(ty, (uint64_t)std::stoll(v), true);
          ok = B.CreateOr(ok, B.CreateICmpEQ(got, want));
        }
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      return built;
    };
    std::map<int, Built> roots;
    auto rootFor = [&](int arg) -> Built {
      auto it = roots.find(arg);
      if (it != roots.end())
        return it->second;
      Piece p = args.count(arg) ? args[arg] : Piece{};
      if (p.size < 8)
        p.size = 8;
      Built b = mat(p);
      roots.emplace(arg, b);
      return b;
    };
    auto place = [&](const Built &root, const Suffix &suf) -> std::pair<Value *, uint64_t> {
      const Built *cur = &root;
      Value *at = root.base;
      uint64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        const Step &s = suf[i];
        if (s.deref || open) {
          auto it = cur->child.find((int64_t)acc);
          if (it == cur->child.end())
            break;
          cur = &it->second;
          at = cur->base;
          acc = 0;
        }
        acc += (uint64_t)(s.off < 0 ? 0 : s.off);
        open = fieldIsPointer(s.type, s.off) && i + 1 < suf.size();
      }
      return {at, acc};
    };
    auto addressOf = [&](const Built &root, const Suffix &suf) -> Value * {
      auto at = place(root, suf);
      if (!at.second)
        return at.first;
      return B.CreateGEP(i8, at.first, {ConstantInt::get(i64, at.second)});
    };
    auto valueOf = [&](const Built &root, const Suffix &suf) -> Value * {
      const Built *cur = &root;
      uint64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        const Step &s = suf[i];
        if (s.deref || open) {
          auto it = cur->child.find((int64_t)acc);
          if (it == cur->child.end())
            break;
          cur = &it->second;
          acc = 0;
        }
        acc += (uint64_t)(s.off < 0 ? 0 : s.off);
        open = fieldIsPointer(s.type, s.off) && i + 1 < suf.size();
      }
      auto it = cur->child.find((int64_t)acc);
      if (it != cur->child.end())
        return it->second.base;
      if (suf.empty())
        return root.base;
      return B.CreateLoad(ptrTy, addressOf(root, suf));
    };
    auto symInt = [&](Type *ty) -> Value * {
      unsigned bits = ty->getIntegerBitWidth();
      uint64_t n = std::max<uint64_t>(1, (bits + 7) / 8);
      Value *mem = B.CreateAlloca(ty);
      auto *nm = B.CreateGlobalString("i" + std::to_string(nameN++));
      B.CreateCall(sym, {mem, ConstantInt::get(i64, n), nm});
      return B.CreateLoad(ty, mem);
    };
    std::vector<Value *> acts;
    ai = 0;
    for (Argument &A : entry->args()) {
      Act a = ai < callActs.size() ? callActs[ai] : Act{};
      ++ai;
      Value *act = nullptr;
      if (a.nullPtr) {
        act = Constant::getNullValue(A.getType());
      } else if (!a.fn.empty()) {
        Function *F = fnNamed(a.fn);
        act = F ? declare(F) : Constant::getNullValue(A.getType());
      } else if (A.getType()->isIntegerTy()) {
        auto tc = tiedCount.find((int)acts.size());
        if (tc != tiedCount.end())
          act = ConstantInt::get(A.getType(), tc->second);
        else if (a.haveInt)
          act = ConstantInt::get(A.getType(), (uint64_t)a.ival, true);
        else if (a.loc && !a.address)
          act = B.CreateLoad(A.getType(), addressOf(rootFor(a.loc->arg), a.loc->suf));
        else
          act = symInt(A.getType());
      } else if (A.getType()->isPointerTy() && a.loc) {
        Built root = rootFor(a.loc->arg);
        act = a.address || a.loc->suf.empty() ? addressOf(root, a.loc->suf) : valueOf(root, a.loc->suf);
      } else if (A.getType()->isPointerTy()) {
        Piece p;
        uint64_t n = 8;
        if (A.hasAttribute(Attribute::Dereferenceable))
          n = std::max(n, A.getAttribute(Attribute::Dereferenceable).getDereferenceableBytes());
        if (A.hasStructRetAttr()) {
          Type *T = A.getAttribute(Attribute::StructRet).getValueAsType();
          if (T && T->isSized())
            n = std::max(n, (uint64_t)dl.getTypeAllocSize(T).getFixedValue());
        }
        p.size = n;
        act = mat(p).base;
      } else {
        act = Constant::getNullValue(A.getType());
      }
      acts.push_back(act);
    }
    for (const Rel &r : rels) {
      unsigned wd = r.bytes;
      if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
        wd = 8;
      Type *ty = Type::getIntNTy(ctx, wd * 8);
      auto loadAt = [&](int arg, const Suffix &suf) -> Value * {
        Built root = rootFor(arg);
        auto at = place(root, suf);
        Value *slot = at.second ? B.CreateGEP(i8, at.first, {ConstantInt::get(i64, at.second)}) : at.first;
        return B.CreateLoad(ty, slot);
      };
      Value *cmp = B.CreateICmp((ICmpInst::Predicate)r.pred, loadAt(r.a, r.asuf), loadAt(r.b, r.bsuf));
      B.CreateCall(assume, {B.CreateZExt(cmp, i64)});
    }
    B.CreateCall(exp, acts);
    B.CreateRet(ConstantInt::get(i32, 0));
  }
};

static bool loadSink(const fs::path &yaml, std::string &file, unsigned &line) {
  std::ifstream in(yaml);
  std::string s;
  file.clear();
  line = 0;
  while (std::getline(in, s)) {
    auto pos = s.find_first_not_of(" \t");
    if (pos == std::string::npos)
      continue;
    s = s.substr(pos);
    if (s.rfind("File:", 0) == 0) {
      auto v = s.substr(5);
      auto b = v.find_first_not_of(" \t");
      file = b == std::string::npos ? "" : v.substr(b);
    } else if (s.rfind("Line:", 0) == 0)
      line = (unsigned)std::stoul(s.substr(5));
  }
  return !file.empty() && line != 0;
}

int main(int argc, char **argv) {
  if (argc != 3 && argc != 4) {
    errs() << "usage: model <cve-dir> <out-dir> [sequence]\n";
    return 1;
  }
  fs::path dir = argv[1];
  fs::path outDir = argv[2];
  int seqPick = argc == 4 ? std::atoi(argv[3]) : 0;
  std::string file;
  unsigned line = 0;
  if (!loadSink(dir / "sink.yaml", file, line)) {
    errs() << "missing sink\n";
    return 1;
  }
  LLVMContext ctx;
  SMDiagnostic err;
  auto up = parseIRFile((dir / "upstream.bc").string(), err, ctx);
  if (!up) {
    err.print("model", errs());
    return 1;
  }
  SMDiagnostic derr;
  auto down = parseIRFile((dir / "se_lib" / "downstream.closure.bc").string(), derr, ctx);
  if (!down) {
    derr.print("model", errs());
    return 1;
  }
  std::error_code ec;
  fs::create_directories(outDir);
  raw_fd_ostream out((outDir / "state.txt").string(), ec);
  if (ec) {
    errs() << ec.message() << "\n";
    return 1;
  }
  Model model(*down, *up, file, line);
  model.run(seqPick, out);
  out.flush();
  errs() << dir.filename().string() << " " << (outDir / "state.txt").string() << "\n";
  if (!model.exportFn())
    return 0;
  Module harness("harness", ctx);
  model.emit(harness);
  if (verifyModule(harness, &errs()))
    return 1;
  Linker linker(harness);
  if (linker.linkInModule(std::move(down)) || linker.linkInModule(std::move(up))) {
    errs() << "link failed\n";
    return 1;
  }
  // An internal definition is renamed when an external declaration of the
  // same name already exists. The cell stores that declaration; point it at
  // the definition.
  std::vector<Function *> decls;
  for (Function &F : harness)
    if (F.isDeclaration() && F.getName() != "klee_make_symbolic" && F.getName() != "klee_assume")
      decls.push_back(&F);
  for (Function *D : decls) {
    Function *body = nullptr;
    std::string prefix = (D->getName() + ".").str();
    for (Function &F : harness) {
      if (F.isDeclaration() || F.getFunctionType() != D->getFunctionType())
        continue;
      if (F.getName() == D->getName() || F.getName().starts_with(prefix)) {
        body = &F;
        break;
      }
    }
    if (!body)
      continue;
    D->replaceAllUsesWith(body);
    D->eraseFromParent();
  }
  // A call with no body whose pointer argument is the address of a pointer
  // the caller then loads stores an object of its last integer argument.
  std::map<Function *, int> allocSlot;
  std::map<Function *, int> allocSize;
  std::set<Function *> allocSkip;
  for (Function &F : harness) {
    if (F.isDeclaration())
      continue;
    for (Instruction &I : instructions(F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Function *D = CB->getCalledFunction();
      if (!D || !D->isDeclaration() || D->getName().starts_with("llvm.") || !D->getReturnType()->isIntegerTy())
        continue;
      int lastInt = -1;
      int slot = -1;
      for (unsigned a = 0; a < CB->arg_size() && a < D->arg_size(); ++a) {
        if (D->getArg(a)->getType()->isIntegerTy())
          lastInt = (int)a;
        if (!D->getArg(a)->getType()->isPointerTy())
          continue;
        auto *Al = dyn_cast<AllocaInst>(CB->getArgOperand(a)->stripPointerCasts());
        if (!Al)
          continue;
        bool loaded = false;
        for (User *U : Al->users()) {
          auto *Ld = dyn_cast<LoadInst>(U);
          if (Ld && Ld->getType()->isPointerTy() && Ld->getPointerOperand()->stripPointerCasts() == Al)
            loaded = true;
        }
        if (!loaded)
          continue;
        if (slot != -1 && slot != (int)a)
          slot = -2;
        else if (slot != -2)
          slot = (int)a;
      }
      if (slot < 0 || lastInt < 0)
        continue;
      auto sit = allocSlot.find(D);
      if (sit == allocSlot.end()) {
        allocSlot[D] = slot;
        allocSize[D] = lastInt;
      } else if (sit->second != slot || allocSize[D] != lastInt)
        allocSkip.insert(D);
    }
  }
  Function *Malloc = harness.getFunction("malloc");
  if (!Malloc)
    Malloc = Function::Create(FunctionType::get(PointerType::get(ctx, 0), {Type::getInt64Ty(ctx)}, false),
                              GlobalValue::ExternalLinkage, "malloc", &harness);
  for (const auto &kv : allocSlot) {
    Function *D = kv.first;
    if (!D->isDeclaration() || allocSkip.count(D))
      continue;
    int slot = kv.second;
    int sz = allocSize[D];
    if (slot < 0 || sz < 0 || (unsigned)slot >= D->arg_size() || (unsigned)sz >= D->arg_size())
      continue;
    auto *BB = BasicBlock::Create(ctx, "entry", D);
    IRBuilder<> IB(BB);
    Value *n = D->getArg((unsigned)sz);
    if (n->getType() != Type::getInt64Ty(ctx))
      n = n->getType()->getIntegerBitWidth() < 64 ? IB.CreateZExt(n, Type::getInt64Ty(ctx))
                                                  : IB.CreateTrunc(n, Type::getInt64Ty(ctx));
    IB.CreateStore(IB.CreateCall(Malloc, {n}), D->getArg((unsigned)slot));
    IB.CreateRet(Constant::getNullValue(D->getReturnType()));
  }
  std::error_code bec;
  raw_fd_ostream bc((outDir / "run.bc").string(), bec);
  if (bec) {
    errs() << bec.message() << "\n";
    return 1;
  }
  WriteBitcodeToFile(harness, bc);
  return 0;
}
