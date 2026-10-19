#include "Field.hpp"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <climits>
#include <limits>
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {
namespace {

constexpr int64_t Any = INT64_MIN;

struct Step {
  int parent = 0;
  int formal = -1;
  int type = 0;
  int64_t off = 0;
  uint64_t seen = 0;
  // Join of how the gep that built this step was reached. FromLoad means the
  // pointer was a load, so the step is a new object. FromAddr means it was
  // the previous address, so the step is a field of the same object. Both
  // bits may be set. The bit is not part of the step's identity: two arrivals
  // that differ only here are one step, and the join is height 2.
  uint8_t bound = 0;
};

constexpr uint8_t FromAddr = 1;
constexpr uint8_t FromLoad = 2;

struct InternKey {
  int parent, formal, type;
  int64_t off;
  bool operator==(const InternKey &o) const {
    return parent == o.parent && formal == o.formal && type == o.type && off == o.off;
  }
};

struct InternHash {
  size_t operator()(const InternKey &k) const {
    size_t h = (size_t)k.parent * 1315423911u;
    h ^= (size_t)k.formal + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= (size_t)k.type + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= (size_t)k.off + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};

struct VKey {
  const llvm::Value *v;
  int formal;
  int path;
  bool operator==(const VKey &o) const { return v == o.v && formal == o.formal && path == o.path; }
};

struct VHash {
  size_t operator()(const VKey &k) const {
    return ((size_t)k.v >> 4) ^ ((size_t)k.formal * 1315423911u) ^ ((size_t)k.path * 2654435761u);
  }
};

struct Fact {
  int dep = 0;
  // FromAddr, FromLoad, or both. The next gep joins this into the step.
  uint8_t origin = 0;
};

struct PairHash {
  size_t operator()(const std::pair<int, int64_t> &p) const {
    return (size_t)p.first * 1315423911u ^ (size_t)p.second;
  }
};

struct VecHash {
  size_t operator()(const std::vector<int> &v) const {
    size_t h = v.size();
    for (int x : v)
      h = h * 1315423911u + (size_t)x;
    return h;
  }
};

struct Slot {
  int formal = -1;
  int key = 0;
};

struct Ret {
  int formal = -1;
  int path = 0;
  int dep = 0;
  int fdep = 0;
  int sdep = 0;
  uint8_t origin = 0;
};

struct Wr {
  int formal = -1;
  int path = 0;
  int64_t len = 0;
  int dep = 0;
  int fdep = 0;
  int sdep = 0;
  int key = 0;
  // The stored value is this formal's object. A later load of `path` denotes
  // `srcFormal` at `srcPath`. -1 means the value is not one formal.
  int srcFormal = -1;
  int srcPath = 0;
  std::string fn;
};

struct CopySite {
  int df = -1, dp = 0, sf = -1, sp = 0;
  int64_t n = 0;
  bool anyN = true;
};

// kind 0 formal, 1 alloca or noalias return, 2 global, 3 open.
// pointee: the actual is a loaded pointer, so the callee's offsets are bytes
// of that object and the path is the cell that holds its address.
struct LiftFrom {
  int kind = 3;
  int formal = -1;
  int path = 0;
  std::string name;
  bool pointee = false;
  bool operator==(const LiftFrom &o) const {
    return kind == o.kind && formal == o.formal && path == o.path && name == o.name && pointee == o.pointee;
  }
};

// A store into an alloca that is passed to the callee. The value is a formal
// of the caller, so a load of this byte offset in the callee is that formal.
struct Carried {
  int64_t off = 0;
  int formal = -1;
  int path = 0;
  bool operator==(const Carried &o) const { return off == o.off && formal == o.formal && path == o.path; }
};

struct ArgAt {
  std::vector<int> keys;
  std::vector<int> formals;
  std::vector<int> vformals;
  std::vector<LiftFrom> lift;
  std::vector<Carried> carried;
  int chain = 0;
};

struct Pub {
  int formal = -1;
  int slot = 0;
  int box = -1;
};

// An indirect call whose operand denotes formal `formal` of `home`.
struct CallArg {
  int formal = -1;
  llvm::FunctionType *fty = nullptr;
};

// A read of the fd held by formal `obj` of this function.
// `len > 0` is a constant byte count. `len == 0` with `a` or `b` set names
// those formals as the factors. `len == 0` with both factors unset means the
// transfer size is the size the call executes. `buf` is the formal the
// bytes are written into, or -1 when that pointer is not a formal. `keys`
// are the field keys of the buffer and of stores of values loaded from it.
struct PRead {
  int obj = -1;
  int buf = -1;
  int a = -1;
  int b = -1;
  int64_t len = 0;
  int fdGroup = -1;
  std::vector<int> keys;
};

// One call argument after casts and alloca reloads. `group` identifies the
// pointer. `formal` is set when that pointer is a single formal.
struct ArgBind {
  int formal = -1;
  int group = -1;
  int64_t cst = 0;
};

// One predicate that must hold for this call to be the taken one.
// The loaded cell is (formal, path), `len` bytes.
// `vals` are constants of an icmp against that load. EQ with several
// values is their disjunction. `otherFormal >= 0` means the other
// operand is that access path, and `vals` is empty.
struct Fix {
  int formal = -1;
  int path = 0;
  int otherFormal = -1;
  int otherPath = 0;
  int64_t len = 0;
  unsigned pred = 0;
  std::vector<llvm::APInt> vals;
  // The icmp reads (cell & mask), not the whole cell.
  bool masked = false;
  llvm::APInt mask{1, 0};
};

bool sameFix(const Fix &a, const Fix &b) {
  if (a.formal != b.formal || a.path != b.path || a.otherFormal != b.otherFormal || a.otherPath != b.otherPath ||
      a.len != b.len || a.pred != b.pred || a.vals != b.vals || a.masked != b.masked)
    return false;
  if (!a.masked)
    return true;
  return a.mask.getBitWidth() == b.mask.getBitWidth() && a.mask == b.mask;
}

struct Site {
  llvm::Function *callee = nullptr;
  llvm::Function *home = nullptr;
  llvm::FunctionType *fty = nullptr;
  int calleeBox = -1;
  int idx = 0;
  std::vector<int> calleeFormals;
  std::vector<int> calleeKeys;
  // Access path of the pointer an indirect call loads. One formal, one path.
  int calleeFormal = -1;
  int calleePath = 0;
  // Every access path the loaded pointer may denote.
  std::vector<std::pair<int, int>> calleeAt;
  // Virtual call: byte offset in the vtable, and the receiver object.
  int vtableOff = -1;
  std::vector<std::pair<int, int>> vtableRecv;
  std::string vtableTy;
  std::vector<ArgAt> args;
  std::vector<Fix> fixes;
  // Block of the call. The zero-path flips that reach this block are settings.
  const llvm::BasicBlock *at = nullptr;
  const llvm::Instruction *call = nullptr;
};

struct Edge {
  llvm::Function *fn = nullptr;
  int arg = -1;
};

struct FAHash {
  size_t operator()(const std::pair<llvm::Function *, int> &p) const {
    return ((size_t)p.first >> 4) ^ ((size_t)p.second * 1315423911u);
  }
};

// Predicates that hold at one return, in this function's formals.
// `concrete` is true when the returned value is one integer.
struct RetPred {
  bool concrete = false;
  llvm::APInt val{1, 0};
  std::vector<Fix> cond;
  const llvm::BasicBlock *at = nullptr;
};

struct FnSum {
  std::vector<Ret> rets;
  std::vector<RetPred> retPreds;
  std::vector<Wr> writes;
  std::vector<CopySite> copies;
  std::vector<Site> sites;
  std::vector<Pub> pubs;
  std::vector<CallArg> callArgs;
  std::vector<int> lineKeys;
  std::vector<int> nameKeys;
  std::vector<int> lineFormals;
  std::vector<int> nameFormals;
  std::vector<Edge> lineEdges;
  std::vector<Edge> nameEdges;
  std::vector<int> indirectKeys;
  // Set when analyze() wrote this summary. A lookup that only default-inserts
  // the map entry has not summarized the function.
  bool ran = false;
  // A read of a file opened from this formal. len is a constant byte count.
  std::vector<std::pair<int, int64_t>> files;
  // Formals passed to open or fopen in this function.
  std::vector<int> opens;
  // Formal `obj` holds an fd opened from formal `path` of this function.
  std::vector<std::pair<int, int>> carries;
  std::vector<PRead> preads;
  // Parallel to sites. One row per call, one bind per argument.
  std::vector<std::vector<ArgBind>> binds;
  // Function pointers the zero path loads on the way to a success return.
  // formal/path name the slot in this function. name is the stored function.
  struct ZeroFn {
    int formal = -1;
    int path = 0;
    std::string name;
    llvm::Function *fn = nullptr;
  };
  std::vector<ZeroFn> zeroFns;
  // A store performed by this function. valFormal >= 0 means the cell holds
  // that formal's object. hasConst means the cell holds cnst.
  struct DataStore {
    int formal = -1;
    int path = 0;
    int key = 0;
    int valFormal = -1;
    bool hasConst = false;
    llvm::APInt cnst{1, 0};
    int64_t len = 0;
  };
  std::vector<DataStore> data;
  // A load of a tracked field. `at` is the block that executes it.
  // `pointee` is the struct a later getelementptr reads through this pointer.
  struct Rd {
    const llvm::BasicBlock *at = nullptr;
    int formal = -1;
    int path = 0;
    int key = 0;
    int64_t len = 0;
    int64_t objLen = 0;
    bool pointer = false;
    bool ptrField = false;
    std::string pointee;
  };
  std::vector<Rd> reads;
  const llvm::BasicBlock *sinkAt = nullptr;
  // Group of each formal after alloca reloads.
  std::vector<int> argGroup;
  // A store of `group` into formal `obj`.
  std::vector<std::pair<int, int>> holds;
  // A pointer `group` loaded from formal `obj`.
  std::vector<std::pair<int, int>> fromObj;
  // The fopen result `group` was opened from formal `path`.
  std::vector<std::pair<int, int>> openAt;
  // fdopen's stream group carries the file of its fd group.
  std::vector<std::pair<int, int>> streamOf;
  // A byte loaded from the source formal is stored through the dest formal.
  std::vector<std::pair<int, int>> byteFrom;
  // A pointer store and a pointer load at the same address. The load carries
  // the file of the stored value.
  std::vector<std::pair<int, int>> ptrStore;
  std::vector<std::pair<int, int>> ptrLoad;
  bool hitLine = false;
  bool hitName = false;
  uint64_t retSig = 0;
  uint64_t fnSig = 0;
};

struct WRef {
  llvm::Function *fn = nullptr;
  Wr w;
};

class Engine {
 public:
  Engine(llvm::Module &down, llvm::Module &up, std::string file, unsigned line, std::vector<std::string> sinks)
      : down(down), up(up), file(std::move(file)), line(line), sinkFns(std::move(sinks)) {
    steps.push_back(Step{});
    deps.push_back({});
    fdeps.push_back({});
    slots.push_back(Slot{});
    sdeps.push_back({});
  }

  FieldReport run(const std::vector<std::string> &chops,
                        const std::unordered_map<std::string, std::vector<Input>> &inputs) {
    for (const std::string &c : chops)
      chopName.insert(c);
    for (const auto &kv : inputs)
      for (const Input &in : kv.second)
        if (in.arg >= 0)
          passIn.insert({in.func, in.arg});
    inMap = &inputs;
    numberInsts();
    index();
    callGraph();
    orderFns();
    solve();
    forwardCopies();
    return answer();
  }

 private:
  llvm::Module &down;
  llvm::Module &up;
  std::string file;
  unsigned line = 0;
  std::vector<std::string> sinkFns;
  std::unordered_map<llvm::Function *, bool> sinkReach;
  bool anyLine = false;

  std::vector<Step> steps;
  std::unordered_map<InternKey, int, InternHash> interned;
  std::unordered_map<InternKey, int, InternHash> appendMemo;
  std::unordered_map<InternKey, int, InternHash> appendMemoPrecise;

  std::vector<std::string> typeName;
  std::unordered_map<std::string, int> typeByName;
  std::unordered_map<int, unsigned> typeElems;
  std::unordered_set<std::string> structNames;
  std::unordered_map<const llvm::StructType *, int> typeId;
  std::unordered_map<int, const llvm::StructType *> typeById;
  std::unordered_map<std::pair<int, int64_t>, int, PairHash> keys;
  std::unordered_map<InternKey, int, InternHash> chainMemo;
  int chainN = 1;
  std::vector<int> chainParent{0};
  std::vector<int> chainTy{0};
  std::vector<int64_t> chainOff{0};
  std::vector<std::vector<int>> deps;
  std::unordered_map<std::vector<int>, int, VecHash> depMemo;
  std::unordered_map<std::uint64_t, int> uniteMemo;
  std::vector<std::vector<int>> fdeps;
  std::unordered_map<std::vector<int>, int, VecHash> fdepMemo;
  std::unordered_map<std::uint64_t, int> funiteMemo;
  std::vector<Slot> slots;
  std::unordered_map<std::uint64_t, int> slotMemo;
  std::vector<std::vector<int>> sdeps;
  std::unordered_map<std::vector<int>, int, VecHash> sdepMemo;
  std::unordered_map<std::uint64_t, int> suniteMemo;

  std::unordered_map<std::string, llvm::Function *> byName;
  std::unordered_map<const llvm::Instruction *, int> instOrd;
  std::unordered_map<llvm::Function *, std::vector<llvm::Function *>> callers, callees;
  std::unordered_map<llvm::Function *, std::unordered_set<llvm::Function *>> indirectCallers;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> watchers;
  std::vector<llvm::Function *> order;
  std::unordered_map<llvm::Function *, int> ord;
  std::unordered_map<llvm::Function *, FnSum> sum;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> fnAt;
  // Functions stored by one function. The witness keeps the stores of the
  // function that also stores a callee of the kept sequence.
  std::unordered_map<llvm::Function *, std::unordered_set<llvm::Function *>> storesOf;
  // Functions named by a global initializer. A codec is selected from that
  // table. A store in a function that is not in the table is the default.
  std::unordered_set<llvm::Function *> globalFns;
  // Itanium vtable slots, keyed by the byte offset from the address point.
  bool vtableFilled = false;
  std::unordered_map<int, std::vector<std::pair<llvm::Function *, std::string>>> vtFns;
  // Functions passed as a formal, keyed by the callee and the formal index.
  std::unordered_map<llvm::Function *, std::unordered_map<int, std::unordered_set<llvm::Function *>>> fnPassed;
  // Slots where a global initializer stores a function. A call that loads
  // the same field calls that function. Vtable address-point keys stay apart.
  std::unordered_map<llvm::Function *, std::vector<int>> initSlotOf;
  // Slots a function returns. A call of that return loads these slots.
  std::unordered_map<const llvm::Function *, std::vector<int>> retSlotCache;
  std::unordered_set<const llvm::Function *> retSlotBusy;
  std::unordered_set<llvm::Function *> analyzing;
  // Set while a return or an sret write is being read. The callee is
  // summarized first, and that summary may summarize the call that fills
  // the object it returns. The backward cone does not follow these calls.
  bool deepSum = false;
  // Summaries of callees are read while laying out one sequence. The fixpoint
  // that builds call edges does not follow those callees.
  bool alongSequence = false;
  std::unordered_set<llvm::Function *> deepened;
  std::unordered_set<const llvm::Value *> *walkStack = nullptr;
  // Functions stored through a call, keyed by the object's field chain and the inner slot.
  std::unordered_map<std::uint64_t, std::unordered_set<llvm::Function *>> held;
  std::vector<WRef> extra;
  std::set<std::string> chopName;
  std::set<std::pair<std::string, int>> passIn;
  const std::unordered_map<std::string, std::vector<Input>> *inMap = nullptr;
  std::unordered_set<int> pointerOnly;

  static bool allPointers(const llvm::StructType *T) {
    if (!T || T->isOpaque() || T->getNumElements() == 0)
      return false;
    for (llvm::Type *E : T->elements()) {
      if (E->isPointerTy())
        continue;
      if (const auto *A = llvm::dyn_cast<llvm::ArrayType>(E))
        if (A->getElementType()->isPointerTy())
          continue;
      return false;
    }
    return true;
  }

  llvm::Function *bodyOf(llvm::Function *F) {
    if (!F || F->isIntrinsic())
      return nullptr;
    if (!F->isDeclaration())
      return F;
    if (!F->hasName())
      return nullptr;
    std::string n = F->getName().str();
    auto defined = [&](const std::string &m) -> llvm::Function * {
      auto it = byName.find(m);
      if (it == byName.end() || it->second->isDeclaration())
        return nullptr;
      return it->second;
    };
    if (llvm::Function *G = defined(n))
      return G;
    // Itanium: a declaration of the complete or allocating constructor is
    // the base constructor when that one is the body in this module. The
    // same rule joins the deleting and complete destructors to the base
    // destructor. The class and the parameters stay the same.
    auto alt = [&](const char *a, const char *b) -> llvm::Function * {
      auto pos = n.find(a);
      if (pos == std::string::npos)
        return nullptr;
      std::string m = n;
      m.replace(pos, std::char_traits<char>::length(a), b);
      return defined(m);
    };
    if (llvm::Function *G = alt("C1E", "C2E"))
      return G;
    if (llvm::Function *G = alt("C3E", "C2E"))
      return G;
    if (llvm::Function *G = alt("C2E", "C1E"))
      return G;
    if (llvm::Function *G = alt("C1E", "C3E"))
      return G;
    if (llvm::Function *G = alt("C3E", "C1E"))
      return G;
    if (llvm::Function *G = alt("C2E", "C3E"))
      return G;
    if (llvm::Function *G = alt("D1E", "D2E"))
      return G;
    if (llvm::Function *G = alt("D0E", "D2E"))
      return G;
    if (llvm::Function *G = alt("D2E", "D1E"))
      return G;
    if (llvm::Function *G = alt("D0E", "D1E"))
      return G;
    if (llvm::Function *G = alt("D1E", "D0E"))
      return G;
    if (llvm::Function *G = alt("D2E", "D0E"))
      return G;
    return nullptr;
  }

  std::string canonicalName(llvm::StringRef n) const {
    auto dot = n.rfind('.');
    if (dot == llvm::StringRef::npos || dot + 1 >= n.size())
      return n.str();
    for (size_t i = dot + 1; i < n.size(); ++i)
      if (n[i] < '0' || n[i] > '9')
        return n.str();
    std::string prefix = n.substr(0, dot).str();
    if (!structNames.count(prefix))
      return n.str();
    return prefix;
  }

  int internType(const llvm::StructType *T) {
    auto cached = typeId.find(T);
    if (cached != typeId.end())
      return cached->second;
    if (T->hasName()) {
      std::string n = canonicalName(T->getName());
      unsigned nEl = T->getNumElements();
      auto nit = typeByName.find(n);
      if (nit != typeByName.end() && typeElems[nit->second] == nEl) {
        typeId.emplace(T, nit->second);
        return nit->second;
      }
      if (nit != typeByName.end())
        n = T->getName().str();
      int id = (int)typeName.size() + 1;
      typeByName.emplace(n, id);
      typeElems.emplace(id, nEl);
      typeName.push_back(std::move(n));
      typeId.emplace(T, id);
      typeById.emplace(id, T);
      if (allPointers(T))
        pointerOnly.insert(id);
      return id;
    }
    int id = (int)typeName.size() + 1;
    typeName.push_back("anon" + std::to_string(id));
    typeId.emplace(T, id);
    typeById.emplace(id, T);
    if (allPointers(T))
      pointerOnly.insert(id);
    return id;
  }

  // A string is basic_string or string_view by declared name. A struct of
  // pointers, such as heif_track, is an object.
  bool stringTypeName(llvm::StringRef n) {
    return n.contains("basic_string") || n.contains("string_view");
  }

  bool diCharContainer(const llvm::DIType *T) {
    std::unordered_set<const llvm::DIType *> seen;
    std::function<bool(const llvm::DIType *)> peel = [&](const llvm::DIType *U) -> bool {
      if (!U || !seen.insert(U).second)
        return false;
      if (const auto *D = llvm::dyn_cast<llvm::DIDerivedType>(U)) {
        unsigned tag = D->getTag();
        if (tag == llvm::dwarf::DW_TAG_typedef || tag == llvm::dwarf::DW_TAG_const_type ||
            tag == llvm::dwarf::DW_TAG_restrict_type || tag == llvm::dwarf::DW_TAG_volatile_type ||
            tag == llvm::dwarf::DW_TAG_reference_type || tag == llvm::dwarf::DW_TAG_rvalue_reference_type ||
            tag == llvm::dwarf::DW_TAG_pointer_type || tag == llvm::dwarf::DW_TAG_member ||
            tag == llvm::dwarf::DW_TAG_inheritance)
          return peel(D->getBaseType());
        return false;
      }
      if (llvm::isa<llvm::DIBasicType>(U))
        return false;
      const auto *C = llvm::dyn_cast<llvm::DICompositeType>(U);
      return C && stringTypeName(C->getName());
    };
    return peel(T);
  }

  bool argDiChar(llvm::Function *Fn, int formal) {
    if (!Fn || Fn->isDeclaration() || formal < 0 || formal >= (int)Fn->arg_size())
      return false;
    bool saw = false;
    bool ok = true;
    auto take = [&](const llvm::DIType *Ty) {
      if (!Ty)
        return;
      saw = true;
      if (!diCharContainer(Ty))
        ok = false;
    };
    for (llvm::Instruction &I : llvm::instructions(*Fn)) {
      const auto *D = llvm::dyn_cast<llvm::DbgDeclareInst>(&I);
      if (!D || !D->getVariable() || D->getVariable()->getArg() != (unsigned)formal + 1)
        continue;
      take(D->getVariable()->getType());
    }
    const llvm::Argument *A = Fn->getArg((unsigned)formal);
    for (llvm::DbgDeclareInst *D : llvm::findDbgDeclares(const_cast<llvm::Argument *>(A))) {
      if (!D || !D->getVariable() || D->getVariable()->getArg() != (unsigned)formal + 1)
        continue;
      take(D->getVariable()->getType());
    }
    return saw && ok;
  }

  int internStep(int parent, int formal, int type, int64_t off) {
    if (parent > 0)
      formal = steps[parent].formal;
    InternKey k{parent, formal, type, off};
    auto it = interned.find(k);
    if (it != interned.end())
      return it->second;
    int id = (int)steps.size();
    uint64_t seen = parent > 0 ? steps[parent].seen : 0;
    seen |= 1ull << ((unsigned)type & 63);
    steps.push_back(Step{parent, formal, type, off, seen, 0});
    interned.emplace(k, id);
    return id;
  }

  void noteBound(int step, uint8_t origin) {
    if (step <= 0 || (size_t)step >= steps.size())
      return;
    // A step that already denotes the loaded object stays that object. Adding
    // the address bit would also place the same offset in the pointer cell.
    if (steps[step].bound == FromLoad)
      origin = (uint8_t)(origin & ~FromAddr);
    steps[step].bound = (uint8_t)(steps[step].bound | (origin & (FromAddr | FromLoad)));
  }

  int append(int formal, int path, int type, int64_t off, bool *step = nullptr, bool precise = false) {
    auto done = [&](int id, bool isStep) {
      if (step)
        *step = isStep;
      return id;
    };
    if (type <= 0 && off != Any)
      return done(path, false);
    // Two unknown indices in a row are one unknown cell. A constant field
    // after an unknown address is a field of the object that address points
    // at, so it stays on the path.
    if (path > 0 && steps[path].off == Any && off == Any)
      return done(path, true);
    InternKey memoKey{path, formal, type, off};
    auto &memo = precise ? appendMemoPrecise : appendMemo;
    auto mit = memo.find(memoKey);
    if (mit != memo.end())
      return done(mit->second, true);
    // Inside one function a repeated type-hash joins the earlier step, so that
    // walk stays finite. Across a call, the same type under a different parent
    // is a different object and is kept. The parent walk runs only when the
    // hash is already present.
    int repeat = 0;
    uint64_t bit = 1ull << ((unsigned)type & 63);
    if (off != Any && path > 0 && (steps[path].seen & bit)) {
      int parentTy = precise && path > 0 ? steps[path].type : 0;
      int hashed = 0;
      for (int p = path; p > 0; p = steps[p].parent) {
        uint64_t prev = steps[p].parent > 0 ? steps[steps[p].parent].seen : 0;
        if ((steps[p].seen & bit) && !(prev & bit))
          hashed = p;
        if (!precise)
          continue;
        int pty = steps[p].parent > 0 ? steps[steps[p].parent].type : 0;
        if (steps[p].type == type && steps[p].off == off && pty == parentTy) {
          repeat = p;
          break;
        }
      }
      // A 6-bit hash joins only inside one function. On a call sequence the
      // type is exact: a different parent is a different object, and a cycle
      // is the earlier step of that same type and offset.
      if (repeat == 0 && !precise)
        repeat = hashed;
    }
    int result;
    if (repeat == 0) {
      result = internStep(path, formal, type, off);
      // The parent step is a pointer cell that was loaded. This offset is a
      // byte of the loaded object, so the step denotes that object.
      if (path > 0 && off != Any && (steps[path].bound & FromLoad) && (steps[path].bound & FromAddr))
        steps[result].bound = FromLoad;
    } else
      result = repeat;
    memo.emplace(memoKey, result);
    return done(result, true);
  }

  int concat(int formal, int base, int ext, bool precise = false) {
    struct Part {
      int type;
      int64_t off;
      uint8_t bound;
    };
    std::vector<Part> suf;
    for (int p = ext; p > 0; p = steps[p].parent)
      suf.push_back(Part{steps[p].type, steps[p].off, steps[p].bound});
    int cur = base;
    for (int i = (int)suf.size() - 1; i >= 0; --i) {
      bool stepped = false;
      cur = append(formal, cur, suf[i].type, suf[i].off, &stepped, precise);
      if (stepped)
        noteBound(cur, suf[i].bound);
    }
    return cur;
  }

  int keyAt(int type, int64_t off) {
    if (type <= 0)
      return 0;
    if (pointerOnly.count(type)) {
      auto e = typeElems.find(type);
      if (e == typeElems.end() || e->second < 2)
        return 0;
    }
    auto it = keys.find({type, off});
    if (it != keys.end())
      return it->second;
    int id = (int)keys.size() + 1;
    keys.emplace(std::pair<int, int64_t>{type, off}, id);
    return id;
  }

  int lastKey(int path) {
    if (path <= 0)
      return 0;
    return keyAt(steps[path].type, steps[path].off);
  }

  // Slot identity is the sequence of struct fields, outer field first.
  // Two puns of one LLVM struct match only when that sequence is the same.
  int slotStep(int parent, int type, int64_t off) {
    if (type <= 0)
      return parent;
    InternKey k{parent, 0, type, off};
    auto it = chainMemo.find(k);
    if (it != chainMemo.end())
      return it->second;
    int id = chainN++;
    chainMemo.emplace(k, id);
    if ((int)chainParent.size() <= id) {
      chainParent.resize((size_t)id + 1);
      chainTy.resize((size_t)id + 1);
      chainOff.resize((size_t)id + 1);
    }
    chainParent[(size_t)id] = parent;
    chainTy[(size_t)id] = type;
    chainOff[(size_t)id] = off;
    return id;
  }

  int pathToSlot(int path) {
    std::vector<std::pair<int, int64_t>> rev;
    for (int p = path; p > 0; p = steps[p].parent)
      rev.push_back({steps[p].type, steps[p].off});
    int cur = 0;
    for (int i = (int)rev.size() - 1; i >= 0; --i)
      cur = slotStep(cur, rev[i].first, rev[i].second);
    return cur;
  }

  static bool callTypeMatches(const llvm::Function *F, const llvm::FunctionType *Ty) {
    if (!Ty)
      return true;
    return F && F->getFunctionType() == Ty;
  }

  int internDep(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = depMemo.find(v);
    if (it != depMemo.end())
      return it->second;
    int id = (int)deps.size();
    depMemo.emplace(v, id);
    deps.push_back(std::move(v));
    return id;
  }

  int unite(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = uniteMemo.find(k);
    if (it != uniteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(deps[a].size() + deps[b].size());
    m.insert(m.end(), deps[a].begin(), deps[a].end());
    m.insert(m.end(), deps[b].begin(), deps[b].end());
    int id = internDep(std::move(m));
    uniteMemo.emplace(k, id);
    return id;
  }

  int oneKey(int key) {
    if (key <= 0)
      return 0;
    return internDep({key});
  }

  int internF(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = fdepMemo.find(v);
    if (it != fdepMemo.end())
      return it->second;
    int id = (int)fdeps.size();
    fdepMemo.emplace(v, id);
    fdeps.push_back(std::move(v));
    return id;
  }

  int uniteF(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = funiteMemo.find(k);
    if (it != funiteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(fdeps[a].size() + fdeps[b].size());
    m.insert(m.end(), fdeps[a].begin(), fdeps[a].end());
    m.insert(m.end(), fdeps[b].begin(), fdeps[b].end());
    int id = internF(std::move(m));
    funiteMemo.emplace(k, id);
    return id;
  }

  int oneF(int formal) {
    if (formal < 0)
      return 0;
    return internF({formal});
  }

  int internSlot(int formal, int key) {
    if (formal < 0 || key <= 0)
      return 0;
    uint64_t k = ((uint64_t)(unsigned)formal << 32) | (unsigned)key;
    auto it = slotMemo.find(k);
    if (it != slotMemo.end())
      return it->second;
    int id = (int)slots.size();
    slots.push_back(Slot{formal, key});
    slotMemo.emplace(k, id);
    return id;
  }

  int internS(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = sdepMemo.find(v);
    if (it != sdepMemo.end())
      return it->second;
    int id = (int)sdeps.size();
    sdepMemo.emplace(v, id);
    sdeps.push_back(std::move(v));
    return id;
  }

  int uniteS(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = suniteMemo.find(k);
    if (it != suniteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(sdeps[a].size() + sdeps[b].size());
    m.insert(m.end(), sdeps[a].begin(), sdeps[a].end());
    m.insert(m.end(), sdeps[b].begin(), sdeps[b].end());
    int id = internS(std::move(m));
    suniteMemo.emplace(k, id);
    return id;
  }

  int oneS(int slot) {
    if (slot <= 0)
      return 0;
    return internS({slot});
  }

  static std::string baseName(llvm::StringRef p) {
    auto s = p.find_last_of("/\\");
    return (s == llvm::StringRef::npos ? p : p.drop_front(s + 1)).str();
  }

  bool onLine(const llvm::Instruction &I) const {
    const llvm::DebugLoc &DL = I.getDebugLoc();
    if (!DL || file.empty() || line == 0)
      return false;
    const llvm::DILocation *S = DL.get();
    while (S) {
      if (S->getLine() == line && S->getFile() && baseName(S->getFile()->getFilename()) == baseName(file))
        return true;
      S = S->getInlinedAt();
    }
    return false;
  }

  bool nameMatch(llvm::Function &F) const {
    if (!F.hasName() || sinkFns.empty())
      return false;
    std::string raw = F.getName().str();
    std::string dem = llvm::demangle(raw);
    for (const std::string &s : sinkFns)
      if (!s.empty() && (s == raw || s == dem))
        return true;
    return false;
  }

  // A function reaches the sink by a direct call or by a function stored in a
  // slot it loads. A true answer stays true as more stores appear. A false
  // answer is not cached: a later store can add the missing edge.
  bool reachesSink(llvm::Function *Start) {
    if (!Start)
      return false;
    auto it = sinkReach.find(Start);
    if (it != sinkReach.end() && it->second)
      return true;
    std::unordered_set<llvm::Function *> seen;
    std::vector<llvm::Function *> q{Start};
    bool yes = false;
    while (!q.empty()) {
      llvm::Function *G = q.back();
      q.pop_back();
      if (!G || G->isDeclaration() || !seen.insert(G).second)
        continue;
      if (nameMatch(*G)) {
        yes = true;
        break;
      }
      bool here = false;
      for (llvm::Instruction &I : llvm::instructions(*G))
        if (onLine(I))
          here = true;
      if (here) {
        yes = true;
        break;
      }
      const llvm::DataLayout &DL = G->getParent()->getDataLayout();
      for (llvm::Instruction &I : llvm::instructions(*G)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB)
          continue;
        llvm::Function *C = CB->getCalledFunction();
        if (!C)
          if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            C = FN;
        if (C)
          C = bodyOf(C);
        if (C && !C->isDeclaration()) {
          q.push_back(C);
          continue;
        }
        for (int slot : fnSlotsOf(CB->getCalledOperand(), DL)) {
          eachAt(slot, [&](llvm::Function *T) {
            if (callTypeMatches(T, CB->getFunctionType()))
              if (llvm::Function *B = bodyOf(T))
                q.push_back(B);
          });
        }
      }
    }
    if (yes)
      sinkReach[Start] = true;
    return yes;
  }

  void numberInsts() {
    int n = 0;
    auto walk = [&](llvm::Module &M) {
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F))
          instOrd.emplace(&I, n++);
      }
    };
    walk(down);
    walk(up);
  }

  // Instruction order across both modules. A non-instruction is ordered by
  // its operand text, so the walk does not follow the use list.
  bool userBefore(const llvm::User *a, const llvm::User *b) const {
    if (a == b)
      return false;
    const auto *ia = llvm::dyn_cast<llvm::Instruction>(a);
    const auto *ib = llvm::dyn_cast<llvm::Instruction>(b);
    auto ordOf = [&](const llvm::Instruction *I) {
      if (!I)
        return INT_MAX;
      auto it = instOrd.find(I);
      return it == instOrd.end() ? INT_MAX : it->second;
    };
    int oa = ordOf(ia);
    int ob = ordOf(ib);
    if (oa != ob)
      return oa < ob;
    if (oa != INT_MAX)
      return false;
    std::string sa, sb;
    llvm::raw_string_ostream osa(sa), osb(sb);
    a->printAsOperand(osa, false);
    b->printAsOperand(osb, false);
    return sa < sb;
  }

  std::vector<const llvm::User *> orderedUsers(const llvm::Value *V) const {
    std::vector<const llvm::User *> us;
    if (!V)
      return us;
    for (const llvm::User *U : V->users())
      us.push_back(U);
    std::sort(us.begin(), us.end(), [&](const llvm::User *a, const llvm::User *b) { return userBefore(a, b); });
    return us;
  }

  void index() {
    auto add = [&](llvm::Module &M) {
      for (llvm::StructType *T : M.getIdentifiedStructTypes())
        if (T->hasName())
          structNames.insert(T->getName().str());
      for (llvm::Function &F : M) {
        if (F.isDeclaration() || F.isIntrinsic() || !F.hasName())
          continue;
        byName.emplace(F.getName().str(), &F);
      }
    };
    add(down);
    add(up);
    std::vector<llvm::StructType *> namedTy;
    auto collectNamed = [&](llvm::Module &M) {
      for (llvm::StructType *T : M.getIdentifiedStructTypes())
        if (T->hasName() && !T->isOpaque() && T->getNumElements() > 0)
          namedTy.push_back(T);
    };
    collectNamed(down);
    collectNamed(up);
    auto sameType = [&](llvm::Type *a, llvm::Type *b, const llvm::DataLayout &DL, auto &self) -> bool {
      if (a == b)
        return true;
      if (a->isPointerTy() && b->isPointerTy())
        return true;
      if (const auto *aa = llvm::dyn_cast<llvm::ArrayType>(a)) {
        const auto *bb = llvm::dyn_cast<llvm::ArrayType>(b);
        return bb && aa->getNumElements() == bb->getNumElements() &&
               self(aa->getElementType(), bb->getElementType(), DL, self);
      }
      auto *as = llvm::dyn_cast<llvm::StructType>(a);
      auto *bs = llvm::dyn_cast<llvm::StructType>(b);
      if (!as || !bs || as->isOpaque() || bs->isOpaque() || as->getNumElements() != bs->getNumElements())
        return false;
      const llvm::StructLayout *A = DL.getStructLayout(as);
      const llvm::StructLayout *B = DL.getStructLayout(bs);
      if (A->getSizeInBytes() != B->getSizeInBytes())
        return false;
      for (unsigned i = 0; i < as->getNumElements(); ++i) {
        if (A->getElementOffset(i) != B->getElementOffset(i))
          return false;
        if (!self(as->getElementType(i), bs->getElementType(i), DL, self))
          return false;
      }
      return true;
    };
    auto scanInit = [&](llvm::Constant *C, const llvm::DataLayout &DL, int parent, auto &self) -> void {
      if (!C)
        return;
      if (const auto *Fn0 = llvm::dyn_cast<llvm::Function>(C->stripPointerCasts()))
        if (Fn0->hasName() && !Fn0->isIntrinsic())
          globalFns.insert(const_cast<llvm::Function *>(Fn0));
      if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
        auto *ST = const_cast<llvm::StructType *>(CS->getType());
        int ty = internType(ST);
        const llvm::StructLayout *SL = DL.getStructLayout(ST);
        std::vector<int> twins;
        if (!ST->hasName()) {
          for (llvm::StructType *NT : namedTy) {
            if (NT->getNumElements() != ST->getNumElements())
              continue;
            const llvm::StructLayout *NL = DL.getStructLayout(NT);
            if (!sameType(ST, NT, DL, sameType))
              continue;
            twins.push_back(internType(NT));
          }
        }
        for (unsigned i = 0; i < CS->getNumOperands(); ++i) {
          llvm::Constant *Op = CS->getOperand(i);
          int64_t off = (int64_t)SL->getElementOffset(i);
          int slot = slotStep(parent, ty, off);
          const auto *Fn = llvm::dyn_cast<llvm::Function>(Op->stripPointerCasts());
          if (Fn && Fn->hasName() && !Fn->isIntrinsic()) {
            llvm::Function *BF = bodyOf(const_cast<llvm::Function *>(Fn));
            if (!BF)
              BF = const_cast<llvm::Function *>(Fn);
            if (slot > 0) {
              fnAt[slot].insert(BF);
              initSlotOf[BF].push_back(slot);
            }
            for (int nt : twins) {
              int alt = slotStep(parent, nt, off);
              if (alt > 0) {
                fnAt[alt].insert(BF);
                initSlotOf[BF].push_back(alt);
              }
            }
          }
          self(Op, DL, slot, self);
        }
        return;
      }
      if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
        for (llvm::Value *Op : CA->operands())
          self(llvm::cast<llvm::Constant>(Op), DL, parent, self);
      }
    };
    auto scanGlobals = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      for (llvm::GlobalVariable &G : M.globals())
        if (G.hasInitializer())
          scanInit(G.getInitializer(), DL, 0, scanInit);
    };
    scanGlobals(down);
    scanGlobals(up);
    // A vtable is a global array of functions. The object stores the array
    // address plus a constant bias. A call loads a constant index from that
    // address. The target set is the functions at that index whose object has
    // the receiver's size. A base embedded at byte 0 shares the receiver size.
    auto fileRelative = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      constexpr int kRel = 0x40000000;
      auto pack = [](int sz, int64_t off) -> int64_t {
        return ((int64_t)sz << 32) | (off & 0xffffffffLL);
      };
      for (llvm::GlobalVariable &G : M.globals()) {
        if (!G.hasInitializer())
          continue;
        struct Bias {
          std::set<int> sizes;
          std::set<int> tys;
        };
        std::map<int64_t, Bias> byBias;
        for (const llvm::User *U : orderedUsers(&G)) {
          const auto *GOP = llvm::dyn_cast<llvm::GEPOperator>(U);
          if (!GOP)
            continue;
          llvm::APInt ap(DL.getIndexSizeInBits(GOP->getPointerAddressSpace()), 0);
          if (!GOP->accumulateConstantOffset(DL, ap) || ap.isNegative())
            continue;
          int64_t bias = ap.getSExtValue();
          for (const llvm::User *UU : orderedUsers(U)) {
            auto *St = llvm::dyn_cast<llvm::StoreInst>(UU);
            if (!St || St->getValueOperand()->stripPointerCasts() != U)
              continue;
            const llvm::Value *dest = St->getPointerOperand()->stripPointerCasts();
            std::set<int> sizes;
            std::set<int> tys;
            std::set<llvm::StructType *> seenTy;
            auto addSizes = [&](llvm::StructType *ST, auto &self) -> void {
              if (!ST || ST->isOpaque() || !seenTy.insert(ST).second)
                return;
              int id = internType(ST);
              if (id > 0)
                tys.insert(id);
              int sz = (int)DL.getTypeAllocSize(ST);
              if (sz > 0)
                sizes.insert(sz);
              if (ST->getNumElements() == 0)
                return;
              if (DL.getStructLayout(ST)->getElementOffset(0) != 0)
                return;
              if (auto *fs = llvm::dyn_cast<llvm::StructType>(ST->getElementType(0)))
                self(fs, self);
            };
            for (const llvm::Instruction &I : llvm::instructions(*St->getFunction())) {
              const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(&I);
              if (!GG || GG->getPointerOperand()->stripPointerCasts() != dest)
                continue;
              if (auto *ST = llvm::dyn_cast<llvm::StructType>(GG->getSourceElementType()))
                addSizes(const_cast<llvm::StructType *>(ST), addSizes);
            }
            if (const auto *A = llvm::dyn_cast<llvm::Argument>(dest)) {
              if (A->hasAttribute(llvm::Attribute::Dereferenceable)) {
                uint64_t d = A->getAttribute(llvm::Attribute::Dereferenceable).getDereferenceableBytes();
                if (d > 0 && d < 0x80000000u)
                  sizes.insert((int)d);
              }
            }
            byBias[bias].sizes.insert(sizes.begin(), sizes.end());
            byBias[bias].tys.insert(tys.begin(), tys.end());
          }
        }
        if (byBias.empty())
          continue;
        auto rec = [&](llvm::Constant *C, int64_t at, auto &self) -> void {
          if (!C)
            return;
          if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
            const llvm::StructLayout *SL = DL.getStructLayout(CS->getType());
            for (unsigned i = 0; i < CS->getNumOperands(); ++i)
              self(CS->getOperand(i), at + (int64_t)SL->getElementOffset(i), self);
            return;
          }
          if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
            int64_t es = (int64_t)DL.getTypeAllocSize(CA->getType()->getElementType());
            for (unsigned i = 0; i < CA->getNumOperands(); ++i)
              self(llvm::cast<llvm::Constant>(CA->getOperand(i)), at + (int64_t)i * es, self);
            return;
          }
          const auto *Fn = llvm::dyn_cast<llvm::Function>(C->stripPointerCasts());
          if (!Fn || !Fn->hasName() || Fn->isIntrinsic())
            return;
          for (const auto &bs : byBias) {
            if (at < bs.first)
              continue;
            int64_t rel = at - bs.first;
            for (int sz : bs.second.sizes) {
              int slot = slotStep(0, kRel, pack(sz, rel));
              if (slot > 0)
                fnAt[slot].insert(const_cast<llvm::Function *>(Fn));
            }
            for (int ty : bs.second.tys) {
              int slot = slotStep(0, kRel + 1, ((int64_t)ty << 32) | (rel & 0xffffffffLL));
              if (slot > 0)
                fnAt[slot].insert(const_cast<llvm::Function *>(Fn));
            }
          }
        };
        rec(G.getInitializer(), 0, rec);
      }
    };
    fileRelative(down);
    fileRelative(up);
  }

  void callGraph() {
    auto scan = [&](llvm::Module &M) {
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          llvm::Function *D = nullptr;
          if (llvm::Function *CF = CB->getCalledFunction())
            D = bodyOf(CF);
          else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            D = bodyOf(FN);
          if (!D || D == &F)
            continue;
          callees[&F].push_back(D);
          callers[D].push_back(&F);
        }
      }
    };
    scan(down);
    scan(up);
  }

  bool sinkBody(llvm::Function &F) const {
    if (F.isDeclaration())
      return false;
    if (nameMatch(F))
      return true;
    for (const llvm::Instruction &I : llvm::instructions(F))
      if (onLine(I))
        return true;
    return false;
  }

  bool namedChop(llvm::Function &F) const {
    if (!F.hasName() || chopName.empty())
      return false;
    if (chopName.count(F.getName().str()))
      return true;
    return chopName.count(showFn(&F)) > 0;
  }

  // The initial state is a call sequence from an export to the sink. A
  // function is on such a sequence exactly when a direct call chain reaches
  // the sink instruction or the chop that calls it. The rest of the module
  // does not define a cell of that sequence.
  void orderFns() {
    std::unordered_set<llvm::Function *> reach;
    std::unordered_set<llvm::Function *> roots;
    std::vector<llvm::Function *> q;
    auto add = [&](llvm::Function *F) {
      if (!F)
        return;
      F = bodyOf(F);
      if (!F || F->isDeclaration())
        return;
      if (reach.insert(F).second)
        q.push_back(F);
    };
    auto seed = [&](llvm::Module &M) {
      for (llvm::Function &F : M)
        if (sinkBody(F) || namedChop(F))
          add(&F);
    };
    seed(down);
    seed(up);
    // The sequence starts at the export the driver calls. That function is on
    // the sequence even when the call into the next function is indirect.
    if (inMap) {
      std::unordered_set<std::string> want;
      for (const auto &kv : *inMap)
        for (const Input &in : kv.second)
          if (!in.func.empty())
            want.insert(in.func);
      auto takeIn = [&](llvm::Module &M) {
        for (llvm::Function &F : M) {
          if (F.isDeclaration() || !F.hasName())
            continue;
          if (want.count(F.getName().str()) || want.count(showFn(&F))) {
            llvm::Function *B = bodyOf(&F);
            if (B && reach.insert(B).second)
              roots.insert(B);
            else if (B)
              roots.insert(B);
          }
        }
      };
      takeIn(down);
      takeIn(up);
    }
    // A call through a function pointer reaches the sink when the slot holds a
    // function already on the way to the sink. The stored function may enter
    // that set only after a direct caller is found, so the slot is followed
    // again each time the set grows. A global initializer is already in fnAt.
    std::unordered_map<int, std::vector<llvm::Function *>> slotCaller;
    auto indexSlot = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm() || CB->getCalledFunction())
            continue;
          for (int s : fnSlotsOf(CB->getCalledOperand(), DL))
            for (int suf : slotSuffixes(s))
              slotCaller[suf].push_back(&F);
          for (int s : vtableSlots(CB, DL))
            if (s > 0)
              slotCaller[s].push_back(&F);
        }
      }
    };
    indexSlot(down);
    indexSlot(up);
    std::unordered_map<llvm::Function *, std::vector<int>> storeSlotOf;
    std::unordered_map<llvm::Function *, std::vector<llvm::Function *>> storedBy;
    auto scanStores = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      for (llvm::Function &S : M) {
        if (S.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(S)) {
          auto *St = llvm::dyn_cast<llvm::StoreInst>(&I);
          if (!St)
            continue;
          auto *Fn = llvm::dyn_cast<llvm::Function>(St->getValueOperand()->stripPointerCasts());
          if (!Fn || Fn->isIntrinsic())
            continue;
          Fn = bodyOf(Fn);
          if (!Fn)
            continue;
          storedBy[Fn].push_back(&S);
          for (int slot : fnSlotsOf(St->getPointerOperand(), DL))
            storeSlotOf[Fn].push_back(slot);
        }
      }
    };
    scanStores(down);
    scanStores(up);
    std::unordered_map<llvm::Function *, std::vector<int>> globalSlotOf;
    for (const auto &kv : fnAt)
      for (llvm::Function *T : kv.second)
        if (llvm::Function *B = bodyOf(T))
          globalSlotOf[B].push_back(kv.first);
    // A callee is on the file path when a direct call chain from it reaches
    // the read or the open. Those callees are summarized with the sequence.
    auto fileOpName = [](llvm::StringRef nm) {
      return nm == "open" || nm == "open64" || nm == "fopen" || nm == "fopen64" || nm == "openat" ||
             nm == "openat64" || nm == "read" || nm == "pread" || nm == "pread64" || nm == "gzread" ||
             nm == "fread" || nm == "fgets";
    };
    std::unordered_set<llvm::Function *> fileOp;
    auto markFile = [&](llvm::Module &M) {
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          llvm::Function *CF = CB->getCalledFunction();
          if (CF && CF->hasName() && fileOpName(CF->getName()))
            fileOp.insert(&F);
        }
      }
    };
    markFile(down);
    markFile(up);
    // A function pulled only because it reads the file is summarized, and a
    // callee that itself opens or reads is too. Its callers are not on the
    // sink sequence.
    retSlotCache.clear();
    retSlotBusy.clear();
    std::unordered_set<llvm::Function *> seedReach = reach;
    std::unordered_set<llvm::Function *> fileOnly;
    std::unordered_set<llvm::Function *> opened;
    std::vector<llvm::Function *> work(reach.begin(), reach.end());
    int relRound = 0;
    std::unordered_set<llvm::Function *> relBase;
    while (true) {
      if (work.empty()) {
        // A virtual call loads a constant index of the receiver's vtable.
        // Follow that index once from the functions already on the sink path,
        // then take the direct callers of whoever the vtable names. Following
        // the same index again from the newly reached functions is a different
        // table and is not this sequence.
        if (relRound == 1)
          break;
        relRound = 1;
        relBase = reach;
        for (llvm::Function *H : relBase) {
          if (!H || fileOnly.count(H))
            continue;
          opened.erase(H);
          work.push_back(H);
        }
        if (work.empty())
          break;
        continue;
      }
      llvm::Function *G = work.back();
      work.pop_back();
      if (!G || !opened.insert(G).second)
        continue;
      auto pullSink = [&](llvm::Function *C) {
        if (!C)
          return;
        C = bodyOf(C);
        if (!C || C->isDeclaration())
          return;
        bool wasFile = fileOnly.erase(C) > 0;
        if (reach.insert(C).second || wasFile) {
          if (wasFile)
            opened.erase(C);
          work.push_back(C);
        }
      };
      auto pullFile = [&](llvm::Function *C) {
        if (!C)
          return;
        C = bodyOf(C);
        if (!C || C->isDeclaration() || (reach.count(C) && !fileOnly.count(C)))
          return;
        fileOnly.insert(C);
        if (reach.insert(C).second)
          work.push_back(C);
      };
      if (!roots.count(G) && !fileOnly.count(G)) {
        auto cit = callers.find(G);
        if (cit != callers.end())
          for (llvm::Function *C : cit->second)
            pullSink(C);
        auto kit = callees.find(G);
        if (kit != callees.end())
          for (llvm::Function *C : kit->second)
            if (fileOp.count(C))
              pullFile(C);
        // A function with no direct call is reached when a caller passes it
        // and the callee calls that argument. A function that already has a
        // direct caller is reached by that caller.
        if (!callers.count(G)) {
          for (const llvm::User *U : G->users()) {
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
            if (!CB || CB->isInlineAsm())
              continue;
            bool asArg = false;
            for (const llvm::Value *Op : CB->args())
              if (Op->stripPointerCasts() == G)
                asArg = true;
            if (asArg)
              pullSink(const_cast<llvm::Function *>(CB->getFunction()));
          }
        }
        // A callee that stores this call's function argument into a cell is
        // summarized, so the load of that cell names the function. Its own
        // callers are not on the sink sequence.
        for (llvm::Instruction &I : llvm::instructions(*G)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          bool passesFn = false;
          for (const llvm::Value *Op : CB->args()) {
            const auto *Fn = llvm::dyn_cast<llvm::Function>(Op->stripPointerCasts());
            if (Fn && Fn->hasName() && !Fn->isIntrinsic())
              passesFn = true;
          }
          if (!passesFn)
            continue;
          llvm::Function *C = nullptr;
          if (llvm::Function *CF = CB->getCalledFunction())
            C = bodyOf(CF);
          else if (const auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            C = bodyOf(const_cast<llvm::Function *>(FN));
          if (C)
            pullFile(C);
        }
      } else if (fileOnly.count(G)) {
        auto kit = callees.find(G);
        if (kit != callees.end())
          for (llvm::Function *C : kit->second)
            if (fileOp.count(C))
              pullFile(C);
      }
      if (fileOnly.count(G))
        continue;
      auto follow = [&](const std::vector<int> &slots) {
        for (int slot : slots)
          for (int suf : slotSuffixes(slot)) {
            auto sc = slotCaller.find(suf);
            if (sc == slotCaller.end())
              continue;
            for (llvm::Function *C : sc->second)
              pullSink(C);
          }
      };
      auto sit = storeSlotOf.find(G);
      if (sit != storeSlotOf.end())
        follow(sit->second);
      auto iit = initSlotOf.find(G);
      if (iit != initSlotOf.end())
        follow(iit->second);
      // A global table entry is followed for the sink, the chop, and the
      // export. A store is followed for every function already on the way
      // to the sink. The function that writes the store is summarized so the
      // cell is visible, and its callers stay off this sequence.
      if (seedReach.count(G)) {
        auto git = globalSlotOf.find(G);
        if (git != globalSlotOf.end())
          follow(git->second);
      }
      if (relRound == 1 && relBase.count(G)) {
        auto git = globalSlotOf.find(G);
        if (git != globalSlotOf.end()) {
          std::vector<int> rels;
          for (int s : git->second)
            if (s > 0 && (size_t)s < chainTy.size() &&
                (chainTy[(size_t)s] == 0x40000000 || chainTy[(size_t)s] == 0x40000001))
              rels.push_back(s);
          follow(rels);
        }
      }
      auto bit = storedBy.find(G);
      if (bit != storedBy.end())
        for (llvm::Function *S : bit->second)
          pullFile(S);
    }
    // A global that embeds a cone function is the table the sequence copies
    // into an object. The function that names that global, and the direct
    // callers of that function, are on the sequence.
    std::unordered_set<const llvm::GlobalValue *> tables;
    auto tablesIn = [&](llvm::Module &M) {
      for (llvm::GlobalVariable &G : M.globals()) {
        if (!G.hasInitializer())
          continue;
        bool hit = false;
        std::unordered_set<const llvm::Constant *> seenC;
        std::function<void(const llvm::Constant *)> walkC = [&](const llvm::Constant *C) {
          if (!C || !seenC.insert(C).second)
            return;
          if (const auto *Fn = llvm::dyn_cast<llvm::Function>(C->stripPointerCasts())) {
            llvm::Function *B = bodyOf(const_cast<llvm::Function *>(Fn));
            if (B && reach.count(B))
              hit = true;
          }
          for (const llvm::Use &U : C->operands())
            if (const auto *Op = llvm::dyn_cast<llvm::Constant>(U.get()))
              walkC(Op);
        };
        walkC(G.getInitializer());
        if (hit)
          tables.insert(&G);
      }
    };
    tablesIn(down);
    tablesIn(up);
    auto usesTable = [&](llvm::Module &M) {
      for (llvm::Function &F : M) {
        if (F.isDeclaration() || reach.count(&F))
          continue;
        for (const llvm::Instruction &I : llvm::instructions(F)) {
          for (const llvm::Use &U : I.operands()) {
            const llvm::Value *V = U.get()->stripPointerCasts();
            if (const auto *G = llvm::dyn_cast<llvm::GlobalValue>(V))
              if (tables.count(G))
                reach.insert(&F);
          }
        }
      }
    };
    usesTable(down);
    usesTable(up);
    for (size_t i = 0; i < q.size(); ++i) {
      if (roots.count(q[i]) || fileOnly.count(q[i]))
        continue;
      auto cit = callers.find(q[i]);
      if (cit == callers.end())
        continue;
      for (llvm::Function *C : cit->second)
        add(C);
    }
    for (llvm::Function *F : reach)
      if (!roots.count(F) && !fileOnly.count(F) && std::find(q.begin(), q.end(), F) == q.end())
        q.push_back(F);
    for (size_t i = 0; i < q.size(); ++i) {
      if (roots.count(q[i]) || fileOnly.count(q[i]))
        continue;
      auto cit = callers.find(q[i]);
      if (cit == callers.end())
        continue;
      for (llvm::Function *C : cit->second)
        add(C);
    }
    std::unordered_set<llvm::Function *> seen;
    std::function<void(llvm::Function *)> dfs = [&](llvm::Function *F) {
      if (!F || !reach.count(F) || !seen.insert(F).second)
        return;
      auto it = callees.find(F);
      if (it != callees.end())
        for (llvm::Function *C : it->second)
          dfs(C);
      ord[F] = (int)order.size();
      order.push_back(F);
    };
    auto walk = [&](llvm::Module &M) {
      for (llvm::Function &F : M)
        if (!F.isDeclaration())
          dfs(&F);
    };
    if (reach.empty()) {
      reach.clear();
      for (llvm::Function &F : down)
        if (!F.isDeclaration())
          reach.insert(&F);
      for (llvm::Function &F : up)
        if (!F.isDeclaration())
          reach.insert(&F);
    }
    walk(down);
    walk(up);
  }

  static uint64_t retSigOf(const FnSum &s) {
    uint64_t h = s.rets.size();
    for (const Ret &r : s.rets) {
      h ^= (uint64_t)r.formal * 0x9e3779b97f4a7c15ULL;
      h ^= (uint64_t)r.path << 1;
      h ^= (uint64_t)r.fdep * 0xbf58476d1ce4e5b9ULL;
      h ^= (uint64_t)r.sdep * 0x94d049bb133111ebULL;
    }
    for (const Pub &p : s.pubs) {
      h ^= (uint64_t)(unsigned)p.formal * 0x85ebca6bULL;
      h ^= (uint64_t)(unsigned)p.slot * 0xc2b2ae35ULL;
      h ^= (uint64_t)(unsigned)p.box * 0x27d4eb2fULL;
    }
    for (const CallArg &c : s.callArgs) {
      h ^= (uint64_t)(unsigned)c.formal * 0x165667b1ULL;
      if (c.fty) {
        h ^= (uint64_t)c.fty->getNumParams() * 0x27d4eb2fULL;
        if (c.fty->isVarArg())
          h ^= 0x165667b1ULL;
      }
    }
    return h;
  }

  static uint64_t fnSigOf(const FnSum &s) {
    uint64_t h = 0;
    for (const Wr &w : s.writes) {
      if (w.fn.empty())
        continue;
      h ^= (uint64_t)w.key * 0x9e3779b97f4a7c15ULL;
      for (char c : w.fn)
        h = h * 131 + (unsigned char)c;
    }
    return h;
  }

  void solve() {
    std::set<std::pair<int, llvm::Function *>> dirty;
    for (llvm::Function *F : order)
      dirty.insert({ord[F], F});
    while (!dirty.empty()) {
      llvm::Function *F = dirty.begin()->second;
      dirty.erase(dirty.begin());
      uint64_t oldRet = sum[F].retSig;
      uint64_t oldFn = sum[F].fnSig;
      std::unordered_set<int> oldKeys;
      for (const Wr &w : sum[F].writes)
        if (!w.fn.empty())
          oldKeys.insert(w.key);
      analyze(*F);
      auto touch = [&](llvm::Function *C) {
        auto it = ord.find(C);
        if (it != ord.end())
          dirty.insert({it->second, C});
      };
      if (sum[F].retSig != oldRet) {
        auto cit = callers.find(F);
        if (cit != callers.end())
          for (llvm::Function *C : cit->second)
            touch(C);
        auto iit = indirectCallers.find(F);
        if (iit != indirectCallers.end())
          for (llvm::Function *C : iit->second)
            touch(C);
      }
      if (sum[F].fnSig != oldFn) {
        for (const Wr &w : sum[F].writes) {
          if (w.fn.empty() || oldKeys.count(w.key))
            continue;
          auto wit = watchers.find(w.key);
          if (wit == watchers.end())
            continue;
          for (llvm::Function *C : wit->second)
            touch(C);
        }
      }
    }
    for (llvm::Function *F : order) {
      auto sit = sum.find(F);
      if (sit == sum.end())
        continue;
      FnSum &fn = sit->second;
      std::map<std::pair<int, int>, std::map<std::string, llvm::Function *>> slotFn;
      auto keep = [&](int formal, int path, llvm::Function *G) {
        if (formal < 0 || path <= 0 || !G)
          return;
        slotFn[{formal, path}].emplace(showFn(G), G);
      };
      for (const Site &s : fn.sites) {
        if (!s.callee) {
          for (int slot : s.calleeKeys) {
            eachAt(slot, [&](llvm::Function *G) {
              if (!callTypeMatches(G, s.fty))
                return;
              for (const auto &ap : s.calleeAt)
                keep(ap.first, ap.second, G);
            });
          }
          continue;
        }
        auto git = sum.find(s.callee);
        if (git == sum.end())
          continue;
        for (const FnSum::ZeroFn &z : git->second.zeroFns) {
          if (z.formal < 0 || (unsigned)z.formal >= s.args.size())
            continue;
          int n = 0;
          for (const LiftFrom &lf : s.args[(size_t)z.formal].lift) {
            if (lf.formal < 0)
              continue;
            int p = concat(lf.formal, lf.path, z.path);
            if (p <= 0)
              continue;
            keep(lf.formal, p, z.fn);
            ++n;
          }
          if (n == 0 && s.args[(size_t)z.formal].formals.size() == 1)
            keep(s.args[(size_t)z.formal].formals[0], z.path, z.fn);
        }
      }
      fn.zeroFns.clear();
      for (const auto &kv : slotFn)
        for (const auto &nf : kv.second)
          fn.zeroFns.push_back(FnSum::ZeroFn{kv.first.first, kv.first.second, nf.first, nf.second});
    }
  }

  // Formals this value may denote. A phi, select, or alloca joins every
  // formal any incoming value denotes. A field load is a different value.
  std::vector<int> denoteFormals(const llvm::Value *V) const {
    std::unordered_set<const llvm::Value *> seen;
    std::set<int> found;
    std::function<void(const llvm::Value *)> walk = [&](const llvm::Value *U) {
      if (!U || !seen.insert(U).second)
        return;
      if (const auto *A = llvm::dyn_cast<llvm::Argument>(U)) {
        found.insert((int)A->getArgNo());
        return;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
        walk(C->getOperand(0));
        return;
      }
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(U)) {
        if (CE->isCast())
          walk(CE->getOperand(0));
        return;
      }
      if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
        walk(Fz->getOperand(0));
        return;
      }
      if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
          walk(PN->getIncomingValue(i));
        return;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
        walk(Sel->getTrueValue());
        walk(Sel->getFalseValue());
        return;
      }
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
        const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
        if (!AI)
          return;
        for (const llvm::User *SU : orderedUsers(AI)) {
          const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
          if (!St || St->getPointerOperand()->stripPointerCasts() != AI)
            continue;
          walk(St->getValueOperand());
        }
      }
    };
    walk(V);
    return std::vector<int>(found.begin(), found.end());
  }

  // The struct this argument pointer is indexed as. The function's own
  // constant-offset GEP names it. A direct callee that receives that same
  // pointer and indexes it names the same object. A struct return is the
  // object the call creates, not this argument.
  std::map<int, std::string> indexedArgTypes(llvm::Function *F) {
    std::map<int, std::string> out;
    if (!F || F->isDeclaration())
      return out;
    std::map<int, std::set<std::string>> seen;
    auto note = [&](int arg, llvm::Type *T) {
      const auto *ST = llvm::dyn_cast<llvm::StructType>(T);
      if (!ST || arg < 0)
        return;
      int id = internType(const_cast<llvm::StructType *>(ST));
      if (id <= 0 || id > (int)typeName.size())
        return;
      seen[arg].insert(typeName[(size_t)id - 1]);
    };
    auto scan = [&](llvm::Function *G, int formal, int record) {
      if (!G || G->isDeclaration() || formal < 0 || formal >= (int)G->arg_size())
        return;
      const llvm::Argument *A = G->getArg((unsigned)formal);
      std::unordered_set<const llvm::Value *> ptrs;
      std::vector<const llvm::Value *> q;
      auto add = [&](const llvm::Value *V) {
        if (V && ptrs.insert(V).second)
          q.push_back(V);
      };
      add(A);
      for (size_t qi = 0; qi < q.size(); ++qi) {
        const llvm::Value *V = q[qi];
        for (const llvm::User *U : V->users()) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
            add(C);
          else if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U))
            add(Fz);
          else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(U))
            add(P);
          else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U))
            add(Sel);
          else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(U)) {
            if (S->getValueOperand() == V) {
              const llvm::Value *P = S->getPointerOperand();
              while (const auto *C = llvm::dyn_cast<llvm::CastInst>(P))
                P = C->getOperand(0);
              if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(P))
                add(AI);
            }
          } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
            const llvm::Value *P = L->getPointerOperand();
            while (const auto *C = llvm::dyn_cast<llvm::CastInst>(P))
              P = C->getOperand(0);
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(P))
              if (ptrs.count(AI))
                add(L);
          } else if (const auto *GEp = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
            if (GEp->getPointerOperand() == V)
              note(record, GEp->getSourceElementType());
          }
        }
      }
    };
    for (unsigned a = 0; a < F->arg_size(); ++a) {
      if (F->hasParamAttribute(a, llvm::Attribute::StructRet))
        continue;
      if (llvm::Type *T = F->getParamByValType(a))
        note((int)a, T);
      scan(F, (int)a, (int)a);
      if (seen.count((int)a) && seen[(int)a].size() == 1)
        continue;
      for (llvm::BasicBlock &BB : *F) {
        for (llvm::Instruction &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          llvm::Function *Cal = CB->getCalledFunction();
          if (!Cal || Cal->isDeclaration())
            continue;
          for (unsigned i = 0; i < CB->arg_size() && i < Cal->arg_size(); ++i) {
            if (CB->paramHasAttr(i, llvm::Attribute::StructRet))
              continue;
            std::vector<int> fs = denoteFormals(CB->getArgOperand(i));
            if (std::find(fs.begin(), fs.end(), (int)a) == fs.end())
              continue;
            scan(Cal, (int)i, (int)a);
          }
        }
      }
    }
    for (const auto &kv : seen)
      if (kv.second.size() == 1)
        out.emplace(kv.first, *kv.second.begin());
    return out;
  }

  // A load of an alloca is the value that was stored. Unoptimized IR spills a
  // field through a local; the field loads are the cells the comparison reads.
  std::vector<const llvm::LoadInst *> fieldLoads(const llvm::Value *V) const {
    std::vector<const llvm::LoadInst *> out;
    std::unordered_set<const llvm::Value *> seen;
    std::function<void(const llvm::Value *)> walk = [&](const llvm::Value *U) {
      if (!U || !seen.insert(U).second)
        return;
      while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
        U = C->getOperand(0);
      const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
      if (!Ld)
        return;
      const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
      if (!AI) {
        out.push_back(Ld);
        return;
      }
      for (const llvm::User *SU : orderedUsers(AI)) {
        const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
        if (!St || St->getPointerOperand()->stripPointerCasts() != AI)
          continue;
        walk(St->getValueOperand());
      }
    };
    walk(V);
    return out;
  }

  // A constant-masked and is a predicate on those bits of the remaining value.
  void peelMask(const llvm::Value *V, const llvm::Value *&base, bool &masked, llvm::APInt &mask) const {
    base = V;
    masked = false;
    mask = llvm::APInt(1, 0);
    std::unordered_set<const llvm::Value *> seen;
    while (base && seen.insert(base).second) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(base)) {
        base = C->getOperand(0);
        continue;
      }
      const auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(base);
      if (!BO || BO->getOpcode() != llvm::Instruction::And)
        break;
      const llvm::ConstantInt *M = nullptr;
      const llvm::Value *rest = nullptr;
      if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
        M = C;
        rest = BO->getOperand(0);
      } else if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
        M = C;
        rest = BO->getOperand(1);
      }
      if (!M)
        break;
      if (!masked) {
        mask = M->getValue();
        masked = true;
      } else if (mask.getBitWidth() == M->getBitWidth()) {
        mask &= M->getValue();
      } else {
        break;
      }
      base = rest;
    }
  }

  // The single formal a pointer denotes, after constant GEPs and casts.
  // A load of an alloca is the stored formal. Two formals is not one object.
  int argBase(const llvm::Value *V) const {
    std::unordered_set<const llvm::Value *> seen;
    const llvm::Value *p = V;
    while (p && seen.insert(p).second) {
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(p)) {
        p = G->getPointerOperand();
        continue;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(p)) {
        p = C->getOperand(0);
        continue;
      }
      break;
    }
    std::vector<int> bs = denoteFormals(p);
    if (bs.size() == 1)
      return bs[0];
    return -1;
  }

  // The formal whose object this value is. A field of that object is not the
  // object. A load of the alloca the formal was spilled to is the formal.
  int objectFormal(const llvm::Value *V) const {
    std::unordered_set<const llvm::Value *> seen;
    const llvm::Value *p = V;
    while (p && seen.insert(p).second) {
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(p)) {
        p = C->getOperand(0);
        continue;
      }
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(p)) {
        if (!CE->isCast())
          return -1;
        p = CE->getOperand(0);
        continue;
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(p)) {
        if (!G->hasAllZeroIndices())
          return -1;
        p = G->getPointerOperand();
        continue;
      }
      break;
    }
    std::vector<int> bs = denoteFormals(p);
    if (bs.size() == 1)
      return bs[0];
    return -1;
  }

  void analyze(llvm::Function &F) {
    if (F.isDeclaration())
      return;
    if (!analyzing.insert(&F).second)
      return;
    const llvm::DataLayout &DL = F.getParent()->getDataLayout();
    std::unordered_map<VKey, Fact, VHash> state;
    std::unordered_map<const llvm::Value *, std::vector<VKey>> byVal;
    struct Q {
      const llvm::Value *v;
      int formal;
      int path;
      int gen;
    };
    std::vector<Q> work;
    std::unordered_map<VKey, int, VHash> gen;
    auto grow = [&](const llvm::Value *v, int formal, int path, int dep, uint8_t origin = 0) {
      if (!v)
        return;
      VKey k{v, formal, path};
      auto it = state.find(k);
      if (it == state.end()) {
        state.emplace(k, Fact{dep, origin});
        byVal[v].push_back(k);
        int g = ++gen[k];
        work.push_back(Q{v, formal, path, g});
        return;
      }
      int u = unite(it->second.dep, dep);
      uint8_t o = (uint8_t)(it->second.origin | origin);
      if (u == it->second.dep && o == it->second.origin)
        return;
      it->second.dep = u;
      it->second.origin = o;
      int g = ++gen[k];
      work.push_back(Q{v, formal, path, g});
    };
    auto depOf = [&](const llvm::Value *v) {
      int d = 0;
      auto it = byVal.find(v);
      if (it == byVal.end())
        return d;
      for (const VKey &k : it->second) {
        auto st = state.find(k);
        if (st != state.end())
          d = unite(d, st->second.dep);
      }
      return d;
    };

    std::function<void(const llvm::CallBase *)> applyCall;
    applyCall = [&](const llvm::CallBase *CB) {
      if (CB->isInlineAsm())
        return;
      auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(CB);
      if (II && (II->getIntrinsicID() == llvm::Intrinsic::memcpy || II->getIntrinsicID() == llvm::Intrinsic::memmove ||
                 II->getIntrinsicID() == llvm::Intrinsic::memset))
        return;
      // dynamic_cast returns a pointer into the object it was given. A zero
      // offset is that same address. The cast is the language operator, so the
      // return denotes the first argument.
      if (llvm::Function *CF = CB->getCalledFunction()) {
        if (CF->getName() == "__dynamic_cast" && CB->getType()->isPointerTy() && CB->arg_size() >= 1) {
          bool zero = true;
          if (CB->arg_size() >= 4) {
            const auto *Off = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(3));
            zero = Off && Off->isZero();
          }
          if (zero) {
            auto it = byVal.find(CB->getArgOperand(0));
            if (it != byVal.end()) {
              for (const VKey &s : it->second) {
                if (s.formal < 0)
                  continue;
                auto st = state.find(s);
                int sd = st == state.end() ? 0 : st->second.dep;
                uint8_t origin = st == state.end() ? 0 : st->second.origin;
                grow(CB, s.formal, s.path, sd, origin);
              }
            }
            return;
          }
        }
      }
      llvm::Function *target = nullptr;
      if (llvm::Function *CF = CB->getCalledFunction())
        target = bodyOf(CF);
      else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
        target = bodyOf(FN);
      // A pointer returned by a callee is a field of the object this call
      // passed. That field is only known once the callee itself is summarized.
      if (target && !target->isDeclaration() && CB->getType()->isPointerTy()) {
        auto pit = sum.find(target);
        if (pit == sum.end() || !pit->second.ran)
          analyze(*target);
      }
      auto takeRet = [&](llvm::Function *G) {
        if (!G)
          return;
        indirectCallers[G].insert(&F);
        for (const Ret &r : sum[G].rets) {
          if (r.formal >= 0 && r.formal < (int)CB->arg_size()) {
            const llvm::Value *arg = CB->getArgOperand(r.formal);
            auto it = byVal.find(arg);
            if (it == byVal.end()) {
              if (!CB->getType()->isVoidTy() && !CB->getType()->isPointerTy())
                grow(CB, -1, 0, r.dep);
              continue;
            }
            for (const VKey &s : it->second) {
              auto st = state.find(s);
              int sd = st == state.end() ? 0 : st->second.dep;
              int path = concat(s.formal, s.path, r.path);
              int d = unite(sd, r.dep);
              if (CB->getType()->isPointerTy())
                grow(CB, s.formal, path, d, r.origin);
              else if (!CB->getType()->isVoidTy())
                grow(CB, -1, 0, d);
            }
          } else if (!CB->getType()->isVoidTy()) {
            grow(CB, -1, 0, r.dep);
          }
        }
      };
      auto ensurePointer = [&]() {
        if (!CB->getType()->isPointerTy() || byVal.count(CB))
          return;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          if (!arg->getType()->isPointerTy())
            continue;
          auto it = byVal.find(arg);
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int path = append(s.formal, s.path, 0, Any);
            auto st = state.find(s);
            int sd = st == state.end() ? 0 : st->second.dep;
            grow(CB, s.formal, path, sd, FromAddr);
          }
        }
      };
      if (target) {
        auto pit = sum.find(target);
        if (pit != sum.end()) {
          for (const Pub &p : pit->second.pubs) {
            if (p.slot <= 0 || p.formal < 0 || p.formal >= (int)CB->arg_size())
              continue;
            const llvm::Value *arg = CB->getArgOperand((unsigned)p.formal);
            const auto *Fn = llvm::dyn_cast<llvm::Function>(arg->stripPointerCasts());
            if (!Fn || !Fn->hasName())
              continue;
            auto nit = byName.find(Fn->getName().str());
            if (nit == byName.end())
              continue;
            if (p.box >= 0 && p.box < (int)CB->arg_size()) {
              for (int container : fnSlotsOf(CB->getArgOperand((unsigned)p.box), DL)) {
                if (container <= 0)
                  continue;
                held[(uint64_t)(unsigned)container << 32 | (unsigned)p.slot].insert(nit->second);
              }
            }
            // The cell is this field. A load of the field names the function
            // stored there, including when the object is held in an argument.
            fnAt[p.slot].insert(nit->second);
          }
          for (const CallArg &c : pit->second.callArgs) {
            if (c.formal < 0 || c.formal >= (int)CB->arg_size())
              continue;
            const auto *Fn = llvm::dyn_cast<llvm::Function>(CB->getArgOperand((unsigned)c.formal)->stripPointerCasts());
            if (!Fn || !Fn->hasName() || !callTypeMatches(Fn, c.fty))
              continue;
            auto nit = byName.find(Fn->getName().str());
            if (nit == byName.end())
              continue;
            fnPassed[target][c.formal].insert(nit->second);
          }
        }
        takeRet(target);
        // A call that copies one argument into a local builds that local as
        // the copied object. Later loads and calls on the local denote the
        // argument. The common prefix of the copied fields is the object; the
        // fields that differ are bytes of it.
        if (target != &F && !target->isDeclaration()) {
          bool need = false;
          auto peelA = [](const llvm::Value *V) {
            while (V) {
              if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
                V = C->getOperand(0);
              else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
                if (!CE->isCast())
                  break;
                V = CE->getOperand(0);
              } else
                break;
            }
            return V;
          };
          auto copiesObject = [&](unsigned i) {
            bool tracked = false;
            for (unsigned j = 0; j < CB->arg_size(); ++j) {
              if (j == i)
                continue;
              if (byVal.count(CB->getArgOperand(j)))
                tracked = true;
            }
            if (!tracked)
              return false;
            if (CB->paramHasAttr(i, llvm::Attribute::StructRet))
              return true;
            // A constructor is one block that forwards the object to one callee.
            if (i != 0 || !target->getReturnType()->isVoidTy() || target->size() != 1)
              return false;
            unsigned calls = 0;
            for (const llvm::Instruction &I : target->getEntryBlock()) {
              if (I.isDebugOrPseudoInst())
                continue;
              if (llvm::isa<llvm::CallBase>(I))
                ++calls;
            }
            return calls == 1;
          };
          for (unsigned i = 0; i < CB->arg_size(); ++i) {
            if (copiesObject(i) && llvm::isa<llvm::AllocaInst>(peelA(CB->getArgOperand(i))))
              need = true;
          }
          if (need) {
            ensureRan(target);
            auto git = sum.find(target);
            if (git != sum.end() && git->second.ran) {
              for (unsigned i = 0; i < CB->arg_size(); ++i) {
                if (!copiesObject(i))
                  continue;
                const llvm::Value *dest = peelA(CB->getArgOperand(i));
                const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(dest);
                if (!AI)
                  continue;
                std::map<int, std::vector<int>> bySrc;
                for (const Wr &w : git->second.writes) {
                  if (w.formal != (int)i || w.srcFormal < 0 || w.srcFormal >= (int)CB->arg_size() || w.srcPath <= 0)
                    continue;
                  bySrc[w.srcFormal].push_back(w.srcPath);
                }
                if (bySrc.size() != 1)
                  continue;
                const auto &paths = bySrc.begin()->second;
                std::vector<std::vector<std::pair<int, int64_t>>> seqs;
                for (int p : paths) {
                  std::vector<std::pair<int, int64_t>> s;
                  for (int x = p; x > 0; x = steps[x].parent)
                    s.push_back({steps[x].type, steps[x].off});
                  std::reverse(s.begin(), s.end());
                  seqs.push_back(std::move(s));
                }
                size_t npre = seqs.empty() ? 0 : seqs[0].size();
                for (const auto &s : seqs)
                  npre = std::min(npre, s.size());
                int prefix = 0;
                for (size_t k = 0; k < npre; ++k) {
                  bool same = true;
                  for (const auto &s : seqs)
                    if (s[k].second != seqs[0][k].second)
                      same = false;
                  if (!same)
                    break;
                  bool stepped = false;
                  prefix = append(-1, prefix, seqs[0][k].first, seqs[0][k].second, &stepped, true);
                }
                const llvm::Value *src = CB->getArgOperand((unsigned)bySrc.begin()->first);
                auto sit = byVal.find(src);
                if (sit == byVal.end())
                  continue;
                for (const VKey &s : sit->second) {
                  if (s.formal < 0)
                    continue;
                  int path = prefix > 0 ? concat(s.formal, s.path, prefix, true) : s.path;
                  auto st = state.find(s);
                  int sd = st == state.end() ? 0 : st->second.dep;
                  uint8_t origin = st == state.end() ? (uint8_t)FromAddr : st->second.origin;
                  grow(AI, s.formal, path, sd, origin);
                  for (const llvm::User *LU : AI->users()) {
                    const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(LU);
                    if (Ld && Ld->getPointerOperand() == AI)
                      grow(Ld, s.formal, path, sd, (uint8_t)(origin | FromLoad));
                  }
                }
              }
            }
          }
        }
        ensurePointer();
        return;
      }
      std::unordered_set<llvm::Function *> targets;
      for (int slot : fnSlotsOf(CB->getCalledOperand(), DL)) {
        if (slot <= 0)
          continue;
        for (int suf : slotSuffixes(slot))
          watchers[suf].insert(&F);
        eachAt(slot, [&](llvm::Function *T) {
          if (callTypeMatches(T, CB->getFunctionType()))
            targets.insert(T);
        });
      }
      if (targets.empty()) {
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          if (!arg->getType()->isPointerTy())
            continue;
          auto it = byVal.find(arg);
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int path = append(s.formal, s.path, 0, Any);
            auto st = state.find(s);
            int sd = st == state.end() ? 0 : st->second.dep;
            if (CB->getType()->isPointerTy())
              grow(CB, s.formal, path, sd, FromAddr);
            else if (!CB->getType()->isVoidTy())
              grow(CB, -1, 0, sd);
          }
        }
        return;
      }
      std::vector<llvm::Function *> ordered(targets.begin(), targets.end());
      std::sort(ordered.begin(), ordered.end(),
                [&](llvm::Function *A, llvm::Function *B) { return fnBefore(A, B); });
      for (llvm::Function *G : ordered)
        takeRet(G);
      ensurePointer();
    };

    for (llvm::Argument &A : F.args())
      if (A.getType()->isPointerTy())
        grow(&A, A.getArgNo(), 0, 0, FromAddr);

    while (!work.empty()) {
      Q q = work.back();
      work.pop_back();
      VKey k{q.v, q.formal, q.path};
      auto git = gen.find(k);
      if (git == gen.end() || git->second != q.gen)
        continue;
      int dep = state[k].dep;
      uint8_t origin = state[k].origin;
      for (const llvm::User *U : orderedUsers(q.v)) {
        if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
          if (!CB->isInlineAsm())
            applyCall(CB);
          continue;
        }
        if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (St->getValueOperand() == q.v && St->getPointerOperand() != q.v) {
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(St->getPointerOperand())) {
              for (const llvm::User *LU : orderedUsers(AI)) {
                const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(LU);
                if (Ld && Ld->getPointerOperand() == AI)
                  grow(Ld, q.formal, q.path, dep, origin);
              }
            }
          }
          continue;
        }
        if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
          if (Ld->getPointerOperand() != q.v)
            continue;
          // A reload of an alloca is the stored pointer, copied by the store
          // above. A load of any other pointer is a new object.
          if (llvm::isa<llvm::AllocaInst>(q.v))
            continue;
          int d = dep;
          int key = lastKey(q.path);
          if (key > 0)
            d = unite(d, oneKey(key));
          if (Ld->getType()->isPointerTy() || (Ld->getType()->isIntegerTy() && q.path > 0))
            grow(Ld, q.formal, q.path, d, FromLoad);
          else
            grow(Ld, -1, 0, d);
          continue;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
          if (C->getType()->isPointerTy())
            grow(C, q.formal, q.path, dep, origin);
          else
            grow(C, -1, 0, dep);
          continue;
        }
        if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
          if (Fz->getType()->isPointerTy())
            grow(Fz, q.formal, q.path, dep, origin);
          else
            grow(Fz, -1, 0, dep);
          continue;
        }
        if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
          if (PN->getType()->isPointerTy())
            grow(PN, q.formal, q.path, dep, origin);
          else
            grow(PN, -1, 0, dep);
          continue;
        }
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getType()->isPointerTy())
            grow(Sel, q.formal, q.path, dep, origin);
          else
            grow(Sel, -1, 0, dep);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (llvm::isa<llvm::ConstantExpr>(U) || G->getPointerOperand() != q.v)
            continue;
          int ty = 0;
          int64_t off = Any;
          bool element = false;
          const llvm::Type *src = G->getSourceElementType();
          const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
          if (!ST)
            if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
              ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
          if (ST)
            ty = internType(ST);
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          int64_t inner = 0;
          if (ty > 0 && G->accumulateConstantOffset(DL, ap)) {
            if (ap.getSignificantBits() > 63 && !ap.isNegative())
              off = Any;
            else
              off = ap.getSExtValue();
          } else if (ty > 0 && arrayElement(G, DL, inner)) {
            // A variable index of the array a constant field holds is one
            // element. The array is the cell. The element's fields are fields
            // of that cell.
            off = inner;
            element = true;
          } else if (ty > 0 && !llvm::isa<llvm::StructType>(src)) {
            off = 0;
            element = true;
          }
          int path2 = q.path;
          if (ty > 0) {
            bool stepped = false;
            int nxt = append(q.formal, q.path, ty, off, &stepped);
            if (stepped)
              noteBound(nxt, element ? (uint8_t)FromLoad : origin);
            path2 = nxt;
          }
          if (G->getType()->isPointerTy())
            grow(G, q.formal, path2, dep, FromAddr);
          continue;
        }
        if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(U)) {
          if (BI->isConditional() && BI->getCondition() == q.v)
            for (unsigned s = 0; s < BI->getNumSuccessors(); ++s)
              for (llvm::PHINode &PN : BI->getSuccessor(s)->phis())
                grow(&PN, -1, 0, dep);
          continue;
        }
        if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(U)) {
          if (SW->getCondition() == q.v)
            for (unsigned s = 0; s < SW->getNumSuccessors(); ++s)
              for (llvm::PHINode &PN : SW->getSuccessor(s)->phis())
                grow(&PN, -1, 0, dep);
          continue;
        }
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U)) {
          if (I->getType()->isVoidTy() || llvm::isa<llvm::ReturnInst>(I))
            continue;
          if (I->getType()->isPointerTy())
            grow(I, q.formal, q.path, dep, origin);
          else
            grow(I, -1, 0, dep);
        }
      }
    }

    std::unordered_map<const llvm::BasicBlock *, std::vector<const llvm::Value *>> ctrl;
    struct Pole {
      const llvm::Value *cond = nullptr;
      int succ = -1;
    };
    std::unordered_map<const llvm::BasicBlock *, std::vector<Pole>> pole;
    {
      llvm::PostDominatorTree PDT;
      PDT.recalculate(F);
      auto addEdge = [&](const llvm::BasicBlock *X, const llvm::BasicBlock *S, const llvm::Value *ctrlCond,
                         const llvm::Value *poleCond, int succ) {
        auto *nx = PDT.getNode(X);
        auto *node = PDT.getNode(S);
        if (!nx || !node || !ctrlCond || !poleCond)
          return;
        auto *stop = nx->getIDom();
        while (node && node != stop) {
          if (const llvm::BasicBlock *B = node->getBlock()) {
            auto &v = ctrl[B];
            bool seen = false;
            for (const llvm::Value *c : v)
              if (c == ctrlCond)
                seen = true;
            if (!seen)
              v.push_back(ctrlCond);
            auto &ps = pole[B];
            bool have = false;
            for (const Pole &p : ps)
              if (p.cond == poleCond && p.succ == succ)
                have = true;
            if (!have)
              ps.push_back(Pole{poleCond, succ});
          }
          node = node->getIDom();
        }
      };
      for (llvm::BasicBlock &X : F) {
        auto *T = X.getTerminator();
        if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(T)) {
          if (BI->isConditional())
            for (unsigned s = 0; s < BI->getNumSuccessors(); ++s)
              addEdge(&X, BI->getSuccessor(s), BI->getCondition(), BI->getCondition(), (int)s);
        } else if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(T)) {
          for (unsigned s = 0; s < SW->getNumSuccessors(); ++s)
            addEdge(&X, SW->getSuccessor(s), SW->getCondition(), SW, (int)s);
        }
      }
    }

    // A branch edge is necessary for a block when its successor dominates
    // that block. Reaching the block requires the edge, including when the
    // block does not postdominate the successor.
    std::unordered_map<const llvm::BasicBlock *, std::vector<Pole>> domEdge;
    {
      llvm::DominatorTree DT(F);
      std::unordered_map<const llvm::BasicBlock *, Pole> entered;
      for (llvm::BasicBlock &X : F) {
        const llvm::Instruction *T = X.getTerminator();
        const auto *BR = llvm::dyn_cast<llvm::BranchInst>(T);
        const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(T);
        if (BR && !BR->isConditional())
          continue;
        if (!BR && !SW)
          continue;
        unsigned nSucc = BR ? BR->getNumSuccessors() : SW->getNumSuccessors();
        const llvm::Value *cond = BR ? BR->getCondition() : static_cast<const llvm::Value *>(SW);
        for (unsigned s = 0; s < nSucc; ++s) {
          const llvm::BasicBlock *S = BR ? BR->getSuccessor(s) : SW->getSuccessor(s);
          if (S->getSinglePredecessor() == &X)
            entered.emplace(S, Pole{cond, (int)s});
        }
      }
      for (llvm::BasicBlock &B : F) {
        for (auto *N = DT.getNode(&B); N; N = N->getIDom()) {
          const llvm::BasicBlock *S = N->getBlock();
          auto it = entered.find(S);
          if (it == entered.end())
            continue;
          auto &ps = domEdge[&B];
          bool have = false;
          for (const Pole &p : ps)
            if (p.cond == it->second.cond && p.succ == it->second.succ)
              have = true;
          if (!have)
            ps.push_back(it->second);
        }
      }
    }

    std::unordered_map<const llvm::Value *, int> fOf;
    std::unordered_map<const llvm::Value *, int> sOf;
    auto addFset = [&](const llvm::Value *v, int id) {
      if (!v || id <= 0)
        return false;
      int cur = 0;
      auto it = fOf.find(v);
      if (it != fOf.end())
        cur = it->second;
      int nxt = uniteF(cur, id);
      if (nxt == cur)
        return false;
      fOf[v] = nxt;
      return true;
    };
    auto addSset = [&](const llvm::Value *v, int id) {
      if (!v || id <= 0)
        return false;
      int cur = 0;
      auto it = sOf.find(v);
      if (it != sOf.end())
        cur = it->second;
      int nxt = uniteS(cur, id);
      if (nxt == cur)
        return false;
      sOf[v] = nxt;
      return true;
    };
    for (llvm::Argument &A : F.args())
      addFset(&A, oneF((int)A.getArgNo()));
    for (auto &kv : byVal)
      for (const VKey &s : kv.second)
        if (s.formal >= 0)
          addFset(kv.first, oneF(s.formal));
    struct FH {
      size_t operator()(const std::pair<int, int> &p) const {
        return (size_t)p.first * 1315423911u ^ (size_t)p.second;
      }
    };
    std::unordered_map<std::pair<int, int>, std::vector<const llvm::LoadInst *>, FH> loadsAt;
    std::unordered_map<const llvm::Value *, std::vector<std::pair<int, int>>> slotsOf;
    std::vector<FnSum::Rd> earlyReads;
    std::set<std::tuple<const llvm::BasicBlock *, int, int>> seenRd;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        auto it = byVal.find(Ld->getPointerOperand());
        if (it == byVal.end())
          continue;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (s.formal >= 0 && key > 0)
            loadsAt[{s.formal, key}].push_back(Ld);
          if (s.formal < 0 || s.path <= 0 || key <= 0)
            continue;
          if (!seenRd.insert({Ld->getParent(), s.formal, s.path}).second)
            continue;
          FnSum::Rd rd;
          rd.at = Ld->getParent();
          rd.formal = s.formal;
          rd.path = s.path;
          rd.key = key;
          rd.len = (int64_t)DL.getTypeStoreSize(Ld->getType());
          rd.pointer = Ld->getType()->isPointerTy();
          if (rd.pointer) {
            auto findGep = [](const llvm::Value *V) -> const llvm::GEPOperator * {
              if (!V)
                return nullptr;
              for (const llvm::User *U : V->users()) {
                if (const auto *P = llvm::dyn_cast<llvm::GEPOperator>(U))
                  return P;
                const auto *C = llvm::dyn_cast<llvm::CastInst>(U);
                if (!C)
                  continue;
                for (const llvm::User *W : C->users())
                  if (const auto *P = llvm::dyn_cast<llvm::GEPOperator>(W))
                    return P;
              }
              return nullptr;
            };
            const llvm::GEPOperator *G = findGep(Ld);
            if (!G) {
              for (const llvm::User *U : Ld->users()) {
                const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
                if (!St || St->getValueOperand() != Ld)
                  continue;
                const auto *A = llvm::dyn_cast<llvm::AllocaInst>(St->getPointerOperand());
                if (!A)
                  continue;
                for (const llvm::User *AU : A->users()) {
                  const auto *L2 = llvm::dyn_cast<llvm::LoadInst>(AU);
                  if (!L2)
                    continue;
                  G = findGep(L2);
                  if (G)
                    break;
                }
                if (G)
                  break;
              }
            }
            if (G) {
              llvm::Type *elt = G->getSourceElementType();
              if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(elt))
                elt = AT->getElementType();
              if (const auto *S = llvm::dyn_cast<llvm::StructType>(elt)) {
                if (S->hasName() && !S->isOpaque()) {
                  int id = internType(S);
                  if (id > 0 && id <= (int)typeName.size())
                    rd.pointee = typeName[(size_t)id - 1];
                  rd.objLen = (int64_t)DL.getTypeAllocSize(const_cast<llvm::StructType *>(S));
                  for (unsigned ei = 0; ei < S->getNumElements(); ++ei)
                    if (S->getElementType(ei)->isPointerTy())
                      rd.ptrField = true;
                }
              } else if (elt->isPointerTy()) {
                rd.ptrField = true;
              }
            }
          }
          earlyReads.push_back(std::move(rd));
        }
      } else if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto it = byVal.find(St->getPointerOperand());
        if (it == byVal.end())
          continue;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (s.formal >= 0 && key > 0)
            slotsOf[St->getValueOperand()].push_back({s.formal, key});
        }
      }
    }
    std::vector<const llvm::Value *> fq;
    std::unordered_set<const llvm::Value *> inq;
    auto enq = [&](const llvm::Value *v) {
      if (v && inq.insert(v).second)
        fq.push_back(v);
    };
    std::unordered_map<const llvm::Value *, int> appear;
    int appearN = 0;
    for (llvm::Argument &A : F.args())
      appear.emplace(&A, appearN++);
    for (llvm::Instruction &I : llvm::instructions(F))
      appear.emplace(&I, appearN++);
    std::vector<std::pair<int, int>> loadKeys;
    loadKeys.reserve(loadsAt.size());
    for (auto &kv : loadsAt)
      loadKeys.push_back(kv.first);
    std::sort(loadKeys.begin(), loadKeys.end());
    for (const std::pair<int, int> &key : loadKeys) {
      int slot = oneS(internSlot(key.first, key.second));
      for (const llvm::LoadInst *Ld : loadsAt[key])
        if (addSset(Ld, slot))
          enq(Ld);
    }
    std::vector<const llvm::Value *> fvals;
    fvals.reserve(fOf.size());
    for (auto &kv : fOf)
      fvals.push_back(kv.first);
    std::sort(fvals.begin(), fvals.end(), [&](const llvm::Value *a, const llvm::Value *b) {
      int ia = appear.count(a) ? appear[a] : INT_MAX;
      int ib = appear.count(b) ? appear[b] : INT_MAX;
      if (ia != ib)
        return ia < ib;
      auto ordOf = [&](const llvm::Value *v) {
        const auto *I = llvm::dyn_cast<llvm::Instruction>(v);
        if (!I)
          return INT_MAX;
        auto it = instOrd.find(I);
        return it == instOrd.end() ? INT_MAX : it->second;
      };
      int oa = ordOf(a);
      int ob = ordOf(b);
      if (oa != ob)
        return oa < ob;
      std::string sa, sb;
      llvm::raw_string_ostream osa(sa), osb(sb);
      a->printAsOperand(osa, false);
      b->printAsOperand(osb, false);
      return sa < sb;
    });
    for (const llvm::Value *v : fvals)
      enq(v);
    auto slotUsed = [&](int sdep, int idx) {
      if (sdep <= 0 || sdep >= (int)sdeps.size())
        return false;
      for (int sid : sdeps[sdep]) {
        if (sid <= 0 || sid >= (int)slots.size())
          continue;
        if (slots[sid].formal == idx)
          return true;
      }
      return false;
    };
    auto mapRetSlots = [&](const llvm::CallBase *CB, llvm::Function *target) {
      if (!target || CB->getType()->isVoidTy())
        return;
      auto sit = sum.find(target);
      if (sit == sum.end())
        return;
      for (const Ret &r : sit->second.rets) {
        if (r.sdep <= 0 || r.sdep >= (int)sdeps.size())
          continue;
        for (int sid : sdeps[r.sdep]) {
          if (sid <= 0 || sid >= (int)slots.size())
            continue;
          const Slot &sl = slots[sid];
          if (sl.formal < 0 || sl.key <= 0 || sl.formal >= (int)CB->arg_size())
            continue;
          auto it = byVal.find(CB->getArgOperand((unsigned)sl.formal));
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int got = oneS(internSlot(s.formal, sl.key));
            if (addSset(CB, got))
              enq(CB);
          }
        }
      }
    };
    for (size_t qi = 0; qi < fq.size(); ++qi) {
      const llvm::Value *v = fq[qi];
      inq.erase(v);
      int id = 0;
      int sid = 0;
      auto fit = fOf.find(v);
      if (fit != fOf.end())
        id = fit->second;
      auto sit0 = sOf.find(v);
      if (sit0 != sOf.end())
        sid = sit0->second;
      if (id <= 0 && sid <= 0)
        continue;
      for (const llvm::User *U : orderedUsers(v)) {
        if (llvm::isa<llvm::StoreInst>(U) || llvm::isa<llvm::BranchInst>(U) || llvm::isa<llvm::SwitchInst>(U) ||
            llvm::isa<llvm::ReturnInst>(U))
          continue;
        if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
          if (CB->isInlineAsm() || CB->getType()->isVoidTy())
            continue;
          int idx = -1;
          for (unsigned i = 0; i < CB->arg_size(); ++i)
            if (CB->getArgOperand(i) == v)
              idx = (int)i;
          if (idx < 0)
            continue;
          llvm::Function *target = nullptr;
          if (llvm::Function *CF = CB->getCalledFunction())
            target = bodyOf(CF);
          else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            target = bodyOf(FN);
          bool known = false;
          bool use = false;
          if (target) {
            auto sit = sum.find(target);
            if (sit != sum.end() && !sit->second.rets.empty()) {
              known = true;
              for (const Ret &r : sit->second.rets) {
                if (r.formal == idx)
                  use = true;
                if (r.fdep > 0 && r.fdep < (int)fdeps.size())
                  for (int f : fdeps[r.fdep])
                    if (f == idx)
                      use = true;
                if (slotUsed(r.sdep, idx))
                  use = true;
              }
            }
          }
          if (!known && v->getType()->isPointerTy())
            use = true;
          if (!use)
            continue;
          bool grew = addFset(CB, id) || addSset(CB, sid);
          mapRetSlots(CB, target);
          if (grew)
            enq(CB);
          continue;
        }
        if (const auto *UI = llvm::dyn_cast<llvm::Instruction>(U))
          if (addFset(UI, id) || addSset(UI, sid))
            enq(UI);
      }
      auto sit = slotsOf.find(v);
      if (sit == slotsOf.end())
        continue;
      for (auto slot : sit->second) {
        auto lit = loadsAt.find(slot);
        if (lit == loadsAt.end())
          continue;
        int slotId = oneS(internSlot(slot.first, slot.second));
        for (const llvm::LoadInst *Ld : lit->second)
          if (addFset(Ld, id) || addSset(Ld, sid) || addSset(Ld, slotId))
            enq(Ld);
      }
    }

    FnSum next;
    next.reads = std::move(earlyReads);
    if (F.hasName()) {
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *St = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!St)
          continue;
        if (const auto *Fn = llvm::dyn_cast<llvm::Function>(St->getValueOperand()->stripPointerCasts())) {
          if (Fn->hasName()) {
            auto nit = byName.find(Fn->getName().str());
            if (nit != byName.end()) {
              for (int slot : fnSlotsOf(St->getPointerOperand(), DL))
                if (slot > 0)
                  fnAt[slot].insert(nit->second);
              storesOf[&F].insert(nit->second);
            }
          }
        }
        std::vector<int> pubSlots = fnSlotsOf(St->getPointerOperand(), DL);
        if (!pubSlots.empty()) {
          int box = -1;
          auto bit = byVal.find(St->getPointerOperand());
          if (bit != byVal.end())
            for (const VKey &s : bit->second)
              if (s.formal >= 0 && (box < 0 || s.formal < box))
                box = s.formal;
          auto vit = byVal.find(St->getValueOperand());
          if (vit != byVal.end())
            for (const VKey &s : vit->second)
              if (s.formal >= 0)
                for (int pubSlot : pubSlots)
                  if (pubSlot > 0)
                    next.pubs.push_back(Pub{s.formal, pubSlot, box});
        }
        auto ait = byVal.find(St->getPointerOperand());
        if (ait == byVal.end())
          continue;
        const std::vector<VKey> &addr = ait->second;
        int vd = depOf(St->getValueOperand());
        std::string fn;
        if (const auto *Fn = llvm::dyn_cast<llvm::Function>(St->getValueOperand()->stripPointerCasts()))
          if (Fn->hasName())
            fn = Fn->getName().str();
        int64_t len = (int64_t)DL.getTypeStoreSize(St->getValueOperand()->getType());
        for (const VKey &s : addr) {
          int key = lastKey(s.path);
          if (key <= 0)
            continue;
          auto st = state.find(s);
          int pd = st == state.end() ? 0 : st->second.dep;
          Wr w;
          w.formal = s.formal;
          w.path = s.path;
          w.len = len;
          int cd = 0;
          auto cit = ctrl.find(St->getParent());
          if (cit != ctrl.end())
            for (const llvm::Value *c : cit->second)
              cd = unite(cd, depOf(c));
          w.dep = unite(unite(vd, pd), cd);
          w.key = key;
          w.fn = fn;
          {
            auto vit = byVal.find(St->getValueOperand());
            const VKey *src = nullptr;
            int nsrc = 0;
            if (vit != byVal.end()) {
              for (const VKey &s : vit->second) {
                if (s.formal < 0)
                  continue;
                src = &s;
                ++nsrc;
              }
            }
            if (nsrc == 1 && src) {
              w.srcFormal = src->formal;
              w.srcPath = src->path;
              auto st = state.find(*src);
              if (st != state.end() && (st->second.origin & FromLoad))
                noteBound(src->path, FromLoad);
            }
          }
          auto fit = fOf.find(St->getValueOperand());
          if (fit != fOf.end())
            w.fdep = fit->second;
          auto sit = sOf.find(St->getValueOperand());
          if (sit != sOf.end())
            w.sdep = sit->second;
          next.writes.push_back(w);
          if (fn.empty() && s.path > 0 && s.formal >= 0) {
            FnSum::DataStore d;
            d.formal = s.formal;
            d.path = s.path;
            d.key = key;
            d.len = len;
            int vf = objectFormal(St->getValueOperand());
            if (vf == s.formal) {
              d.valFormal = vf;
              next.data.push_back(std::move(d));
            } else if (len > 0 && len <= (int64_t)(std::numeric_limits<unsigned>::max() / 8)) {
              if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(St->getValueOperand()->stripPointerCasts())) {
                if (!CI->isZero()) {
                  d.hasConst = true;
                  d.cnst = CI->getValue().zextOrTrunc((unsigned)len * 8);
                  next.data.push_back(std::move(d));
                }
              }
            }
          }
          if (!fn.empty()) {
            auto nit = byName.find(fn);
            if (nit != byName.end()) {
              for (int slot : fnSlotsOf(St->getPointerOperand(), DL))
                if (slot > 0)
                  fnAt[slot].insert(nit->second);
              storesOf[&F].insert(nit->second);
            }
          }
        }
      }
    }
    for (llvm::BasicBlock &BB : F) {
      auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      auto it = byVal.find(R->getReturnValue());
      if (it == byVal.end()) {
        Ret r;
        r.dep = depOf(R->getReturnValue());
        auto fit = fOf.find(R->getReturnValue());
        if (fit != fOf.end())
          r.fdep = fit->second;
        auto sit = sOf.find(R->getReturnValue());
        if (sit != sOf.end())
          r.sdep = sit->second;
        if (r.dep != 0 || r.fdep != 0 || r.sdep != 0)
          next.rets.push_back(r);
        continue;
      }
      for (const VKey &s : it->second) {
        auto st = state.find(s);
        Ret r;
        r.formal = s.formal;
        r.path = s.path;
        r.origin = st == state.end() ? 0 : st->second.origin;
        r.dep = st == state.end() ? 0 : st->second.dep;
        auto fit = fOf.find(R->getReturnValue());
        if (fit != fOf.end())
          r.fdep = fit->second;
        auto sit = sOf.find(R->getReturnValue());
        if (sit != sOf.end())
          r.sdep = sit->second;
        if (r.formal >= 0)
          r.fdep = uniteF(r.fdep, oneF(r.formal));
        next.rets.push_back(r);
      }
    }
    for (llvm::Instruction &I : llvm::instructions(F)) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      bool isCopy = false;
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(CB))
        isCopy = II->getIntrinsicID() == llvm::Intrinsic::memcpy || II->getIntrinsicID() == llvm::Intrinsic::memmove;
      else if (llvm::Function *CF = CB->getCalledFunction())
        isCopy = CF->getName() == "memcpy" || CF->getName() == "memmove";
      if (!isCopy) {
        llvm::Function *callee = nullptr;
        if (llvm::Function *CF = CB->getCalledFunction())
          callee = bodyOf(CF);
        else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
          callee = bodyOf(FN);
        Site site;
        site.callee = callee;
        site.home = &F;
        site.at = I.getParent();
        site.call = &I;
        if (!callee) {
          site.fty = CB->getFunctionType();
          for (int denoted : denoteFormals(CB->getCalledOperand())) {
            site.calleeFormals.push_back(denoted);
            next.callArgs.push_back(CallArg{denoted, CB->getFunctionType()});
          }
          for (int slot : fnSlotsOf(CB->getCalledOperand(), DL)) {
            if (slot <= 0)
              continue;
            site.calleeKeys.push_back(slot);
            next.indirectKeys.push_back(slot);
          }
          for (int vslot : vtableSlots(CB, DL)) {
            if (vslot <= 0)
              continue;
            site.calleeKeys.push_back(vslot);
            next.indirectKeys.push_back(vslot);
          }
          {
            const llvm::Value *V = CB->getCalledOperand();
            auto peel = [](const llvm::Value *X) {
              while (X) {
                if (const auto *C = llvm::dyn_cast<llvm::CastInst>(X))
                  X = C->getOperand(0);
                else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(X)) {
                  if (!CE->isCast())
                    break;
                  X = CE->getOperand(0);
                } else
                  break;
              }
              return X;
            };
            V = peel(V);
            const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(V);
            const auto *G = Ld ? llvm::dyn_cast<llvm::GEPOperator>(peel(Ld->getPointerOperand())) : nullptr;
            llvm::APInt ap(DL.getIndexSizeInBits(0), 0);
            if (G && G->getSourceElementType()->isPointerTy() && G->accumulateConstantOffset(DL, ap) &&
                !ap.isNegative() && ap.getSExtValue() > 0 && ap.getSExtValue() <= INT_MAX) {
              const auto *vptr = llvm::dyn_cast<llvm::LoadInst>(peel(G->getPointerOperand()));
              if (vptr) {
                const llvm::Value *obj = peel(vptr->getPointerOperand());
                site.vtableOff = (int)ap.getSExtValue();
                auto oit = byVal.find(obj);
                if (oit != byVal.end()) {
                  for (const VKey &s : oit->second)
                    if (s.formal >= 0)
                      site.vtableRecv.push_back({s.formal, s.path});
                }
                // A pointer the callee copied into an sret is that field of
                // the other argument, composed onto the caller.
                if (obj) {
                  std::vector<LiftFrom> lifts;
                  std::set<std::pair<const llvm::Value *, int>> seenV;
                  collectActual(obj, 0, DL, seenV, lifts);
                  for (const LiftFrom &L : lifts)
                    if (L.kind == 0 && L.formal >= 0 && L.path > 0)
                      site.vtableRecv.push_back({L.formal, L.path});
                }
                for (const llvm::Instruction &II : llvm::instructions(F)) {
                  const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(&II);
                  if (!GG || peel(GG->getPointerOperand()) != obj)
                    continue;
                  auto *ST = llvm::dyn_cast<llvm::StructType>(GG->getSourceElementType());
                  if (!ST || !ST->hasName())
                    continue;
                  int id = internType(const_cast<llvm::StructType *>(ST));
                  if (id > 0 && id <= (int)typeName.size())
                    site.vtableTy = typeName[(size_t)id - 1];
                  break;
                }
              }
            }
          }
          auto bit = byVal.find(CB->getCalledOperand());
          if (bit != byVal.end()) {
            int box = -1;
            for (const VKey &s : bit->second)
              if (s.formal >= 0 && (box < 0 || s.formal < box))
                box = s.formal;
            if (box >= 0)
              site.calleeBox = box;
          }
          const llvm::Value *addr = CB->getCalledOperand();
          while (addr) {
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(addr))
              addr = C->getOperand(0);
            else
              break;
          }
          if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(addr)) {
            const llvm::Value *slot = Ld->getPointerOperand();
            while (slot) {
              if (const auto *C = llvm::dyn_cast<llvm::CastInst>(slot))
                slot = C->getOperand(0);
              else
                break;
            }
            auto sit = byVal.find(slot);
            if (sit != byVal.end()) {
              int formal = -2;
              int path = 0;
              bool clash = false;
              for (const VKey &s : sit->second) {
                if (s.formal < 0 || s.path <= 0)
                  continue;
                if (formal == -2) {
                  formal = s.formal;
                  path = s.path;
                } else if (formal != s.formal || path != s.path) {
                  clash = true;
                }
              }
              for (const VKey &s : sit->second)
                if (s.formal >= 0 && s.path > 0)
                  site.calleeAt.push_back({s.formal, s.path});
              if (!clash && formal >= 0 && path > 0) {
                site.calleeFormal = formal;
                site.calleePath = path;
              }
            }
          }
        }
        site.args.resize(CB->arg_size());
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          ArgAt &a = site.args[i];
          int d = depOf(arg);
          if (d > 0)
            a.keys.insert(a.keys.end(), deps[d].begin(), deps[d].end());
          auto fit = fOf.find(arg);
          if (fit != fOf.end() && fit->second > 0)
            a.vformals = fdeps[fit->second];
          a.chain = fnSlotOf(arg, DL);
          auto it = byVal.find(arg);
          bool gotFormal = false;
          if (it != byVal.end()) {
            for (const VKey &s : it->second) {
              int key = lastKey(s.path);
              if (key > 0)
                a.keys.push_back(key);
              if (s.formal >= 0) {
                gotFormal = true;
                a.formals.push_back(s.formal);
                auto st = state.find(s);
                bool pointee = st != state.end() && (st->second.origin & FromLoad);
                a.lift.push_back(LiftFrom{0, s.formal, s.path, {}, pointee});
              }
            }
          }
          if (!gotFormal && arg->getType()->isPointerTy()) {
            std::set<std::pair<const llvm::Value *, int>> seenV;
            collectActual(arg, 0, DL, seenV, a.lift);
          }
          std::sort(a.keys.begin(), a.keys.end());
          a.keys.erase(std::unique(a.keys.begin(), a.keys.end()), a.keys.end());
          std::sort(a.formals.begin(), a.formals.end());
          a.formals.erase(std::unique(a.formals.begin(), a.formals.end()), a.formals.end());
          std::sort(a.lift.begin(), a.lift.end(), [](const LiftFrom &x, const LiftFrom &y) {
            if (x.kind != y.kind)
              return x.kind < y.kind;
            if (x.formal != y.formal)
              return x.formal < y.formal;
            if (x.path != y.path)
              return x.path < y.path;
            return x.name < y.name;
          });
          a.lift.erase(std::unique(a.lift.begin(), a.lift.end()), a.lift.end());
          bool allocaArg = false;
          for (const LiftFrom &L : a.lift)
            if (L.kind == 1 && L.path == 0)
              allocaArg = true;
          const llvm::Value *base = arg;
          while (base) {
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(base))
              base = C->getOperand(0);
            else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(base)) {
              if (!CE->isCast())
                break;
              base = CE->getOperand(0);
            } else
              break;
          }
          const auto *AI = allocaArg ? llvm::dyn_cast<llvm::AllocaInst>(base) : nullptr;
          if (AI) {
            std::unordered_set<const llvm::BasicBlock *> reach;
            std::vector<const llvm::BasicBlock *> rst{CB->getParent()};
            while (!rst.empty()) {
              const llvm::BasicBlock *B = rst.back();
              rst.pop_back();
              if (!reach.insert(B).second)
                continue;
              for (const llvm::BasicBlock *P : llvm::predecessors(B))
                rst.push_back(P);
            }
            struct Box {
              int formal = -1;
              int path = 0;
              bool clash = false;
              bool seen = false;
            };
            std::map<int64_t, Box> boxes;
            auto note = [&](int64_t off, const llvm::Value *Val) {
              Box &b = boxes[off];
              auto vit = byVal.find(Val);
              int formal = -1;
              int path = 0;
              bool one = false;
              if (vit != byVal.end()) {
                for (const VKey &s : vit->second) {
                  if (s.formal < 0)
                    continue;
                  if (!one) {
                    formal = s.formal;
                    path = s.path;
                    one = true;
                  } else if (formal != s.formal || path != s.path) {
                    one = false;
                    break;
                  }
                }
              }
              if (!one) {
                // The stored value is the address of a local. A local that
                // holds one formal is that formal: the callee loads the
                // address, then loads the formal.
                const llvm::Value *slot = Val;
                while (slot) {
                  if (const auto *C = llvm::dyn_cast<llvm::CastInst>(slot))
                    slot = C->getOperand(0);
                  else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(slot)) {
                    if (!CE->isCast())
                      break;
                    slot = CE->getOperand(0);
                  } else
                    break;
                }
                const auto *AI2 = llvm::dyn_cast<llvm::AllocaInst>(slot);
                if (AI2) {
                  int sf = -1;
                  int sp = 0;
                  bool seen = false;
                  bool bad = false;
                  for (const llvm::User *U : AI2->users()) {
                    const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
                    if (!St)
                      continue;
                    const llvm::Value *spv = St->getPointerOperand();
                    while (spv) {
                      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(spv))
                        spv = C->getOperand(0);
                      else
                        break;
                    }
                    if (spv != AI2)
                      continue;
                    auto vit2 = byVal.find(St->getValueOperand());
                    int f2 = -1;
                    int p2 = 0;
                    bool one2 = false;
                    if (vit2 != byVal.end()) {
                      for (const VKey &s2 : vit2->second) {
                        if (s2.formal < 0)
                          continue;
                        if (!one2) {
                          f2 = s2.formal;
                          p2 = s2.path;
                          one2 = true;
                        } else if (f2 != s2.formal || p2 != s2.path) {
                          one2 = false;
                          break;
                        }
                      }
                    }
                    if (!one2 || (seen && (sf != f2 || sp != p2)))
                      bad = true;
                    else {
                      seen = true;
                      sf = f2;
                      sp = p2;
                    }
                  }
                  if (seen && !bad) {
                    formal = sf;
                    path = sp;
                    one = true;
                  }
                }
              }
              if (!one) {
                b.clash = true;
                return;
              }
              if (!b.seen) {
                b.seen = true;
                b.formal = formal;
                b.path = path;
              } else if (b.formal != formal || b.path != path) {
                b.clash = true;
              }
            };
            bool unknown = false;
            std::vector<std::pair<int64_t, int64_t>> cover;
            for (const llvm::Instruction &SI : llvm::instructions(F)) {
              const auto *St = llvm::dyn_cast<llvm::StoreInst>(&SI);
              if (!St || !reach.count(St->getParent()))
                continue;
              if (St->getParent() == CB->getParent() && !St->comesBefore(CB))
                continue;
              const llvm::Value *ptr = St->getPointerOperand();
              while (ptr) {
                if (const auto *C = llvm::dyn_cast<llvm::CastInst>(ptr))
                  ptr = C->getOperand(0);
                else
                  break;
              }
              const auto *G = llvm::dyn_cast<llvm::GEPOperator>(ptr);
              if (!G)
                continue;
              const llvm::Value *gb = G->getPointerOperand();
              while (gb) {
                if (const auto *C = llvm::dyn_cast<llvm::CastInst>(gb))
                  gb = C->getOperand(0);
                else
                  break;
              }
              if (gb != AI)
                continue;
              llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
              if (G->accumulateConstantOffset(DL, ap) && !ap.isNegative()) {
                note(ap.getSExtValue(), St->getValueOperand());
                continue;
              }
              llvm::APInt acc(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
              bool bounded = false;
              int64_t lo = 0;
              int64_t hi = 0;
              for (llvm::gep_type_iterator GTI = llvm::gep_type_begin(G), GTE = llvm::gep_type_end(G); GTI != GTE;
                   ++GTI) {
                const llvm::Value *idx = GTI.getOperand();
                if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(idx)) {
                  if (llvm::StructType *ST = GTI.getStructTypeOrNull()) {
                    unsigned fi = (unsigned)CI->getZExtValue();
                    if (ST->isOpaque() || fi >= ST->getNumElements()) {
                      bounded = false;
                      break;
                    }
                    acc += DL.getStructLayout(ST)->getElementOffset(fi);
                  } else {
                    acc += CI->getValue().sextOrTrunc(acc.getBitWidth()) *
                           DL.getTypeAllocSize(GTI.getIndexedType());
                  }
                  bounded = false;
                } else {
                  llvm::Type *span = GTI.getIndexedType();
                  if (!span) {
                    bounded = false;
                    break;
                  }
                  lo = acc.getSExtValue();
                  hi = lo + (int64_t)DL.getTypeAllocSize(span);
                  bounded = true;
                  break;
                }
              }
              if (!bounded)
                unknown = true;
              else
                cover.push_back({lo, hi});
            }
            if (!unknown) {
              for (const auto &rg : cover) {
                for (auto &kv : boxes) {
                  if (kv.first < rg.second && kv.first + 8 > rg.first)
                    kv.second.clash = true;
                }
              }
              for (const auto &kv : boxes) {
                if (kv.second.clash || !kv.second.seen || kv.second.formal < 0)
                  continue;
                a.carried.push_back(Carried{kv.first, kv.second.formal, kv.second.path});
              }
            }
          }
        }
        std::sort(site.calleeKeys.begin(), site.calleeKeys.end());
        site.calleeKeys.erase(std::unique(site.calleeKeys.begin(), site.calleeKeys.end()), site.calleeKeys.end());
        site.idx = (int)next.sites.size();
        {
          auto notPred = [](unsigned p) -> unsigned {
            using P = llvm::ICmpInst::Predicate;
            switch (p) {
            case P::ICMP_EQ: return P::ICMP_NE;
            case P::ICMP_NE: return P::ICMP_EQ;
            case P::ICMP_UGT: return P::ICMP_ULE;
            case P::ICMP_UGE: return P::ICMP_ULT;
            case P::ICMP_ULT: return P::ICMP_UGE;
            case P::ICMP_ULE: return P::ICMP_UGT;
            case P::ICMP_SGT: return P::ICMP_SLE;
            case P::ICMP_SGE: return P::ICMP_SLT;
            case P::ICMP_SLT: return P::ICMP_SGE;
            case P::ICMP_SLE: return P::ICMP_SGT;
            default: return 0;
            }
          };
          auto swapPred = [](unsigned p) -> unsigned {
            using P = llvm::ICmpInst::Predicate;
            switch (p) {
            case P::ICMP_UGT: return P::ICMP_ULT;
            case P::ICMP_UGE: return P::ICMP_ULE;
            case P::ICMP_ULT: return P::ICMP_UGT;
            case P::ICMP_ULE: return P::ICMP_UGE;
            case P::ICMP_SGT: return P::ICMP_SLT;
            case P::ICMP_SGE: return P::ICMP_SLE;
            case P::ICMP_SLT: return P::ICMP_SGT;
            case P::ICMP_SLE: return P::ICMP_SGE;
            default: return p;
            }
          };
          auto oneLoad = [&](const llvm::Value *V) -> const VKey * {
            const llvm::Value *U = V;
            while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
              U = C->getOperand(0);
            const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
            if (!Ld)
              return nullptr;
            auto bit = byVal.find(Ld->getPointerOperand());
            if (bit == byVal.end())
              return nullptr;
            const VKey *one = nullptr;
            int nform = 0;
            for (const VKey &s : bit->second) {
              if (s.formal < 0 || s.path <= 0)
                continue;
              one = &s;
              ++nform;
            }
            if (nform != 1 || !one)
              return nullptr;
            int64_t len = (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
            if (len <= 0)
              return nullptr;
            return one;
          };
          auto loadLen = [&](const llvm::Value *V) -> int64_t {
            const llvm::Value *U = V;
            while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
              U = C->getOperand(0);
            const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
            if (!Ld)
              return 0;
            return (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
          };
          std::map<const llvm::Value *, std::set<int>> need;
          auto pit = pole.find(I.getParent());
          if (pit != pole.end())
            for (const Pole &p : pit->second)
              need[p.cond].insert(p.succ);
          auto dit = domEdge.find(I.getParent());
          if (dit != domEdge.end())
            for (const Pole &p : dit->second)
              need[p.cond].insert(p.succ);
          for (const auto &nk : need) {
            if (const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(nk.first)) {
              if (nk.second.size() != 1)
                continue;
              unsigned pred = icmp->getPredicate();
              if (*nk.second.begin() == 1)
                pred = notPred(pred);
              if (pred == 0)
                continue;
              const llvm::Value *lhs = icmp->getOperand(0);
              const llvm::Value *rhs = icmp->getOperand(1);
              const llvm::ConstantInt *cst = nullptr;
              const llvm::Value *cell = nullptr;
              if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
                cst = C;
                cell = lhs;
              } else if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
                cst = C;
                cell = rhs;
                pred = swapPred(pred);
              }
              if (cst && cell) {
                int64_t len = loadLen(cell);
                unsigned w = 0;
                if (len > 0 && (uint64_t)len <= std::numeric_limits<unsigned>::max() / 8)
                  w = (unsigned)len * 8;
                int nkeys = 0;
                if (w != 0 && cst->getBitWidth() == w) {
                  for (const llvm::LoadInst *Ld : fieldLoads(cell)) {
                    int64_t got = (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
                    if (got != len)
                      continue;
                    auto bit = byVal.find(Ld->getPointerOperand());
                    if (bit == byVal.end())
                      continue;
                    for (const VKey &s : bit->second) {
                      if (s.formal < 0 || s.path <= 0)
                        continue;
                      ++nkeys;
                      Fix fx;
                      fx.formal = s.formal;
                      fx.path = s.path;
                      fx.len = len;
                      fx.pred = pred;
                      fx.vals.push_back(cst->getValue());
                      site.fixes.push_back(std::move(fx));
                    }
                  }
                }
                if (nkeys == 0) {
                  const llvm::Value *cv = cell;
                  while (const auto *C = llvm::dyn_cast<llvm::CastInst>(cv))
                    cv = C->getOperand(0);
                  const auto *Inner = llvm::dyn_cast<llvm::CallBase>(cv);
                  llvm::Function *G = Inner ? Inner->getCalledFunction() : nullptr;
                  auto git = G ? sum.find(G) : sum.end();
                  if (Inner && G && !G->isDeclaration() && git != sum.end()) {
                    auto holds = [&](const llvm::APInt &rv) {
                      const llvm::APInt &cv2 = cst->getValue();
                      if (rv.getBitWidth() != cv2.getBitWidth())
                        return false;
                      using P = llvm::ICmpInst::Predicate;
                      switch (pred) {
                      case P::ICMP_EQ: return rv.eq(cv2);
                      case P::ICMP_NE: return rv.ne(cv2);
                      case P::ICMP_UGT: return rv.ugt(cv2);
                      case P::ICMP_UGE: return rv.uge(cv2);
                      case P::ICMP_ULT: return rv.ult(cv2);
                      case P::ICMP_ULE: return rv.ule(cv2);
                      case P::ICMP_SGT: return rv.sgt(cv2);
                      case P::ICMP_SGE: return rv.sge(cv2);
                      case P::ICMP_SLT: return rv.slt(cv2);
                      case P::ICMP_SLE: return rv.sle(cv2);
                      default: return false;
                      }
                    };
                std::vector<const RetPred *> match;
                for (const RetPred &rp : git->second.retPreds)
                  if (rp.concrete && holds(rp.val))
                    match.push_back(&rp);
                // One satisfying return is a sufficient witness. The return
                // dominated by the most conditions is the one that performed
                // the setup the later call reads. Returns with fewer
                // conditions stay feasible when those conditions do not
                // constrain them. Several returns at that size are intersected.
                std::vector<Fix> keep;
                size_t most = 0;
                for (const RetPred *rp : match)
                  if (rp->cond.size() > most)
                    most = rp->cond.size();
                auto sameFix = [](const Fix &a, const Fix &b) {
                  return a.formal == b.formal && a.path == b.path && a.otherFormal == b.otherFormal &&
                         a.otherPath == b.otherPath && a.len == b.len && a.pred == b.pred && a.vals == b.vals;
                };
                bool first = true;
                for (const RetPred *rp : match) {
                  if (rp->cond.size() != most)
                    continue;
                  if (first) {
                    keep = rp->cond;
                    first = false;
                    continue;
                  }
                  std::vector<Fix> nxt;
                  for (const Fix &a : keep)
                    for (const Fix &b : rp->cond)
                      if (sameFix(a, b))
                        nxt.push_back(a);
                  keep.swap(nxt);
                }
                    for (const Fix &fx : keep) {
                      if (fx.formal < 0 || fx.formal >= (int)Inner->arg_size() || fx.path <= 0)
                        continue;
                      const llvm::Value *act = Inner->getArgOperand((unsigned)fx.formal);
                      auto bit = byVal.find(act);
                      if (bit == byVal.end())
                        continue;
                      const VKey *base = nullptr;
                      int nf = 0;
                      for (const VKey &s : bit->second) {
                        if (s.formal < 0)
                          continue;
                        base = &s;
                        ++nf;
                      }
                      if (nf != 1 || !base)
                        continue;
                      Fix out = fx;
                      out.formal = base->formal;
                      out.path = concat(base->formal, base->path, fx.path);
                      if (out.path <= 0)
                        continue;
                      if (fx.otherFormal >= 0) {
                        if (fx.otherFormal >= (int)Inner->arg_size())
                          continue;
                        const llvm::Value *oact = Inner->getArgOperand((unsigned)fx.otherFormal);
                        if (const auto *OC = llvm::dyn_cast<llvm::ConstantInt>(oact)) {
                          if (OC->getBitWidth() != (unsigned)fx.len * 8)
                            continue;
                          out.otherFormal = -1;
                          out.otherPath = 0;
                          out.vals = {OC->getValue()};
                        } else {
                          auto oit = byVal.find(oact);
                          const VKey *ob = nullptr;
                          int no = 0;
                          if (oit != byVal.end())
                            for (const VKey &s : oit->second) {
                              if (s.formal < 0)
                                continue;
                              ob = &s;
                              ++no;
                            }
                          if (no == 1 && ob && ob->path > 0) {
                            out.otherFormal = ob->formal;
                            out.otherPath = concat(ob->formal, ob->path, fx.otherPath);
                          } else {
                            std::vector<int> ofs = denoteFormals(oact);
                            if (ofs.size() != 1)
                              continue;
                            out.otherFormal = ofs[0];
                            out.otherPath = 0;
                          }
                        }
                      }
                      site.fixes.push_back(std::move(out));
                    }
                  }
                }
                continue;
              }
              auto bareFormal = [&](const llvm::Value *V) -> int {
                if (oneLoad(V))
                  return -1;
                std::vector<int> fs = denoteFormals(V);
                if (fs.size() != 1)
                  return -1;
                return fs[0];
              };
              const VKey *kl = oneLoad(lhs);
              const VKey *kr = oneLoad(rhs);
              const VKey *loadKey = nullptr;
              int formalSide = -1;
              unsigned ap = pred;
              if (kl && !kr) {
                loadKey = kl;
                formalSide = bareFormal(rhs);
              } else if (kr && !kl) {
                loadKey = kr;
                formalSide = bareFormal(lhs);
                ap = swapPred(pred);
              }
              if (loadKey && formalSide >= 0 && ap != 0) {
                Fix fx;
                fx.formal = loadKey->formal;
                fx.path = loadKey->path;
                fx.otherFormal = formalSide;
                fx.otherPath = 0;
                fx.len = loadLen(loadKey == kl ? lhs : rhs);
                fx.pred = ap;
                if (fx.len > 0)
                  site.fixes.push_back(std::move(fx));
                continue;
              }
              const VKey *a = oneLoad(lhs);
              const VKey *b = oneLoad(rhs);
              int64_t len = loadLen(lhs);
              if (!a || !b || len <= 0 || len != loadLen(rhs))
                continue;
              Fix fx;
              fx.formal = a->formal;
              fx.path = a->path;
              fx.otherFormal = b->formal;
              fx.otherPath = b->path;
              fx.len = len;
              fx.pred = pred;
              site.fixes.push_back(std::move(fx));
            } else if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(nk.first)) {
              if ((int)nk.second.size() == (int)SW->getNumSuccessors())
                continue;
              const VKey *one = oneLoad(SW->getCondition());
              int64_t len = loadLen(SW->getCondition());
              unsigned w = 0;
              if (len > 0 && (uint64_t)len <= std::numeric_limits<unsigned>::max() / 8)
                w = (unsigned)len * 8;
              if (!one || w == 0)
                continue;
              bool allConst = true;
              std::vector<llvm::APInt> taken, left;
              for (unsigned s = 1; s < SW->getNumSuccessors(); ++s) {
                const auto *C = llvm::dyn_cast<llvm::ConstantInt>(SW->getOperand(s * 2));
                if (!C || C->getBitWidth() != w) {
                  allConst = false;
                  break;
                }
                if (nk.second.count((int)s))
                  taken.push_back(C->getValue());
                else
                  left.push_back(C->getValue());
              }
              if (!allConst)
                continue;
              bool def = nk.second.count(0) != 0;
              if (!def) {
                if (taken.empty())
                  continue;
                Fix fx;
                fx.formal = one->formal;
                fx.path = one->path;
                fx.len = len;
                fx.pred = llvm::ICmpInst::ICMP_EQ;
                fx.vals = std::move(taken);
                site.fixes.push_back(std::move(fx));
              } else {
                for (const llvm::APInt &v : left) {
                  Fix fx;
                  fx.formal = one->formal;
                  fx.path = one->path;
                  fx.len = len;
                  fx.pred = llvm::ICmpInst::ICMP_NE;
                  fx.vals.push_back(v);
                  site.fixes.push_back(std::move(fx));
                }
              }
            }
          }
        }
        next.sites.push_back(std::move(site));
        continue;
      }
      if (CB->arg_size() < 3)
        continue;
      int64_t n = 0;
      bool anyN = true;
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(2))) {
        anyN = false;
        n = CI->getSExtValue();
      }
      auto dit = byVal.find(CB->getArgOperand(0));
      auto sit = byVal.find(CB->getArgOperand(1));
      if (dit == byVal.end() || sit == byVal.end())
        continue;
      for (const VKey &d : dit->second)
        for (const VKey &s : sit->second)
          next.copies.push_back(CopySite{d.formal, d.path, s.formal, s.path, n, anyN});
    }
    auto addUse = [&](const llvm::Instruction &I, std::vector<int> &out, std::vector<int> &forms, std::vector<Edge> &edges) {
      auto takeVal = [&](const llvm::Value *op) {
        if (!op || llvm::isa<llvm::BasicBlock>(op))
          return;
        int d = depOf(op);
        if (d > 0)
          out.insert(out.end(), deps[d].begin(), deps[d].end());
        auto it = byVal.find(op);
        if (it == byVal.end())
          return;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (key > 0)
            out.push_back(key);
          if (s.formal >= 0)
            forms.push_back(s.formal);
        }
      };
      takeVal(&I);
      for (const llvm::Value *op : I.operands())
        takeVal(op);
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (CB->isInlineAsm())
          return;
        llvm::Function *callee = nullptr;
        if (llvm::Function *CF = CB->getCalledFunction())
          callee = bodyOf(CF);
        else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
          callee = bodyOf(FN);
        if (!callee)
          return;
        auto sit = sum.find(callee);
        if (sit == sum.end())
          return;
        for (const Ret &r : sit->second.rets)
          if (r.formal >= 0)
            edges.push_back(Edge{callee, r.formal});
      }
    };
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (onLine(I)) {
        anyLine = true;
        next.hitLine = true;
        if (!next.sinkAt)
          next.sinkAt = I.getParent();
        addUse(I, next.lineKeys, next.lineFormals, next.lineEdges);
      }
    }
    if (nameMatch(F)) {
      next.hitName = true;
      for (llvm::Instruction &I : llvm::instructions(F))
        if (llvm::isa<llvm::LoadInst>(I) || llvm::isa<llvm::StoreInst>(I) || llvm::isa<llvm::CallBase>(I))
          addUse(I, next.nameKeys, next.nameFormals, next.nameEdges);
    }
    auto uniqInts = [](std::vector<int> &v) {
      std::sort(v.begin(), v.end());
      v.erase(std::unique(v.begin(), v.end()), v.end());
    };
    uniqInts(next.lineKeys);
    uniqInts(next.nameKeys);
    uniqInts(next.lineFormals);
    uniqInts(next.nameFormals);
    auto uniqEdges = [&](std::vector<Edge> &v) {
      std::sort(v.begin(), v.end(), [&](const Edge &a, const Edge &b) {
        if (a.fn != b.fn)
          return fnBefore(a.fn, b.fn);
        return a.arg < b.arg;
      });
      v.erase(std::unique(v.begin(), v.end(), [](const Edge &a, const Edge &b) { return a.fn == b.fn && a.arg == b.arg; }),
              v.end());
    };
    uniqEdges(next.lineEdges);
    uniqEdges(next.nameEdges);
    std::sort(next.pubs.begin(), next.pubs.end(), [](const Pub &a, const Pub &b) {
      if (a.formal != b.formal)
        return a.formal < b.formal;
      if (a.slot != b.slot)
        return a.slot < b.slot;
      return a.box < b.box;
    });
    next.pubs.erase(std::unique(next.pubs.begin(), next.pubs.end(),
                                [](const Pub &a, const Pub &b) {
                                  return a.formal == b.formal && a.slot == b.slot && a.box == b.box;
                                }),
                    next.pubs.end());
    std::sort(next.indirectKeys.begin(), next.indirectKeys.end());
    next.indirectKeys.erase(std::unique(next.indirectKeys.begin(), next.indirectKeys.end()), next.indirectKeys.end());
    std::sort(next.callArgs.begin(), next.callArgs.end(), [](const CallArg &a, const CallArg &b) {
      if (a.formal != b.formal)
        return a.formal < b.formal;
      auto key = [](const llvm::FunctionType *t) {
        if (!t)
          return std::pair<int, int>{-1, -1};
        return std::pair<int, int>{(int)t->getNumParams(), t->isVarArg() ? 1 : 0};
      };
      return key(a.fty) < key(b.fty);
    });
    next.callArgs.erase(std::unique(next.callArgs.begin(), next.callArgs.end(),
                                    [](const CallArg &a, const CallArg &b) {
                                      return a.formal == b.formal && a.fty == b.fty;
                                    }),
                        next.callArgs.end());
    std::vector<std::pair<int, int64_t>> fileReads;
    {
      std::unordered_map<const llvm::Value *, std::vector<int>> fdFrom;
      auto formalsAt = [&](const llvm::Value *v) {
        std::vector<int> fs;
        if (!v)
          return fs;
        auto it = byVal.find(v);
        if (it != byVal.end())
          for (const VKey &s : it->second)
            if (s.formal >= 0)
              fs.push_back(s.formal);
        auto ft = fdFrom.find(v);
        if (ft != fdFrom.end())
          fs.insert(fs.end(), ft->second.begin(), ft->second.end());
        std::sort(fs.begin(), fs.end());
        fs.erase(std::unique(fs.begin(), fs.end()), fs.end());
        return fs;
      };
      std::vector<const llvm::Value *> fdQ;
      auto addFd = [&](const llvm::Value *v, const std::vector<int> &fs) {
        if (!v || fs.empty())
          return;
        std::vector<int> &dst = fdFrom[v];
        bool grew = false;
        for (int f : fs)
          if (std::find(dst.begin(), dst.end(), f) == dst.end()) {
            dst.push_back(f);
            grew = true;
          }
        if (grew)
          fdQ.push_back(v);
      };
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB)
          continue;
        llvm::Function *CF = CB->getCalledFunction();
        if (!CF || !CF->hasName())
          continue;
        llvm::StringRef n = CF->getName();
        int pathArg = -1;
        if (n == "open" || n == "open64" || n == "fopen" || n == "fopen64")
          pathArg = 0;
        else if (n == "openat" || n == "openat64")
          pathArg = 1;
        else
          continue;
        const llvm::Value *path =
            pathArg >= 0 && pathArg < (int)CB->arg_size() ? CB->getArgOperand((unsigned)pathArg) : nullptr;
        for (int f : formalsAt(path))
          next.opens.push_back(f);
        addFd(CB, formalsAt(path));
      }
      for (size_t qi = 0; qi < fdQ.size(); ++qi) {
        const llvm::Value *v = fdQ[qi];
        std::vector<int> fs = fdFrom[v];
        for (const llvm::Use &U : v->uses()) {
          const auto *User = llvm::dyn_cast<llvm::Instruction>(U.getUser());
          if (!User || User->getFunction() != &F)
            continue;
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(User)) {
            if (C->getOperand(0) == v)
              addFd(C, fs);
          } else if (llvm::isa<llvm::PHINode>(User)) {
            addFd(User, fs);
          } else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(User)) {
            if (S->getValueOperand() == v) {
              const llvm::Value *slot = S->getPointerOperand()->stripPointerCasts();
              if (llvm::isa<llvm::AllocaInst>(slot))
                addFd(slot, fs);
            }
          } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(User)) {
            if (L->getPointerOperand()->stripPointerCasts() == v && llvm::isa<llvm::AllocaInst>(v))
              addFd(L, fs);
          }
        }
      }
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!S)
          continue;
        int obj = argBase(S->getPointerOperand());
        if (obj < 0)
          continue;
        for (int f : formalsAt(S->getValueOperand()))
          if (f != obj)
            next.carries.push_back({obj, f});
      }
      std::sort(next.carries.begin(), next.carries.end());
      next.carries.erase(std::unique(next.carries.begin(), next.carries.end()), next.carries.end());
      std::unordered_map<const llvm::Value *, const llvm::Value *> parent;
      auto findG = [&](const llvm::Value *v) -> const llvm::Value * {
        if (!v)
          return nullptr;
        std::vector<const llvm::Value *> seen;
        const llvm::Value *cur = v;
        while (true) {
          auto it = parent.find(cur);
          if (it == parent.end()) {
            parent.emplace(cur, cur);
            break;
          }
          if (it->second == cur)
            break;
          seen.push_back(cur);
          cur = it->second;
        }
        for (const llvm::Value *s : seen)
          parent[s] = cur;
        return cur;
      };
      auto uniteG = [&](const llvm::Value *a, const llvm::Value *b) {
        a = findG(a);
        b = findG(b);
        if (a && b && a != b)
          parent[b] = a;
      };
      std::unordered_map<const llvm::Value *, int> gnum;
      int nG = 0;
      auto groupOf = [&](const llvm::Value *v) -> int {
        const llvm::Value *r = findG(v);
        if (!r)
          return -1;
        auto it = gnum.find(r);
        if (it != gnum.end())
          return it->second;
        int id = nG++;
        gnum.emplace(r, id);
        return id;
      };
      std::unordered_map<const llvm::Value *, int> baseCache;
      auto cachedBase = [&](const llvm::Value *v) -> int {
        const llvm::Value *p = v;
        std::unordered_set<const llvm::Value *> seen;
        while (p && seen.insert(p).second) {
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(p)) {
            p = G->getPointerOperand();
            continue;
          }
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(p)) {
            p = C->getOperand(0);
            continue;
          }
          break;
        }
        auto it = baseCache.find(p);
        if (it != baseCache.end())
          return it->second;
        std::vector<int> bs = denoteFormals(p);
        int obj = bs.size() == 1 ? bs[0] : -1;
        baseCache.emplace(p, obj);
        return obj;
      };
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(&I))
          uniteG(&I, C->getOperand(0));
        else if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(&I)) {
          for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
            uniteG(&I, PN->getIncomingValue(i));
        } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(&I)) {
          uniteG(&I, Sel->getTrueValue());
          uniteG(&I, Sel->getFalseValue());
        } else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          const llvm::Value *slot = S->getPointerOperand()->stripPointerCasts();
          if (llvm::isa<llvm::AllocaInst>(slot))
            uniteG(slot, S->getValueOperand());
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          const llvm::Value *slot = L->getPointerOperand()->stripPointerCasts();
          if (llvm::isa<llvm::AllocaInst>(slot))
            uniteG(&I, slot);
        }
      }
      for (llvm::Argument &A : F.args())
        next.argGroup.push_back(groupOf(&A));
      auto copyCall = [](const llvm::CallBase *CB) {
        if (const auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(CB))
          return II->getIntrinsicID() == llvm::Intrinsic::memcpy || II->getIntrinsicID() == llvm::Intrinsic::memmove;
        if (const llvm::Function *CF = CB->getCalledFunction())
          return CF->getName() == "memcpy" || CF->getName() == "memmove";
        return false;
      };
      size_t bindAt = 0;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          const llvm::Value *slot = S->getPointerOperand()->stripPointerCasts();
          if (!llvm::isa<llvm::AllocaInst>(slot)) {
            int obj = cachedBase(S->getPointerOperand());
            if (obj >= 0)
              next.holds.push_back({obj, groupOf(S->getValueOperand())});
            if (S->getValueOperand()->getType()->isPointerTy())
              next.ptrStore.push_back({groupOf(slot), groupOf(S->getValueOperand())});
          }
        } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          const llvm::Value *slot = L->getPointerOperand()->stripPointerCasts();
          if (!llvm::isa<llvm::AllocaInst>(slot) && L->getType()->isPointerTy()) {
            int obj = cachedBase(L->getPointerOperand());
            if (obj >= 0)
              next.fromObj.push_back({groupOf(&I), obj});
            next.ptrLoad.push_back({groupOf(slot), groupOf(&I)});
          }
        }
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || copyCall(CB))
          continue;
        if (bindAt >= next.sites.size())
          break;
        std::vector<ArgBind> row;
        row.reserve(CB->arg_size());
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          ArgBind b;
          b.group = groupOf(CB->getArgOperand(i));
          b.formal = cachedBase(CB->getArgOperand(i));
          if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(i)))
            if (C->getSExtValue() > 0)
              b.cst = C->getSExtValue();
          row.push_back(b);
        }
        next.binds.push_back(std::move(row));
        ++bindAt;
        llvm::Function *CF = CB->getCalledFunction();
        if (!CF || !CF->hasName())
          continue;
        llvm::StringRef nm = CF->getName();
        int pathArg = -1;
        if (nm == "open" || nm == "open64" || nm == "fopen" || nm == "fopen64")
          pathArg = 0;
        else if (nm == "openat" || nm == "openat64")
          pathArg = 1;
        if (pathArg < 0 || pathArg >= (int)CB->arg_size()) {
          if (nm == "fdopen" && CB->arg_size() > 0)
            next.streamOf.push_back({groupOf(CB->getArgOperand(0)), groupOf(CB)});
          continue;
        }
        int g = groupOf(CB);
        std::vector<int> paths = denoteFormals(CB->getArgOperand((unsigned)pathArg));
        if (paths.empty()) {
          // The path is a local buffer a copy filled from an argument.
          const llvm::Value *buf = CB->getArgOperand((unsigned)pathArg)->stripPointerCasts();
          const llvm::Value *root = buf;
          if (const auto *GP = llvm::dyn_cast<llvm::GEPOperator>(buf))
            root = GP->getPointerOperand()->stripPointerCasts();
          for (llvm::Instruction &J : llvm::instructions(F)) {
            auto *C2 = llvm::dyn_cast<llvm::CallBase>(&J);
            if (!C2 || C2 == CB)
              continue;
            bool hit = false;
            for (unsigned i = 0; i < C2->arg_size(); ++i) {
              const llvm::Value *a = C2->getArgOperand(i)->stripPointerCasts();
              if (a == buf || a == root) {
                hit = true;
                break;
              }
            }
            if (!hit)
              continue;
            for (unsigned i = 0; i < C2->arg_size(); ++i) {
              const llvm::Value *a = C2->getArgOperand(i)->stripPointerCasts();
              if (a == buf || a == root)
                continue;
              for (int f : denoteFormals(C2->getArgOperand(i)))
                paths.push_back(f);
            }
          }
          std::sort(paths.begin(), paths.end());
          paths.erase(std::unique(paths.begin(), paths.end()), paths.end());
        }
        for (int f : paths)
          next.openAt.push_back({g, f});
      }
      auto uniqPairs = [](std::vector<std::pair<int, int>> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
      };
      uniqPairs(next.holds);
      uniqPairs(next.fromObj);
      uniqPairs(next.openAt);
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB)
          continue;
        llvm::Function *CF = CB->getCalledFunction();
        if (!CF || !CF->hasName())
          continue;
        llvm::StringRef n = CF->getName();
        int fdArg = -1;
        int lenArg = -1;
        int bufArg = -1;
        if (n == "read" || n == "pread" || n == "pread64" || n == "gzread") {
          fdArg = 0;
          lenArg = 2;
          bufArg = 1;
        } else if (n == "fread") {
          fdArg = 3;
          lenArg = 1;
          bufArg = 0;
        } else if (n == "fgets") {
          fdArg = 2;
          lenArg = 1;
          bufArg = 0;
        } else {
          continue;
        }
        if (fdArg < 0 || fdArg >= (int)CB->arg_size() || bufArg < 0 || bufArg >= (int)CB->arg_size())
          continue;
        int64_t len = 0;
        int facA = -1;
        int facB = -1;
        if (n == "fread" && CB->arg_size() > 2) {
          const auto *sz = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(1));
          const auto *nm = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(2));
          if (sz && nm && sz->getSExtValue() > 0 && nm->getSExtValue() > 0 &&
              sz->getSExtValue() <= INT64_MAX / nm->getSExtValue())
            len = sz->getSExtValue() * nm->getSExtValue();
          else if (sz && sz->getSExtValue() > 0)
            len = sz->getSExtValue();
          else if (nm && nm->getSExtValue() > 0)
            len = nm->getSExtValue();
          auto one = [&](const llvm::Value *v) {
            std::vector<int> fs = formalsAt(v);
            if (fs.size() == 1)
              return fs[0];
            return argBase(v);
          };
          if (!sz)
            facA = one(CB->getArgOperand(1));
          if (!nm)
            facB = one(CB->getArgOperand(2));
        } else if (lenArg >= 0 && lenArg < (int)CB->arg_size()) {
          if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand((unsigned)lenArg)))
            if (C->getSExtValue() > 0)
              len = C->getSExtValue();
        }
        const llvm::Value *fd = CB->getArgOperand((unsigned)fdArg);
        const llvm::Value *buf = CB->getArgOperand((unsigned)bufArg);
        int obj = argBase(fd);
        if (obj < 0) {
          std::vector<int> fs = formalsAt(fd);
          if (fs.size() == 1)
            obj = fs[0];
        }
        if (len > 0)
          for (int f : formalsAt(fd))
            fileReads.push_back({f, len});
        if (obj < 0)
          continue;
        PRead pr;
        pr.obj = obj;
        pr.buf = argBase(buf);
        pr.a = facA;
        pr.b = facB;
        pr.len = len;
        pr.fdGroup = groupOf(fd);
        std::unordered_set<const llvm::Value *> seenB;
        std::vector<const llvm::Value *> bq{buf};
        auto takeKey = [&](const llvm::Value *v) {
          if (!v)
            return;
          auto it = byVal.find(v);
          if (it != byVal.end())
            for (const VKey &s : it->second) {
              int k = lastKey(s.path);
              if (k > 0)
                pr.keys.push_back(k);
            }
          int d = depOf(v);
          if (d > 0)
            pr.keys.insert(pr.keys.end(), deps[d].begin(), deps[d].end());
        };
        while (!bq.empty()) {
          const llvm::Value *v = bq.back();
          bq.pop_back();
          if (!v || !seenB.insert(v).second)
            continue;
          takeKey(v);
          for (const llvm::User *U : v->users()) {
            const auto *UI = llvm::dyn_cast<llvm::Instruction>(U);
            if (!UI || UI->getFunction() != &F)
              continue;
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(UI)) {
              if (C->getOperand(0) == v)
                bq.push_back(C);
            } else if (llvm::isa<llvm::PHINode>(UI) || llvm::isa<llvm::SelectInst>(UI)) {
              bq.push_back(UI);
            } else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(UI)) {
              if (G->getPointerOperand() == v)
                bq.push_back(G);
            } else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(UI)) {
              if (L->getPointerOperand() == v)
                bq.push_back(L);
            } else if (const auto *S = llvm::dyn_cast<llvm::StoreInst>(UI)) {
              if (S->getValueOperand() == v)
                takeKey(S->getPointerOperand());
            }
          }
        }
        std::sort(pr.keys.begin(), pr.keys.end());
        pr.keys.erase(std::unique(pr.keys.begin(), pr.keys.end()), pr.keys.end());
        next.preads.push_back(std::move(pr));
      }
    }
    std::map<int, int64_t> fileMax;
    for (const auto &fr : fileReads)
      if (fr.second > fileMax[fr.first])
        fileMax[fr.first] = fr.second;
    for (const auto &fr : fileMax)
      next.files.push_back(fr);
    {
      auto notP = [](unsigned p) -> unsigned {
        using P = llvm::ICmpInst::Predicate;
        switch (p) {
        case P::ICMP_EQ: return P::ICMP_NE;
        case P::ICMP_NE: return P::ICMP_EQ;
        case P::ICMP_UGT: return P::ICMP_ULE;
        case P::ICMP_UGE: return P::ICMP_ULT;
        case P::ICMP_ULT: return P::ICMP_UGE;
        case P::ICMP_ULE: return P::ICMP_UGT;
        case P::ICMP_SGT: return P::ICMP_SLE;
        case P::ICMP_SGE: return P::ICMP_SLT;
        case P::ICMP_SLT: return P::ICMP_SGE;
        case P::ICMP_SLE: return P::ICMP_SGT;
        default: return 0;
        }
      };
      auto swapP = [](unsigned p) -> unsigned {
        using P = llvm::ICmpInst::Predicate;
        switch (p) {
        case P::ICMP_UGT: return P::ICMP_ULT;
        case P::ICMP_UGE: return P::ICMP_ULE;
        case P::ICMP_ULT: return P::ICMP_UGT;
        case P::ICMP_ULE: return P::ICMP_UGE;
        case P::ICMP_SGT: return P::ICMP_SLT;
        case P::ICMP_SGE: return P::ICMP_SLE;
        case P::ICMP_SLT: return P::ICMP_SGT;
        case P::ICMP_SLE: return P::ICMP_SGE;
        default: return p;
        }
      };
      auto oneOf = [&](const llvm::Value *V) -> const VKey * {
        const llvm::Value *U = V;
        while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
          U = C->getOperand(0);
        const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
        if (!Ld)
          return nullptr;
        auto bit = byVal.find(Ld->getPointerOperand());
        if (bit == byVal.end())
          return nullptr;
        const VKey *one = nullptr;
        int nform = 0;
        for (const VKey &s : bit->second) {
          if (s.formal < 0 || s.path <= 0)
            continue;
          one = &s;
          ++nform;
        }
        if (nform != 1 || !one)
          return nullptr;
        return one;
      };
      auto lenOfLd = [&](const llvm::Value *V) -> int64_t {
        const llvm::Value *U = V;
        while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
          U = C->getOperand(0);
        const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
        if (!Ld)
          return 0;
        return (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
      };
      auto fixesOn = [&](const llvm::BasicBlock *B) {
        std::vector<Fix> out;
        std::map<const llvm::Value *, std::set<int>> need;
        auto dit = domEdge.find(B);
        if (dit != domEdge.end())
          for (const Pole &p : dit->second)
            need[p.cond].insert(p.succ);
        for (const auto &nk : need) {
          if (const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(nk.first)) {
            if (nk.second.size() != 1)
              continue;
            unsigned pred = icmp->getPredicate();
            if (*nk.second.begin() == 1)
              pred = notP(pred);
            if (pred == 0)
              continue;
            const llvm::Value *lhs = icmp->getOperand(0);
            const llvm::Value *rhs = icmp->getOperand(1);
            const llvm::ConstantInt *cst = nullptr;
            const llvm::Value *cell = nullptr;
            if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
              cst = C;
              cell = lhs;
            } else if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
              cst = C;
              cell = rhs;
              pred = swapP(pred);
            }
            if (cst && cell) {
              const VKey *one = oneOf(cell);
              int64_t len = lenOfLd(cell);
              unsigned w = 0;
              if (len > 0 && (uint64_t)len <= std::numeric_limits<unsigned>::max() / 8)
                w = (unsigned)len * 8;
              if (!one) {
                const llvm::Value *cv = cell;
                while (const auto *C = llvm::dyn_cast<llvm::CastInst>(cv))
                  cv = C->getOperand(0);
                const auto *Inner = llvm::dyn_cast<llvm::CallBase>(cv);
                llvm::Function *G = Inner ? Inner->getCalledFunction() : nullptr;
                if (G)
                  G = bodyOf(G);
                auto git = G ? sum.find(G) : sum.end();
                if (!Inner || !G || G->isDeclaration() || git == sum.end())
                  continue;
                auto holds = [&](const llvm::APInt &rv) {
                  const llvm::APInt &cv2 = cst->getValue();
                  if (rv.getBitWidth() != cv2.getBitWidth())
                    return false;
                  using P = llvm::ICmpInst::Predicate;
                  switch (pred) {
                  case P::ICMP_EQ: return rv.eq(cv2);
                  case P::ICMP_NE: return rv.ne(cv2);
                  case P::ICMP_UGT: return rv.ugt(cv2);
                  case P::ICMP_UGE: return rv.uge(cv2);
                  case P::ICMP_ULT: return rv.ult(cv2);
                  case P::ICMP_ULE: return rv.ule(cv2);
                  case P::ICMP_SGT: return rv.sgt(cv2);
                  case P::ICMP_SGE: return rv.sge(cv2);
                  case P::ICMP_SLT: return rv.slt(cv2);
                  case P::ICMP_SLE: return rv.sle(cv2);
                  default: return false;
                  }
                };
                std::vector<const RetPred *> match;
                for (const RetPred &rp : git->second.retPreds)
                  if (rp.concrete && holds(rp.val))
                    match.push_back(&rp);
                if (match.empty())
                  continue;
                // Same witness as a call site: the satisfying return dominated
                // by the most conditions, not the conditions common to every return.
                std::vector<Fix> keep;
                size_t most = 0;
                for (const RetPred *rp : match)
                  if (rp->cond.size() > most)
                    most = rp->cond.size();
                auto sameFix = [](const Fix &a, const Fix &b) {
                  return a.formal == b.formal && a.path == b.path && a.otherFormal == b.otherFormal &&
                         a.otherPath == b.otherPath && a.len == b.len && a.pred == b.pred && a.vals == b.vals;
                };
                bool first = true;
                for (const RetPred *rp : match) {
                  if (rp->cond.size() != most)
                    continue;
                  if (first) {
                    keep = rp->cond;
                    first = false;
                    continue;
                  }
                  std::vector<Fix> nxt;
                  for (const Fix &a : keep)
                    for (const Fix &b : rp->cond)
                      if (sameFix(a, b))
                        nxt.push_back(a);
                  keep.swap(nxt);
                }
                for (const Fix &fx0 : keep) {
                  if (fx0.formal < 0 || fx0.formal >= (int)Inner->arg_size() || fx0.path <= 0)
                    continue;
                  const llvm::Value *act = Inner->getArgOperand((unsigned)fx0.formal);
                  auto bit = byVal.find(act);
                  if (bit == byVal.end())
                    continue;
                  const VKey *base = nullptr;
                  int nf = 0;
                  for (const VKey &s : bit->second) {
                    if (s.formal < 0)
                      continue;
                    base = &s;
                    ++nf;
                  }
                  if (nf != 1 || !base)
                    continue;
                  Fix outFx = fx0;
                  outFx.formal = base->formal;
                  outFx.path = concat(base->formal, base->path, fx0.path);
                  if (outFx.path <= 0)
                    continue;
                  if (fx0.otherFormal >= 0) {
                    if (fx0.otherFormal >= (int)Inner->arg_size())
                      continue;
                    const llvm::Value *oact = Inner->getArgOperand((unsigned)fx0.otherFormal);
                    if (const auto *OC = llvm::dyn_cast<llvm::ConstantInt>(oact)) {
                      if (OC->getBitWidth() != (unsigned)fx0.len * 8)
                        continue;
                      outFx.otherFormal = -1;
                      outFx.otherPath = 0;
                      outFx.vals = {OC->getValue()};
                    } else {
                      auto oit = byVal.find(oact);
                      const VKey *ob = nullptr;
                      int no = 0;
                      if (oit != byVal.end())
                        for (const VKey &s : oit->second) {
                          if (s.formal < 0)
                            continue;
                          ob = &s;
                          ++no;
                        }
                      if (no == 1 && ob && ob->path > 0) {
                        outFx.otherFormal = ob->formal;
                        outFx.otherPath = concat(ob->formal, ob->path, fx0.otherPath);
                      } else {
                        std::vector<int> ofs = denoteFormals(oact);
                        if (ofs.size() != 1)
                          continue;
                        outFx.otherFormal = ofs[0];
                        outFx.otherPath = 0;
                      }
                    }
                  }
                  out.push_back(std::move(outFx));
                }
                continue;
              }
              if (w == 0 || cst->getBitWidth() != w)
                continue;
              Fix fx;
              fx.formal = one->formal;
              fx.path = one->path;
              fx.len = len;
              fx.pred = pred;
              fx.vals.push_back(cst->getValue());
              out.push_back(std::move(fx));
              continue;
            }
            auto bareFormal = [&](const llvm::Value *V) -> int {
              if (oneOf(V))
                return -1;
              std::vector<int> fs = denoteFormals(V);
              if (fs.size() != 1)
                return -1;
              return fs[0];
            };
            const VKey *kl = oneOf(lhs);
            const VKey *kr = oneOf(rhs);
            const VKey *loadKey = nullptr;
            int formalSide = -1;
            unsigned ap = pred;
            if (kl && !kr) {
              loadKey = kl;
              formalSide = bareFormal(rhs);
            } else if (kr && !kl) {
              loadKey = kr;
              formalSide = bareFormal(lhs);
              ap = swapP(pred);
            }
            if (loadKey && formalSide >= 0 && ap != 0) {
              int64_t len = lenOfLd(loadKey == kl ? lhs : rhs);
              if (len <= 0)
                continue;
              Fix fx;
              fx.formal = loadKey->formal;
              fx.path = loadKey->path;
              fx.otherFormal = formalSide;
              fx.otherPath = 0;
              fx.len = len;
              fx.pred = ap;
              out.push_back(std::move(fx));
            }
          }
        }
        return out;
      };
      // The bytes the harness leaves alone are 0. Walk from the entry to the
      // target and, where that 0 successor cannot reach the target, take the
      // successor that can. The predicate of that edge is a setting the
      // downstream object needs for this target.
      std::unordered_set<const llvm::BasicBlock *> *visit = nullptr;
      auto flipsTo = [&](const llvm::BasicBlock *target) {
        std::vector<Fix> out;
        if (!target)
          return out;
        std::unordered_set<const llvm::BasicBlock *> reach;
        std::unordered_set<const llvm::BasicBlock *> walkedBack;
        std::vector<const llvm::BasicBlock *> stack{target};
        auto fault = [](const llvm::BasicBlock *B) {
          for (const llvm::Instruction &I : *B) {
            const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB || CB->isInlineAsm())
              continue;
            const llvm::Function *CF = CB->getCalledFunction();
            if (!CF || CF->doesNotReturn())
              return true;
          }
          return llvm::isa<llvm::UnreachableInst>(B->getTerminator());
        };
        while (!stack.empty()) {
          const llvm::BasicBlock *B = stack.back();
          stack.pop_back();
          if (!walkedBack.insert(B).second)
            continue;
          if (B != target && fault(B))
            continue;
          reach.insert(B);
          for (const llvm::BasicBlock *P : llvm::predecessors(B))
            stack.push_back(P);
        }
        auto holds0 = [](unsigned pred, const llvm::APInt &c) {
          llvm::APInt z(c.getBitWidth(), 0);
          using P = llvm::ICmpInst::Predicate;
          switch (pred) {
          case P::ICMP_EQ: return z.eq(c);
          case P::ICMP_NE: return z.ne(c);
          case P::ICMP_UGT: return z.ugt(c);
          case P::ICMP_UGE: return z.uge(c);
          case P::ICMP_ULT: return z.ult(c);
          case P::ICMP_ULE: return z.ule(c);
          case P::ICMP_SGT: return z.sgt(c);
          case P::ICMP_SGE: return z.sge(c);
          case P::ICMP_SLT: return z.slt(c);
          case P::ICMP_SLE: return z.sle(c);
          default: return false;
          }
        };
        const llvm::BasicBlock *bb = &F.getEntryBlock();
        std::unordered_set<const llvm::BasicBlock *> seen;
        while (bb && bb != target && seen.insert(bb).second) {
          if (visit)
            visit->insert(bb);
          const llvm::Instruction *T = bb->getTerminator();
          const auto *BR = llvm::dyn_cast<llvm::BranchInst>(T);
          if (!BR) {
            const auto *SU = llvm::dyn_cast<llvm::SwitchInst>(T);
            if (SU && SU->getNumSuccessors() == 1)
              bb = SU->getSuccessor(0);
            else
              break;
            continue;
          }
          if (!BR->isConditional()) {
            bb = BR->getSuccessor(0);
            continue;
          }
          const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(BR->getCondition());
          int taken = -1;
          unsigned pred = 0;
          const llvm::ConstantInt *cst = nullptr;
          const llvm::Value *cell = nullptr;
          bool swapped = false;
          if (icmp) {
            pred = icmp->getPredicate();
            const llvm::Value *lhs = icmp->getOperand(0);
            const llvm::Value *rhs = icmp->getOperand(1);
            if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
              cst = C;
              cell = lhs;
            } else if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
              cst = C;
              cell = rhs;
              swapped = true;
            }
            if (cst) {
              unsigned ev = swapped ? swapP(pred) : pred;
              taken = holds0(ev, cst->getValue()) ? 0 : 1;
            }
          }
          auto reaches = [&](unsigned s) { return reach.count(BR->getSuccessor(s)) > 0; };
          int go = -1;
          if (taken >= 0 && reaches((unsigned)taken))
            go = taken;
          else {
            for (unsigned s = 0; s < BR->getNumSuccessors(); ++s)
              if (reaches(s)) {
                go = (int)s;
                break;
              }
          }
          if (go < 0)
            break;
          bool otherSide = false;
          for (unsigned s = 0; s < BR->getNumSuccessors(); ++s)
            if ((int)s != go && reaches(s))
              otherSide = true;
          if (icmp && cst && !otherSide) {
            unsigned ep = swapped ? swapP(pred) : pred;
            if (go == 1)
              ep = notP(ep);
            const llvm::Value *base = cell;
            bool masked = false;
            llvm::APInt mask(1, 0);
            if (cell)
              peelMask(cell, base, masked, mask);
            int64_t len = lenOfLd(base ? base : cell);
            unsigned w = 0;
            if (len > 0 && (uint64_t)len <= std::numeric_limits<unsigned>::max() / 8)
              w = (unsigned)len * 8;
            if (w == 0 && cst->getBitWidth() % 8 == 0)
              w = cst->getBitWidth();
            int nkeys = 0;
            if (w != 0 && cst->getBitWidth() == w && ep != 0 &&
                (!masked || mask.getBitWidth() == w)) {
              len = (int64_t)w / 8;
              for (const llvm::LoadInst *Ld : fieldLoads(base ? base : cell)) {
                int64_t got = (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
                if (got != len)
                  continue;
                auto bit = byVal.find(Ld->getPointerOperand());
                if (bit == byVal.end())
                  continue;
                for (const VKey &s : bit->second) {
                  if (s.formal < 0 || s.path <= 0)
                    continue;
                  ++nkeys;
                  Fix fx;
                  fx.formal = s.formal;
                  fx.path = s.path;
                  fx.len = len;
                  fx.pred = ep;
                  fx.vals.push_back(cst->getValue());
                  fx.masked = masked;
                  if (masked)
                    fx.mask = mask;
                  out.push_back(std::move(fx));
                }
              }
            }
            if (!masked && ep == llvm::ICmpInst::ICMP_NE && cst->isZero()) {
              struct CellK {
                int formal = -1;
                int path = 0;
                int64_t len = 0;
              };
              std::function<std::optional<CellK>(const llvm::Value *)> oneCell;
              std::function<void(const llvm::Value *)> force;
              oneCell = [&](const llvm::Value *V) -> std::optional<CellK> {
                std::vector<const llvm::Value *> q{V};
                std::unordered_set<const llvm::Value *> seen;
                std::set<std::pair<int, int>> keys;
                int64_t got = 0;
                while (!q.empty()) {
                  const llvm::Value *U = q.back();
                  q.pop_back();
                  if (!U || !seen.insert(U).second)
                    continue;
                  while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
                    U = C->getOperand(0);
                  if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
                    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
                      q.push_back(PN->getIncomingValue(i));
                    continue;
                  }
                  if (!llvm::isa<llvm::LoadInst>(U)) {
                    if (const auto *Arg = llvm::dyn_cast<llvm::Argument>(U)) {
                      if (Arg->getType()->isIntegerTy()) {
                        keys.insert({(int)Arg->getArgNo(), 0});
                        if (got <= 0)
                          got = (int64_t)(Arg->getType()->getPrimitiveSizeInBits() / 8);
                      }
                    }
                    auto bit = byVal.find(U);
                    if (bit != byVal.end()) {
                      for (const VKey &s : bit->second) {
                        if (s.formal < 0)
                          continue;
                        keys.insert({s.formal, s.path});
                        if (got <= 0 && U->getType()->isIntegerTy())
                          got = (int64_t)(U->getType()->getPrimitiveSizeInBits() / 8);
                      }
                    }
                  }
                  const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U);
                  if (!Ld)
                    continue;
                  const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                  if (AI) {
                    for (const llvm::User *SU : orderedUsers(AI)) {
                      const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
                      if (St && St->getPointerOperand()->stripPointerCasts() == AI)
                        q.push_back(St->getValueOperand());
                    }
                    continue;
                  }
                  auto self = byVal.find(Ld);
                  auto bit = self != byVal.end() ? self : byVal.find(Ld->getPointerOperand());
                  if (bit == byVal.end())
                    continue;
                  int64_t sz = (int64_t)DL.getTypeStoreSize(Ld->getType()).getFixedValue();
                  for (const VKey &s : bit->second) {
                    if (s.formal < 0)
                      continue;
                    keys.insert({s.formal, s.path});
                    got = sz;
                  }
                }
                std::set<std::pair<int, int>> named;
                for (const auto &k : keys)
                  if (k.second > 0)
                    named.insert(k);
                const std::set<std::pair<int, int>> &use = named.empty() ? keys : named;
                if (use.size() != 1 || got <= 0)
                  return std::nullopt;
                auto it = use.begin();
                return CellK{it->first, it->second, got};
              };
              force = [&](const llvm::Value *V) {
                if (!V)
                  return;
                std::vector<const llvm::Value *> q{V};
                std::unordered_set<const llvm::Value *> seen;
                while (!q.empty()) {
                  const llvm::Value *U = q.back();
                  q.pop_back();
                  if (!U || !seen.insert(U).second)
                    continue;
                  while (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
                    U = C->getOperand(0);
                  if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
                    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
                      q.push_back(PN->getIncomingValue(i));
                    continue;
                  }
                  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
                    const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                    if (AI) {
                      for (const llvm::User *SU : orderedUsers(AI)) {
                        const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
                        if (St && St->getPointerOperand()->stripPointerCasts() == AI)
                          q.push_back(St->getValueOperand());
                      }
                      continue;
                    }
                  }
                  const auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
                  if (BO && (BO->getOpcode() == llvm::Instruction::SDiv || BO->getOpcode() == llvm::Instruction::UDiv)) {
                    auto lhs = oneCell(BO->getOperand(0));
                    auto rhs = oneCell(BO->getOperand(1));
                    if (!lhs || !rhs || lhs->len != rhs->len || lhs->len <= 0)
                      continue;
                    Fix rel;
                    rel.formal = lhs->formal;
                    rel.path = lhs->path;
                    rel.otherFormal = rhs->formal;
                    rel.otherPath = rhs->path;
                    rel.len = lhs->len;
                    rel.pred = llvm::ICmpInst::ICMP_UGE;
                    out.push_back(std::move(rel));
                    Fix nz;
                    nz.formal = rhs->formal;
                    nz.path = rhs->path;
                    nz.len = rhs->len;
                    nz.pred = llvm::ICmpInst::ICMP_NE;
                    nz.vals.push_back(llvm::APInt((unsigned)rhs->len * 8, 0));
                    out.push_back(std::move(nz));
                    ++nkeys;
                    continue;
                  }
                  if (auto cell = oneCell(U)) {
                    if (cell->path <= 0)
                      continue;
                    Fix nz;
                    nz.formal = cell->formal;
                    nz.path = cell->path;
                    nz.len = cell->len;
                    nz.pred = llvm::ICmpInst::ICMP_NE;
                    nz.vals.push_back(llvm::APInt((unsigned)cell->len * 8, 0));
                    out.push_back(std::move(nz));
                    ++nkeys;
                  }
                }
              };
              force(base ? base : cell);
            }
            if (nkeys == 0 && cell) {
              const llvm::Value *cv = cell;
              while (const auto *C = llvm::dyn_cast<llvm::CastInst>(cv))
                cv = C->getOperand(0);
              const auto *Inner = llvm::dyn_cast<llvm::CallBase>(cv);
              llvm::Function *G = Inner ? Inner->getCalledFunction() : nullptr;
              if (G)
                G = bodyOf(G);
              auto git = G ? sum.find(G) : sum.end();
              if (Inner && G && !G->isDeclaration() && git != sum.end()) {
                unsigned ep = icmp->getPredicate();
                if (swapped)
                  ep = swapP(ep);
                if (go == 1)
                  ep = notP(ep);
                auto holds = [&](const llvm::APInt &rv) {
                  if (rv.getBitWidth() != cst->getBitWidth())
                    return false;
                  using P = llvm::ICmpInst::Predicate;
                  const llvm::APInt &cv2 = cst->getValue();
                  switch (ep) {
                  case P::ICMP_EQ: return rv.eq(cv2);
                  case P::ICMP_NE: return rv.ne(cv2);
                  case P::ICMP_UGT: return rv.ugt(cv2);
                  case P::ICMP_UGE: return rv.uge(cv2);
                  case P::ICMP_ULT: return rv.ult(cv2);
                  case P::ICMP_ULE: return rv.ule(cv2);
                  case P::ICMP_SGT: return rv.sgt(cv2);
                  case P::ICMP_SGE: return rv.sge(cv2);
                  case P::ICMP_SLT: return rv.slt(cv2);
                  case P::ICMP_SLE: return rv.sle(cv2);
                  default: return false;
                  }
                };
                const RetPred *best = nullptr;
                for (const RetPred &rp : git->second.retPreds) {
                  if (!rp.concrete || !holds(rp.val))
                    continue;
                  if (!best || rp.cond.size() > best->cond.size())
                    best = &rp;
                }
                if (best) {
                  for (const Fix &fx0 : best->cond) {
                    if (fx0.formal < 0 || fx0.formal >= (int)Inner->arg_size() || fx0.path <= 0)
                      continue;
                    const llvm::Value *act = Inner->getArgOperand((unsigned)fx0.formal);
                    auto bit = byVal.find(act);
                    if (bit == byVal.end())
                      continue;
                    const VKey *base = nullptr;
                    int nf = 0;
                    for (const VKey &s : bit->second) {
                      if (s.formal < 0)
                        continue;
                      base = &s;
                      ++nf;
                    }
                    if (nf != 1 || !base)
                      continue;
                    Fix outFx = fx0;
                    outFx.formal = base->formal;
                    outFx.path = concat(base->formal, base->path, fx0.path);
                    if (outFx.path <= 0)
                      continue;
                    out.push_back(std::move(outFx));
                  }
                }
              }
            }
          }
          bb = BR->getSuccessor((unsigned)go);
        }
        if (visit && bb == target)
          visit->insert(target);
        return out;
      };
      auto mergeFlips = [&](std::vector<Fix> cond, const llvm::BasicBlock *B) {
        for (Fix &fx : flipsTo(B)) {
          bool have = false;
          for (const Fix &a : cond)
            if (sameFix(a, fx))
              have = true;
          if (!have)
            cond.push_back(std::move(fx));
        }
        return cond;
      };
      for (Site &site : next.sites) {
        if (!site.at)
          continue;
        for (Fix &fx : flipsTo(site.at)) {
          bool have = false;
          for (const Fix &a : site.fixes)
            if (sameFix(a, fx))
              have = true;
          if (!have)
            site.fixes.push_back(std::move(fx));
        }
      }
      auto icmpFix = [&](const llvm::Value *cond, unsigned succ) {
        std::vector<Fix> out;
        const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(cond);
        if (!icmp || succ > 1)
          return out;
        unsigned pred = icmp->getPredicate();
        if (succ == 1)
          pred = notP(pred);
        const llvm::Value *lhs = icmp->getOperand(0);
        const llvm::Value *rhs = icmp->getOperand(1);
        const llvm::ConstantInt *cst = nullptr;
        const llvm::Value *cell = nullptr;
        if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
          cst = C;
          cell = lhs;
        } else if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
          cst = C;
          cell = rhs;
          pred = swapP(pred);
        }
        if (!cst || !cell || pred == 0)
          return out;
        const VKey *one = oneOf(cell);
        if (!one) {
          const llvm::Value *slot = cell;
          while (const auto *C = llvm::dyn_cast<llvm::CastInst>(slot))
            slot = C->getOperand(0);
          const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(slot);
          auto bit = Ld ? byVal.find(Ld->getPointerOperand()) : byVal.end();
          if (Ld && bit != byVal.end()) {
            const VKey *agree = nullptr;
            bool clash = false;
            for (const VKey &s : bit->second) {
              if (s.formal < 0 || s.path <= 0)
                continue;
              if (!agree)
                agree = &s;
              else if (agree->formal != s.formal || agree->path != s.path)
                clash = true;
            }
            if (!clash)
              one = agree;
          }
        }
        int64_t len = lenOfLd(cell);
        if (!one || one->formal < 0 || one->path <= 0 || len <= 0 ||
            (uint64_t)len > std::numeric_limits<unsigned>::max() / 8)
          return out;
        Fix fx;
        fx.formal = one->formal;
        fx.path = one->path;
        fx.len = len;
        fx.pred = pred;
        fx.vals.push_back(cst->getValue().zextOrTrunc((unsigned)len * 8));
        out.push_back(std::move(fx));
        return out;
      };
      auto alongPred = [&](const llvm::BasicBlock *B, const llvm::APInt &val) {
        if (!B)
          return;
        for (const llvm::BasicBlock *P : llvm::predecessors(B)) {
          const auto *BI = llvm::dyn_cast<llvm::BranchInst>(P->getTerminator());
          if (!BI || !BI->isConditional())
            continue;
          unsigned s = 2;
          if (BI->getSuccessor(0) == B)
            s = 0;
          if (BI->getSuccessor(1) == B)
            s = s == 0 ? 2 : 1;
          if (s > 1)
            continue;
          RetPred rp;
          rp.concrete = true;
          rp.val = val;
          rp.cond = mergeFlips(fixesOn(P), P);
          for (Fix &fx : icmpFix(BI->getCondition(), s)) {
            bool have = false;
            for (const Fix &a : rp.cond)
              if (sameFix(a, fx))
                have = true;
            if (!have)
              rp.cond.push_back(std::move(fx));
          }
          rp.at = P;
          if (!rp.cond.empty())
            next.retPreds.push_back(std::move(rp));
        }
      };
      for (llvm::BasicBlock &BB : F) {
        const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue())
          continue;
        const llvm::Value *rv = R->getReturnValue();
        while (const auto *C = llvm::dyn_cast<llvm::CastInst>(rv))
          rv = C->getOperand(0);
        if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(rv)) {
          RetPred rp;
          rp.concrete = true;
          rp.val = C->getValue();
          rp.cond = mergeFlips(fixesOn(&BB), &BB);
          rp.at = &BB;
          next.retPreds.push_back(std::move(rp));
          alongPred(&BB, C->getValue());
          continue;
        }
        const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(rv);
        const auto *AI =
            Ld ? llvm::dyn_cast<llvm::AllocaInst>(Ld->getPointerOperand()->stripPointerCasts()) : nullptr;
        if (!AI)
          continue;
        bool open = false;
        std::vector<std::pair<const llvm::ConstantInt *, const llvm::BasicBlock *>> slots;
        for (const llvm::User *U : AI->users()) {
          const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
          if (!St || St->getPointerOperand()->stripPointerCasts() != AI)
            continue;
          if (const auto *C = llvm::dyn_cast<llvm::ConstantInt>(St->getValueOperand()))
            slots.push_back({C, St->getParent()});
          else
            open = true;
        }
        (void)open;
        for (const auto &st : slots) {
          RetPred rp;
          rp.concrete = true;
          rp.val = st.first->getValue();
          rp.cond = mergeFlips(fixesOn(st.second), st.second);
          rp.at = st.second;
          next.retPreds.push_back(std::move(rp));
          alongPred(st.second, st.first->getValue());
        }
      }
      std::unordered_set<const llvm::BasicBlock *> walked;
      visit = &walked;
      for (llvm::Instruction &I : llvm::instructions(F))
        if (onLine(I))
          flipsTo(I.getParent());
      for (const Site &s : next.sites)
        if (s.at)
          flipsTo(s.at);
      visit = nullptr;
      std::map<std::pair<int, int>, std::pair<std::string, llvm::Function *>> slotFn;
      auto keepFn = [&](int formal, int path, llvm::Function *fn) {
        if (formal < 0 || path <= 0 || !fn)
          return;
        std::string name = showFn(fn);
        auto it = slotFn.find({formal, path});
        if (it == slotFn.end() || name < it->second.first)
          slotFn[{formal, path}] = {name, fn};
      };
      for (const llvm::BasicBlock *B : walked) {
        for (const llvm::Instruction &I : *B) {
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          llvm::Function *direct = CB->getCalledFunction();
          if (!direct)
            if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
              direct = FN;
          if (direct)
            direct = bodyOf(direct);
          if (direct && !direct->isDeclaration()) {
            auto git = sum.find(direct);
            if (git == sum.end())
              continue;
            for (const FnSum::ZeroFn &z : git->second.zeroFns) {
              if (z.formal < 0 || (unsigned)z.formal >= CB->arg_size())
                continue;
              const llvm::Value *act = CB->getArgOperand((unsigned)z.formal);
              auto bit = byVal.find(act);
              int n = 0;
              if (bit != byVal.end()) {
                for (const VKey &s : bit->second) {
                  if (s.formal < 0)
                    continue;
                  int p = concat(s.formal, s.path, z.path);
                  if (p <= 0)
                    continue;
                  keepFn(s.formal, p, z.fn);
                  ++n;
                }
              }
              if (n == 0) {
                std::vector<int> fs = denoteFormals(act);
                if (fs.size() == 1)
                  keepFn(fs[0], z.path, z.fn);
              }
            }
            const RetPred *best = nullptr;
            for (const RetPred &rp : git->second.retPreds) {
              if (!rp.concrete)
                continue;
              if (!best || rp.cond.size() > best->cond.size())
                best = &rp;
            }
            if (best) {
              for (const Fix &fx0 : best->cond) {
                if (fx0.formal < 0 || fx0.path <= 0 || (unsigned)fx0.formal >= CB->arg_size())
                  continue;
                const llvm::Value *act = CB->getArgOperand((unsigned)fx0.formal);
                auto bit = byVal.find(act);
                if (bit == byVal.end())
                  continue;
                const VKey *base = nullptr;
                int nf = 0;
                for (const VKey &s : bit->second) {
                  if (s.formal < 0)
                    continue;
                  base = &s;
                  ++nf;
                }
                if (nf != 1 || !base)
                  continue;
                Fix lifted = fx0;
                lifted.formal = base->formal;
                lifted.path = concat(base->formal, base->path, fx0.path);
                if (lifted.path <= 0)
                  continue;
                for (Site &site : next.sites) {
                  if (!site.at || !walked.count(site.at))
                    continue;
                  bool have = false;
                  for (const Fix &a : site.fixes)
                    if (sameFix(a, lifted))
                      have = true;
                  if (!have)
                    site.fixes.push_back(lifted);
                }
              }
            }
            continue;
          }
          const Site *site = nullptr;
          for (const Site &s : next.sites)
            if (s.call == &I)
              site = &s;
          if (!site)
            continue;
          std::vector<llvm::Function *> cands;
          for (int slot : site->calleeKeys) {
            eachAt(slot, [&](llvm::Function *G) {
              if (callTypeMatches(G, site->fty))
                cands.push_back(G);
            });
          }
          std::sort(cands.begin(), cands.end());
          cands.erase(std::unique(cands.begin(), cands.end()), cands.end());
          std::vector<llvm::Function *> reach;
          for (llvm::Function *G : cands)
            if (reachesSink(G))
              reach.push_back(G);
          if (reach.empty())
            continue;
          llvm::Function *best = nullptr;
          for (llvm::Function *G : reach)
            if (!best || fnBefore(G, best))
              best = G;
          if (!best)
            continue;
          for (const auto &ap : site->calleeAt)
            keepFn(ap.first, ap.second, best);
        }
      }
      for (const auto &kv : slotFn)
        next.zeroFns.push_back(
            FnSum::ZeroFn{kv.first.first, kv.first.second, kv.second.first, kv.second.second});
    }
    // A store of one formal into an sret or constructor destination is the
    // same store on the object this call is building.
    auto oneFormal = [&](const llvm::Value *V, int &formal, int &path) -> bool {
      auto it = byVal.find(V);
      if (it == byVal.end())
        return false;
      formal = -1;
      path = 0;
      bool one = false;
      for (const VKey &s : it->second) {
        if (s.formal < 0)
          continue;
        if (!one) {
          formal = s.formal;
          path = s.path;
          one = true;
        } else if (formal != s.formal || path != s.path) {
          return false;
        }
      }
      return one;
    };
    std::vector<Wr> carried;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || CB->isInlineAsm())
        continue;
      llvm::Function *G = nullptr;
      if (llvm::Function *CF = CB->getCalledFunction())
        G = bodyOf(CF);
      else if (const auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
        G = bodyOf(const_cast<llvm::Function *>(FN));
      if (!G || G->isDeclaration() || G == &F)
        continue;
      if (deepSum) {
        bool copy = false;
        for (unsigned i = 0; i < CB->arg_size() && !copy; ++i) {
          bool destSlot = CB->paramHasAttr(i, llvm::Attribute::StructRet) ||
                          (i == 0 && G->getReturnType()->isVoidTy());
          int df = -1, dp = 0;
          if (destSlot && oneFormal(CB->getArgOperand(i), df, dp))
            copy = true;
        }
        if (copy)
          ensureRan(G);
      }
      auto git = sum.find(G);
      if (git == sum.end() || !git->second.ran)
        continue;
      for (unsigned i = 0; i < CB->arg_size(); ++i) {
        bool destSlot = CB->paramHasAttr(i, llvm::Attribute::StructRet) ||
                        (i == 0 && G->getReturnType()->isVoidTy());
        if (!destSlot)
          continue;
        int df = -1, dp = 0;
        if (!oneFormal(CB->getArgOperand(i), df, dp))
          continue;
        for (const Wr &w : git->second.writes) {
          if (w.formal != (int)i || w.srcFormal < 0 || w.srcFormal >= (int)CB->arg_size())
            continue;
          int sf = -1, sp = 0;
          if (!oneFormal(CB->getArgOperand((unsigned)w.srcFormal), sf, sp))
            continue;
          Wr n;
          n.formal = df;
          n.path = concat(df, dp, w.path, true);
          n.srcFormal = sf;
          n.srcPath = concat(sf, sp, w.srcPath, true);
          n.len = w.len;
          carried.push_back(n);
        }
      }
    }
    for (Wr &w : carried)
      next.writes.push_back(std::move(w));
    next.retSig = retSigOf(next);
    next.fnSig = fnSigOf(next);
    {
      auto addBC = [&](std::vector<std::pair<int, int>> &bc, int d, int s) {
        if (d < 0 || s < 0 || d == s)
          return;
        bc.push_back({d, s});
      };
      std::vector<std::pair<int, int>> bc;
      for (const CopySite &c : next.copies)
        addBC(bc, c.df, c.sf);
      for (llvm::Instruction &I : llvm::instructions(F)) {
        const auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!S || !S->getValueOperand()->getType()->isIntegerTy(8))
          continue;
        const auto *L = llvm::dyn_cast<llvm::LoadInst>(S->getValueOperand());
        if (!L)
          continue;
        std::vector<int> ds = denoteFormals(S->getPointerOperand());
        std::vector<int> ss = denoteFormals(L->getPointerOperand());
        if (ds.size() == 1 && ss.size() == 1)
          addBC(bc, ds[0], ss[0]);
      }
      std::sort(bc.begin(), bc.end());
      bc.erase(std::unique(bc.begin(), bc.end()), bc.end());
      next.byteFrom = std::move(bc);
    }
    next.ran = true;
    sum[&F] = std::move(next);
    analyzing.erase(&F);
  }

  bool isPrefix(int whole, int pre, std::vector<std::tuple<int, int64_t, uint8_t>> &suf) const {
    suf.clear();
    if (pre == 0)
      return false;
    int p = whole;
    while (p > 0 && p != pre) {
      suf.push_back({steps[p].type, steps[p].off, steps[p].bound});
      p = steps[p].parent;
    }
    if (p != pre)
      return false;
    std::reverse(suf.begin(), suf.end());
    return true;
  }

  void forwardCopies() {
    struct At {
      llvm::Function *fn = nullptr;
      CopySite c;
    };
    // Copies are few. Walk each write's ancestors and apply the copies that
    // name that ancestor, instead of listing every write under every ancestor.
    std::unordered_map<int, std::vector<At>> copiesAt;
    for (auto &kv : sum)
      for (const CopySite &c : kv.second.copies)
        if (c.sp > 0)
          copiesAt[c.sp].push_back(At{kv.first, c});
    std::vector<WRef> added;
    if (copiesAt.empty()) {
      extra = std::move(added);
      return;
    }
    // Parent steps are allocated before their children. A step is hot when it
    // or one of its ancestors is the source of a copy.
    std::vector<int> hot(steps.size(), 0);
    for (int id = 1; id < (int)steps.size(); ++id) {
      int parent = steps[(size_t)id].parent;
      int above = parent > 0 ? hot[(size_t)parent] : 0;
      hot[(size_t)id] = copiesAt.count(id) ? id : above;
    }
    for (auto &kv : sum) {
      for (const Wr &src : kv.second.writes) {
        if (src.path <= 0 || hot[(size_t)src.path] == 0)
          continue;
        std::vector<std::tuple<int, int64_t, uint8_t>> chain;
        std::vector<int> ids;
        for (int p = src.path; p > 0; p = steps[p].parent) {
          chain.push_back({steps[p].type, steps[p].off, steps[p].bound});
          ids.push_back(p);
        }
        for (size_t i = 0; i < ids.size(); ++i) {
          auto it = copiesAt.find(ids[i]);
          if (it == copiesAt.end())
            continue;
          // Suffix is the steps above this ancestor, closest first in `chain`.
          int64_t bytes = 0;
          bool any = false;
          for (size_t s = 0; s < i; ++s) {
            int64_t o = std::get<1>(chain[s]);
            if (o == Any)
              any = true;
            else
              bytes += o < 0 ? -o : o;
          }
          for (const At &at : it->second) {
            const CopySite &c = at.c;
            if (!c.anyN && (any || bytes >= c.n))
              continue;
            int path = c.dp;
            for (size_t s = i; s-- > 0;) {
              bool stepped = false;
              path = append(c.df, path, std::get<0>(chain[s]), std::get<1>(chain[s]), &stepped);
              if (stepped)
                noteBound(path, std::get<2>(chain[s]));
            }
            Wr w = src;
            w.formal = c.df;
            w.fdep = c.sf >= 0 ? oneF(c.sf) : 0;
            int sk = lastKey(c.sp);
            w.sdep = c.sf >= 0 ? oneS(internSlot(c.sf, sk)) : 0;
            w.path = path;
            w.key = lastKey(path);
            if (w.key <= 0)
              continue;
            added.push_back(WRef{at.fn, std::move(w)});
          }
        }
      }
    }
    extra = std::move(added);
  }

  std::string showFn(const llvm::Function *F) const {
    if (!F || !F->hasName())
      return "?";
    std::string n = F->getName().str();
    std::string d = llvm::demangle(n);
    if (d.empty() || d == n)
      return n;
    return d;
  }

  // Total order used when several may-targets are the same length.
  // Demangled name, then the callee-first index from the direct call graph,
  // then the IR name. Two distinct bodies are never ordered by address.
  bool fnBefore(const llvm::Function *a, const llvm::Function *b) const {
    if (a == b)
      return false;
    std::string na = showFn(a);
    std::string nb = showFn(b);
    if (na != nb)
      return na < nb;
    auto ia = ord.find(const_cast<llvm::Function *>(a));
    auto ib = ord.find(const_cast<llvm::Function *>(b));
    int oa = ia == ord.end() ? INT_MAX : ia->second;
    int ob = ib == ord.end() ? INT_MAX : ib->second;
    if (oa != ob)
      return oa < ob;
    std::string iaName = a && a->hasName() ? a->getName().str() : std::string();
    std::string ibName = b && b->hasName() ? b->getName().str() : std::string();
    return iaName < ibName;
  }

  bool seqBefore(const std::vector<llvm::Function *> &a, const std::vector<llvm::Function *> &b) const {
    size_t n = std::min(a.size(), b.size());
    for (size_t i = 0; i < n; ++i)
      if (a[i] != b[i])
        return fnBefore(a[i], b[i]);
    return a.size() < b.size();
  }

  int gepStep(const llvm::GEPOperator *G, const llvm::DataLayout &DL) {
    int ty = 0;
    int64_t off = Any;
    const llvm::Type *src = G->getSourceElementType();
    const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
    if (!ST)
      if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
        ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
    if (ST)
      ty = internType(ST);
    if (ty <= 0)
      return 0;
    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
    int64_t inner = 0;
    if (G->accumulateConstantOffset(DL, ap)) {
      if (ap.getSignificantBits() > 63 && !ap.isNegative())
        off = Any;
      else
        off = ap.getSExtValue();
    } else if (arrayElement(G, DL, inner)) {
      off = inner;
    } else if (!llvm::isa<llvm::StructType>(G->getSourceElementType())) {
      off = 0;
    }
    return append(-1, 0, ty, off);
  }

  // A variable index selects one element when it indexes an array. A variable
  // index that selects a field of a struct names no cell. Constant fields
  // inside the element stay on that cell.
  bool arrayElement(const llvm::GEPOperator *G, const llvm::DataLayout &DL, int64_t &inner) const {
    inner = 0;
    bool saw = false;
    llvm::APInt acc(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
    for (llvm::gep_type_iterator GTI = llvm::gep_type_begin(G), GTE = llvm::gep_type_end(G); GTI != GTE; ++GTI) {
      const llvm::Value *idx = GTI.getOperand();
      if (!llvm::isa<llvm::ConstantInt>(idx)) {
        if (GTI.getStructTypeOrNull())
          return false;
        saw = true;
        continue;
      }
      const auto *CI = llvm::cast<llvm::ConstantInt>(idx);
      if (llvm::StructType *STy = GTI.getStructTypeOrNull()) {
        unsigned fi = (unsigned)CI->getZExtValue();
        if (STy->isOpaque() || fi >= STy->getNumElements())
          return false;
        acc += DL.getStructLayout(STy)->getElementOffset(fi);
      } else {
        llvm::Type *span = GTI.getIndexedType();
        if (!span)
          return false;
        acc += CI->getValue().sextOrTrunc(acc.getBitWidth()) * DL.getTypeAllocSize(span);
      }
    }
    if (!saw || acc.getSignificantBits() > 63)
      return false;
    inner = acc.getSExtValue();
    return true;
  }

  // holder.field0 is the embedded struct `inner` when their layouts match.
  bool embeddedHeader(const llvm::StructType *holder, const llvm::StructType *inner, const llvm::DataLayout &DL) const {
    if (!holder || !inner || holder->isOpaque() || inner->isOpaque() || holder->getNumElements() == 0)
      return false;
    const llvm::StructLayout *SL = DL.getStructLayout(const_cast<llvm::StructType *>(holder));
    for (unsigned i = 0; i < holder->getNumElements(); ++i) {
      if (SL->getElementOffset(i) != 0)
        continue;
      const auto *fs = llvm::dyn_cast<llvm::StructType>(holder->getElementType(i));
      if (!fs || fs->isOpaque())
        return false;
      if (fs == inner)
        return true;
      if (fs->getNumElements() != inner->getNumElements())
        return false;
      const llvm::StructLayout *A = DL.getStructLayout(const_cast<llvm::StructType *>(fs));
      const llvm::StructLayout *B = DL.getStructLayout(const_cast<llvm::StructType *>(inner));
      if (A->getSizeInBytes() != B->getSizeInBytes())
        return false;
      for (unsigned j = 0; j < fs->getNumElements(); ++j) {
        if (A->getElementOffset(j) != B->getElementOffset(j))
          return false;
        const llvm::Type *ea = fs->getElementType(j);
        const llvm::Type *eb = inner->getElementType(j);
        if (ea->isPointerTy() && eb->isPointerTy())
          continue;
        if (ea != eb)
          return false;
      }
      return true;
    }
    return false;
  }

  // Slots of (value, context) are the union of the operand slots in the
  // derived contexts. A cycle adds nothing. A finished pair is reused by
  // every caller, so the set does not depend on which arm is walked first.
  // The slots a function returns. A caller that calls the returned pointer
  // loads these slots. The cache stops a cycle through a returned call.
  void returnedSlots(const llvm::Function *F, std::set<int> &out) {
    if (!F || F->isDeclaration())
      return;
    auto it = retSlotCache.find(F);
    if (it != retSlotCache.end()) {
      out.insert(it->second.begin(), it->second.end());
      return;
    }
    if (!retSlotBusy.insert(F).second)
      return;
    const llvm::DataLayout &DL = F->getParent()->getDataLayout();
    std::set<int> acc;
    for (const llvm::BasicBlock &BB : *F) {
      const auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      collectFnSlots(R->getReturnValue(), DL, acc);
    }
    retSlotBusy.erase(F);
    auto &saved = retSlotCache[F];
    saved.assign(acc.begin(), acc.end());
    out.insert(saved.begin(), saved.end());
  }

  void collectFnSlots(const llvm::Value *V, const llvm::DataLayout &DL, std::set<int> &out) {
    struct Key {
      const llvm::Value *v = nullptr;
      bool outermost = false;
      const llvm::StructType *into = nullptr;
      bool operator==(const Key &o) const { return v == o.v && outermost == o.outermost && into == o.into; }
    };
    struct KH {
      size_t operator()(const Key &k) const {
        return ((size_t)k.v >> 4) ^ (k.outermost ? 0x9e3779b9u : 0) ^ ((size_t)k.into >> 4);
      }
    };
    std::unordered_map<Key, std::set<int>, KH> cur;
    std::unordered_set<Key, KH> stack;
    std::unordered_set<Key, KH> done;
    std::function<std::set<int>(const llvm::Value *, bool, const llvm::StructType *)> eval =
        [&](const llvm::Value *U, bool outermost, const llvm::StructType *into) -> std::set<int> {
          if (!U)
            return {};
          Key key{U, outermost, into};
          if (stack.count(key))
            return {};
          if (done.count(key))
            return cur[key];
          stack.insert(key);
          std::set<int> acc;
          auto add = [&](int k) {
            if (k > 0)
              acc.insert(k);
          };
          auto addAll = [&](const std::set<int> &s) { acc.insert(s.begin(), s.end()); };
          if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(U)) {
            if (CE->isCast())
              addAll(eval(CE->getOperand(0), outermost, into));
            else if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
              // fall through to the GEP case via the same pointer
            } else {
              stack.erase(key);
              cur[key] = acc;
              done.insert(key);
              return cur[key];
            }
          }
          if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
            const llvm::Type *src = G->getSourceElementType();
            const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
            if (!ST)
              if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
                ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
            std::set<int> bases = eval(G->getPointerOperand(), false, ST);
            int64_t off = Any;
            llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            int64_t inner = 0;
            if (G->accumulateConstantOffset(DL, ap)) {
              if (ap.getSignificantBits() <= 63 || ap.isNegative())
                off = ap.getSExtValue();
            } else if (arrayElement(G, DL, inner)) {
              off = inner;
            }
            if (!ST) {
              addAll(bases);
            } else {
              if (bases.empty())
                bases.insert(0);
              int ty = internType(ST);
              for (int base : bases) {
                if (off == 0 && !outermost && embeddedHeader(ST, into, DL))
                  add(base);
                else
                  add(slotStep(base, ty, off));
              }
            }
          } else if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
            addAll(eval(Ld->getPointerOperand(), false, nullptr));
          } else if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(U)) {
            for (const llvm::User *SU : orderedUsers(AI)) {
              const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
              if (!St || St->getPointerOperand() != AI)
                continue;
              addAll(eval(St->getValueOperand(), true, nullptr));
            }
          } else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
            if (!CB->isInlineAsm()) {
              llvm::Function *target = nullptr;
              if (llvm::Function *CF = CB->getCalledFunction())
                target = bodyOf(CF);
              else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
                target = bodyOf(FN);
              if (target) {
                std::set<int> returned;
                returnedSlots(target, returned);
                for (int s : returned)
                  add(s);
                auto sit = sum.find(target);
                if (sit != sum.end())
                  for (const Ret &r : sit->second.rets)
                    add(pathToSlot(r.path));
              }
            }
          } else if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
            addAll(eval(C->getOperand(0), outermost, into));
          } else if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
            addAll(eval(Fz->getOperand(0), outermost, into));
          } else if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
            for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
              addAll(eval(PN->getIncomingValue(i), outermost, into));
          } else if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
            addAll(eval(Sel->getTrueValue(), outermost, into));
            addAll(eval(Sel->getFalseValue(), outermost, into));
          }
          stack.erase(key);
          cur[key] = std::move(acc);
          done.insert(key);
          return cur[key];
        };
    std::set<int> got = eval(V, true, nullptr);
    out.insert(got.begin(), got.end());
  }

  // (type name, byte offset) sequence, outer field first. Names, not intern ids.
  std::string typeKey(int ty) const {
    if (ty <= 0 || ty > (int)typeName.size())
      return "#" + std::to_string(ty);
    const std::string &n = typeName[(size_t)ty - 1];
    if (n.rfind("anon", 0) != 0)
      return n;
    auto it = typeById.find(ty);
    if (it == typeById.end() || !it->second)
      return n;
    const llvm::StructType *ST = it->second;
    const llvm::DataLayout &DL = down.getDataLayout();
    if (ST->isOpaque())
      return "anon-opaque";
    const llvm::StructLayout *SL = DL.getStructLayout(const_cast<llvm::StructType *>(ST));
    std::string s = "anon{" + std::to_string(SL->getSizeInBytes());
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      s += "," + std::to_string(SL->getElementOffset(i)) + ":";
      llvm::Type *E = ST->getElementType(i);
      if (const auto *ES = llvm::dyn_cast<llvm::StructType>(E)) {
        if (ES->hasName())
          s += canonicalName(ES->getName());
        else
          s += "s" + std::to_string(DL.getTypeAllocSize(const_cast<llvm::StructType *>(ES)));
      } else if (E->isPointerTy()) {
        s += "ptr";
      } else {
        s += std::to_string(DL.getTypeAllocSize(const_cast<llvm::Type *>(E)));
      }
    }
    s += "}";
    return s;
  }

  bool chainBefore(int a, int b) const {
    if (a == b)
      return false;
    auto stepsOf = [&](int id) {
      std::vector<std::pair<std::string, int64_t>> s;
      for (int c = id; c > 0 && (size_t)c < chainParent.size(); c = chainParent[(size_t)c]) {
        s.push_back({typeKey(chainTy[(size_t)c]), chainOff[(size_t)c]});
      }
      std::reverse(s.begin(), s.end());
      return s;
    };
    return stepsOf(a) < stepsOf(b);
  }

  int fnSlotOf(const llvm::Value *V, const llvm::DataLayout &DL) {
    std::set<int> slots;
    collectFnSlots(V, DL, slots);
    int best = 0;
    for (int s : slots)
      if (best == 0 || chainBefore(s, best))
        best = s;
    return best;
  }

  std::vector<int> fnSlotsOf(const llvm::Value *V, const llvm::DataLayout &DL) {
    std::set<int> slots;
    collectFnSlots(V, DL, slots);
    return std::vector<int>(slots.begin(), slots.end());
  }

  // A call loads one cell of one object. The function may have been stored in
  // that cell, or in the same field of the table that object was copied from.
  // The field sequence from the outside of the loaded object is the same key.
  std::vector<int> slotSuffixes(int key) {
    std::vector<std::pair<int, int64_t>> steps;
    for (int c = key; c > 0 && (size_t)c < chainParent.size(); c = chainParent[(size_t)c])
      steps.push_back({chainTy[(size_t)c], chainOff[(size_t)c]});
    std::reverse(steps.begin(), steps.end());
    std::vector<int> suffixes;
    std::unordered_set<int> seen;
    auto add = [&](int id) {
      if (id > 0 && seen.insert(id).second)
        suffixes.push_back(id);
    };
    for (size_t s = 0; s < steps.size(); ++s) {
      int id = 0;
      bool ok = true;
      for (size_t k = s; k < steps.size(); ++k) {
        if (steps[k].first <= 0) {
          ok = false;
          break;
        }
        id = slotStep(id, steps[k].first, steps[k].second);
      }
      if (ok)
        add(id);
    }
    if (suffixes.empty())
      add(key);
    return suffixes;
  }

  template <typename Fn>
  void eachAt(int key, Fn &&use) {
    std::unordered_set<llvm::Function *> seen;
    for (int suf : slotSuffixes(key)) {
      auto fit = fnAt.find(suf);
      if (fit == fnAt.end())
        continue;
      for (llvm::Function *T : fit->second)
        if (seen.insert(T).second)
          use(T);
    }
  }

  // Virtual call: load the vptr, then a constant pointer index. The receiver
  // is the object whose vptr was loaded, and its size is the dereferenceable
  // byte count on that call argument. The same pair is what fileRelative stores.
  std::vector<int> vtableSlot(const llvm::CallBase *CB, const llvm::DataLayout &DL) {
    const llvm::Value *V = CB->getCalledOperand();
    auto peel = [](const llvm::Value *X) {
      while (X) {
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(X))
          X = C->getOperand(0);
        else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(X)) {
          if (!CE->isCast())
            break;
          X = CE->getOperand(0);
        } else
          break;
      }
      return X;
    };
    V = peel(V);
    const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(V);
    if (!Ld)
      return {};
    const auto *G = llvm::dyn_cast<llvm::GEPOperator>(peel(Ld->getPointerOperand()));
    if (!G || !G->getSourceElementType()->isPointerTy())
      return {};
    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
    if (!G->accumulateConstantOffset(DL, ap) || ap.isNegative())
      return {};
    int64_t off = ap.getSExtValue();
    if (off <= 0)
      return {};
    const auto *vptr = llvm::dyn_cast<llvm::LoadInst>(peel(G->getPointerOperand()));
    if (!vptr)
      return {};
    const llvm::Value *obj = peel(vptr->getPointerOperand());
    int sz = 0;
    for (unsigned i = 0; i < CB->arg_size(); ++i) {
      if (peel(CB->getArgOperand(i)) != obj)
        continue;
      uint64_t d = CB->getParamDereferenceableBytes(i);
      if (d > 0 && d < 0x80000000u)
        sz = (int)d;
      break;
    }
    std::vector<int> keys;
    if (sz > 0)
      keys.push_back(slotStep(0, 0x40000000, ((int64_t)sz << 32) | (off & 0xffffffffLL)));
    if (const auto *home = CB->getFunction()) {
      std::set<llvm::StructType *> seenTy;
      auto addTy = [&](llvm::StructType *ST, auto &self) -> void {
        if (!ST || ST->isOpaque() || !seenTy.insert(ST).second)
          return;
        int id = internType(ST);
        if (id > 0)
          keys.push_back(slotStep(0, 0x40000001, ((int64_t)id << 32) | (off & 0xffffffffLL)));
        if (ST->getNumElements() == 0)
          return;
        if (DL.getStructLayout(ST)->getElementOffset(0) != 0)
          return;
        if (auto *fs = llvm::dyn_cast<llvm::StructType>(ST->getElementType(0)))
          self(fs, self);
      };
      for (const llvm::Instruction &I : llvm::instructions(*home)) {
        const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(&I);
        if (!GG || peel(GG->getPointerOperand()) != obj)
          continue;
        if (auto *ST = llvm::dyn_cast<llvm::StructType>(GG->getSourceElementType()))
          addTy(const_cast<llvm::StructType *>(ST), addTy);
      }
    }
    return keys;
  }

  std::vector<int> vtableSlots(const llvm::CallBase *CB, const llvm::DataLayout &DL) {
    return vtableSlot(CB, DL);
  }

  // A global initializer holds callee at this byte offset. That global is a
  // vtable (or a table of function pointers) selecting the sequence callee.
  bool vtableHas(llvm::Function *callee, int off) {
    if (!callee || off <= 0)
      return false;
    auto scan = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      std::function<bool(llvm::Constant *, uint64_t)> walk = [&](llvm::Constant *C, uint64_t at) -> bool {
        if (!C)
          return false;
        if (C->stripPointerCasts() == callee)
          return (int)at == off;
        if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
          const llvm::StructLayout *SL = DL.getStructLayout(CS->getType());
          for (unsigned i = 0; i < CS->getNumOperands(); ++i)
            if (walk(CS->getOperand(i), at + SL->getElementOffset(i)))
              return true;
          return false;
        }
        if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
          uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
          for (unsigned i = 0; i < CA->getNumOperands(); ++i)
            if (walk(CA->getOperand(i), at + es * i))
              return true;
          return false;
        }
        if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(C)) {
          if (CE->isCast())
            return walk(CE->getOperand(0), at);
        }
        return false;
      };
      for (llvm::GlobalVariable &G : M.globals())
        if (G.hasInitializer() && walk(G.getInitializer(), 0))
          return true;
      return false;
    };
    return scan(down) || scan(up);
  }

  bool sameShape(int a, int b) const {
    while (a > 0 || b > 0) {
      if (a <= 0 || b <= 0)
        return false;
      if (steps[a].type != steps[b].type || steps[a].off != steps[b].off)
        return false;
      a = steps[a].parent;
      b = steps[b].parent;
    }
    return true;
  }

  // A copied field and the field a later load reads are the same cell when
  // their constant offsets match. A type pun at that address is the same cell.
  // The unmatched suffix is the field of the copied value.
  bool splitBytes(int whole, int pre, std::vector<std::pair<int, int64_t>> &rest) const {
    rest.clear();
    std::vector<std::pair<int, int64_t>> w, p;
    for (int x = whole; x > 0; x = steps[x].parent)
      w.push_back({steps[x].type, steps[x].off});
    for (int x = pre; x > 0; x = steps[x].parent)
      p.push_back({steps[x].type, steps[x].off});
    std::reverse(w.begin(), w.end());
    std::reverse(p.begin(), p.end());
    if (p.size() > w.size())
      return false;
    for (size_t i = 0; i < p.size(); ++i)
      if (w[i].second != p[i].second)
        return false;
    rest.assign(w.begin() + (std::ptrdiff_t)p.size(), w.end());
    return true;
  }

  // Functions installed at `off` bytes past an Itanium vtable address point.
  // `ident` is the class name; the vtable symbol carries that name with its
  // Itanium length prefix. An empty ident is every class.
  std::vector<llvm::Function *> vtableFns(int off, const std::string &ident) {
    if (!vtableFilled) {
      vtableFilled = true;
      auto scan = [&](llvm::Module &M) {
        const llvm::DataLayout &DL = M.getDataLayout();
        unsigned ptr = DL.getPointerSize();
        if (ptr == 0)
          return;
        std::function<void(llvm::Constant *, bool, const std::string &)> walk =
            [&](llvm::Constant *C, bool itanium, const std::string &gname) {
              if (!C)
                return;
              if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
                if (!CA->getType()->getElementType()->isPointerTy()) {
                  for (unsigned i = 0; i < CA->getNumOperands(); ++i)
                    walk(CA->getOperand(i), itanium, gname);
                  return;
                }
                int addr = itanium ? -1 : 0;
                for (unsigned i = 0; i < CA->getNumOperands(); ++i) {
                  llvm::Constant *E = CA->getOperand(i);
                  llvm::Constant *S = E->stripPointerCasts();
                  if (itanium) {
                    if (const auto *G = llvm::dyn_cast<llvm::GlobalValue>(S)) {
                      if (G->hasName() && G->getName().starts_with("_ZTI")) {
                        addr = (int)i + 1;
                        continue;
                      }
                    }
                    if (addr < 0 || (int)i < addr)
                      continue;
                  }
                  if (auto *Fn = llvm::dyn_cast<llvm::Function>(S)) {
                    int slot = ((int)i - addr) * (int)ptr;
                    if (slot > 0)
                      vtFns[slot].push_back({Fn, gname});
                  }
                }
                return;
              }
              if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
                for (unsigned i = 0; i < CS->getNumOperands(); ++i)
                  walk(CS->getOperand(i), itanium, gname);
                return;
              }
              if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(C))
                if (CE->isCast())
                  walk(CE->getOperand(0), itanium, gname);
            };
        for (llvm::GlobalVariable &G : M.globals()) {
          if (!G.hasInitializer() || !G.hasName())
            continue;
          walk(G.getInitializer(), G.getName().starts_with("_ZTV"), G.getName().str());
        }
      };
      scan(down);
      scan(up);
      for (auto &kv : vtFns) {
        auto &v = kv.second;
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
      }
    }
    std::vector<llvm::Function *> out;
    auto it = vtFns.find(off);
    if (it == vtFns.end())
      return out;
    std::string key = ident.empty() ? std::string() : std::to_string(ident.size()) + ident;
    for (const auto &p : it->second) {
      if (!key.empty() && p.second.find(key) == std::string::npos)
        continue;
      if (p.first && !p.first->isDeclaration())
        out.push_back(p.first);
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
  }

  // suffix is the field path from V out to the callsite actual.
  void ensureRan(llvm::Function *G) {
    if (!alongSequence || !G || G->isDeclaration())
      return;
    if (!deepened.insert(G).second)
      return;
    bool prev = deepSum;
    deepSum = true;
    analyze(*G);
    deepSum = prev;
  }

  void collectActual(const llvm::Value *V, int suffix, const llvm::DataLayout &DL,
                     std::set<std::pair<const llvm::Value *, int>> &seen, std::vector<LiftFrom> &out) {
    if (!V)
      return;
    bool top = walkStack == nullptr;
    std::unordered_set<const llvm::Value *> local;
    if (top)
      walkStack = &local;
    if (!walkStack->insert(V).second) {
      if (top)
        walkStack = nullptr;
      return;
    }
    struct Pop {
      Engine *e;
      const llvm::Value *v;
      bool top;
      ~Pop() {
        e->walkStack->erase(v);
        if (top)
          e->walkStack = nullptr;
      }
    } pop{this, V, top};
    if (!seen.insert({V, suffix}).second)
      return;
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (A->getType()->isPointerTy())
        out.push_back(LiftFrom{0, (int)A->getArgNo(), suffix, {}});
      else
        out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    if (llvm::isa<llvm::AllocaInst>(V)) {
      // The alloca is storage, not the object. A call that writes it (an sret
      // result, or a constructor) stores one of its arguments there. The loaded
      // field denotes that argument.
      auto peelC = [](const llvm::Value *X) {
        while (X) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(X))
            X = C->getOperand(0);
          else if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(X)) {
            if (!CE->isCast())
              break;
            X = CE->getOperand(0);
          } else
            break;
        }
        return X;
      };
      std::vector<const llvm::User *> uses;
      std::vector<const llvm::Value *> frontier{V};
      std::set<const llvm::Value *> seenUse;
      for (size_t qi = 0; qi < frontier.size(); ++qi) {
        for (const llvm::User *U : frontier[qi]->users()) {
          if (!seenUse.insert(U).second)
            continue;
          if (llvm::isa<llvm::CastInst>(U))
            frontier.push_back(U);
          else
            uses.push_back(U);
        }
      }
      for (const llvm::User *U : uses) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
        if (!CB)
          continue;
        int idx = -1;
        for (unsigned a = 0; a < CB->arg_size(); ++a) {
          if (peelC(CB->getArgOperand(a)) == V) {
            idx = (int)a;
            break;
          }
        }
        if (idx < 0)
          continue;
        std::vector<llvm::Function *> cands;
        if (llvm::Function *CF = CB->getCalledFunction()) {
          if (llvm::Function *B = bodyOf(CF))
            cands.push_back(B);
        } else if (const auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts())) {
          if (llvm::Function *B = bodyOf(const_cast<llvm::Function *>(FN)))
            cands.push_back(B);
        }
        if (cands.empty()) {
          const llvm::Value *Op = peelC(CB->getCalledOperand());
          const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(Op);
          const auto *Gp = Ld ? llvm::dyn_cast<llvm::GEPOperator>(peelC(Ld->getPointerOperand())) : nullptr;
          llvm::APInt ap(DL.getIndexSizeInBits(0), 0);
          if (Gp && Gp->getSourceElementType()->isPointerTy() && Gp->accumulateConstantOffset(DL, ap) &&
              !ap.isNegative() && ap.getSExtValue() > 0 && ap.getSExtValue() <= INT_MAX) {
            std::string ident;
            const auto *vptr = llvm::dyn_cast<llvm::LoadInst>(peelC(Gp->getPointerOperand()));
            const llvm::Value *obj = vptr ? peelC(vptr->getPointerOperand()) : nullptr;
            const llvm::Function *HF = CB->getFunction();
            if (obj && HF) {
              for (const llvm::Instruction &II : llvm::instructions(*HF)) {
                const auto *GG = llvm::dyn_cast<llvm::GEPOperator>(&II);
                if (!GG || peelC(GG->getPointerOperand()) != obj)
                  continue;
                auto *ST = llvm::dyn_cast<llvm::StructType>(GG->getSourceElementType());
                if (!ST || !ST->hasName())
                  continue;
                llvm::StringRef nm = ST->getName();
                llvm::StringRef best;
                while (!nm.empty()) {
                  auto dot = nm.find('.');
                  llvm::StringRef part = dot == llvm::StringRef::npos ? nm : nm.substr(0, dot);
                  bool digits = !part.empty();
                  for (char c : part)
                    if (c < '0' || c > '9')
                      digits = false;
                  if (!digits && part != "class" && part != "struct")
                    best = part;
                  if (dot == llvm::StringRef::npos)
                    break;
                  nm = nm.substr(dot + 1);
                }
                ident = best.str();
                break;
              }
            }
            cands = vtableFns((int)ap.getSExtValue(), ident);
          }
        }
        std::sort(cands.begin(), cands.end());
        cands.erase(std::unique(cands.begin(), cands.end()), cands.end());
        for (llvm::Function *Gfn : cands) {
          ensureRan(Gfn);
          auto git = sum.find(Gfn);
          if (git == sum.end() || !git->second.ran)
            continue;
          for (const Wr &w : git->second.writes) {
            if (w.formal != idx || w.srcFormal < 0 || w.srcFormal >= (int)CB->arg_size())
              continue;
            std::vector<std::pair<int, int64_t>> rest;
            if (w.path > 0) {
              if (suffix <= 0 || !splitBytes(suffix, w.path, rest))
                continue;
            } else if (suffix > 0) {
              for (int x = suffix; x > 0; x = steps[x].parent)
                rest.push_back({steps[x].type, steps[x].off});
              std::reverse(rest.begin(), rest.end());
            } else
              continue;
            int follow = w.srcPath;
            if (!rest.empty()) {
              int extra = 0;
              for (const auto &part : rest) {
                bool stepped = false;
                extra = append(-1, extra, part.first, part.second, &stepped);
              }
              follow = concat(-1, w.srcPath, extra, true);
            }
            int src = follow > 0 ? concat(-1, 0, follow, true) : 0;
            collectActual(CB->getArgOperand((unsigned)w.srcFormal), src, DL, seen, out);
          }
        }
      }
      out.push_back(LiftFrom{1, -1, suffix, {}});
      std::vector<const llvm::Value *> q{V};
      for (size_t i = 0; i < q.size(); ++i) {
        for (const llvm::User *U : q[i]->users()) {
          if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
            q.push_back(C);
          else if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
            for (unsigned a = 0; a < CB->arg_size(); ++a) {
              const llvm::Value *op = CB->getArgOperand(a);
              if (op == q[i] || !op->getType()->isPointerTy())
                continue;
              collectActual(op, suffix, DL, seen, out);
            }
          }
        }
      }
      return;
    }
    if (const auto *GV = llvm::dyn_cast<llvm::GlobalValue>(V)) {
      out.push_back(LiftFrom{2, -1, suffix, GV->hasName() ? GV->getName().str() : std::string()});
      return;
    }
    if (llvm::isa<llvm::ConstantPointerNull>(V) || llvm::isa<llvm::UndefValue>(V) || llvm::isa<llvm::PoisonValue>(V)) {
      out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      if (CE->isCast()) {
        collectActual(CE->getOperand(0), suffix, DL, seen, out);
        return;
      }
      if (CE->getOpcode() != llvm::Instruction::GetElementPtr) {
        out.push_back(LiftFrom{3, -1, suffix, {}});
        return;
      }
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      int step = gepStep(G, DL);
      int next = step > 0 ? concat(-1, step, suffix, true) : suffix;
      collectActual(G->getPointerOperand(), next, DL, seen, out);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      collectActual(C->getOperand(0), suffix, DL, seen, out);
      return;
    }
    if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      collectActual(Fz->getOperand(0), suffix, DL, seen, out);
      return;
    }
    if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
        collectActual(PN->getIncomingValue(i), suffix, DL, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      collectActual(Sel->getTrueValue(), suffix, DL, seen, out);
      collectActual(Sel->getFalseValue(), suffix, DL, seen, out);
      return;
    }
    if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(V)) {
      const llvm::Value *ptr = Ld->getPointerOperand();
      while (ptr) {
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(ptr))
          ptr = C->getOperand(0);
        else
          break;
      }
      if (llvm::isa<llvm::AllocaInst>(ptr)) {
        bool any = false;
        for (const llvm::User *U : ptr->users()) {
          const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
          if (!St)
            continue;
          const llvm::Value *sp = St->getPointerOperand();
          while (sp) {
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(sp))
              sp = C->getOperand(0);
            else
              break;
          }
          if (sp != ptr)
            continue;
          any = true;
          collectActual(St->getValueOperand(), suffix, DL, seen, out);
        }
        if (any)
          return;
      }
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      llvm::Function *target = nullptr;
      if (llvm::Function *CF = CB->getCalledFunction())
        target = bodyOf(CF);
      else if (const auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
        target = bodyOf(const_cast<llvm::Function *>(FN));
      auto sit = target ? sum.find(target) : sum.end();
      if (sit != sum.end() && !sit->second.ran)
        sit = sum.end();
      bool followed = false;
      if (sit != sum.end()) {
        for (const Ret &r : sit->second.rets) {
          if (r.formal < 0 || r.formal >= (int)CB->arg_size())
            continue;
          followed = true;
          int next = r.path > 0 ? concat(-1, r.path, suffix, true) : suffix;
          collectActual(CB->getArgOperand((unsigned)r.formal), next, DL, seen, out);
        }
      }
      if (followed)
        return;
      if (CB->hasRetAttr(llvm::Attribute::NoAlias))
        out.push_back(LiftFrom{1, -1, suffix, {}});
      else
        out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    out.push_back(LiftFrom{3, -1, suffix, {}});
  }

  std::string pathString(int formal, int path) const {
    struct Key {
      int type;
      int64_t off;
      uint8_t bound;
    };
    std::vector<Key> keys;
    for (int p = path; p > 0; p = steps[p].parent)
      keys.push_back(Key{steps[p].type, steps[p].off, steps[p].bound});
    std::string s = formal >= 0 ? "arg" + std::to_string(formal) : "ext";
    for (int i = (int)keys.size() - 1; i >= 0; --i) {
      s += ".";
      int ty = keys[i].type;
      if (ty > 0 && ty <= (int)typeName.size())
        s += typeName[ty - 1];
      else
        s += "ext";
      uint8_t b = keys[i].bound;
      if ((b & FromLoad) && (b & FromAddr))
        s += "*";
      else if (b & FromLoad)
        s += "^";
      else
        s += "+";
      s += keys[i].off == Any ? "any" : std::to_string(keys[i].off);
    }
    return s;
  }

  FieldReport answer() {
    std::unordered_set<int> K;
    const bool useLine = anyLine;
    struct SiteRef {
      llvm::Function *caller;
      const Site *site;
    };
    std::unordered_map<llvm::Function *, std::vector<SiteRef>> directAt;
    std::unordered_map<int, std::vector<SiteRef>> indirectAt;
    std::unordered_map<int, std::vector<std::pair<llvm::Function *, const Wr *>>> writesAt;
    auto typeOk = [](const llvm::Function *T, const llvm::FunctionType *Ty) {
      if (!Ty)
        return true;
      return T && T->getFunctionType() == Ty;
    };
    std::unordered_map<llvm::Function *, std::vector<SiteRef>> viaFn;
    auto byCaller = [&](const SiteRef &a, const SiteRef &b) {
      if (a.caller != b.caller)
        return fnBefore(a.caller, b.caller);
      return a.site->idx < b.site->idx;
    };
    // Site and write pointers address the current summaries. Re-analysis
    // replaces those summaries, so the indexes are built again afterwards.
    auto reindex = [&]() {
      directAt.clear();
      indirectAt.clear();
      writesAt.clear();
      viaFn.clear();
      for (auto &kv : sum) {
        for (const Site &site : kv.second.sites) {
          if (site.callee)
            directAt[site.callee].push_back(SiteRef{kv.first, &site});
          for (int k : site.calleeKeys)
            indirectAt[k].push_back(SiteRef{kv.first, &site});
        }
        for (const Wr &w : kv.second.writes)
          if (w.key > 0)
            writesAt[w.key].push_back({kv.first, &w});
      }
      for (const WRef &e : extra)
        if (e.w.key > 0)
          writesAt[e.w.key].push_back({e.fn, &e.w});
      for (auto &kv : fnAt) {
        auto sit = indirectAt.find(kv.first);
        if (sit == indirectAt.end())
          continue;
        for (llvm::Function *T : kv.second)
          for (const SiteRef &r : sit->second)
            if (typeOk(T, r.site->fty))
              viaFn[T].push_back(r);
      }
      for (auto &kv : directAt)
        std::sort(kv.second.begin(), kv.second.end(), byCaller);
      for (auto &kv : viaFn)
        std::sort(kv.second.begin(), kv.second.end(), byCaller);
    };
    reindex();

    std::unordered_set<std::pair<llvm::Function *, int>, FAHash> seenFormal;
    std::vector<std::pair<llvm::Function *, int>> fq;
    std::vector<int> kq;
    auto addKey = [&](int k) {
      if (k <= 0 || !K.insert(k).second)
        return;
      kq.push_back(k);
    };
    auto addFormal = [&](llvm::Function *fn, int arg) {
      if (!fn || arg < 0)
        return;
      if (!seenFormal.emplace(fn, arg).second)
        return;
      fq.emplace_back(fn, arg);
    };
    auto bindActual = [&](llvm::Function *F, int arg, const SiteRef &r) {
      if (arg >= (int)r.site->args.size())
        return;
      const ArgAt &a = r.site->args[(size_t)arg];
      for (int k : a.keys)
        addKey(k);
      for (int j : a.formals)
        addFormal(r.caller, j);
      for (int k : r.site->calleeKeys)
        addKey(k);
      (void)F;
    };

    for (auto &kv : sum) {
      bool take = useLine ? kv.second.hitLine : kv.second.hitName;
      if (!take)
        continue;
      const std::vector<int> &seed = useLine ? kv.second.lineKeys : kv.second.nameKeys;
      for (int k : seed)
        addKey(k);
      const std::vector<int> &forms = useLine ? kv.second.lineFormals : kv.second.nameFormals;
      for (int arg : forms)
        addFormal(kv.first, arg);
      const std::vector<Edge> &edges = useLine ? kv.second.lineEdges : kv.second.nameEdges;
      for (const Edge &e : edges)
        addFormal(e.fn, e.arg);
    }

    std::size_t fi = 0, ki = 0;
    while (fi < fq.size() || ki < kq.size()) {
      if (fi < fq.size()) {
        llvm::Function *F = fq[fi].first;
        int arg = fq[fi].second;
        ++fi;
        auto dit = directAt.find(F);
        if (dit != directAt.end())
          for (const SiteRef &r : dit->second)
            bindActual(F, arg, r);
        auto vit = viaFn.find(F);
        if (vit != viaFn.end())
          for (const SiteRef &r : vit->second)
            bindActual(F, arg, r);
        continue;
      }
      int k = kq[ki++];
      auto wit = writesAt.find(k);
      if (wit != writesAt.end())
        for (auto &wr : wit->second) {
          const Wr *w = wr.second;
          if (w->dep > 0)
            for (int d : deps[w->dep])
              addKey(d);
        }
      auto fit = fnAt.find(k);
      auto iit = indirectAt.find(k);
      if (fit == fnAt.end() || iit == indirectAt.end())
        continue;
      for (llvm::Function *T : fit->second)
        for (const SiteRef &r : iit->second) {
          if (!typeOk(T, r.site->fty))
            continue;
          for (unsigned i = 0; i < r.site->args.size(); ++i)
            addFormal(T, (int)i);
        }
    }
    struct OKey {
      llvm::Function *fn = nullptr;
      int formal = -1;
      bool operator==(const OKey &o) const { return fn == o.fn && formal == o.formal; }
    };
    struct OKeyHash {
      size_t operator()(const OKey &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u);
      }
    };
    struct Hit {
      llvm::Function *who = nullptr;
      int arg = -1;
      int viaHead = -1;
      // Access path of this export argument: each caller's actual concatenated
      // in front of the callee path. The same (function, formal) reached by
      // two actuals keeps both paths.
      int path = 0;
      // Printed path from the export argument, actuals in front of the write.
      // Empty when the root uses `path` instead.
      std::string layout;
    };
    std::vector<std::pair<llvm::Function *, int>> viaNodes;
    auto pushVia = [&](int prev, llvm::Function *fn) {
      viaNodes.push_back({fn, prev});
      return (int)viaNodes.size() - 1;
    };
    auto isInput = [&](llvm::Function *F, int formal) {
      if (!F || formal < 0 || !F->hasName())
        return false;
      if (passIn.count({F->getName().str(), formal}))
        return true;
      return passIn.count({showFn(F), formal}) > 0;
    };
    struct Pref {
      llvm::Function *who = nullptr;
      int arg = -1;
      int viaHead = -1;
      // Field steps of one path from this export to the sink formal.
      // A path is kept when it carries an actual the others do not.
      std::string steps;
    };
    std::unordered_map<OKey, std::vector<Pref>, OKeyHash> prefCache;
    std::unordered_set<OKey, OKeyHash> prefDone;
    // Caller actuals in front of a formal. Each call edge is kept. The
    // object graph is the union of those actuals, so a path is emitted only
    // to carry an actual the other paths do not. Repeating a (function,
    // formal) is a cycle and is not entered again.
    auto prefixesOf = [&](llvm::Function *start, int formal) -> const std::vector<Pref> & {
      static const std::vector<Pref> none;
      OKey key{start, formal};
      if (!prefDone.insert(key).second)
        return prefCache[key];
      std::vector<Pref> prefs;
      if (!start || formal < 0) {
        prefCache[key] = std::move(prefs);
        return prefCache[key];
      }
      struct Arc {
        int from = 0;
        int to = 0;
        std::string frag;
        llvm::Function *fn = nullptr;
      };
      std::vector<OKey> nodes;
      std::unordered_map<OKey, int, OKeyHash> nodeId;
      std::vector<std::vector<int>> outs;
      std::vector<std::vector<int>> rev;
      std::vector<Arc> arcs;
      auto idOf = [&](llvm::Function *fn, int fml) {
        OKey k{fn, fml};
        auto it = nodeId.find(k);
        if (it != nodeId.end())
          return it->second;
        int id = (int)nodes.size();
        nodeId.emplace(k, id);
        nodes.push_back(k);
        outs.emplace_back();
        rev.emplace_back();
        return id;
      };
      auto fragOf = [&](int path) {
        if (path <= 0)
          return std::string();
        std::string one = pathString(-1, path);
        if (one.size() > 3)
          return one.substr(3);
        return std::string();
      };
      int sink = idOf(start, formal);
      std::vector<int> walk{sink};
      std::unordered_set<int> expanded;
      expanded.insert(sink);
      for (size_t qi = 0; qi < walk.size(); ++qi) {
        int callee = walk[qi];
        llvm::Function *F = nodes[(size_t)callee].fn;
        int fml = nodes[(size_t)callee].formal;
        auto link = [&](llvm::Function *caller, int j, int actual) {
          if (!caller || j < 0)
            return;
          if (caller == F && j == fml)
            return;
          int from = idOf(caller, j);
          Arc a;
          a.from = from;
          a.to = callee;
          a.frag = fragOf(actual);
          a.fn = caller;
          int ai = (int)arcs.size();
          arcs.push_back(std::move(a));
          outs[(size_t)from].push_back(ai);
          rev[(size_t)callee].push_back(ai);
          if (expanded.insert(from).second)
            walk.push_back(from);
        };
        auto step = [&](llvm::Function *caller, const Site &site) {
          if (!caller || fml >= (int)site.args.size())
            return;
          const ArgAt &a = site.args[(size_t)fml];
          bool lifted = false;
          for (const LiftFrom &L : a.lift) {
            if (L.kind != 0 || L.formal < 0)
              continue;
            lifted = true;
            link(caller, L.formal, L.path);
          }
          if (!lifted) {
            for (int j : a.formals)
              link(caller, j, 0);
          }
          for (int j : a.vformals)
            link(caller, j, 0);
        };
        auto dit = directAt.find(F);
        if (dit != directAt.end())
          for (const SiteRef &r : dit->second)
            step(r.caller, *r.site);
        auto vit = viaFn.find(F);
        if (vit != viaFn.end())
          for (const SiteRef &r : vit->second)
            step(r.caller, *r.site);
      }
      std::vector<int> toward((size_t)nodes.size(), -1);
      std::vector<int> back{sink};
      std::vector<char> seenSink((size_t)nodes.size());
      seenSink[(size_t)sink] = 1;
      for (size_t bi = 0; bi < back.size(); ++bi) {
        int at = back[bi];
        for (int ai : rev[(size_t)at]) {
          int from = arcs[(size_t)ai].from;
          if (seenSink[(size_t)from])
            continue;
          seenSink[(size_t)from] = 1;
          toward[(size_t)from] = ai;
          back.push_back(from);
        }
      }
      auto toSink = [&](int node, std::vector<int> &out) {
        std::unordered_set<int> loop;
        for (int n = node; n != sink;) {
          if (!loop.insert(n).second)
            return false;
          int ai = toward[(size_t)n];
          if (ai < 0)
            return false;
          out.push_back(ai);
          n = arcs[(size_t)ai].to;
        }
        return true;
      };
      std::unordered_map<std::string, Pref> best;
      for (int input = 0; input < (int)nodes.size(); ++input) {
        if (!isInput(nodes[(size_t)input].fn, nodes[(size_t)input].formal))
          continue;
        if (!seenSink[(size_t)input] && input != sink)
          continue;
        std::vector<int> parent((size_t)nodes.size(), -1);
        std::vector<int> reach{input};
        std::vector<char> got((size_t)nodes.size());
        got[(size_t)input] = 1;
        for (size_t ri = 0; ri < reach.size(); ++ri) {
          int u = reach[ri];
          for (int ai : outs[(size_t)u]) {
            int v = arcs[(size_t)ai].to;
            if (got[(size_t)v])
              continue;
            got[(size_t)v] = 1;
            parent[(size_t)v] = ai;
            reach.push_back(v);
          }
        }
        auto fromInput = [&](int node, std::vector<int> &out) {
          std::vector<int> revArc;
          std::unordered_set<int> loop;
          for (int n = node; n != input;) {
            if (!loop.insert(n).second)
              return false;
            int ai = parent[(size_t)n];
            if (ai < 0)
              return false;
            revArc.push_back(ai);
            n = arcs[(size_t)ai].from;
          }
          for (int i = (int)revArc.size() - 1; i >= 0; --i)
            out.push_back(revArc[(size_t)i]);
          return true;
        };
        auto consider = [&](const std::vector<int> &seq) {
          std::string steps;
          std::vector<llvm::Function *> fns;
          std::unordered_set<int> loop;
          for (int ai : seq) {
            if (!loop.insert(ai).second)
              return;
            steps += arcs[(size_t)ai].frag;
            if (arcs[(size_t)ai].fn)
              fns.push_back(arcs[(size_t)ai].fn);
          }
          fns.push_back(start);
          std::string id = std::to_string(input) + " " + steps;
          auto it = best.find(id);
          if (it != best.end() && it->second.viaHead >= 0) {
            int oldLen = 0;
            for (int n = it->second.viaHead; n >= 0; n = viaNodes[(size_t)n].second)
              ++oldLen;
            if ((int)fns.size() >= oldLen)
              return;
          }
          int via = -1;
          for (int i = (int)fns.size() - 1; i >= 0; --i)
            via = pushVia(via, fns[(size_t)i]);
          Pref p;
          p.who = nodes[(size_t)input].fn;
          p.arg = nodes[(size_t)input].formal;
          p.viaHead = via;
          p.steps = std::move(steps);
          best[id] = std::move(p);
        };
        if (input == sink) {
          consider({});
          continue;
        }
        std::vector<int> cover;
        for (int u : reach)
          for (int ai : outs[(size_t)u])
            cover.push_back(ai);
        if (cover.empty()) {
          std::vector<int> only;
          if (toSink(input, only))
            consider(only);
          continue;
        }
        for (int ai : cover) {
          if (!got[(size_t)arcs[(size_t)ai].from])
            continue;
          std::vector<int> seq;
          if (!fromInput(arcs[(size_t)ai].from, seq))
            continue;
          seq.push_back(ai);
          std::vector<int> rest;
          if (arcs[(size_t)ai].to != sink && !toSink(arcs[(size_t)ai].to, rest))
            continue;
          seq.insert(seq.end(), rest.begin(), rest.end());
          consider(seq);
        }
      }
      for (auto &kv : best)
        prefs.push_back(std::move(kv.second));
      prefCache[key] = std::move(prefs);
      return prefCache[key];
    };
    auto hitsOf = [&](llvm::Function *start, int formal, int path) {
      std::vector<Hit> hits;
      for (const Pref &p : prefixesOf(start, formal)) {
        Hit h;
        h.who = p.who;
        h.arg = p.arg;
        h.viaHead = p.viaHead;
        h.layout = "arg" + std::to_string(p.arg) + p.steps;
        if (path > 0) {
          std::string one = pathString(-1, path);
          if (one.size() > 3)
            h.layout += one.substr(3);
        }
        hits.push_back(std::move(h));
      }
      return hits;
    };
    std::unordered_map<std::string, std::vector<llvm::Function *>> allShow;
    for (auto &kv : byName) {
      allShow[kv.first].push_back(kv.second);
      std::string d = showFn(kv.second);
      if (d != kv.first)
        allShow[d].push_back(kv.second);
    }
    std::unordered_map<std::string, llvm::Function *> byShow;
    for (auto &kv : allShow) {
      llvm::Function *best = nullptr;
      for (llvm::Function *F : kv.second)
        if (!best || fnBefore(F, best))
          best = F;
      byShow.emplace(kv.first, best);
    }
    auto lookupFn = [&](const std::string &n) -> llvm::Function * {
      auto it = byShow.find(n);
      return it == byShow.end() ? nullptr : it->second;
    };
    auto targetsOf = [&](const Site &site, const std::vector<int> &boxes) {
      std::vector<llvm::Function *> tg;
      auto take = [&](llvm::Function *T) {
        if (typeOk(T, site.fty))
          tg.push_back(T);
      };
      if (site.callee) {
        tg.push_back(site.callee);
        return tg;
      }
      for (int key : site.calleeKeys) {
        std::vector<int> suffixes = slotSuffixes(key);
        for (int id : suffixes) {
          auto fit = fnAt.find(id);
          if (fit != fnAt.end())
            for (llvm::Function *T : fit->second)
              take(T);
        }
        if (site.calleeBox >= 0 && site.calleeBox < (int)boxes.size() && boxes[(size_t)site.calleeBox] > 0) {
          int container = boxes[(size_t)site.calleeBox];
          for (int id : suffixes) {
            uint64_t hk = (uint64_t)(unsigned)container << 32 | (unsigned)id;
            auto hit = held.find(hk);
            if (hit != held.end())
              for (llvm::Function *T : hit->second)
                take(T);
          }
        }
      }
      if (site.home) {
        auto fit = fnPassed.find(site.home);
        if (fit != fnPassed.end())
          for (int formal : site.calleeFormals) {
            auto git = fit->second.find(formal);
            if (git != fit->second.end())
              for (llvm::Function *T : git->second)
                take(T);
          }
      }
      std::sort(tg.begin(), tg.end(), [&](llvm::Function *A, llvm::Function *B) { return fnBefore(A, B); });
      tg.erase(std::unique(tg.begin(), tg.end()), tg.end());
      return tg;
    };
    struct AHit {
      llvm::Function *who = nullptr;
      int arg = -1;
      std::vector<llvm::Function *> seq;
    };
    struct AK {
      llvm::Function *fn = nullptr;
      int formal = -1;
      llvm::Function *who = nullptr;
      int arg = -1;
      bool operator==(const AK &o) const {
        return fn == o.fn && formal == o.formal && who == o.who && arg == o.arg;
      }
    };
    struct AKHash {
      size_t operator()(const AK &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u) ^ ((size_t)k.who >> 4) ^
               ((size_t)k.arg * 1315423911u);
      }
    };
    struct Reach {
      llvm::Function *who = nullptr;
      int arg = -1;
      std::vector<llvm::Function *> seq;
    };
    struct RK {
      llvm::Function *F = nullptr;
      llvm::Function *who = nullptr;
      int arg = -1;
      uint64_t box = 0;
      bool operator==(const RK &o) const { return F == o.F && who == o.who && arg == o.arg && box == o.box; }
    };
    struct RKHash {
      size_t operator()(const RK &k) const {
        return ((size_t)k.F >> 4) ^ ((size_t)k.who >> 4) ^ ((size_t)k.arg * 1315423911u) ^ (size_t)k.box;
      }
    };
    std::unordered_map<llvm::Function *, std::vector<Reach>> reachFromChop;
    {
      auto passBoxes = [](const Site &site, const std::vector<int> &boxes) {
        std::vector<int> next(site.args.size(), 0);
        if (!site.callee)
          return next;
        for (unsigned i = 0; i < site.args.size(); ++i) {
          int c = site.args[i].chain;
          if (c == 0)
            for (int f : site.args[i].formals)
              if (f >= 0 && f < (int)boxes.size() && boxes[(size_t)f] > 0)
                c = boxes[(size_t)f];
          next[i] = c;
        }
        return next;
      };
      auto boxHash = [](const std::vector<int> &boxes) {
        uint64_t bh = 1469598103934665603ull;
        for (int c : boxes)
          bh = (bh ^ (uint64_t)(unsigned)c) * 1099511628211ull;
        return bh;
      };
      // Use-def names the export. A sequence is a path in the resolved graph
      // from that export to the sink. targetsOf orders may-targets by
      // demangled name, and the first visit is the shortest path in that
      // order. The same rule keeps each return to the export and, from the
      // chop, the shortest path that reaches the sink again after a function
      // repeats.
      struct St {
        llvm::Function *F = nullptr;
        uint64_t box = 0;
        bool operator==(const St &o) const { return F == o.F && box == o.box; }
      };
      struct StHash {
        size_t operator()(const St &s) const { return ((size_t)s.F >> 4) ^ (size_t)s.box; }
      };
      for (const auto &kvIn : *inMap) {
        for (const Input &in : kvIn.second) {
          if (in.arg < 0)
            continue;
          llvm::Function *who = lookupFn(in.func);
          if (!who)
            continue;
          struct Node {
            llvm::Function *F = nullptr;
            std::vector<llvm::Function *> seq;
            std::vector<int> boxes;
            uint64_t box = 0;
          };
          std::vector<Node> q;
          std::unordered_set<St, StHash> expanded;
          std::unordered_map<St, std::vector<llvm::Function *>, StHash> treePath;
          std::unordered_map<St, std::vector<int>, StHash> boxesAt;
          std::unordered_map<St, std::vector<St>, StHash> succs;
          std::unordered_map<St, St, StHash> parent;
          std::unordered_set<St, StHash> sinkStates;
          Node start;
          start.F = who;
          start.seq = {who};
          start.box = boxHash(start.boxes);
          q.push_back(std::move(start));
          for (size_t qi = 0; qi < q.size(); ++qi) {
            Node cur = q[qi];
            St cs{cur.F, cur.box};
            if (!cur.F || !expanded.insert(cs).second)
              continue;
            treePath[cs] = cur.seq;
            boxesAt[cs] = cur.boxes;
            Reach rr;
            rr.who = who;
            rr.arg = in.arg;
            rr.seq = cur.seq;
            reachFromChop[cur.F].push_back(std::move(rr));
            if (nameMatch(*cur.F)) {
              sinkStates.insert(cs);
              continue;
            }
            // A direct call steps into a function the backward cone never
            // summarized. Its calls are edges of this sequence.
            {
              auto have = sum.find(cur.F);
              if (!cur.F->isDeclaration() && (have == sum.end() || !have->second.ran))
                analyze(*cur.F);
            }
            auto sit = sum.find(cur.F);
            if (sit == sum.end())
              continue;
            for (const Site &site : sit->second.sites)
              for (llvm::Function *T : targetsOf(site, cur.boxes)) {
                if (!T)
                  continue;
                Node nxt;
                nxt.F = T;
                nxt.seq = cur.seq;
                nxt.seq.push_back(T);
                if (site.callee)
                  nxt.boxes = passBoxes(site, cur.boxes);
                nxt.box = boxHash(nxt.boxes);
                St ns{T, nxt.box};
                succs[cs].push_back(ns);
                if (!parent.count(ns))
                  parent.emplace(ns, cs);
                q.push_back(std::move(nxt));
              }
          }
          std::unordered_set<St, StHash> reach = sinkStates;
          std::vector<St> revq(sinkStates.begin(), sinkStates.end());
          std::unordered_map<St, std::vector<St>, StHash> pred;
          for (auto &kv : succs)
            for (const St &t : kv.second)
              pred[t].push_back(kv.first);
          for (size_t i = 0; i < revq.size(); ++i)
            for (const St &p : pred[revq[i]])
              if (reach.insert(p).second)
                revq.push_back(p);
          std::unordered_map<St, std::vector<llvm::Function *>, StHash> sufMemo;
          auto suffix = [&](const St &v) -> std::vector<llvm::Function *> {
            auto it = sufMemo.find(v);
            if (it != sufMemo.end())
              return it->second;
            struct Qn {
              St s;
              std::vector<llvm::Function *> path;
            };
            std::vector<Qn> sq;
            sq.push_back(Qn{v, {v.F}});
            std::unordered_set<St, StHash> seen;
            std::vector<llvm::Function *> ans;
            for (size_t i = 0; i < sq.size(); ++i) {
              if (!seen.insert(sq[i].s).second)
                continue;
              if (sinkStates.count(sq[i].s)) {
                ans = sq[i].path;
                break;
              }
              auto jt = succs.find(sq[i].s);
              if (jt == succs.end())
                continue;
              for (const St &t : jt->second) {
                if (!reach.count(t))
                  continue;
                Qn n;
                n.s = t;
                n.path = sq[i].path;
                n.path.push_back(t.F);
                sq.push_back(std::move(n));
              }
            }
            sufMemo.emplace(v, ans);
            return ans;
          };
          std::unordered_map<St, std::pair<size_t, Reach>, StHash> bestInto;
          for (auto &kv : succs) {
            auto tp = treePath.find(kv.first);
            if (tp == treePath.end())
              continue;
            for (const St &v : kv.second) {
              if (!reach.count(v))
                continue;
              auto par = parent.find(v);
              if (par != parent.end() && par->second == kv.first)
                continue;
              bool backToExport = v.F == who;
              if (!backToExport && !sinkStates.count(v))
                continue;
              std::vector<llvm::Function *> suf = suffix(v);
              if (suf.empty() || !suf.back() || !nameMatch(*suf.back()))
                continue;
              Reach extra;
              extra.who = who;
              extra.arg = in.arg;
              extra.seq = tp->second;
              extra.seq.insert(extra.seq.end(), suf.begin(), suf.end());
              if (!extra.seq.back())
                continue;
              if (backToExport) {
                reachFromChop[extra.seq.back()].push_back(std::move(extra));
                continue;
              }
              auto bit = bestInto.find(v);
              if (bit == bestInto.end() || extra.seq.size() < bit->second.first ||
                  (extra.seq.size() == bit->second.first && seqBefore(extra.seq, bit->second.second.seq)))
                bestInto[v] = {extra.seq.size(), extra};
            }
          }
          for (auto &kv : bestInto)
            if (kv.second.second.seq.back())
              reachFromChop[kv.second.second.seq.back()].push_back(std::move(kv.second.second));
          // From the chop, expand again with the prefix states not yet seen, so a
          // return to the export is still a path that can reach the sink.
          llvm::Function *chop = lookupFn(kvIn.first);
          if (chop && chop != who) {
            bool have = false;
            St at;
            size_t n = 0;
            std::vector<llvm::Function *> bestSeq;
            for (auto &kv : treePath) {
              if (kv.first.F != chop)
                continue;
              if (!have || kv.second.size() < n || (kv.second.size() == n && seqBefore(kv.second, bestSeq))) {
                have = true;
                at = kv.first;
                n = kv.second.size();
                bestSeq = kv.second;
              }
            }
            if (have) {
              std::vector<Node> cq;
              Node seed;
              seed.F = chop;
              seed.seq = treePath[at];
              seed.boxes = boxesAt[at];
              seed.box = at.box;
              cq.push_back(std::move(seed));
              std::unordered_set<St, StHash> seenC;
              bool tookLoop = false;
              for (size_t qi = 0; qi < cq.size(); ++qi) {
                Node cur = cq[qi];
                St cs{cur.F, cur.box};
                if (!cur.F)
                  continue;
                if (!seenC.insert(cs).second) {
                  if (!tookLoop && nameMatch(*cur.F)) {
                    std::unordered_set<llvm::Function *> once;
                    bool rep = false;
                    for (llvm::Function *F : cur.seq)
                      if (F && !once.insert(F).second)
                        rep = true;
                    if (rep) {
                      Reach rr;
                      rr.who = who;
                      rr.arg = in.arg;
                      rr.seq = cur.seq;
                      reachFromChop[cur.F].push_back(std::move(rr));
                      tookLoop = true;
                    }
                  }
                  continue;
                }
                Reach rr;
                rr.who = who;
                rr.arg = in.arg;
                rr.seq = cur.seq;
                reachFromChop[cur.F].push_back(rr);
                if (nameMatch(*cur.F))
                  continue;
                auto sit = sum.find(cur.F);
                if (sit == sum.end())
                  continue;
                for (const Site &site : sit->second.sites)
                  for (llvm::Function *T : targetsOf(site, cur.boxes)) {
                    if (!T)
                      continue;
                    Node nxt;
                    nxt.F = T;
                    nxt.seq = cur.seq;
                    nxt.seq.push_back(T);
                    if (site.callee)
                      nxt.boxes = passBoxes(site, cur.boxes);
                    nxt.box = boxHash(nxt.boxes);
                    cq.push_back(std::move(nxt));
                  }
              }
            }
          }
        }
      }
    }
    struct ArgId {
      llvm::Function *fn = nullptr;
      int formal = -1;
      bool operator==(const ArgId &o) const { return fn == o.fn && formal == o.formal; }
    };
    struct ArgIdHash {
      size_t operator()(const ArgId &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u);
      }
    };
    std::unordered_map<ArgId, std::unordered_set<ArgId, ArgIdHash>, ArgIdHash> pointedAt;
    std::unordered_map<ArgId, std::unordered_set<int>, ArgIdHash> pointedTy;
    auto fillPointed = [&](llvm::Function *from, int arg) {
      ArgId pk{from, arg};
      if (pointedAt.count(pk))
        return;
      struct P {
        llvm::Function *fn;
        int formal;
        bool operator==(const P &o) const { return fn == o.fn && formal == o.formal; }
      };
      struct PH {
        size_t operator()(const P &p) const { return ((size_t)p.fn >> 4) ^ (size_t)p.formal * 1315423911u; }
      };
      std::unordered_set<P, PH> got;
      std::vector<P> q;
      q.push_back({from, arg});
      for (size_t qi = 0; qi < q.size(); ++qi) {
        P cur = q[qi];
        if (!cur.fn || !got.insert(cur).second)
          continue;
        auto sit = sum.find(cur.fn);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites)
          for (unsigned i = 0; i < site.args.size(); ++i) {
            bool pass = false;
            for (int f : site.args[i].formals)
              pass = pass || f == cur.formal;
            if (!pass)
              continue;
            for (llvm::Function *T : targetsOf(site, {}))
              if (T)
                q.push_back({T, (int)i});
          }
      }
      std::unordered_set<ArgId, ArgIdHash> pack;
      for (const P &p : got)
        pack.insert(ArgId{p.fn, p.formal});
      pointedAt.emplace(pk, std::move(pack));
      std::unordered_set<int> tys;
      struct FK {
        llvm::Function *fn;
        int formal;
        bool operator==(const FK &o) const { return fn == o.fn && formal == o.formal; }
      };
      struct FKH {
        size_t operator()(const FK &k) const { return ((size_t)k.fn >> 4) ^ (size_t)k.formal * 17u; }
      };
      std::unordered_map<FK, int, FKH> bestDepth;
      auto strict = [&](llvm::Function *Fn, int formal, int depth, auto &self) -> void {
        if (!Fn || Fn->isDeclaration() || formal < 0 || formal >= (int)Fn->arg_size())
          return;
        FK key{Fn, formal};
        auto dit = bestDepth.find(key);
        if (dit != bestDepth.end() && dit->second <= depth)
          return;
        bestDepth[key] = depth;
        const llvm::Argument *Arg = Fn->getArg((unsigned)formal);
        std::unordered_set<const llvm::Value *> derived;
        std::unordered_set<const llvm::Value *> slots;
        derived.insert(Arg);
        bool grew = true;
        while (grew) {
          grew = false;
          for (llvm::Instruction &I : llvm::instructions(*Fn)) {
            bool ok = false;
            if (const auto *B = llvm::dyn_cast<llvm::BitCastInst>(&I))
              ok = derived.count(B->getOperand(0)) > 0;
            else if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(&I))
              ok = derived.count(Fz->getOperand(0)) > 0;
            else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I))
              ok = derived.count(G->getPointerOperand()) > 0;
            else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(&I)) {
              ok = P->getNumIncomingValues() > 0;
              for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
                ok = ok && derived.count(P->getIncomingValue(i)) > 0;
            } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(&I))
              ok = derived.count(S->getTrueValue()) > 0 && derived.count(S->getFalseValue()) > 0;
            else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I))
              ok = slots.count(L->getPointerOperand()->stripPointerCasts()) > 0;
            if (ok && derived.insert(&I).second)
              grew = true;
            if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              const llvm::Value *Dst = St->getPointerOperand()->stripPointerCasts();
              if (derived.count(St->getValueOperand()) > 0 && llvm::isa<llvm::AllocaInst>(Dst) && slots.insert(Dst).second)
                grew = true;
            }
          }
        }
        for (const llvm::Value *V : derived) {
          const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(V);
          if (!G)
            continue;
          llvm::Type *Src = G->getSourceElementType();
          if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(Src))
            Src = AT->getElementType();
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(Src)) {
            int id = internType(ST);
            if (id > 0)
              tys.insert(id);
          }
        }
        for (llvm::Instruction &I : llvm::instructions(*Fn)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          auto *Cal = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts());
          if (!Cal)
            continue;
          if (Cal->isDeclaration()) {
            auto nit = byName.find(Cal->getName().str());
            if (nit != byName.end())
              Cal = nit->second;
          }
          for (unsigned i = 0; i < CB->arg_size(); ++i)
            if (derived.count(CB->getArgOperand(i)) > 0)
              self(Cal, (int)i, depth + 1, self);
        }
      };
      strict(from, arg, 0, strict);
      pointedTy.emplace(pk, std::move(tys));
    };
    auto charArg = [&](llvm::Function *from, int arg) {
      auto it = pointedTy.find(ArgId{from, arg});
      if (it == pointedTy.end() || it->second.empty())
        return argDiChar(from, arg);
      for (int id : it->second) {
        if (id <= 0 || id > (int)typeName.size() || !stringTypeName(typeName[(size_t)id - 1]))
          return false;
      }
      return true;
    };
    for (const auto &kvIn : *inMap)
      for (const Input &in : kvIn.second) {
        llvm::Function *who = lookupFn(in.func);
        if (who && in.arg >= 0)
          fillPointed(who, in.arg);
      }
    auto pointerHits = [&](llvm::Function *from, int arg, llvm::Function *to, int formal) {
      auto it = pointedAt.find(ArgId{from, arg});
      return it != pointedAt.end() && it->second.count(ArgId{to, formal}) > 0;
    };
    std::unordered_map<OKey, std::vector<AHit>, OKeyHash> anchorAt;
    {
      struct Item {
        llvm::Function *fn;
        int formal;
        llvm::Function *who;
        int arg;
        std::vector<llvm::Function *> seq;
      };
      std::vector<Item> q;
      std::unordered_set<AK, AKHash> seen;
      for (const auto &kvIn : *inMap) {
        llvm::Function *chop = lookupFn(kvIn.first);
        if (!chop)
          continue;
        for (const Input &in : kvIn.second) {
          if (in.arg < 0 || in.chopArg < 0 || in.chopArg >= (int)chop->arg_size())
            continue;
          llvm::Function *who = lookupFn(in.func);
          if (!who || charArg(who, in.arg))
            continue;
          if (!pointerHits(who, in.arg, chop, in.chopArg))
            continue;
          Item it;
          it.fn = chop;
          it.formal = in.chopArg;
          it.who = who;
          it.arg = in.arg;
          it.seq = {who, chop};
          q.push_back(std::move(it));
        }
      }
      for (size_t qi = 0; qi < q.size(); ++qi) {
        Item cur = q[qi];
        if (!seen.insert(AK{cur.fn, cur.formal, cur.who, cur.arg}).second)
          continue;
        anchorAt[OKey{cur.fn, cur.formal}].push_back(AHit{cur.who, cur.arg, cur.seq});
        auto sit = sum.find(cur.fn);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites)
          for (llvm::Function *T : targetsOf(site, {}))
            for (unsigned i = 0; i < site.args.size(); ++i) {
              const ArgAt &a = site.args[i];
              bool pass = false;
              for (int f : a.formals)
                if (f == cur.formal)
                  pass = true;
              for (int f : a.vformals)
                if (f == cur.formal)
                  pass = true;
              if (!pass)
                continue;
              Item nxt;
              nxt.fn = T;
              nxt.formal = (int)i;
              nxt.who = cur.who;
              nxt.arg = cur.arg;
              nxt.seq = cur.seq;
              nxt.seq.push_back(T);
              q.push_back(std::move(nxt));
            }
      }
    }
    auto anchorLine = [&](const AHit &h, const std::string &path) {
      std::string s = "pass ";
      s += std::to_string(h.arg);
      s += " ";
      s += path;
      s += " :: ";
      s += showFn(h.who);
      s += " :: ";
      for (size_t i = 0; i < h.seq.size(); ++i) {
        if (i != 0)
          s += " => ";
        s += showFn(h.seq[i]);
      }
      return s;
    };


    std::vector<Cell> out;
    std::unordered_map<std::string, size_t> cellAt;
    auto emit = [&](llvm::Function *F, const Wr &w) {
      if (!F || !F->hasName() || w.path <= 0)
        return;
      int ty = steps[w.path].type;
      std::string type = ty > 0 && ty <= (int)typeName.size() ? typeName[ty - 1] : "";
      if (!K.count(w.key))
        return;
      std::string path = pathString(w.formal, w.path);
      std::string key = std::to_string(w.key) + " " + F->getName().str() + " " + std::to_string(w.len) + " " + w.fn +
                        " " + path;
      Cell c;
      c.chopArg = -1;
      c.off = steps[w.path].off;
      c.len = w.len;
      c.func = F->getName().str();
      c.fn = w.fn;
      c.type = std::move(type);
      c.path = std::move(path);
      std::vector<Hit> hits;
      for (const Hit &h : hitsOf(F, w.formal, w.path))
        hits.push_back(h);
      auto allow = [&](llvm::Function *, int) { return true; };
      struct Cand {
        llvm::Function *who = nullptr;
        int arg = -1;
        int acc = 0;
        std::string layout;
        std::vector<llvm::Function *> seq;
      };
      std::vector<Cand> cands;
      for (const Hit &h : hits) {
        if (!allow(h.who, h.arg))
          continue;
        Cand cd;
        cd.who = h.who;
        cd.arg = h.arg;
        cd.acc = h.path;
        cd.layout = h.layout;
        for (int n = h.viaHead; n >= 0; n = viaNodes[(size_t)n].second)
          cd.seq.push_back(viaNodes[(size_t)n].first);
        if (!cd.seq.empty())
          cands.push_back(std::move(cd));
      }
      if (cands.empty()) {
        auto rit = reachFromChop.find(F);
        if (rit != reachFromChop.end())
          for (const Reach &r : rit->second) {
            if (!allow(r.who, r.arg) || r.seq.empty())
              continue;
            Cand cd;
            cd.who = r.who;
            cd.arg = r.arg;
            cd.acc = w.path;
            cd.seq = r.seq;
            cands.push_back(std::move(cd));
          }
      }
      if (cands.empty())
        return;
      // One root per export argument and composed access path. The call
      // sequence kept for that pair is the shortest, then the name-smallest.
      std::vector<Cand> best;
      auto rootLess = [&](const std::vector<llvm::Function *> &a, const std::vector<llvm::Function *> &b) {
        if (a.size() != b.size())
          return a.size() < b.size();
        return seqBefore(a, b);
      };
      for (const Cand &cd : cands) {
        auto it = std::find_if(best.begin(), best.end(), [&](const Cand &k) {
          return k.arg == cd.arg && k.layout == cd.layout && k.acc == cd.acc && showFn(k.who) == showFn(cd.who);
        });
        if (it == best.end())
          best.push_back(cd);
        else if (rootLess(cd.seq, it->seq))
          *it = cd;
      }
      for (const Cand &cd : best) {
        AHit h;
        h.who = cd.who;
        h.arg = cd.arg;
        h.seq = cd.seq;
        c.roots.push_back(anchorLine(h, cd.layout.empty() ? pathString(cd.arg, cd.acc) : cd.layout));
      }
      if (c.roots.empty())
        return;
      auto headOf = [](const std::string &s) {
        size_t p = s.find(" :: ");
        if (p == std::string::npos)
          return s;
        p = s.find(" :: ", p + 4);
        return p == std::string::npos ? s : s.substr(0, p);
      };
      auto hopsOf = [](const std::string &s) {
        size_t n = 1;
        for (size_t p = 0; (p = s.find(" => ", p)) != std::string::npos; p += 4)
          ++n;
        return n;
      };
      auto lineBefore = [&](const std::string &a, const std::string &b) {
        size_t ha = hopsOf(a);
        size_t hb = hopsOf(b);
        if (ha != hb)
          return ha < hb;
        return a < b;
      };
      auto place = cellAt.find(key);
      if (place == cellAt.end()) {
        std::sort(c.roots.begin(), c.roots.end());
        c.roots.erase(std::unique(c.roots.begin(), c.roots.end()), c.roots.end());
        cellAt.emplace(key, out.size());
        out.push_back(std::move(c));
        return;
      }
      Cell &have = out[place->second];
      for (const std::string &line : c.roots) {
        std::string head = headOf(line);
        auto it = std::find_if(have.roots.begin(), have.roots.end(), [&](const std::string &old) {
          return headOf(old) == head;
        });
        if (it == have.roots.end())
          have.roots.push_back(line);
        else if (lineBefore(line, *it))
          *it = line;
      }
      std::sort(have.roots.begin(), have.roots.end());
      have.roots.erase(std::unique(have.roots.begin(), have.roots.end()), have.roots.end());
    };
    for (auto &kv : sum)
      for (const Wr &w : kv.second.writes)
        emit(kv.first, w);
    for (const WRef &e : extra)
      emit(e.fn, e.w);
    std::sort(out.begin(), out.end(), [](const Cell &a, const Cell &b) {
      if (a.type != b.type)
        return a.type < b.type;
      if (a.off != b.off)
        return a.off < b.off;
      if (a.func != b.func)
        return a.func < b.func;
      if (a.fn != b.fn)
        return a.fn < b.fn;
      if (a.len != b.len)
        return a.len < b.len;
      return a.path < b.path;
    });
    std::vector<std::string> seqs;
    std::unordered_set<std::string> seenSeq;
    for (const auto &kv : reachFromChop)
      for (const Reach &r : kv.second) {
        if (!r.who || r.seq.empty() || !r.seq.back() || !nameMatch(*r.seq.back()))
          continue;
        std::string s = "pass ";
        s += std::to_string(r.arg);
        s += " :: ";
        s += showFn(r.who);
        s += " :: ";
        for (size_t i = 0; i < r.seq.size(); ++i) {
          if (i != 0)
            s += " => ";
          s += showFn(r.seq[i]);
        }
        if (seenSeq.insert(s).second)
          seqs.push_back(std::move(s));
      }
    std::sort(seqs.begin(), seqs.end());
    // An opener token is (function, path formal) of the open or fopen. The
    // formal that the fd is stored into carries the token. A pointer loaded
    // from that object carries the same token. A read counts when its buffer
    // is in the sink slice and the read is on the kept sequence, or in a
    // function that sequence calls to perform the read. The length is the
    // largest constant count among those reads. A read whose count is not a
    // constant leaves the length at zero. No such read leaves no line.
    using Tok = std::pair<llvm::Function *, int>;
    std::unordered_map<llvm::Function *, std::unordered_map<int, std::vector<Tok>>> ftok;
    std::unordered_map<llvm::Function *, std::unordered_map<int, std::vector<Tok>>> gtok;
    auto addTok = [](std::vector<Tok> &dst, const Tok &t) {
      if (!t.first || std::find(dst.begin(), dst.end(), t) != dst.end())
        return false;
      dst.push_back(t);
      return true;
    };
    auto inSlice = [&](llvm::Function *home, int buf, const std::vector<int> &keys, const std::vector<int> &forms) {
      if (home && buf >= 0 && seenFormal.count({home, buf}))
        return true;
      if (home)
        for (int j : forms)
          if (j >= 0 && seenFormal.count({home, j}))
            return true;
      for (int k : keys)
        if (K.count(k))
          return true;
      return false;
    };
    auto noteRead = [&](llvm::Function *, const Tok &, int64_t) {};
    for (auto &kv : sum) {
      for (const auto &c : kv.second.carries)
        if (c.first >= 0 && c.second >= 0)
          addTok(ftok[kv.first][c.first], Tok{kv.first, c.second});
      for (const auto &o : kv.second.openAt)
        if (o.first >= 0 && o.second >= 0)
          addTok(gtok[kv.first][o.first], Tok{kv.first, o.second});
    }
    std::vector<llvm::Function *> flowQ;
    std::unordered_set<llvm::Function *> inq;
    auto poke = [&](llvm::Function *Fn) {
      if (!Fn || Fn->isDeclaration())
        return;
      if (inq.insert(Fn).second)
        flowQ.push_back(Fn);
    };
    std::vector<llvm::Function *> seedFns;
    for (auto &kv : sum)
      if (!kv.second.carries.empty() || !kv.second.openAt.empty() || !kv.second.preads.empty())
        seedFns.push_back(kv.first);
    for (llvm::Function *Fn : seedFns) {
      poke(Fn);
      auto cit = callers.find(Fn);
      if (cit == callers.end())
        continue;
      for (llvm::Function *C : cit->second)
        poke(C);
    }
    auto readTargets = [&](const Site &site) {
      std::vector<llvm::Function *> ts;
      if (site.callee) {
        ts.push_back(site.callee);
        return ts;
      }
      for (int k : site.calleeKeys) {
        auto fit = fnAt.find(k);
        if (fit == fnAt.end())
          continue;
        for (llvm::Function *T : fit->second)
          if (typeOk(T, site.fty))
            ts.push_back(T);
      }
      std::sort(ts.begin(), ts.end());
      ts.erase(std::unique(ts.begin(), ts.end()), ts.end());
      return ts;
    };
    for (size_t qi = 0; qi < flowQ.size(); ++qi) {
      llvm::Function *F = flowQ[qi];
      inq.erase(F);
      if (!F || F->isDeclaration())
        continue;
      auto fit = sum.find(F);
      if (fit == sum.end())
        continue;
      const FnSum &fs = fit->second;
      bool again = false;
      auto addF = [&](llvm::Function *fn, int formal, const Tok &t) {
        if (!fn || formal < 0)
          return;
        if (!addTok(ftok[fn][formal], t))
          return;
        again = again || fn == F;
        poke(fn);
        auto cit = callers.find(fn);
        if (cit == callers.end())
          return;
        for (llvm::Function *C : cit->second)
          poke(C);
      };
      auto addG = [&](llvm::Function *fn, int g, const Tok &t) {
        if (!fn || g < 0)
          return;
        if (!addTok(gtok[fn][g], t))
          return;
        again = again || fn == F;
        poke(fn);
      };
      auto toksAt = [&](int g, int formal) {
        std::vector<Tok> h;
        if (g >= 0) {
          auto git = gtok[F].find(g);
          if (git != gtok[F].end())
            for (const Tok &t : git->second)
              addTok(h, t);
        }
        if (formal >= 0) {
          auto fit2 = ftok[F].find(formal);
          if (fit2 != ftok[F].end())
            for (const Tok &t : fit2->second)
              addTok(h, t);
        }
        return h;
      };
      for (int i = 0; i < (int)fs.argGroup.size(); ++i) {
        int g = fs.argGroup[(size_t)i];
        for (const Tok &t : toksAt(g, i)) {
          addG(F, g, t);
          addF(F, i, t);
        }
      }
      for (const auto &o : fs.openAt)
        addG(F, o.first, Tok{F, o.second});
      for (const auto &h : fs.holds)
        for (const Tok &t : toksAt(h.second, -1))
          addF(F, h.first, t);
      for (const auto &ld : fs.fromObj)
        for (const Tok &t : toksAt(-1, ld.second))
          addG(F, ld.first, t);
      for (const PRead &pr : fs.preads) {
        for (const Tok &t : toksAt(pr.fdGroup, pr.obj))
          noteRead(F, t, pr.len);
      }
      for (size_t si = 0; si < fs.sites.size() && si < fs.binds.size(); ++si) {
        const Site &site = fs.sites[si];
        const std::vector<ArgBind> &row = fs.binds[si];
        std::vector<llvm::Function *> tg = readTargets(site);
        for (int j = 0; j < (int)row.size(); ++j) {
          std::vector<Tok> here = toksAt(row[(size_t)j].group, row[(size_t)j].formal);
          if (here.empty())
            continue;
          for (llvm::Function *callee : tg) {
            for (const Tok &t : here)
              addF(callee, j, t);
            auto cit = ftok.find(callee);
            if (cit != ftok.end()) {
              auto jt = cit->second.find(j);
              if (jt != cit->second.end())
                for (const Tok &t : jt->second) {
                  addG(F, row[(size_t)j].group, t);
                  addF(F, row[(size_t)j].formal, t);
                }
            }
            auto sit = sum.find(callee);
            if (sit == sum.end())
              continue;
            for (const PRead &pr : sit->second.preads) {
              if (pr.obj != j)
                continue;
              for (const Tok &t : here)
                noteRead(callee, t, pr.len);
            }
          }
        }
      }
      if (again)
        poke(F);
    }
    std::vector<FileBytes> files;
    struct Cand {
      std::string line;
      const Reach *r = nullptr;
    };
    std::vector<Cand> cands;
    for (const auto &rkv : reachFromChop)
      for (const Reach &r : rkv.second) {
        if (!r.who || r.seq.size() < 2 || !r.seq.back() || !nameMatch(*r.seq.back()))
          continue;
        std::string s = "pass ";
        s += std::to_string(r.arg);
        s += " :: ";
        s += showFn(r.who);
        s += " :: ";
        for (size_t i = 0; i < r.seq.size(); ++i) {
          if (i != 0)
            s += " => ";
          s += showFn(r.seq[i]);
        }
        cands.push_back(Cand{std::move(s), &r});
      }
    // A hop is a call when the caller has a direct callee of that function.
    // A slot load is a call of whatever that load names, and it is not a
    // direct hop. The witness is the sequence with the fewest hops that are
    // not direct calls, then the shortest, then the name-smallest.
    auto nonDirect = [&](const std::vector<llvm::Function *> &seq) {
      int n = 0;
      for (size_t i = 0; i + 1 < seq.size(); ++i) {
        llvm::Function *F = seq[i];
        llvm::Function *G = seq[i + 1];
        if (!F || !G) {
          ++n;
          continue;
        }
        bool direct = false;
        auto sit = sum.find(F);
        if (sit != sum.end()) {
          for (const Site &site : sit->second.sites) {
            llvm::Function *C = site.callee;
            if (!C)
              continue;
            if (C == G || bodyOf(C) == G || C == bodyOf(G))
              direct = true;
          }
        }
        if (!direct)
          ++n;
      }
      return n;
    };
    std::sort(cands.begin(), cands.end(), [&](const Cand &a, const Cand &b) {
      int da = nonDirect(a.r->seq);
      int db = nonDirect(b.r->seq);
      if (da != db)
        return da < db;
      if (a.r->seq.size() != b.r->seq.size())
        return a.r->seq.size() < b.r->seq.size();
      return a.line < b.line;
    });
    cands.erase(std::unique(cands.begin(), cands.end(),
                            [](const Cand &a, const Cand &b) { return a.line == b.line; }),
                cands.end());
    struct IntLess {
      bool operator()(const llvm::APInt &a, const llvm::APInt &b) const {
        if (a.getBitWidth() != b.getBitWidth())
          return a.getBitWidth() < b.getBitWidth();
        return a.ult(b);
      }
    };
    using Ints = std::set<llvm::APInt, IntLess>;
    auto fits = [](llvm::APInt bits, int64_t len, unsigned pred, llvm::APInt bound) {
      if (len <= 0 || (uint64_t)len > std::numeric_limits<unsigned>::max() / 8)
        return false;
      unsigned w = (unsigned)len * 8;
      if (bits.getBitWidth() != w)
        bits = bits.zextOrTrunc(w);
      if (bound.getBitWidth() != w)
        bound = bound.zextOrTrunc(w);
      using P = llvm::ICmpInst::Predicate;
      switch (pred) {
      case P::ICMP_EQ: return bits.eq(bound);
      case P::ICMP_NE: return bits.ne(bound);
      case P::ICMP_ULT: return bits.ult(bound);
      case P::ICMP_ULE: return bits.ule(bound);
      case P::ICMP_UGT: return bits.ugt(bound);
      case P::ICMP_UGE: return bits.uge(bound);
      case P::ICMP_SLT: return bits.slt(bound);
      case P::ICMP_SLE: return bits.sle(bound);
      case P::ICMP_SGT: return bits.sgt(bound);
      case P::ICMP_SGE: return bits.sge(bound);
      default: return false;
      }
    };
    auto swapPred = [](unsigned p) -> unsigned {
      using P = llvm::ICmpInst::Predicate;
      switch (p) {
      case P::ICMP_UGT: return P::ICMP_ULT;
      case P::ICMP_UGE: return P::ICMP_ULE;
      case P::ICMP_ULT: return P::ICMP_UGT;
      case P::ICMP_ULE: return P::ICMP_UGE;
      case P::ICMP_SGT: return P::ICMP_SLT;
      case P::ICMP_SGE: return P::ICMP_SLE;
      case P::ICMP_SLT: return P::ICMP_SGT;
      case P::ICMP_SLE: return P::ICMP_SGE;
      default: return p;
      }
    };
    auto notPred = [](unsigned p) -> unsigned {
      using P = llvm::ICmpInst::Predicate;
      switch (p) {
      case P::ICMP_EQ: return P::ICMP_NE;
      case P::ICMP_NE: return P::ICMP_EQ;
      case P::ICMP_UGT: return P::ICMP_ULE;
      case P::ICMP_UGE: return P::ICMP_ULT;
      case P::ICMP_ULT: return P::ICMP_UGE;
      case P::ICMP_ULE: return P::ICMP_UGT;
      case P::ICMP_SGT: return P::ICMP_SLE;
      case P::ICMP_SGE: return P::ICMP_SLT;
      case P::ICMP_SLT: return P::ICMP_SGE;
      case P::ICMP_SLE: return P::ICMP_SGT;
      default: return 0;
      }
    };
    using CK = std::tuple<std::string, int, std::string>;
    struct Box {
      bool top = true;
      bool dead = false;
      bool finite = false;
      int64_t len = 0;
      Ints allow;
      Ints forbid;
      std::vector<std::pair<unsigned, llvm::APInt>> ranges;
    };
    struct Band {
      llvm::APInt mask{1, 0};
      llvm::APInt val{1, 0};
      unsigned pred = 0;
      int64_t len = 0;
    };
    auto conj = [&](Box &b, unsigned pred, const std::vector<llvm::APInt> &vals, int64_t len) {
      if (b.dead)
        return false;
      if (b.len == 0)
        b.len = len;
      if (b.len != len || len <= 0 || (uint64_t)len > std::numeric_limits<unsigned>::max() / 8) {
        b.dead = true;
        return false;
      }
      unsigned w = (unsigned)len * 8;
      auto uz = [&](llvm::APInt x) {
        if (x.getBitWidth() != w)
          x = x.zextOrTrunc(w);
        return x;
      };
      if (pred == llvm::ICmpInst::ICMP_EQ) {
        Ints add;
        for (const llvm::APInt &v : vals)
          add.insert(uz(v));
        auto keep = [&](const llvm::APInt &v) {
          if (b.forbid.count(v))
            return false;
          for (const auto &rg : b.ranges)
            if (!fits(v, len, rg.first, rg.second))
              return false;
          return true;
        };
        Ints next;
        if (b.top || !b.finite) {
          for (const llvm::APInt &v : add)
            if (keep(v))
              next.insert(v);
        } else {
          for (const llvm::APInt &v : b.allow)
            if (add.count(v) && keep(v))
              next.insert(v);
        }
        b.top = false;
        b.finite = true;
        b.allow.swap(next);
        if (b.allow.empty()) {
          b.dead = true;
          return false;
        }
        return true;
      }
      if (pred == llvm::ICmpInst::ICMP_NE && vals.size() == 1) {
        llvm::APInt c = uz(vals[0]);
        b.top = false;
        if (b.finite) {
          b.allow.erase(c);
          if (b.allow.empty()) {
            b.dead = true;
            return false;
          }
        } else {
          b.forbid.insert(c);
        }
        return true;
      }
      if (vals.size() != 1) {
        b.dead = true;
        return false;
      }
      llvm::APInt c = uz(vals[0]);
      b.top = false;
      b.ranges.push_back({pred, c});
      if (b.finite) {
        Ints next;
        for (const llvm::APInt &v : b.allow)
          if (fits(v, len, pred, c))
            next.insert(v);
        b.allow.swap(next);
        if (b.allow.empty()) {
          b.dead = true;
          return false;
        }
      }
      return true;
    };
    using RelK = std::tuple<int, std::string, int, std::string, int64_t>;
    std::vector<GuardFix> guards;
    std::vector<FnBind> fns;
    std::string kept;
    auto firstType = [](const std::string &layout) {
      auto dot = layout.find('.');
      if (dot == std::string::npos)
        return std::string();
      auto end = layout.find_first_of("+^*", dot + 1);
      if (end == std::string::npos)
        return std::string();
      return layout.substr(dot + 1, end - (dot + 1));
    };
    // The witness root of an argument is the struct the kept sequence's first
    // call indexes. Another struct the may-analysis also assigned to that
    // formal is a different candidate, not a second value of this witness.
    std::map<int, std::string> witnessRoot;
    llvm::Function *exportFn = nullptr;
    std::vector<llvm::Function *> keptFns;
    std::vector<std::string> witnessSeq;
    std::unordered_set<std::string> witnessName;
    auto typesOf = [](const std::string &layout) {
      std::vector<std::string> t;
      for (size_t i = 0; i < layout.size();) {
        bool st = layout.compare(i, 7, "struct.") == 0;
        bool ex = layout.compare(i, 3, "ext") == 0 && (i == 0 || layout[i - 1] == '.');
        if (!st && !ex) {
          ++i;
          continue;
        }
        size_t stop = layout.size();
        auto nest = layout.find(".struct.", i + 1);
        auto cut = layout.find_first_of("+^", i);
        if (nest != std::string::npos)
          stop = std::min(stop, nest);
        if (cut != std::string::npos)
          stop = std::min(stop, cut);
        t.push_back(layout.substr(i, stop - i));
        i = stop;
      }
      return t;
    };
    std::vector<std::vector<std::string>> witnessSpines;
    // A struct reached by a load is a separate object. A path that embeds
    // that struct in its parent is the other interpretation of the may-join.
    std::unordered_set<std::string> neuType;
    auto markNeu = [](const std::string &path, std::unordered_set<std::string> &out) {
      for (size_t i = 1; i < path.size(); ++i) {
        if (path[i] != '^')
          continue;
        size_t b = path.rfind('.', i - 1);
        b = b == std::string::npos ? 0 : b + 1;
        if (b < i)
          out.insert(path.substr(b, i - b));
      }
    };
    auto collapse = [](std::string layout, const std::unordered_set<std::string> &neu) {
      bool again = true;
      while (again) {
        again = false;
        for (const std::string &ty : neu) {
          std::string mark = ty + "+0.";
          size_t at = 0;
          while ((at = layout.find(mark, at)) != std::string::npos) {
            size_t rest = at + mark.size();
            size_t plus = layout.find_first_of("+^", rest);
            if (plus == std::string::npos) {
              at = rest;
              continue;
            }
            size_t num = plus + 1;
            size_t end = num;
            while (end < layout.size() && (std::isdigit(static_cast<unsigned char>(layout[end])) || layout[end] == '-'))
              ++end;
            if (end == num) {
              at = rest;
              continue;
            }
            layout.replace(at, end - at, ty + "^" + layout.substr(num, end - num));
            again = true;
            at = at + ty.size() + 1;
          }
        }
      }
      return layout;
    };
    auto embedsNeu = [&](const std::string &layout, const std::unordered_set<std::string> &neu) {
      for (const std::string &ty : neu)
        if (layout.find(ty + "+") != std::string::npos || layout.find(ty + "*") != std::string::npos)
          return true;
      return false;
    };
    std::function<std::string(const std::string &)> anchored = [](const std::string &s) { return s; };
    struct PtrNeed {
      int arg = -1;
      std::string path;
      int64_t len = 0;
      std::string func;
      std::string root;
    };
    std::vector<PtrNeed> ptrNeed;
    for (const Cand &cand : cands) {
      const Reach &r = *cand.r;
      {
        bool prevS = alongSequence;
        bool prevD = deepSum;
        alongSequence = true;
        deepSum = true;
        for (llvm::Function *fn : r.seq)
          if (fn && !fn->isDeclaration())
            analyze(*fn);
        deepSum = prevD;
        alongSequence = prevS;
        reindex();
      }
      bool bad = false;
      std::map<CK, Ints> allow;
      std::map<CK, int64_t> alen;
      std::map<CK, std::vector<std::pair<unsigned, llvm::APInt>>> ranges;
      std::map<CK, int64_t> rlen;
      std::map<CK, Ints> forbids;
      std::map<CK, int64_t> flen;
      std::map<CK, std::vector<Band>> edgeBands;
      std::map<RelK, unsigned> rels;
      std::map<std::pair<int, std::string>, std::string> fnWant;
      // Paths an indirect call on the sequence actually loads. A store of the
      // same function at another address is a different cell.
      std::set<std::pair<int, std::string>> loadAt;
      struct PinV {
        bool ptr = false;
        std::string val;
        int64_t len = 0;
        bool clash = false;
      };
      std::map<std::string, PinV> rawPin;
      std::set<std::pair<int, std::string>> fnBad;
      struct Demand {
        llvm::Function *fn = nullptr;
        const FnSum::Rd *rd = nullptr;
      };
      std::vector<Demand> demand;
      std::set<std::tuple<llvm::Function *, int, int>> seenDemand;
      std::unordered_set<llvm::Function *> seqWriters;
      auto faultBlock = [](const llvm::BasicBlock *B) {
        for (const llvm::Instruction &I : *B) {
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          const llvm::Function *CF = CB->getCalledFunction();
          if (!CF || CF->doesNotReturn())
            return true;
        }
        return llvm::isa<llvm::UnreachableInst>(B->getTerminator());
      };
      auto reachOf = [&](const llvm::BasicBlock *target) {
        std::unordered_set<const llvm::BasicBlock *> reach;
        if (!target)
          return reach;
        std::unordered_set<const llvm::BasicBlock *> walked;
        std::vector<const llvm::BasicBlock *> stack{target};
        while (!stack.empty()) {
          const llvm::BasicBlock *B = stack.back();
          stack.pop_back();
          if (!walked.insert(B).second)
            continue;
          if (B != target && faultBlock(B))
            continue;
          reach.insert(B);
          for (const llvm::BasicBlock *P : llvm::predecessors(B))
            stack.push_back(P);
        }
        return reach;
      };
      auto takeReads = [&](llvm::Function *fn, const std::unordered_set<const llvm::BasicBlock *> &reach) {
        if (!fn || reach.empty())
          return;
        auto sit = sum.find(fn);
        if (sit == sum.end())
          return;
        for (const FnSum::Rd &rd : sit->second.reads) {
          if (!rd.at || rd.path <= 0 || rd.key <= 0 || !reach.count(rd.at))
            continue;
          if (!seenDemand.insert({fn, rd.formal, rd.path}).second)
            continue;
          demand.push_back(Demand{fn, &rd});
        }
      };
      // The layout of a formal is the actuals along the kept sequence, from
      // the export down to that formal. A prefix through some other caller
      // is a different object.
      struct Lay {
        int arg = -1;
        std::string layout;
      };
      using LayKey = std::tuple<llvm::Function *, int, int>;
      // One sequence composes each (function, formal, path) once. The same
      // actual is reused wherever that formal is read again.
      std::map<LayKey, std::vector<Lay>> layMemo;
      std::function<void(llvm::Function *, int, int, std::vector<Lay> &, std::set<LayKey> &)> walkLay;
      walkLay = [&](llvm::Function *fn, int formal, int path, std::vector<Lay> &out,
                    std::set<LayKey> &stack) {
        if (!fn || formal < 0)
          return;
        LayKey key{fn, formal, path};
        auto mit = layMemo.find(key);
        if (mit != layMemo.end()) {
          out.insert(out.end(), mit->second.begin(), mit->second.end());
          return;
        }
        if (!stack.insert(key).second)
          return;
        size_t mark = out.size();
        auto finish = [&]() {
          layMemo.emplace(key, std::vector<Lay>(out.begin() + (std::ptrdiff_t)mark, out.end()));
          stack.erase(key);
        };
        auto addSteps = [&](int arg, std::string layout) {
          if (path > 0) {
            std::string one = pathString(-1, path);
            if (one.size() > 3)
              layout += one.substr(3);
          }
          if (!layout.empty())
            out.push_back(Lay{arg, std::move(layout)});
        };
        if (fn == r.who) {
          if (formal < (int)fn->arg_size())
            addSteps(formal, "arg" + std::to_string(formal));
          finish();
          return;
        }
        for (size_t i = 1; i < r.seq.size(); ++i) {
          llvm::Function *here = r.seq[i];
          llvm::Function *hb = bodyOf(here);
          if (here != fn && hb != fn)
            continue;
          llvm::Function *caller = r.seq[i - 1];
          std::vector<const Site *> sites;
          auto take = [&](const std::vector<SiteRef> &refs) {
            for (const SiteRef &sr : refs)
              if (sr.caller == caller && sr.site)
                sites.push_back(sr.site);
          };
          auto dit = directAt.find(here);
          if (dit != directAt.end())
            take(dit->second);
          if (hb && hb != here) {
            auto d2 = directAt.find(hb);
            if (d2 != directAt.end())
              take(d2->second);
          }
          auto vit = viaFn.find(here);
          if (vit != viaFn.end())
            take(vit->second);
          if (hb && hb != here) {
            auto v2 = viaFn.find(hb);
            if (v2 != viaFn.end())
              take(v2->second);
          }
          if (sites.empty()) {
            llvm::Function *cb = bodyOf(here);
            auto sit = sum.find(caller);
            if (sit != sum.end())
              for (const Site &site : sit->second.sites) {
                if (site.callee)
                  continue;
                if (typeOk(here, site.fty) || (cb && cb != here && typeOk(cb, site.fty)))
                  sites.push_back(&site);
                else if (site.vtableOff > 0 && (vtableHas(here, site.vtableOff) || (cb && vtableHas(cb, site.vtableOff))))
                  sites.push_back(&site);
              }
          }
          for (const Site *site : sites) {
            if (formal >= (int)site->args.size())
              continue;
            const ArgAt &a = site->args[(size_t)formal];
            bool lifted = false;
            auto innerOf = [&](int full) {
              int outer = full;
              while (outer > 0 && steps[outer].parent > 0)
                outer = steps[outer].parent;
              if (outer <= 0)
                return 0;
              std::vector<int> ids;
              for (int p = full; p > 0; p = steps[p].parent)
                if (p != outer)
                  ids.push_back(p);
              int cur = 0;
              for (int i = (int)ids.size() - 1; i >= 0; --i) {
                bool stepped = false;
                int n = append(-1, cur, steps[ids[i]].type, steps[ids[i]].off, &stepped, true);
                if (stepped)
                  noteBound(n, steps[ids[i]].bound);
                cur = n;
              }
              return cur;
            };
            std::vector<int> liftOrd;
            liftOrd.reserve(a.lift.size());
            for (int li = 0; li < (int)a.lift.size(); ++li)
              if (a.lift[li].pointee)
                liftOrd.push_back(li);
            for (int li = 0; li < (int)a.lift.size(); ++li)
              if (!a.lift[li].pointee)
                liftOrd.push_back(li);
            for (int li : liftOrd) {
              const LiftFrom &L = a.lift[li];
              if (L.kind == 1 && L.path == 0 && path > 0 && !a.carried.empty()) {
                int outer = path;
                while (steps[outer].parent > 0)
                  outer = steps[outer].parent;
                if (steps[outer].off == Any)
                  continue;
                const Carried *hit = nullptr;
                int nmatch = 0;
                for (const Carried &c : a.carried) {
                  if (c.off != steps[outer].off || c.formal < 0)
                    continue;
                  hit = &c;
                  ++nmatch;
                }
                if (nmatch != 1 || !hit)
                  continue;
                lifted = true;
                int composed = concat(hit->formal, hit->path, innerOf(path), true);
                std::vector<Lay> up;
                walkLay(caller, hit->formal, composed, up, stack);
                for (const Lay &p : up)
                  out.push_back(p);
                continue;
              }
              if (L.kind != 0 || L.formal < 0)
                continue;
              if (path > 0 && !a.carried.empty()) {
                int outer = path;
                while (steps[outer].parent > 0)
                  outer = steps[outer].parent;
                if (steps[outer].off != Any) {
                  const Carried *hit0 = nullptr;
                  int n0 = 0;
                  for (const Carried &c : a.carried) {
                    if (c.off != steps[outer].off || c.formal < 0)
                      continue;
                    hit0 = &c;
                    ++n0;
                  }
                  if (n0 == 1 && hit0) {
                    lifted = true;
                    int composed = concat(hit0->formal, hit0->path, innerOf(path), true);
                    std::vector<Lay> up;
                    walkLay(caller, hit0->formal, composed, up, stack);
                    for (const Lay &p : up)
                      out.push_back(p);
                    continue;
                  }
                }
              }
              lifted = true;
              int composed = concat(L.formal, L.path, path, true);
              if (L.pointee && path > 0 && composed > 0) {
                for (int p = composed; p > 0; p = steps[p].parent) {
                  if (steps[p].parent == L.path) {
                    // A load denotes one new object. The callee's first offset
                    // is a byte of that object when the parent step is still
                    // the cell that was loaded. When the parent step already
                    // denotes the loaded object, this offset is a field of
                    // that same object and keeps the address bound concat
                    // recorded.
                    // A load denotes one new object. The callee's first offset is a
                    // byte of that object when the parent step is still the cell.
                    // When the parent step already denotes the loaded object, this
                    // offset is a field of that same object.
                    if (!(L.path > 0 && steps[L.path].bound == FromLoad))
                      steps[p].bound = FromLoad;
                    break;
                  }
                  if (p == L.path)
                    break;
                }
              }
              std::vector<Lay> up;
              walkLay(caller, L.formal, composed, up, stack);
              for (const Lay &p : up)
                out.push_back(p);
            }
            if (lifted)
              continue;
            for (int j : a.formals) {
              std::vector<Lay> up;
              walkLay(caller, j, path, up, stack);
              for (const Lay &p : up)
                out.push_back(p);
            }
          }
          break;
        }
        finish();
      };
      auto layoutsOf = [&](llvm::Function *fn, int formal, int path) {
        std::vector<Hit> hits;
        std::vector<Lay> lays;
        std::set<std::tuple<llvm::Function *, int, int>> stack;
        walkLay(fn, formal, path, lays, stack);
        std::set<std::pair<int, std::string>> seen;
        for (const Lay &L : lays) {
          if (L.arg < 0 || L.layout.empty() || !seen.insert({L.arg, L.layout}).second)
            continue;
          Hit h;
          h.who = r.who;
          h.arg = L.arg;
          h.layout = L.layout;
          hits.push_back(std::move(h));
        }
        if (hits.empty())
          return hitsOf(fn, formal, path);
        return hits;
      };
      for (size_t i = 0; i + 1 < r.seq.size() && !bad; ++i) {
        llvm::Function *caller = r.seq[i];
        llvm::Function *callee = r.seq[i + 1];
        std::vector<const Site *> sites;
        auto takeSites = [&](const std::vector<SiteRef> &refs) {
          for (const SiteRef &sr : refs)
            if (sr.caller == caller && sr.site)
              sites.push_back(sr.site);
        };
        auto dit = directAt.find(callee);
        if (dit != directAt.end())
          takeSites(dit->second);
        auto vit = viaFn.find(callee);
        if (vit != viaFn.end())
          takeSites(vit->second);
        std::sort(sites.begin(), sites.end());
        sites.erase(std::unique(sites.begin(), sites.end()), sites.end());
        if (sites.empty()) {
          llvm::Function *cb = bodyOf(callee);
          auto sit = sum.find(caller);
          if (sit != sum.end())
            for (const Site &site : sit->second.sites) {
              if (site.callee)
                continue;
              if (typeOk(callee, site.fty) || (cb && cb != callee && typeOk(cb, site.fty)))
                sites.push_back(&site);
              else if (site.vtableOff > 0 && (vtableHas(callee, site.vtableOff) || (cb && vtableHas(cb, site.vtableOff))))
                sites.push_back(&site);
            }
        }
        if (sites.empty())
          continue;
        {
          std::unordered_set<const llvm::BasicBlock *> reach;
          for (const Site *site : sites) {
            auto part = reachOf(site->at);
            reach.insert(part.begin(), part.end());
          }
          takeReads(caller, reach);
        }
        std::vector<const Site *> indirect;
        for (const Site *site : sites)
          if (!site->callee)
            indirect.push_back(site);
        if (!indirect.empty()) {
          std::set<std::pair<int, std::string>> common;
          bool first = true;
          bool ok = true;
          for (const Site *site : indirect) {
            std::vector<std::pair<int, int>> slots = site->calleeAt;
            if (slots.empty() && site->calleeFormal >= 0 && site->calleePath > 0)
              slots.push_back({site->calleeFormal, site->calleePath});
            std::set<std::pair<int, std::string>> here;
            for (const auto &sp : slots) {
              auto hits = layoutsOf(caller, sp.first, sp.second);
              for (const Hit &h : hits) {
                if (h.layout.empty())
                  continue;
                int arg = h.arg;
                std::string layout = h.layout;
                if (h.who != r.who) {
                  std::set<std::pair<llvm::Function *, int>> seenF;
                  llvm::Function *fn = h.who;
                  int formal = h.arg;
                  arg = -1;
                  while (fn && formal >= 0 && seenF.insert({fn, formal}).second) {
                    if (fn == r.who || bodyOf(fn) == r.who) {
                      arg = formal < (int)r.who->arg_size() ? formal : -1;
                      break;
                    }
                    llvm::Function *up = nullptr;
                    llvm::Function *at = fn;
                    for (size_t si = 1; si < r.seq.size(); ++si) {
                      llvm::Function *here = r.seq[si];
                      llvm::Function *hb = bodyOf(here);
                      if (here == fn || hb == fn) {
                        up = r.seq[si - 1];
                        at = here;
                        break;
                      }
                    }
                    if (!up)
                      break;
                    std::vector<const Site *> ss;
                    auto takeS = [&](const std::vector<SiteRef> &refs) {
                      for (const SiteRef &sr : refs)
                        if (sr.caller == up && sr.site)
                          ss.push_back(sr.site);
                    };
                    auto d1 = directAt.find(at);
                    if (d1 != directAt.end())
                      takeS(d1->second);
                    auto v1 = viaFn.find(at);
                    if (v1 != viaFn.end())
                      takeS(v1->second);
                    int parent = -2;
                    bool clash = false;
                    for (const Site *site : ss) {
                      if (formal >= (int)site->args.size())
                        continue;
                      for (const LiftFrom &L : site->args[(size_t)formal].lift) {
                        if (L.kind != 0 || L.formal < 0 || L.path != 0)
                          continue;
                        if (parent == -2)
                          parent = L.formal;
                        else if (parent != L.formal)
                          clash = true;
                      }
                    }
                    if (clash || parent < 0)
                      break;
                    fn = up;
                    formal = parent;
                  }
                  if (arg < 0) {
                    if (h.arg < 0 || h.arg >= (int)r.who->arg_size())
                      continue;
                    arg = h.arg;
                  }
                  std::string from = "arg" + std::to_string(h.arg);
                  std::string to = "arg" + std::to_string(arg);
                  if (layout.compare(0, from.size(), from) == 0 &&
                      (layout.size() == from.size() || layout[from.size()] == '.'))
                    layout = to + layout.substr(from.size());
                }
                here.insert({arg, layout});
              }
            }
            if (here.empty()) {
              ok = false;
              break;
            }
            if (first) {
              common = std::move(here);
              first = false;
            } else {
              std::set<std::pair<int, std::string>> both;
              for (const auto &k : common)
                if (here.count(k))
                  both.insert(k);
              common.swap(both);
            }
          }
          if (ok && !common.empty()) {
            std::string name = showFn(callee);
            for (const auto &k : common) {
              loadAt.insert(k);
              auto it = fnWant.find(k);
              if (it == fnWant.end())
                fnWant.emplace(k, name);
              else if (it->second != name)
                fnBad.insert(k);
            }
          }
          std::set<std::pair<int, std::string>> vcommon;
          bool vfirst = true;
          bool vany = false;
          for (const Site *site : indirect) {
            if (site->vtableOff <= 0)
              continue;
            std::string tail = ".struct.slot^" + std::to_string(site->vtableOff);
            std::set<std::pair<int, std::string>> here;
            for (const auto &sp : site->vtableRecv) {
              if (sp.second > 0) {
                for (const Hit &h : layoutsOf(caller, sp.first, sp.second)) {
                  if (h.who != r.who || h.layout.empty())
                    continue;
                  here.insert({h.arg, h.layout + tail});
                }
              } else if (sp.first >= 0 && caller == r.who && !site->vtableTy.empty()) {
                here.insert({sp.first, "arg" + std::to_string(sp.first) + "." + site->vtableTy + "^0" + tail});
              }
            }
            if (here.empty())
              continue;
            vany = true;
            if (vfirst) {
              vcommon = std::move(here);
              vfirst = false;
            } else {
              std::set<std::pair<int, std::string>> both;
              for (const auto &k : vcommon)
                if (here.count(k))
                  both.insert(k);
              vcommon.swap(both);
            }
          }
          if (vany && !vcommon.empty()) {
            std::string name = showFn(callee);
            for (const auto &k : vcommon) {
              loadAt.insert(k);
              auto it = fnWant.find(k);
              if (it == fnWant.end())
                fnWant.emplace(k, name);
              else if (it->second != name)
                fnBad.insert(k);
            }
          }
        }
        struct Info {
          std::map<CK, Box> cells;
          std::map<CK, std::vector<Band>> bands;
          std::map<RelK, unsigned> rel;
          bool dead = false;
        };
        std::vector<Info> infos;
        for (const Site *site : sites) {
          Info info;
          for (Fix fx : site->fixes) {
            if (caller == r.who) {
              auto bareArg = [&](int formal, int path) {
                return path == 0 && formal >= 0 && formal < (int)caller->arg_size();
              };
              if (bareArg(fx.otherFormal, fx.otherPath)) {
                llvm::Type *ty = caller->getArg((unsigned)fx.otherFormal)->getType();
                if (ty->isPointerTy())
                  continue;
                if (ty->isIntegerTy() && fx.len > 0 &&
                    (uint64_t)fx.len <= std::numeric_limits<unsigned>::max() / 8) {
                  fx.vals.clear();
                  fx.vals.push_back(llvm::APInt((unsigned)fx.len * 8, 0));
                  fx.otherFormal = -1;
                }
              } else if (bareArg(fx.formal, fx.path) && fx.otherFormal >= 0) {
                llvm::Type *ty = caller->getArg((unsigned)fx.formal)->getType();
                if (ty->isPointerTy())
                  continue;
                if (ty->isIntegerTy() && fx.len > 0 &&
                    (uint64_t)fx.len <= std::numeric_limits<unsigned>::max() / 8) {
                  fx.formal = fx.otherFormal;
                  fx.path = fx.otherPath;
                  fx.pred = swapPred(fx.pred);
                  fx.vals.clear();
                  fx.vals.push_back(llvm::APInt((unsigned)fx.len * 8, 0));
                  fx.otherFormal = -1;
                  fx.otherPath = 0;
                }
              }
            }
            if (fx.formal < 0 || fx.len <= 0 || fx.pred == 0 || fx.path < 0 ||
                (fx.path == 0 && fx.otherFormal < 0) || (fx.otherFormal >= 0 && fx.otherPath < 0)) {
              info.dead = true;
              break;
            }
            if (fx.masked && fx.otherFormal < 0) {
              for (const Hit &h : layoutsOf(caller, fx.formal, fx.path)) {
                if (h.who != r.who || h.layout.empty() || fx.vals.size() != 1)
                  continue;
                CK key{showFn(h.who), h.arg, h.layout};
                Band bd;
                bd.mask = fx.mask;
                bd.val = fx.vals[0];
                bd.pred = fx.pred;
                bd.len = fx.len;
                auto &row = info.bands[key];
                bool seen = false;
                for (const Band &a : row)
                  if (a.pred == bd.pred && a.len == bd.len && a.mask.getBitWidth() == bd.mask.getBitWidth() &&
                      a.mask == bd.mask && a.val.getBitWidth() == bd.val.getBitWidth() && a.val == bd.val)
                    seen = true;
                if (!seen)
                  row.push_back(std::move(bd));
              }
            } else if (fx.otherFormal < 0) {
              for (const Hit &h : layoutsOf(caller, fx.formal, fx.path)) {
                if (h.who != r.who || h.layout.empty())
                  continue;
                CK key{showFn(h.who), h.arg, h.layout};
                if (!conj(info.cells[key], fx.pred, fx.vals, fx.len))
                  info.dead = true;
              }
            } else {
              unsigned pred0 = fx.pred;
              struct End {
                int via = -1;
                int arg = -1;
                std::string layout;
              };
              std::vector<End> left, right;
              for (const Hit &h : layoutsOf(caller, fx.formal, fx.path))
                if (h.who == r.who && !h.layout.empty())
                  left.push_back(End{h.viaHead, h.arg, h.layout});
              for (const Hit &h : layoutsOf(caller, fx.otherFormal, fx.otherPath))
                if (h.who == r.who && !h.layout.empty())
                  right.push_back(End{h.viaHead, h.arg, h.layout});
              if (right.empty() && fx.otherPath == 0 && caller == r.who && fx.otherFormal >= 0) {
                std::string layout = "arg" + std::to_string(fx.otherFormal);
                for (const End &L : left)
                  right.push_back(End{L.via, fx.otherFormal, layout});
              }
              if (left.empty() && fx.path == 0 && caller == r.who && fx.formal >= 0) {
                std::string layout = "arg" + std::to_string(fx.formal);
                for (const End &R : right)
                  left.push_back(End{R.via, fx.formal, layout});
              }
              auto viaEq = [&](int va, int vb) {
                while (va >= 0 && vb >= 0) {
                  if ((size_t)va >= viaNodes.size() || (size_t)vb >= viaNodes.size())
                    return false;
                  if (viaNodes[(size_t)va].first != viaNodes[(size_t)vb].first)
                    return false;
                  va = viaNodes[(size_t)va].second;
                  vb = viaNodes[(size_t)vb].second;
                }
                return va < 0 && vb < 0;
              };
              for (const End &L : left)
                for (const End &R : right) {
                  if (!viaEq(L.via, R.via))
                    continue;
                  unsigned pred = pred0;
                  int a1 = L.arg, a2 = R.arg;
                  std::string p1 = L.layout, p2 = R.layout;
                  if (std::tie(a2, p2) < std::tie(a1, p1)) {
                    std::swap(a1, a2);
                    std::swap(p1, p2);
                    pred = swapPred(pred);
                  }
                  RelK key{a1, p1, a2, p2, fx.len};
                  auto it = info.rel.find(key);
                  if (it == info.rel.end())
                    info.rel.emplace(key, pred);
                  else if (it->second != pred)
                    info.dead = true;
                }
            }
          }
          infos.push_back(std::move(info));
        }
        std::vector<Info *> live;
        for (Info &info : infos)
          if (!info.dead)
            live.push_back(&info);
        if (live.empty()) {
          bad = true;
          break;
        }
        // One call site is a sufficient witness. The site reached under the
        // zero default carries the flips; a site with fewer conditions is a
        // different call. Several sites at that size are intersected.
        size_t mostCells = 0;
        for (Info *info : live) {
          size_t n = 0;
          for (const auto &ck : info->cells)
            if (!ck.second.top)
              ++n;
          if (n > mostCells)
            mostCells = n;
        }
        std::vector<Info *> chosen;
        for (Info *info : live) {
          size_t n = 0;
          for (const auto &ck : info->cells)
            if (!ck.second.top)
              ++n;
          if (n == mostCells)
            chosen.push_back(info);
        }
        live.swap(chosen);
        std::set<CK> keys;
        for (Info *info : live)
          for (const auto &ck : info->cells)
            if (!ck.second.top && ck.second.finite)
              keys.insert(ck.first);
        std::map<CK, Ints> edgeAllow;
        std::map<CK, int64_t> edgeLen;
        for (const CK &key : keys) {
          bool every = true;
          Ints uni;
          int64_t len = 0;
          for (Info *info : live) {
            auto it = info->cells.find(key);
            if (it == info->cells.end() || it->second.top || !it->second.finite) {
              every = false;
              break;
            }
            len = it->second.len;
            uni.insert(it->second.allow.begin(), it->second.allow.end());
          }
          if (!every || uni.empty())
            continue;
          edgeAllow[key] = std::move(uni);
          edgeLen[key] = len;
        }
        auto bandHolds = [](const Band &b, llvm::APInt v) {
          unsigned w = b.mask.getBitWidth();
          if (w == 0)
            return true;
          if (v.getBitWidth() != w)
            v = v.zextOrTrunc(w);
          llvm::APInt c = b.val.getBitWidth() == w ? b.val : b.val.zextOrTrunc(w);
          llvm::APInt a = v & b.mask;
          using P = llvm::ICmpInst::Predicate;
          if (b.pred == P::ICMP_EQ)
            return a.eq(c);
          if (b.pred == P::ICMP_NE)
            return a.ne(c);
          return true;
        };
        auto sameBand = [](const Band &a, const Band &b) {
          return a.pred == b.pred && a.len == b.len && a.mask.getBitWidth() == b.mask.getBitWidth() && a.mask == b.mask &&
                 a.val.getBitWidth() == b.val.getBitWidth() && a.val == b.val;
        };
        std::set<CK> bkeys;
        for (Info *info : live)
          for (const auto &bk : info->bands)
            bkeys.insert(bk.first);
        for (const CK &key : bkeys) {
          bool every = true;
          std::vector<Band> common;
          bool firstB = true;
          for (Info *info : live) {
            auto it = info->bands.find(key);
            if (it == info->bands.end() || it->second.empty()) {
              every = false;
              break;
            }
            if (firstB) {
              common = it->second;
              firstB = false;
              continue;
            }
            std::vector<Band> nxt;
            for (const Band &a : common)
              for (const Band &b : it->second)
                if (sameBand(a, b))
                  nxt.push_back(a);
            if (nxt.empty()) {
              every = false;
              break;
            }
            common.swap(nxt);
          }
          if (!every)
            continue;
          auto ait = edgeAllow.find(key);
          if (ait != edgeAllow.end()) {
            Ints keep;
            for (const llvm::APInt &v : ait->second)
              if ([&] {
                    for (const Band &b : common)
                      if (!bandHolds(b, v))
                        return false;
                    return true;
                  }())
                keep.insert(v);
            if (keep.empty()) {
              bad = true;
              break;
            }
            ait->second.swap(keep);
          }
          auto &dst = edgeBands[key];
          for (const Band &b : common) {
            bool seen = false;
            for (const Band &a : dst)
              if (sameBand(a, b))
                seen = true;
            if (!seen)
              dst.push_back(b);
          }
        }
        if (bad)
          break;
        auto sameRng = [](const std::vector<std::pair<unsigned, llvm::APInt>> &a,
                          const std::vector<std::pair<unsigned, llvm::APInt>> &b) {
          if (a.size() != b.size())
            return false;
          for (size_t ri = 0; ri < a.size(); ++ri) {
            if (a[ri].first != b[ri].first || a[ri].second.getBitWidth() != b[ri].second.getBitWidth())
              return false;
            if (!a[ri].second.eq(b[ri].second))
              return false;
          }
          return true;
        };
        std::set<CK> rkeys;
        for (Info *info : live)
          for (const auto &ck : info->cells)
            if (!ck.second.top && !ck.second.finite && !ck.second.ranges.empty())
              rkeys.insert(ck.first);
        for (const CK &key : rkeys) {
          if (edgeAllow.count(key))
            continue;
          bool every = true;
          std::vector<std::pair<unsigned, llvm::APInt>> common;
          bool have = false;
          int64_t len = 0;
          for (Info *info : live) {
            auto it = info->cells.find(key);
            if (it == info->cells.end() || it->second.top || it->second.finite || it->second.ranges.empty()) {
              every = false;
              break;
            }
            if (!have) {
              common = it->second.ranges;
              len = it->second.len;
              have = true;
            } else if (len != it->second.len || !sameRng(common, it->second.ranges)) {
              every = false;
              break;
            }
          }
          if (!every || !have)
            continue;
          auto it = ranges.find(key);
          if (it == ranges.end()) {
            ranges.emplace(key, std::move(common));
            rlen[key] = len;
          } else if (rlen[key] != len || !sameRng(it->second, common)) {
            bad = true;
            break;
          }
        }
        if (bad)
          break;
        std::set<CK> fkeys;
        for (Info *info : live)
          for (const auto &ck : info->cells)
            if (!ck.second.top && !ck.second.finite && !ck.second.forbid.empty())
              fkeys.insert(ck.first);
        for (const CK &key : fkeys) {
          if (edgeAllow.count(key))
            continue;
          bool every = true;
          Ints common;
          bool have = false;
          int64_t len = 0;
          for (Info *info : live) {
            auto it = info->cells.find(key);
            if (it == info->cells.end() || it->second.top || it->second.finite || it->second.forbid.empty()) {
              every = false;
              break;
            }
            if (!have) {
              common = it->second.forbid;
              len = it->second.len;
              have = true;
            } else if (len != it->second.len || common != it->second.forbid) {
              every = false;
              break;
            }
          }
          if (!every || !have)
            continue;
          auto it = forbids.find(key);
          if (it == forbids.end()) {
            forbids.emplace(key, std::move(common));
            flen[key] = len;
          } else if (flen[key] != len || it->second != common) {
            bad = true;
            break;
          }
        }
        if (bad)
          break;
        for (const auto &ek : edgeAllow) {
          auto it = allow.find(ek.first);
          if (it == allow.end()) {
            allow.emplace(ek.first, ek.second);
            alen[ek.first] = edgeLen[ek.first];
          } else {
            Ints both;
            for (const llvm::APInt &v : it->second)
              if (ek.second.count(v))
                both.insert(v);
            if (both.empty() || alen[ek.first] != edgeLen[ek.first]) {
              bad = true;
              break;
            }
            it->second.swap(both);
          }
        }
        std::set<RelK> relKeys;
        for (Info *info : live)
          for (const auto &rk : info->rel)
            relKeys.insert(rk.first);
        for (const RelK &key : relKeys) {
          bool every = true;
          unsigned pred = 0;
          bool have = false;
          for (Info *info : live) {
            auto it = info->rel.find(key);
            if (it == info->rel.end()) {
              every = false;
              break;
            }
            if (!have) {
              pred = it->second;
              have = true;
            } else if (it->second != pred) {
              every = false;
              break;
            }
          }
          if (!every)
            continue;
          auto it = rels.find(key);
          if (it == rels.end())
            rels.emplace(key, pred);
          else if (it->second == notPred(pred) || it->second != pred) {
            bad = true;
            break;
          }
        }
      }
      if (!bad && !r.seq.empty()) {
        llvm::Function *sinkFn = r.seq.back();
        auto sit = sum.find(sinkFn);
        if (sit != sum.end())
          takeReads(sinkFn, reachOf(sit->second.sinkAt));
      }
      if (!bad) {
        // The installer of this sequence is a function that stores one of its
        // callees. A function that stores a different callee into one of those
        // slots is another initialization. Its stores are not this witness.
        std::unordered_set<llvm::Function *> seqFn(r.seq.begin(), r.seq.end());
        std::unordered_map<llvm::Function *, std::unordered_set<int>> slotsOfFn;
        for (const auto &kv : fnAt)
          for (llvm::Function *G : kv.second)
            slotsOfFn[G].insert(kv.first);
        std::unordered_set<llvm::Function *> installers;
        for (const auto &kv : storesOf)
          for (llvm::Function *H : kv.second) {
            llvm::Function *B = bodyOf(H);
            if (seqFn.count(H) || (B && seqFn.count(B)))
              installers.insert(kv.first);
          }
        std::unordered_set<int> instSlots;
        for (llvm::Function *I : installers) {
          auto st = storesOf.find(I);
          if (st == storesOf.end())
            continue;
          for (llvm::Function *H : st->second) {
            auto sl = slotsOfFn.find(H);
            if (sl == slotsOfFn.end())
              continue;
            instSlots.insert(sl->second.begin(), sl->second.end());
          }
        }
        std::unordered_set<llvm::Function *> altInst;
        for (const auto &kv : storesOf) {
          if (installers.count(kv.first) || !globalFns.count(kv.first))
            continue;
          for (llvm::Function *H : kv.second) {
            auto sl = slotsOfFn.find(H);
            if (sl == slotsOfFn.end())
              continue;
            for (int s : sl->second)
              if (instSlots.count(s))
                altInst.insert(kv.first);
          }
        }
        auto otherInit = [&](llvm::Function *G) {
          if (!G)
            return false;
          bool seen = false;
          for (const auto &kv : storesOf) {
            if (!kv.second.count(G))
              continue;
            seen = true;
            if (!altInst.count(kv.first))
              return false;
          }
          return seen;
        };
        struct Pick {
          std::string name;
          bool inst = false;
          bool called = false;
        };
        std::map<std::pair<int, std::string>, Pick> chosen;
        for (llvm::Function *fn : r.seq) {
          auto sit = sum.find(fn);
          if (sit == sum.end())
            continue;
          for (const FnSum::ZeroFn &z : sit->second.zeroFns) {
            if (otherInit(z.fn))
              continue;
            bool inst = false;
            for (const auto &kv : storesOf)
              if (installers.count(kv.first) && kv.second.count(z.fn))
                inst = true;
            // The value in the cell is the callee this sequence calls.
            bool called = false;
            for (size_t i = 0; i + 1 < r.seq.size(); ++i)
              if (r.seq[i] == fn && r.seq[i + 1] == z.fn)
                called = true;
            for (const Hit &h : layoutsOf(fn, z.formal, z.path)) {
              if (h.who != r.who || h.layout.empty())
                continue;
              std::pair<int, std::string> k{h.arg, h.layout};
              auto it = chosen.find(k);
              if (it == chosen.end() || (called && !it->second.called) ||
                  (called == it->second.called && inst && !it->second.inst) ||
                  (called == it->second.called && inst == it->second.inst && z.name < it->second.name))
                chosen[k] = Pick{z.name, inst, called};
            }
          }
        }
        for (const auto &ck : chosen)
          if (!fnWant.count(ck.first) && !fnBad.count(ck.first))
            fnWant.emplace(ck.first, ck.second.name);
        for (llvm::Function *I : installers) {
          auto sit = sum.find(I);
          if (sit == sum.end())
            continue;
          for (const FnSum::DataStore &d : sit->second.data) {
            if (d.path <= 0)
              continue;
            std::string path = pathString(d.formal, d.path);
            if (path.find("any") != std::string::npos)
              continue;
            PinV pv;
            pv.ptr = d.valFormal >= 0;
            pv.len = d.len;
            if (!pv.ptr) {
              llvm::SmallVector<char, 32> buf;
              d.cnst.toString(buf, 10, false);
              pv.val.assign(buf.begin(), buf.end());
            }
            auto it = rawPin.find(path);
            if (it == rawPin.end())
              rawPin.emplace(path, std::move(pv));
            else if (it->second.ptr != pv.ptr || it->second.val != pv.val || it->second.len != pv.len)
              it->second.clash = true;
          }
        }
        seqWriters.insert(installers.begin(), installers.end());
        for (llvm::Function *fn : r.seq)
          if (fn)
            seqWriters.insert(fn);
      }
      {
        std::unordered_set<llvm::Function *> extra;
        auto addFn = [&](llvm::Function *F) {
          if (!F)
            return;
          F = bodyOf(F);
          if (!F || F->isDeclaration())
            return;
          extra.insert(F);
        };
        for (llvm::Function *F : r.seq)
          addFn(F);
        for (const auto &fk : fnWant) {
          auto it = byName.find(fk.second);
          if (it != byName.end())
            addFn(it->second);
        }
        std::vector<llvm::Function *> layer(extra.begin(), extra.end());
        for (llvm::Function *F : layer) {
          auto cit = callees.find(F);
          if (cit == callees.end())
            continue;
          for (llvm::Function *C : cit->second)
            addFn(C);
        }
        for (llvm::Function *F : extra) {
          auto sit = sum.find(F);
          if (sit == sum.end())
            continue;
          for (const FnSum::Rd &rd : sit->second.reads) {
            if (rd.path <= 0 || rd.key <= 0)
              continue;
            if (!seenDemand.insert({F, rd.formal, rd.path}).second)
              continue;
            demand.push_back(Demand{F, &rd});
          }
        }
      }
      if (bad)
        continue;
      kept = cand.line;
      exportFn = r.seq.empty() ? nullptr : r.seq[0];
      keptFns = r.seq;
      witnessSeq.clear();
      witnessName.clear();
      for (llvm::Function *fn : r.seq)
        if (fn) {
          witnessSeq.push_back(showFn(fn));
          witnessName.insert(showFn(fn));
          if (fn->hasName())
            witnessName.insert(fn->getName().str());
        }
      witnessRoot.clear();
      witnessSpines.clear();
      neuType.clear();
      for (const auto &pk : rawPin)
        markNeu(pk.first, neuType);
      {
        llvm::Function *head = r.seq.empty() ? nullptr : r.seq[0];
        llvm::Function *next = r.seq.size() > 1 ? r.seq[1] : nullptr;
        auto hit = head ? sum.find(head) : sum.end();
        std::map<int, bool> fromEdge;
        auto note = [&](int formal, int path, bool edge) {
          if (formal < 0 || path <= 0)
            return;
          std::string ty = firstType(pathString(formal, path));
          if (ty.empty() || ty == "ext")
            return;
          auto it = witnessRoot.find(formal);
          if (it == witnessRoot.end() || (edge && !fromEdge[formal])) {
            witnessRoot[formal] = ty;
            fromEdge[formal] = edge;
          }
        };
        for (llvm::Function *fn : r.seq) {
          auto sit = sum.find(fn);
          if (sit == sum.end())
            continue;
          auto addSpine = [&](int formal, int path) {
            if (formal < 0 || path <= 0)
              return;
            std::string ps = pathString(formal, path);
            markNeu(ps, neuType);
            auto t = typesOf(ps);
            if (t.size() > 1)
              witnessSpines.push_back(std::move(t));
          };
          for (const Site &s : sit->second.sites) {
            for (const Fix &fx : s.fixes)
              addSpine(fx.formal, fx.path);
            for (const auto &ap : s.calleeAt)
              addSpine(ap.first, ap.second);
            for (const ArgAt &a : s.args)
              for (const LiftFrom &L : a.lift)
                if (L.kind == 0)
                  addSpine(L.formal, L.path);
          }
        }
        if (hit != sum.end()) {
          for (const Site &s : hit->second.sites) {
            bool edge = false;
            if (next && s.callee == next)
              edge = true;
            if (next && !s.callee) {
              for (int slot : s.calleeKeys) {
                auto fit = fnAt.find(slot);
                if (fit == fnAt.end())
                  continue;
                for (llvm::Function *G : fit->second)
                  if (G == next || bodyOf(G) == next)
                    edge = true;
              }
            }
            for (const Fix &fx : s.fixes)
              note(fx.formal, fx.path, edge);
            for (const auto &ap : s.calleeAt)
              note(ap.first, ap.second, edge);
            for (const ArgAt &a : s.args)
              for (const LiftFrom &L : a.lift)
                if (L.kind == 0)
                  note(L.formal, L.path, edge);
          }
        }
      }
      {
        std::unordered_map<std::string, std::vector<std::string>> embedAt0;
        const llvm::DataLayout &DL = down.getDataLayout();
        for (const auto &kv : typeById) {
          const llvm::StructType *H = kv.second;
          if (!H || H->isOpaque() || H->getNumElements() == 0 || kv.first <= 0 ||
              kv.first > (int)typeName.size())
            continue;
          const llvm::StructLayout *SL = DL.getStructLayout(const_cast<llvm::StructType *>(H));
          if (SL->getElementOffset(0) != 0)
            continue;
          auto *S = llvm::dyn_cast<llvm::StructType>(H->getElementType(0));
          if (!S || !S->hasName())
            continue;
          int id = internType(S);
          if (id <= 0 || id > (int)typeName.size())
            continue;
          const std::string &inner = typeName[id - 1];
          const std::string &holder = typeName[kv.first - 1];
          auto &hs = embedAt0[inner];
          if (std::find(hs.begin(), hs.end(), holder) == hs.end())
            hs.push_back(holder);
        }
        std::unordered_map<std::string, std::string> reachPrefix;
        auto noteReach = [&](const std::string &layout) {
          std::string ty0 = firstType(layout);
          if (ty0.empty())
            return;
          bool rooted = false;
          for (const auto &wr : witnessRoot)
            if (wr.second == ty0)
              rooted = true;
          if (!rooted)
            return;
          for (size_t i = 0; i < layout.size();) {
            size_t s = layout.find("struct.", i);
            if (s == std::string::npos)
              break;
            size_t end = layout.find_first_of("+^*", s);
            if (end == std::string::npos || end == s)
              break;
            std::string ty = layout.substr(s, end - s);
            std::string pref = layout.substr(0, end + 1);
            auto it = reachPrefix.find(ty);
            if (it == reachPrefix.end() || (layout[end] == '^' && !it->second.empty() && it->second.back() != '^'))
              reachPrefix[ty] = std::move(pref);
            i = end + 1;
          }
        };
        for (const auto &pk : rawPin)
          noteReach(collapse(pk.first, neuType));
        for (const Cell &c : out)
          for (const std::string &line : c.roots) {
            if (line.compare(0, 5, "pass ") != 0)
              continue;
            size_t i = 5;
            while (i < line.size() && std::isdigit(static_cast<unsigned char>(line[i])))
              ++i;
            if (i >= line.size() || line[i] != ' ')
              continue;
            ++i;
            auto sep = line.find(" :: ", i);
            noteReach(collapse(sep == std::string::npos ? line.substr(i) : line.substr(i, sep - i), neuType));
          }
        anchored = [embedAt0 = std::move(embedAt0), reachPrefix = std::move(reachPrefix), &witnessRoot, &neuType,
                    &collapse, &firstType](const std::string &layout0) {
          std::string layout = collapse(layout0, neuType);
          std::string head = firstType(layout);
          if (head.empty() || witnessRoot.empty())
            return layout;
          bool rooted = false;
          for (const auto &wr : witnessRoot)
            if (wr.second == head)
              rooted = true;
          if (rooted)
            return layout;
          std::string at = head;
          std::set<std::string> seenTy;
          std::string pref;
          while (seenTy.insert(at).second) {
            auto it = reachPrefix.find(at);
            if (it != reachPrefix.end()) {
              pref = it->second;
              break;
            }
            auto e = embedAt0.find(at);
            if (e == embedAt0.end() || e->second.empty())
              return layout;
            std::string nxt = e->second.front();
            for (const std::string &h : e->second)
              if (reachPrefix.count(h)) {
                nxt = h;
                break;
              }
            at = nxt;
          }
          if (pref.empty())
            return layout;
          auto dot = layout.find('.');
          if (dot == std::string::npos)
            return layout;
          size_t sep = dot + 1 + head.size();
          if (sep >= layout.size() || (layout[sep] != '+' && layout[sep] != '^' && layout[sep] != '*'))
            return layout;
          size_t num = sep + 1;
          size_t end = num;
          if (end < layout.size() && (layout[end] == '+' || layout[end] == '-'))
            ++end;
          size_t d0 = end;
          while (end < layout.size() && std::isdigit(static_cast<unsigned char>(layout[end])))
            ++end;
          if (end == d0)
            return layout;
          return pref + layout.substr(num, end - num) + layout.substr(end);
        };
      }
      auto inWitness = [&](int arg, const std::string &layout0) {
        std::string layout = anchored(layout0);
        auto it = witnessRoot.find(arg);
        if (it == witnessRoot.end())
          return true;
        std::string ty = firstType(layout);
        if (ty.empty())
          return true;
        if (it->second != "ext" && ty == "ext")
          return false;
        if (ty != it->second)
          return false;
        if (embedsNeu(layout, neuType))
          return false;
        if (witnessSpines.empty())
          return true;
        auto got = typesOf(layout);
        if (got.empty())
          return true;
        bool related = false;
        for (const auto &sp : witnessSpines) {
          if (sp.empty() || sp[0] != got[0])
            continue;
          related = true;
          size_t n = std::min(got.size(), sp.size());
          bool same = true;
          for (size_t i = 0; i < n; ++i)
            if (got[i] != sp[i])
              same = false;
          if (same)
            return true;
        }
        return !related;
      };
      for (size_t hop = 0; hop + 1 < r.seq.size(); ++hop) {
        llvm::Function *caller = r.seq[hop];
        llvm::Function *calleeFn = r.seq[hop + 1];
        if (!caller || !calleeFn)
          continue;
        auto sit = sum.find(caller);
        if (sit == sum.end())
          continue;
        bool direct = false;
        for (const Site &s : sit->second.sites) {
          llvm::Function *C = s.callee ? bodyOf(s.callee) : nullptr;
          if (s.callee == calleeFn || C == calleeFn)
            direct = true;
        }
        if (direct)
          continue;
        for (const Site &s : sit->second.sites) {
          if (s.callee)
            continue;
          bool loads = false;
          for (int slot : s.calleeKeys)
            eachAt(slot, [&](llvm::Function *G) {
              if (G == calleeFn || bodyOf(G) == calleeFn)
                loads = true;
            });
          if (!loads)
            continue;
          for (const auto &ap : s.calleeAt)
            for (const Hit &h : layoutsOf(caller, ap.first, ap.second)) {
              if (h.who != r.who || h.layout.empty() || h.layout.find("any") != std::string::npos)
                continue;
              loadAt.insert({h.arg, h.layout});
              fnWant.emplace(std::pair<int, std::string>{h.arg, h.layout}, showFn(calleeFn));
            }
        }
      }
      {
        // One indirect call loads one cell. A path with an unknown offset names
        // no cell. A vtable call loads the slot, so a byte of an outer object
        // is a different address. A path whose offsets are only the tail of a
        // longer path has dropped the parent object the export argument reaches.
        auto offsetsOf = [](const std::string &layout) {
          std::string s = layout;
          auto slot = s.rfind(".struct.slot^");
          if (slot != std::string::npos)
            s = s.substr(0, slot);
          std::vector<long long> off;
          for (size_t i = 0; i < s.size(); ++i) {
            char c = s[i];
            if (c != '+' && c != '^' && c != '*')
              continue;
            if (i + 4 <= s.size() && s.compare(i + 1, 3, "any") == 0) {
              off.push_back(LLONG_MIN);
              continue;
            }
            size_t j = i + 1;
            if (j < s.size() && s[j] == '-')
              ++j;
            if (j >= s.size() || s[j] < '0' || s[j] > '9')
              continue;
            off.push_back(std::stoll(s.substr(j)));
          }
          return off;
        };
        std::map<std::string, std::vector<std::pair<int, std::string>>> byFn;
        std::set<std::pair<int, std::string>> dropFn;
        std::set<std::string> loadedName;
        for (const auto &fk : fnWant) {
          if (fk.first.second.find("any") != std::string::npos) {
            dropFn.insert(fk.first);
            continue;
          }
          if (loadAt.count(fk.first))
            loadedName.insert(fk.second);
          byFn[fk.second].push_back(fk.first);
        }
        for (const auto &fk : fnWant)
          if (loadedName.count(fk.second) && !loadAt.count(fk.first))
            dropFn.insert(fk.first);
        for (const auto &g : byFn) {
          const auto &paths = g.second;
          bool slot = false;
          for (const auto &p : paths)
            if (p.second.find(".struct.slot^") != std::string::npos)
              slot = true;
          std::vector<std::vector<long long>> offs;
          offs.reserve(paths.size());
          for (const auto &p : paths)
            offs.push_back(offsetsOf(p.second));
          for (size_t i = 0; i < paths.size(); ++i) {
            bool isSlot = paths[i].second.find(".struct.slot^") != std::string::npos;
            if (slot && !isSlot) {
              dropFn.insert(paths[i]);
              continue;
            }
            if (offs[i].empty() || offs[i].back() == LLONG_MIN) {
              dropFn.insert(paths[i]);
              continue;
            }
            for (size_t j = 0; j < paths.size(); ++j) {
              if (i == j || offs[j].size() <= offs[i].size())
                continue;
              if (slot && paths[j].second.find(".struct.slot^") == std::string::npos)
                continue;
              bool suf = true;
              size_t b = offs[j].size() - offs[i].size();
              for (size_t k = 0; k < offs[i].size(); ++k)
                if (offs[j][b + k] != offs[i][k])
                  suf = false;
              if (suf)
                dropFn.insert(paths[i]);
            }
          }
        }
        for (const auto &p : dropFn)
          fnWant.erase(p);
      }
      fns.clear();
      for (const auto &fk : fnWant) {
        std::string check = fk.first.second;
        auto slot = check.rfind(".struct.slot^");
        if (slot != std::string::npos)
          check = check.substr(0, slot);
        if (fnBad.count(fk.first))
          continue;
        auto rootIt = witnessRoot.find(fk.first.first);
        std::string rootTy = firstType(anchored(check));
        if (rootIt != witnessRoot.end()) {
          if (rootTy.empty() || rootTy != rootIt->second)
            continue;
        } else if (!inWitness(fk.first.first, check)) {
          continue;
        }
        FnBind b;
        b.func = showFn(r.who);
        b.arg = fk.first.first;
        b.path = anchored(fk.first.second);
        b.name = fk.second;
        fns.push_back(std::move(b));
      }
      for (const auto &pk : rawPin) {
        if (pk.second.clash)
          continue;
        int arg = -1;
        for (const auto &wr : witnessRoot)
          if (firstType(pk.first) == wr.second)
            arg = wr.first;
        if (arg < 0 || !inWitness(arg, pk.first))
          continue;
        if (pk.second.ptr) {
          FnBind b;
          b.func = showFn(r.who);
          b.arg = arg;
          b.path = anchored(pk.first);
          b.self = true;
          fns.push_back(std::move(b));
          continue;
        }
        if (pk.second.val.empty() || pk.second.len <= 0)
          continue;
        GuardFix g;
        g.func = showFn(r.who);
        g.arg = arg;
        g.path = anchored(pk.first);
        g.len = pk.second.len;
        g.pred = 32;
        g.vals.push_back(pk.second.val);
        guards.push_back(std::move(g));
      }
      for (const auto &bk : edgeBands) {
        if (!inWitness(std::get<1>(bk.first), std::get<2>(bk.first)))
          continue;
        for (const Band &b : bk.second) {
          if (b.len <= 0 || b.mask.getBitWidth() == 0)
            continue;
          GuardFix g;
          g.func = std::get<0>(bk.first);
          g.arg = std::get<1>(bk.first);
          g.path = anchored(std::get<2>(bk.first));
          g.len = b.len;
          g.pred = b.pred;
          llvm::SmallVector<char, 32> buf;
          b.mask.toString(buf, 10, false);
          g.mask.assign(buf.begin(), buf.end());
          buf.clear();
          b.val.toString(buf, 10, false);
          g.vals.emplace_back(buf.begin(), buf.end());
          guards.push_back(std::move(g));
        }
      }
      for (const auto &ak : allow) {
        if (!inWitness(std::get<1>(ak.first), std::get<2>(ak.first)))
          continue;
        GuardFix g;
        g.func = std::get<0>(ak.first);
        g.arg = std::get<1>(ak.first);
        g.path = anchored(std::get<2>(ak.first));
        g.len = alen[ak.first];
        g.pred = llvm::ICmpInst::ICMP_EQ;
        for (const llvm::APInt &v : ak.second) {
          llvm::SmallVector<char, 32> buf;
          v.toString(buf, 10, false);
          g.vals.emplace_back(buf.begin(), buf.end());
        }
        guards.push_back(std::move(g));
      }
      {
        std::unordered_set<llvm::Function *> seenFn;
        std::vector<llvm::Function *> fq = r.seq;
        for (const auto &fk : fnWant) {
          auto it = byName.find(fk.second);
          if (it != byName.end())
            fq.push_back(it->second);
        }
        std::unordered_map<llvm::Function *, bool> contraMemo;
        while (!fq.empty()) {
          llvm::Function *G0 = fq.back();
          fq.pop_back();
          if (!G0)
            continue;
          llvm::Function *G = bodyOf(G0);
          if (!G)
            G = G0;
          if (G->isDeclaration() || G->empty() || !seenFn.insert(G).second)
            continue;
          auto cit = callees.find(G);
          if (cit != callees.end())
            for (llvm::Function *C : cit->second)
              fq.push_back(C);
          auto sit = sum.find(G);
          if (sit == sum.end())
            continue;
          auto contradicts = [&](llvm::Function *start) {
            if (!start)
              return false;
            llvm::Function *key = bodyOf(start);
            if (!key)
              key = start;
            auto mit = contraMemo.find(key);
            if (mit != contraMemo.end())
              return mit->second;
            std::unordered_set<llvm::Function *> seen;
            std::vector<llvm::Function *> q{start};
            while (!q.empty()) {
              llvm::Function *F = q.back();
              q.pop_back();
              if (!F)
                continue;
              llvm::Function *B = bodyOf(F);
              if (B)
                F = B;
              if (!seen.insert(F).second)
                continue;
              auto cit2 = callees.find(F);
              if (cit2 != callees.end())
                for (llvm::Function *C : cit2->second)
                  q.push_back(C);
              auto fs = sum.find(F);
              if (fs == sum.end())
                continue;
              for (const FnSum::DataStore &ds : fs->second.data) {
                if (!ds.hasConst || ds.formal < 0 || ds.path <= 0)
                  continue;
                for (const Hit &h : layoutsOf(F, ds.formal, ds.path)) {
                  if (h.who != r.who || h.layout.empty())
                    continue;
                  std::string layout = anchored(h.layout);
                  for (const auto &ak : allow) {
                    if (std::get<1>(ak.first) != h.arg || anchored(std::get<2>(ak.first)) != layout)
                      continue;
                    bool same = false;
                    for (const llvm::APInt &v : ak.second)
                      if (v.getBitWidth() == ds.cnst.getBitWidth() && v == ds.cnst)
                        same = true;
                    if (!same && !ak.second.empty()) {
                      contraMemo[key] = true;
                      return true;
                    }
                  }
                }
              }
            }
            contraMemo[key] = false;
            return false;
          };
          std::unordered_set<const llvm::BasicBlock *> clobber;
          for (const Site &site : sit->second.sites) {
            if (!site.at || !site.callee)
              continue;
            if (contradicts(site.callee))
              clobber.insert(site.at);
          }
          if (clobber.empty())
            continue;
          std::unordered_set<const llvm::BasicBlock *> reach;
          std::vector<const llvm::BasicBlock *> stack{&G->getEntryBlock()};
          while (!stack.empty()) {
            const llvm::BasicBlock *B = stack.back();
            stack.pop_back();
            if (!B || clobber.count(B) || !reach.insert(B).second)
              continue;
            const llvm::Instruction *term = B->getTerminator();
            if (!term)
              continue;
            for (unsigned i = 0; i < term->getNumSuccessors(); ++i)
              stack.push_back(term->getSuccessor(i));
          }
          const RetPred *best = nullptr;
          for (const RetPred &rp : sit->second.retPreds) {
            if (!rp.at || !reach.count(rp.at) || rp.cond.empty())
              continue;
            if (!best || rp.cond.size() > best->cond.size())
              best = &rp;
          }
          if (!best)
            continue;
          for (const Fix &fx : best->cond) {
            if (fx.formal < 0 || fx.path <= 0 || fx.len <= 0 || fx.pred == 0 || fx.otherFormal >= 0 || fx.vals.empty())
              continue;
            for (const Hit &h : layoutsOf(G, fx.formal, fx.path)) {
              if (h.who != r.who || h.layout.empty())
                continue;
              std::string layout = anchored(h.layout);
              if (layout.empty() || !inWitness(h.arg, layout))
                continue;
              GuardFix g;
              g.func = showFn(r.who);
              g.arg = h.arg;
              g.path = std::move(layout);
              g.len = fx.len;
              g.pred = fx.pred;
              for (const llvm::APInt &v : fx.vals) {
                llvm::SmallVector<char, 32> buf;
                v.toString(buf, 10, false);
                g.vals.emplace_back(buf.begin(), buf.end());
              }
              if (!g.vals.empty())
                guards.push_back(std::move(g));
            }
          }
        }
      }
      for (const auto &ak : ranges) {
        if (!inWitness(std::get<1>(ak.first), std::get<2>(ak.first)))
          continue;
        for (const auto &rg : ak.second) {
          GuardFix g;
          g.func = std::get<0>(ak.first);
          g.arg = std::get<1>(ak.first);
          g.path = anchored(std::get<2>(ak.first));
          g.len = rlen[ak.first];
          g.pred = rg.first;
          llvm::SmallVector<char, 32> buf;
          rg.second.toString(buf, 10, false);
          g.vals.emplace_back(buf.begin(), buf.end());
          guards.push_back(std::move(g));
        }
      }
      for (const auto &ak : forbids) {
        if (!inWitness(std::get<1>(ak.first), std::get<2>(ak.first)))
          continue;
        for (const llvm::APInt &v : ak.second) {
          GuardFix g;
          g.func = std::get<0>(ak.first);
          g.arg = std::get<1>(ak.first);
          g.path = anchored(std::get<2>(ak.first));
          g.len = flen[ak.first];
          g.pred = llvm::ICmpInst::ICMP_NE;
          llvm::SmallVector<char, 32> buf;
          v.toString(buf, 10, false);
          g.vals.emplace_back(buf.begin(), buf.end());
          guards.push_back(std::move(g));
        }
      }
      for (const auto &rk : rels) {
        if (!inWitness(std::get<0>(rk.first), std::get<1>(rk.first)))
          continue;
        if (!inWitness(std::get<2>(rk.first), std::get<3>(rk.first)))
          continue;
        GuardFix g;
        g.func = showFn(r.who);
        g.arg = std::get<0>(rk.first);
        g.path = anchored(std::get<1>(rk.first));
        g.otherArg = std::get<2>(rk.first);
        g.otherPath = anchored(std::get<3>(rk.first));
        g.len = std::get<4>(rk.first);
        g.pred = rk.second;
        guards.push_back(std::move(g));
      }
      {
        std::unordered_map<int, std::vector<std::pair<llvm::Function *, const FnSum::DataStore *>>> dataAt;
        for (auto &skv : sum)
          for (const FnSum::DataStore &ds : skv.second.data)
            if (ds.hasConst && ds.key > 0)
              dataAt[ds.key].push_back({skv.first, &ds});
        std::set<std::pair<int, std::string>> boundFn;
        for (const FnBind &b : fns)
          if (!b.path.empty())
            boundFn.insert({b.arg, b.path});
        std::set<std::string> seenObj;
        std::string seq;
        for (size_t k = 0; k < r.seq.size(); ++k) {
          if (k != 0)
            seq += " => ";
          seq += showFn(r.seq[k]);
        }
        for (const Demand &d : demand) {
          const FnSum::Rd *rd = d.rd;
          if (!d.fn || !rd)
            continue;
          std::string name;
          bool fnClash = false;
          int fnWrites = 0;
          int allWrites = 0;
          std::unordered_set<llvm::Function *> writers;
          auto wit = writesAt.find(rd->key);
          if (wit != writesAt.end()) {
            for (const auto &wr : wit->second) {
              if (!wr.second)
                continue;
              ++allWrites;
              writers.insert(wr.first);
              if (wr.second->fn.empty())
                continue;
              ++fnWrites;
              if (name.empty())
                name = wr.second->fn;
              else if (name != wr.second->fn)
                fnClash = true;
            }
          }
          if (fnClash || fnWrites == 0 || fnWrites != allWrites)
            name.clear();
          const llvm::APInt *cnst = nullptr;
          bool cClash = false;
          std::unordered_set<llvm::Function *> constWriters;
          auto dit = dataAt.find(rd->key);
          if (dit != dataAt.end()) {
            for (const auto &ds : dit->second) {
              if (rd->len <= 0 || (int64_t)(ds.second->cnst.getBitWidth() / 8) != rd->len)
                continue;
              constWriters.insert(ds.first);
              if (!cnst)
                cnst = &ds.second->cnst;
              else if (cnst->getBitWidth() != ds.second->cnst.getBitWidth() || *cnst != ds.second->cnst)
                cClash = true;
            }
          }
          if (cClash || !cnst || constWriters != writers || !name.empty())
            cnst = nullptr;
          for (const Hit &h : layoutsOf(d.fn, rd->formal, rd->path)) {
            if (h.who != r.who)
              continue;
            std::string layout = h.layout.empty() ? pathString(h.arg, h.path) : h.layout;
            layout = anchored(layout);
            if (layout.empty() || !inWitness(h.arg, layout))
              continue;
            if (!name.empty() && boundFn.insert({h.arg, layout}).second) {
              FnBind b;
              b.func = showFn(r.who);
              b.arg = h.arg;
              b.path = layout;
              b.name = name;
              fns.push_back(std::move(b));
            }
            bool pinCnst = cnst != nullptr;
            if (pinCnst) {
              GuardFix g;
              g.func = showFn(r.who);
              g.arg = h.arg;
              g.path = layout;
              g.len = rd->len;
              g.pred = llvm::ICmpInst::ICMP_EQ;
              llvm::SmallVector<char, 32> buf;
              cnst->toString(buf, 10, false);
              g.vals.emplace_back(buf.begin(), buf.end());
              guards.push_back(std::move(g));
            }
            if (name.empty() && !pinCnst && !rd->pointer && rd->len > 0 && layout.find('^') != std::string::npos &&
                seenObj.insert(std::to_string(h.arg) + " " + layout + " " + std::to_string(rd->len)).second) {
              Cell c;
              c.chopArg = -1;
              c.len = rd->len;
              c.func = showFn(r.who);
              c.path = layout;
              c.roots.push_back("pass " + std::to_string(h.arg) + " " + layout + " :: " + showFn(r.who) + " :: " +
                                seq);
              out.push_back(std::move(c));
            }
            if (!rd->pointer || !name.empty())
              continue;
            if (rd->pointee.empty()) {
              std::string mark = layout + ".struct.";
              bool typed = false;
              auto covers = [&](const std::string &path) {
                size_t at = path.find(mark);
                return at != std::string::npos && path.find('^', at + mark.size()) != std::string::npos;
              };
              for (const FnBind &b : fns)
                if (covers(b.path))
                  typed = true;
              for (const GuardFix &g : guards)
                if (!typed && covers(g.path))
                  typed = true;
              for (const Cell &c : out) {
                if (typed)
                  break;
                for (const std::string &line : c.roots)
                  if (covers(line))
                    typed = true;
              }
              if (typed)
                continue;
            }
            std::string suffix;
            int64_t len = 1;
            if (!rd->pointee.empty()) {
              suffix = "." + rd->pointee + "^0";
              len = rd->ptrField ? 1 : std::max<int64_t>(rd->objLen, 1);
            } else if (rd->ptrField) {
              suffix = ".struct.slot^0.struct.slot^0";
            } else {
              suffix = ".struct.slot^0";
            }
            std::string full = layout + suffix;
            if (!seenObj.insert(std::to_string(h.arg) + " " + full).second)
              continue;
            PtrNeed need;
            need.arg = h.arg;
            need.path = full;
            need.len = len;
            need.func = showFn(r.who);
            need.root = "pass " + std::to_string(h.arg) + " " + full + " :: " + need.func + " :: " + seq;
            ptrNeed.push_back(std::move(need));
          }
        }
      }
      {
        std::string seq;
        for (size_t k = 0; k < r.seq.size(); ++k) {
          if (k != 0)
            seq += " => ";
          seq += showFn(r.seq[k]);
        }
        std::set<std::string> seenPath;
        auto leafOf = [&](llvm::Function *fn, unsigned argNo) {
          struct Info {
            std::string ty;
            int64_t n = 1;
            int ptrs = 0;
            bool ptrField = false;
          } info;
          if (!fn || argNo >= fn->arg_size())
            return info;
          const llvm::DataLayout &DL = fn->getParent()->getDataLayout();
          const llvm::Value *cur = fn->getArg(argNo);
          std::set<const llvm::Value *> seenV;
          while (cur && seenV.insert(cur).second) {
            const llvm::GEPOperator *g = nullptr;
            auto takeGep = [&](const llvm::Value *V) {
              for (const llvm::User *U : V->users())
                if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
                  g = G;
                  return;
                }
              for (const llvm::User *U : V->users()) {
                const auto *C = llvm::dyn_cast<llvm::CastInst>(U);
                if (!C)
                  continue;
                for (const llvm::User *V2 : C->users())
                  if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V2)) {
                    g = G;
                    return;
                  }
              }
            };
            takeGep(cur);
            if (!g) {
              const llvm::LoadInst *spill = nullptr;
              for (const llvm::User *U : cur->users()) {
                const auto *St = llvm::dyn_cast<llvm::StoreInst>(U);
                if (!St || St->getValueOperand() != cur)
                  continue;
                const auto *A = llvm::dyn_cast<llvm::AllocaInst>(St->getPointerOperand());
                if (!A)
                  continue;
                for (const llvm::User *AU : A->users())
                  if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(AU)) {
                    spill = Ld;
                    break;
                  }
                if (spill)
                  break;
              }
              if (!spill)
                break;
              cur = spill;
              continue;
            }
            llvm::Type *elt = g->getSourceElementType();
            if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(elt))
              elt = AT->getElementType();
            if (auto *S = llvm::dyn_cast<llvm::StructType>(elt)) {
              if (S->hasName()) {
                int id = internType(S);
                if (id > 0 && id <= (int)typeName.size())
                  info.ty = typeName[(size_t)id - 1];
              }
              if (!S->isOpaque()) {
                info.n = (int64_t)DL.getTypeAllocSize(S);
                for (unsigned ei = 0; ei < S->getNumElements(); ++ei)
                  if (S->getElementType(ei)->isPointerTy())
                    info.ptrField = true;
              }
              break;
            }
            if (elt->isPointerTy()) {
              ++info.ptrs;
              info.n = (int64_t)DL.getPointerSize(0);
              const llvm::LoadInst *Ld = nullptr;
              for (const llvm::User *U : g->users())
                if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(U)) {
                  Ld = L;
                  break;
                }
              if (!Ld)
                break;
              cur = Ld;
              continue;
            }
            if (elt->isIntegerTy() && elt->getIntegerBitWidth() >= 8)
              info.n = (int64_t)(elt->getIntegerBitWidth() / 8);
            break;
          }
          return info;
        };
        for (size_t ei = 0; ei + 1 < r.seq.size(); ++ei) {
          llvm::Function *caller = r.seq[ei];
          llvm::Function *calleeFn = r.seq[ei + 1];
          std::vector<const Site *> sites2;
          auto takeSites = [&](const std::vector<SiteRef> &refs) {
            for (const SiteRef &sr : refs)
              if (sr.caller == caller && sr.site)
                sites2.push_back(sr.site);
          };
          auto dit = directAt.find(calleeFn);
          if (dit != directAt.end())
            takeSites(dit->second);
          auto vit = viaFn.find(calleeFn);
          if (vit != viaFn.end())
            takeSites(vit->second);
          if (sites2.empty()) {
            llvm::Function *cb = bodyOf(calleeFn);
            auto sit = sum.find(caller);
            if (sit != sum.end())
              for (const Site &site : sit->second.sites)
                if (!site.callee && (typeOk(calleeFn, site.fty) || (cb && cb != calleeFn && typeOk(cb, site.fty))))
                  sites2.push_back(&site);
          }
          for (const Site *site : sites2) {
            const auto *CB = llvm::dyn_cast_or_null<llvm::CallBase>(site->call);
            for (unsigned ai = 0; ai < site->args.size(); ++ai) {
              bool pointer = false;
              if (CB && ai < CB->arg_size())
                pointer = CB->getArgOperand(ai)->getType()->isPointerTy();
              else if (calleeFn && ai < calleeFn->arg_size())
                pointer = calleeFn->getArg(ai)->getType()->isPointerTy();
              if (!pointer)
                continue;
              auto info = leafOf(calleeFn, ai);
              std::string suffix;
              for (int s = 0; s < info.ptrs; ++s)
                suffix += ".struct.slot^0";
              int64_t len = 1;
              if (!info.ty.empty()) {
                suffix += "." + info.ty + "^0";
                len = info.ptrField ? 1 : std::max<int64_t>(info.n, 1);
              } else {
                suffix += ".struct.slot^0";
                if (info.ptrs > 0)
                  len = 1;
                else
                  len = std::max<int64_t>(info.n, 1);
              }
              for (const LiftFrom &lf : site->args[ai].lift) {
                if (lf.kind != 0 || lf.formal < 0 || lf.path <= 0)
                  continue;
                for (const Hit &h : layoutsOf(caller, lf.formal, lf.path)) {
                  std::string layout = h.layout.empty() ? pathString(h.arg, h.path) : h.layout;
                  layout = anchored(layout);
                  if (layout.empty() || !inWitness(h.arg, layout))
                    continue;
                  std::string full = layout + suffix;
                  if (!seenPath.insert(std::to_string(h.arg) + " " + full).second)
                    continue;
                  PtrNeed need;
                  need.arg = h.arg;
                  need.path = full;
                  need.len = len;
                  need.func = showFn(r.who);
                  need.root = "pass " + std::to_string(h.arg) + " " + full + " :: " + need.func + " :: " + seq;
                  ptrNeed.push_back(std::move(need));
                }
              }
            }
          }
        }
      }
      break;
    }
    if (!witnessRoot.empty()) {
      for (Cell &c : out) {
        std::vector<std::string> keep;
        for (const std::string &line : c.roots) {
          if (line.compare(0, 5, "pass ") != 0) {
            keep.push_back(line);
            continue;
          }
          size_t i = 5;
          int arg = 0;
          while (i < line.size() && std::isdigit(static_cast<unsigned char>(line[i]))) {
            arg = arg * 10 + (line[i] - '0');
            ++i;
          }
          if (i >= line.size() || line[i] != ' ') {
            keep.push_back(line);
            continue;
          }
          ++i;
          auto sep = line.find(" :: ", i);
          std::string path = sep == std::string::npos ? line.substr(i) : line.substr(i, sep - i);
          std::string rooted = anchored(path);
          std::string lineUse = line;
          if (rooted != path) {
            lineUse = line.substr(0, i) + rooted + (sep == std::string::npos ? std::string() : line.substr(sep));
            path = std::move(rooted);
          }
          auto it = witnessRoot.find(arg);
          std::string ty = firstType(path);
          if (it != witnessRoot.end() && !ty.empty() && ty != it->second)
            continue;
          if (it != witnessRoot.end() && it->second != "ext" && ty == "ext")
            continue;
          if (embedsNeu(path, neuType))
            continue;
          if (!witnessSpines.empty()) {
            auto got = typesOf(path);
            if (got.size() > 1) {
              bool related = false;
              bool same = false;
              for (const auto &sp : witnessSpines) {
                if (sp.empty() || sp[0] != got[0])
                  continue;
                related = true;
                size_t n = std::min(got.size(), sp.size());
                bool eq = true;
                for (size_t k = 0; k < n; ++k)
                  if (got[k] != sp[k])
                    eq = false;
                if (eq)
                  same = true;
              }
              if (related && !same)
                continue;
            }
          }
          if (!witnessSeq.empty()) {
            auto a = lineUse.find(" :: ");
            auto b = a == std::string::npos ? std::string::npos : lineUse.find(" :: ", a + 4);
            if (b != std::string::npos) {
              std::string seq = lineUse.substr(b + 4);
              std::vector<std::string> parts;
              for (size_t at = 0; at < seq.size();) {
                auto n = seq.find(" => ", at);
                if (n == std::string::npos) {
                  parts.push_back(seq.substr(at));
                  break;
                }
                parts.push_back(seq.substr(at, n - at));
                at = n + 4;
              }
              bool prefix = parts.size() <= witnessSeq.size();
              for (size_t k = 0; prefix && k < parts.size(); ++k)
                if (parts[k] != witnessSeq[k])
                  prefix = false;
              if (!prefix)
                continue;
            }
          }
          keep.push_back(lineUse);
        }
        c.roots.swap(keep);
      }
      out.erase(std::remove_if(out.begin(), out.end(), [](const Cell &c) { return c.roots.empty(); }), out.end());
      for (const FnBind &b : fns) {
        if (b.path.compare(0, 3, "arg") != 0)
          continue;
        int arg = 0;
        size_t i = 3;
        if (i >= b.path.size() || b.path[i] < '0' || b.path[i] > '9')
          continue;
        while (i < b.path.size() && b.path[i] >= '0' && b.path[i] <= '9') {
          arg = arg * 10 + (b.path[i] - '0');
          ++i;
        }
        std::string ty = firstType(b.path);
        if (ty.empty() || ty == "ext")
          continue;
        auto it = witnessRoot.find(arg);
        if (it == witnessRoot.end() || b.path.find(".struct.slot^") != std::string::npos)
          witnessRoot[arg] = std::move(ty);
      }
      if (!witnessName.empty()) {
        out.erase(std::remove_if(out.begin(), out.end(),
                                 [&](const Cell &c) {
                                   if (c.off == Any || c.path.find("any") != std::string::npos)
                                     return true;
                                   if (!witnessName.count(c.func))
                                     return true;
                                   // A cell is a constant field of an argument the kept
                                   // sequence indexes. Another root type is a different object.
                                   int arg = -1;
                                   if (c.path.compare(0, 3, "arg") == 0) {
                                     size_t i = 3;
                                     int v = 0;
                                     bool dig = false;
                                     while (i < c.path.size() && c.path[i] >= '0' && c.path[i] <= '9') {
                                       dig = true;
                                       v = v * 10 + (c.path[i] - '0');
                                       ++i;
                                     }
                                     if (dig)
                                       arg = v;
                                   }
                                   auto rt = witnessRoot.find(arg);
                                   if (rt == witnessRoot.end())
                                     return true;
                                   std::string ty = firstType(c.path);
                                   return !ty.empty() && ty != rt->second;
                                 }),
                  out.end());
      }
    }
    {
      auto argIndex = [](const std::string &path) {
        if (path.compare(0, 3, "arg") != 0)
          return -1;
        size_t i = 3;
        if (i >= path.size() || path[i] < '0' || path[i] > '9')
          return -1;
        int arg = 0;
        while (i < path.size() && path[i] >= '0' && path[i] <= '9') {
          arg = arg * 10 + (path[i] - '0');
          ++i;
        }
        return arg;
      };
      auto sretArg = [&](int arg) {
        return exportFn && arg >= 0 && arg < (int)exportFn->arg_size() &&
               exportFn->hasParamAttribute((unsigned)arg, llvm::Attribute::StructRet);
      };
      out.erase(std::remove_if(out.begin(), out.end(),
                               [&](const Cell &c) { return sretArg(argIndex(c.path)); }),
                out.end());
      fns.erase(std::remove_if(fns.begin(), fns.end(),
                               [&](const FnBind &b) { return sretArg(argIndex(b.path)); }),
                fns.end());
      std::map<int, std::string> root = indexedArgTypes(exportFn);
      for (const FnBind &b : fns) {
        if (b.path.compare(0, 3, "arg") != 0)
          continue;
        size_t i = 3;
        if (i >= b.path.size() || b.path[i] < '0' || b.path[i] > '9')
          continue;
        int arg = 0;
        while (i < b.path.size() && b.path[i] >= '0' && b.path[i] <= '9') {
          arg = arg * 10 + (b.path[i] - '0');
          ++i;
        }
        std::string ty = firstType(b.path);
        if (ty.empty() || ty == "ext")
          continue;
        if (!root.count(arg))
          root[arg] = std::move(ty);
      }
      if (!root.empty()) {
        fns.erase(std::remove_if(fns.begin(), fns.end(),
                                 [&](const FnBind &b) {
                                   int arg = argIndex(b.path);
                                   auto it = root.find(arg);
                                   if (it == root.end())
                                     return false;
                                   std::string ty = firstType(b.path);
                                   return !ty.empty() && ty != "ext" && ty != it->second;
                                 }),
                  fns.end());
      }
    for (const PtrNeed &n : ptrNeed) {
      if (n.len <= 0 || n.path.empty() || n.root.empty())
        continue;
      Cell c;
      c.chopArg = -1;
      c.off = 0;
      c.len = n.len;
      c.func = n.func;
      c.path = n.path;
      c.roots.push_back(n.root);
      out.push_back(std::move(c));
    }
      if (!root.empty()) {
        out.erase(std::remove_if(out.begin(), out.end(),
                                 [&](const Cell &c) {
                                   if (c.path.compare(0, 3, "arg") != 0)
                                     return false;
                                   size_t i = 3;
                                   if (i >= c.path.size() || c.path[i] < '0' || c.path[i] > '9')
                                     return false;
                                   int arg = 0;
                                   while (i < c.path.size() && c.path[i] >= '0' && c.path[i] <= '9') {
                                     arg = arg * 10 + (c.path[i] - '0');
                                     ++i;
                                   }
                                   auto it = root.find(arg);
                                   if (it == root.end())
                                     return true;
                                   std::string ty = firstType(c.path);
                                   return !ty.empty() && ty != "ext" && ty != it->second;
                                 }),
                  out.end());
      }
      out.erase(std::remove_if(out.begin(), out.end(),
                               [&](const Cell &c) {
                                 return c.path.compare(0, 3, "arg") != 0 ||
                                        c.path.find("+any") != std::string::npos ||
                                        c.path.find("^any") != std::string::npos ||
                                        c.path.find("*any") != std::string::npos ||
                                        sretArg(argIndex(c.path));
                               }),
                out.end());
    }
    {
      std::vector<GuardFix> keptG;
      keptG.reserve(guards.size());
      for (const GuardFix &g : guards) {
        bool drop = false;
        if (g.pred == llvm::ICmpInst::ICMP_EQ && g.vals.size() == 1) {
          for (const GuardFix &o : guards) {
            if (o.arg != g.arg || o.path != g.path || o.len != g.len)
              continue;
            if (o.pred == llvm::ICmpInst::ICMP_NE && o.vals.size() == 1 && o.vals[0] == g.vals[0])
              drop = true;
            if (!o.mask.empty() && o.pred == llvm::ICmpInst::ICMP_NE && o.vals.size() == 1 && o.vals[0] == "0" &&
                g.vals[0] == "0")
              drop = true;
          }
        }
        if (!drop)
          keptG.push_back(g);
      }
      guards.swap(keptG);
    }
    {
      // One call loads one cell. A vtable load is the slot. A path that keeps
      // only the tail of a longer path has dropped the parent object.
      auto offsOf = [](std::string s) {
        auto slot = s.rfind(".struct.slot^");
        if (slot != std::string::npos)
          s = s.substr(0, slot);
        std::vector<long long> off;
        for (size_t i = 0; i < s.size(); ++i) {
          char c = s[i];
          if (c != '+' && c != '^' && c != '*')
            continue;
          if (i + 4 <= s.size() && s.compare(i + 1, 3, "any") == 0) {
            off.clear();
            return off;
          }
          size_t j = i + 1;
          if (j < s.size() && s[j] == '-')
            ++j;
          if (j >= s.size() || s[j] < '0' || s[j] > '9')
            continue;
          off.push_back(std::stoll(s.substr(j)));
        }
        return off;
      };
      std::vector<char> drop(fns.size(), 0);
      std::map<std::string, std::vector<size_t>> by;
      for (size_t i = 0; i < fns.size(); ++i) {
        if (fns[i].path.find("any") != std::string::npos) {
          drop[i] = 1;
          continue;
        }
        by[fns[i].name].push_back(i);
      }
      for (const auto &g : by) {
        const auto &ix = g.second;
        bool slot = false;
        for (size_t i : ix)
          if (fns[i].path.find(".struct.slot^") != std::string::npos)
            slot = true;
        std::vector<std::vector<long long>> ov(ix.size());
        for (size_t a = 0; a < ix.size(); ++a)
          ov[a] = offsOf(fns[ix[a]].path);
        for (size_t a = 0; a < ix.size(); ++a) {
          if (slot && fns[ix[a]].path.find(".struct.slot^") == std::string::npos) {
            drop[ix[a]] = 1;
            continue;
          }
          for (size_t b = 0; b < ix.size(); ++b) {
            if (a == b || ov[a].empty() || ov[b].size() <= ov[a].size())
              continue;
            size_t pre = 0;
            while (pre < ov[a].size() && ov[a][pre] == ov[b][pre])
              ++pre;
            size_t suf = 0;
            while (suf < ov[a].size() - pre &&
                   ov[a][ov[a].size() - 1 - suf] == ov[b][ov[b].size() - 1 - suf])
              ++suf;
            if (pre + suf == ov[a].size() && ov[b].size() > pre + suf)
              drop[ix[a]] = 1;
          }
        }
      }
      std::vector<FnBind> keptFn;
      for (size_t i = 0; i < fns.size(); ++i)
        if (!drop[i])
          keptFn.push_back(std::move(fns[i]));
      fns.swap(keptFn);
    }
    // A file byte reaches this witness only when the read runs on the kept
    // sequence or in a function that sequence calls to perform the read,
    // including a function pointer it passes. A read elsewhere in the library
    // is another file.
    if (!keptFns.empty()) {
      std::unordered_set<llvm::Function *> cone(keptFns.begin(), keptFns.end());
      std::unordered_set<llvm::Function *> viaCallback;
      auto pull = [&](llvm::Function *G) {
        if (!G)
          return;
        G = bodyOf(G);
        if (G && !G->isDeclaration())
          cone.insert(G);
      };
      for (llvm::Function *F : keptFns) {
        auto sit = sum.find(F);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites) {
          pull(site.callee);
          const auto *cbCall = llvm::dyn_cast<llvm::CallBase>(site.call);
          if (!cbCall)
            continue;
          for (unsigned a = 0; a < cbCall->arg_size(); ++a) {
            const llvm::Value *v = cbCall->getArgOperand(a)->stripPointerCasts();
            auto *cb = const_cast<llvm::Function *>(llvm::dyn_cast<llvm::Function>(v));
            if (!cb || cb->isDeclaration())
              continue;
            llvm::Function *B = bodyOf(cb);
            if (!B || B->isDeclaration())
              continue;
            if (!sum.count(B))
              analyze(*B);
            pull(B);
            viaCallback.insert(B);
            auto cit = sum.find(B);
            if (cit == sum.end())
              continue;
            for (const Site &inner : cit->second.sites) {
              llvm::Function *D = inner.callee ? bodyOf(inner.callee) : nullptr;
              if (!D || D->isDeclaration())
                continue;
              if (!sum.count(D))
                analyze(*D);
              pull(D);
              viaCallback.insert(D);
            }
          }
        }
      }
      std::map<std::pair<llvm::Function *, int>, int64_t> got;
      std::map<std::pair<llvm::Function *, int>, bool> openCount;
      // The fd token moves only inside this cone: the open, a store of that
      // fd into an object, a load of it, and an argument of a call that stays
      // in the cone. A read in another part of the library is not this file.
      {
        using Tok = std::pair<llvm::Function *, int>;
        std::unordered_map<llvm::Function *, std::unordered_map<int, std::vector<Tok>>> ftok;
        std::unordered_map<llvm::Function *, std::unordered_map<int, std::vector<Tok>>> gtok;
        auto addTok = [](std::vector<Tok> &dst, const Tok &t) {
          if (!t.first || std::find(dst.begin(), dst.end(), t) != dst.end())
            return false;
          dst.push_back(t);
          return true;
        };
        std::vector<llvm::Function *> q(cone.begin(), cone.end());
        std::unordered_set<llvm::Function *> inq(cone.begin(), cone.end());
        auto poke = [&](llvm::Function *Fn) {
          if (Fn && cone.count(Fn) && inq.insert(Fn).second)
            q.push_back(Fn);
        };
        for (size_t qi = 0; qi < q.size(); ++qi) {
          llvm::Function *F = q[qi];
          inq.erase(F);
          auto fit = sum.find(F);
          if (fit == sum.end())
            continue;
          const FnSum &fs = fit->second;
          bool again = false;
          auto toksAt = [&](int g, int formal) {
            std::vector<Tok> h;
            if (g >= 0) {
              auto git = gtok[F].find(g);
              if (git != gtok[F].end())
                for (const Tok &t : git->second)
                  addTok(h, t);
            }
            if (formal >= 0) {
              auto fit2 = ftok[F].find(formal);
              if (fit2 != ftok[F].end())
                for (const Tok &t : fit2->second)
                  addTok(h, t);
            }
            return h;
          };
          auto addF = [&](llvm::Function *fn, int formal, const Tok &t) {
            if (!fn || formal < 0 || !cone.count(fn))
              return;
            if (!addTok(ftok[fn][formal], t))
              return;
            again = again || fn == F;
            poke(fn);
          };
          auto addG = [&](llvm::Function *fn, int g, const Tok &t) {
            if (!fn || g < 0 || !cone.count(fn))
              return;
            if (!addTok(gtok[fn][g], t))
              return;
            again = again || fn == F;
            poke(fn);
          };
          for (int i = 0; i < (int)fs.argGroup.size(); ++i)
            for (const Tok &t : toksAt(fs.argGroup[(size_t)i], i)) {
              addG(F, fs.argGroup[(size_t)i], t);
              addF(F, i, t);
            }
          for (const auto &o : fs.openAt)
            addG(F, o.first, Tok{F, o.second});
          for (const auto &s : fs.streamOf)
            for (const Tok &t : toksAt(s.first, -1))
              addG(F, s.second, t);
          for (const auto &st : fs.ptrStore)
            for (const auto &ld : fs.ptrLoad)
              if (st.first == ld.first)
                for (const Tok &t : toksAt(st.second, -1))
                  addG(F, ld.second, t);
          for (const auto &h : fs.holds)
            for (const Tok &t : toksAt(h.second, -1))
              addF(F, h.first, t);
          for (const auto &ld : fs.fromObj)
            for (const Tok &t : toksAt(-1, ld.second))
              addG(F, ld.first, t);
          for (size_t si = 0; si < fs.sites.size() && si < fs.binds.size(); ++si) {
            const Site &site = fs.sites[si];
            std::vector<llvm::Function *> tg;
            if (site.callee) {
              llvm::Function *B = bodyOf(site.callee);
              if (B && cone.count(B))
                tg.push_back(B);
            } else {
              for (int k : site.calleeKeys) {
                auto kit = fnAt.find(k);
                if (kit == fnAt.end())
                  continue;
                for (llvm::Function *T : kit->second)
                  if (cone.count(T))
                    tg.push_back(T);
              }
            }
            if (tg.empty())
              continue;
            const std::vector<ArgBind> &row = fs.binds[si];
            for (llvm::Function *callee : tg) {
              for (int j = 0; j < (int)row.size(); ++j) {
                for (const Tok &t : toksAt(row[(size_t)j].group, row[(size_t)j].formal))
                  addF(callee, j, t);
                auto cit = ftok.find(callee);
                if (cit == ftok.end())
                  continue;
                auto jt = cit->second.find(j);
                if (jt == cit->second.end())
                  continue;
                for (const Tok &t : jt->second) {
                  addG(F, row[(size_t)j].group, t);
                  addF(F, row[(size_t)j].formal, t);
                }
              }
            }
          }
          for (const PRead &pr : fs.preads)
            for (const Tok &t : toksAt(pr.fdGroup, pr.obj)) {
              auto key = t;
              if (pr.len > 0)
                got[key] = std::max(got[key], pr.len);
              else
                openCount[key] = true;
            }
          if (again)
            poke(F);
        }
      }
      for (const auto &kv : got)
        if (!openCount.count(kv.first))
          openCount[kv.first] = false;
      for (const auto &kv : openCount) {
        int64_t n = kv.second ? int64_t{0} : got[kv.first];
        if (n > 0) {
          for (llvm::Function *C : viaCallback) {
            auto it = sum.find(C);
            if (it == sum.end())
              continue;
            for (const PRead &pr : it->second.preads)
              if (pr.len <= 0)
                n = 0;
          }
        }
        // The path formal is followed back through the calls that pass it.
        // The export argument that arrives there is the file, including when
        // that argument is not itself a sink-slice field.
        std::vector<std::pair<llvm::Function *, int>> wq{{kv.first.first, kv.first.second}};
        std::set<std::pair<llvm::Function *, int>> seenUp;
        bool lifted = false;
        for (size_t wi = 0; wi < wq.size(); ++wi) {
          llvm::Function *fn = wq[wi].first;
          int formal = wq[wi].second;
          if (!fn || formal < 0 || !seenUp.insert({fn, formal}).second)
            continue;
          if (isInput(fn, formal)) {
            files.push_back(FileBytes{showFn(fn), formal, n});
            lifted = true;
          }
          auto cit = callers.find(fn);
          if (cit == callers.end())
            continue;
          for (llvm::Function *C : cit->second) {
            auto sit = sum.find(C);
            if (sit == sum.end())
              continue;
            for (size_t si = 0; si < sit->second.sites.size() && si < sit->second.binds.size(); ++si) {
              llvm::Function *cal = sit->second.sites[si].callee ? bodyOf(sit->second.sites[si].callee) : nullptr;
              if (cal != fn)
                continue;
              const std::vector<ArgBind> &row = sit->second.binds[si];
              if (formal >= (int)row.size())
                continue;
              if (row[(size_t)formal].formal >= 0) {
                wq.push_back({C, row[(size_t)formal].formal});
                continue;
              }
              int g = row[(size_t)formal].group;
              if (g < 0)
                continue;
              for (int i = 0; i < (int)sit->second.argGroup.size(); ++i)
                if (sit->second.argGroup[(size_t)i] == g)
                  wq.push_back({C, i});
            }
          }
        }
        if (!lifted) {
          for (const Hit &h : hitsOf(kv.first.first, kv.first.second, 0))
            if (isInput(h.who, h.arg))
              files.push_back(FileBytes{showFn(h.who), h.arg, n});
        }
      }
      // The opened path is a buffer filled by copying an export argument.
      // That argument is the file even when the open itself sees the copy.
      if (!openCount.empty()) {
        int64_t n = 0;
        bool variable = false;
        for (const auto &kv : openCount) {
          if (kv.second)
            variable = true;
          else if (got[kv.first] > n)
            n = got[kv.first];
        }
        if (!variable && n > 0) {
          for (llvm::Function *C : viaCallback) {
            auto it = sum.find(C);
            if (it == sum.end())
              continue;
            for (const PRead &pr : it->second.preads)
              if (pr.len <= 0)
                variable = true;
          }
        }
        if (variable)
          n = 0;
        // The sequence copies bytes of an export argument, and this cone opens
        // a file. That argument is the file. The copy is a byte load from one
        // formal stored through another, or memcpy.
        for (llvm::Function *F : keptFns) {
          auto sit = sum.find(F);
          if (sit == sum.end())
            continue;
          for (size_t si = 0; si < sit->second.sites.size() && si < sit->second.binds.size(); ++si) {
            llvm::Function *cal = sit->second.sites[si].callee ? bodyOf(sit->second.sites[si].callee) : nullptr;
            if (!cal)
              continue;
            auto cit = sum.find(cal);
            if (cit == sum.end() && !cal->isDeclaration()) {
              unsigned nIns = 0;
              for (const llvm::BasicBlock &BB : *cal)
                nIns += BB.size();
              if (nIns > 0 && nIns < 400) {
                analyze(*cal);
                cit = sum.find(cal);
              }
            }
            if (cit == sum.end())
              continue;
            const std::vector<ArgBind> &row = sit->second.binds[si];
            for (const auto &cp : cit->second.byteFrom) {
              if (cp.first < 0 || cp.second < 0 || cp.first >= (int)row.size() || cp.second >= (int)row.size())
                continue;
              int src = row[(size_t)cp.second].formal;
              if (src < 0 || !isInput(F, src))
                continue;
              files.push_back(FileBytes{showFn(F), src, n});
            }
          }
        }
      }
      std::sort(files.begin(), files.end(), [](const FileBytes &a, const FileBytes &b) {
        if (a.func != b.func)
          return a.func < b.func;
        if (a.arg != b.arg)
          return a.arg < b.arg;
        return a.len < b.len;
      });
      files.erase(std::unique(files.begin(), files.end(),
                              [](const FileBytes &a, const FileBytes &b) {
                                return a.func == b.func && a.arg == b.arg && a.len == b.len;
                              }),
                  files.end());
    }
    return FieldReport{std::move(out), std::move(seqs), std::move(files), std::move(guards), std::move(fns),
                       std::move(kept)};
  }
};

} // namespace

FieldReport fieldCells(llvm::Module &downstream, llvm::Module &upstream, const std::string &sinkFile,
                       unsigned sinkLine, const std::vector<std::string> &sinkFns,
                       const std::vector<std::string> &chops,
                       const std::unordered_map<std::string, std::vector<Input>> &inputs) {
  Engine E(downstream, upstream, sinkFile, sinkLine, sinkFns);
  return E.run(chops, inputs);
}

} // namespace chain
