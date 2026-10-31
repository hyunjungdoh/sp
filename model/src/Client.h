#pragma once

#include "Model.h"
#include <climits>
#include <functional>
#include <memory>
#include <optional>
#include <tuple>

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/BinaryFormat/Dwarf.h"

// A total order on functions that does not depend on where they are
// allocated: by name, then by module. Every iteration over functions follows
// it, so equal inputs give the same client.
struct FnOrder {
  bool operator()(const Function *a, const Function *b) const {
    if (a == b)
      return false;
    if (int c = a->getName().compare(b->getName()))
      return c < 0;
    if (int c = a->getParent()->getModuleIdentifier().compare(b->getParent()->getModuleIdentifier()))
      return c < 0;
    return a < b;
  }
  template <class T> bool operator()(const std::pair<Function *, T> &a, const std::pair<Function *, T> &b) const {
    if (a.first != b.first)
      return (*this)(a.first, b.first);
    return a.second < b.second;
  }
};
using FnSet = std::set<Function *, FnOrder>;
template <class V> using FnMap = std::map<Function *, V, FnOrder>;

class Client {
public:
  // What a client passes for one parameter, from its source-level type.
  // Storage is the object a constructor initializes: client memory of the
  // class's size, whatever it holds before.
  enum class Kind { Scalar, Text, Bytes, Callback, Object, Handle, Out, Aggregate, Storage };
  struct Param {
    Kind kind = Kind::Scalar;
    std::string type;
    // For a pointer, the size of what it points to (1 when unknown).
    uint64_t elem = 1;
    // The parameter is a va_list.
    bool va = false;
    // The size of the declared type, in bytes.
    uint64_t size = 0;
    // An aggregate the ABI passes by reference to a copy: of memory class,
    // or not trivially copyable.
    bool indirect = false;
    // The source type the function requires: the declared one, or the
    // larger record the function treats the pointer as (a downcast).
    const DIType *di = nullptr;
  };
  // How a producer yields its handle: its result (-1), an out-parameter
  // (its index), the pointer an owning result holds (Owner), or the
  // storage a constructor initializes (Construct).
  static constexpr int Owner = -2, Construct = -3;
  struct Producer {
    Function *fn = nullptr;
    int out = -1;
    unsigned cost = 0;
  };
  // A field of the entry state the residual formula names: the last
  // (struct type, offset) step of the cell.
  struct Cell {
    std::string type;
    int64_t off = 0;
    std::string text;
    int root = -1;
    std::vector<std::string> path;
    std::string op;
    std::vector<std::string> values;
    // The cell names or reads the client's input file.
    bool file = false;
    // Client Φ = Φ_∂ ∪ Φ_pre ∪ own, from one Loc judgment along π:
    // formal/GEP/load/call (incl. packed locals) → cell → R(π) or D-prefix read.
    // §3.5 Φ_∂: inside a resolved crossing actual (boundaryroot).
    bool boundary = false;
    // §3.5: |R(π)|>0 so Φ_∂ projects; unresolved alone does not set this.
    bool crossing = false;
    // §3.5 Φ_pre: D path condition before first cross read this Loc-cell.
    bool prefix = false;
  };
  // §3.8 정의 3.8.4 키 세터 레버: 인터페이스 W(…, 태그 = tag, …, 가변 인자)가 셀
  // target을 쓴다. 가변 인자의 값은 preds를 만족하는 값 중에서 고른다.
  struct Keyed {
    std::string fn;
    unsigned obj = 0;
    int tag = -1;
    int64_t tagV = 0;
    bool va = false;
    std::vector<std::pair<std::string, int64_t>> preds;
    std::string target;
    int root = -1;
    std::vector<std::string> path;
    int64_t off = -1;
    bool covers(const Cell &c) const { return root == c.root && off == c.off && path == c.path; }
  };
  // 정의 R: a call on the witness whose result the path compares, the
  // obligation `callee pred k` at caller:line.
  struct Ret {
    std::string callee, pred, k, caller;
    unsigned line = 0;
  };
  // §3.8 정의 3.8.6 이름 키 설정: 조회 G(o, κ, d)가 읽는 이름 κ의 값을
  // 클라이언트가 같은 o 위의 세터 S(o, κ, v)로 정한다. κ는 조회 지점이 짓는
  // 그대로 짓는다: init이 있으면 slot 크기의 칸을 init(…, κ, …)로 채우고, 없으면
  // κ가 곧 인자다.
  struct Named {
    Function *setter = nullptr;
    std::string type;
    std::string key;
    unsigned obj = 0, name = 0, value = 0;
    // Per IR parameter of the setter outside obj, name and value: the
    // constant the lookup passes there.
    std::vector<Constant *> rest;
    Function *init = nullptr;
    Type *slot = nullptr;
    // Per argument of init: the constant it takes, or null for the slot
    // (at slotAt) and for κ (at textAt).
    std::vector<Constant *> initArgs;
    unsigned slotAt = 0, textAt = 0;
  };
  // A constraint on an integer field embedded in an entry argument: the
  // field at byte offset off of argument root, width bits wide.
  struct Guard {
    int root = -1;
    int64_t off = 0;
    unsigned width = 0;
    bool eq = true;
    std::vector<int64_t> values;
    std::string text;
    // The client sets the field (configuration) rather than assuming it.
    bool config = false;
  };
  // §3.6 생성자 레버: 클라이언트가 직접 쓸 수 없는(불투명, 생산자가 세우는) 보유
  // 인자의 경로 셀은, 그 셀로 값이 흘러드는 생산자의 입력 형식인자로 실현된다.
  // 클라이언트는 그 인자를 셀이 요구하는 대로 고른다: 등식은 값을 넘기고,
  // 부등식은 가정한다(§4 가드와 같은 의미).
  struct Lever {
    unsigned formal = 0;
    bool eq = true;
    std::vector<int64_t> values;
    std::string text;
  };
  // §3.9: how the plan establishes one obligation cell, first that applies.
  enum class Realize { Own, Lever, Key, Write, Construct, File, Open };
  static const char *realizeName(Realize r);
  struct Realized {
    Cell cell;
    Realize how = Realize::Open;
    // The call the realization relies on: the producer of a lever, the key
    // setter, the covering writer, or the call that reads the input.
    Function *by = nullptr;
    // For an open cell, the condition that left it open.
    std::string why;
  };
  struct WitnessPlan {
    Function *first = nullptr;
    std::vector<Function *> entries;
    bool iface = false;
    // Steering: the configuration and guards at the first function (when
    // it is the entry), the producer levers, and the input name fields.
    bool direct = false;
    std::vector<Guard> guards;
    std::vector<std::pair<Function *, Lever>> levers;
    std::vector<Cell> files;
    // Realization: one per obligation cell, the write cover, and the key
    // setter calls the Key cells use.
    std::vector<Realized> cells;
    // 정의 R: one per return obligation of the witness, realized like a cell.
    std::vector<Realized> returns;
    std::vector<Function *> cover;
    std::vector<std::pair<Function *, Keyed>> keyed;
    // §3.9 정의 E: per Construct cell established by a store, the store's
    // position and the may sequence that reaches it.
    std::vector<std::string> established;
    // 정의 M: the calls barred from realizing a cell, with the obligation
    // they leave at a rejected constant.
    std::vector<std::string> excluded;
    // The function sequence the plan is for, when it answers a 정의 E query.
    std::vector<std::string> seq;
    // §3.9: iface(callable entry exists) ∧ every obligation cell non-Open.
    // Controls which writers and key setters the harness installs.
    bool pass = false;
    // §3.7: indirect dispatch edges of this witness Definition D leaves open.
    unsigned dispatchOpen = 0;
    // §5 따름정리 (실패의 분리): the witness is a faithful program only when a
    // callable interface entry reaches π₀ (pass), every cell obligation is
    // discharged (pass), and no dispatch edge is open. An unrealized witness
    // is a model gap, not a search gap: it opens the H3 gate.
    bool realized = false;
  };
  using Witnesses = std::vector<std::pair<std::vector<std::string>, std::vector<Cell>>>;
  struct Plan {
    // Per entry, a disjunction over its witnesses of the conjunction of
    // their frozen constraints. An entry with an unguarded witness has none.
    FnMap<std::vector<std::vector<Guard>>> guards;
    // Per producer, the constructor levers of the cells its inputs decide.
    FnMap<std::vector<Lever>> levers;
    std::vector<Function *> firsts;
    std::vector<Function *> entries;
    std::vector<std::pair<std::string, std::vector<Producer>>> handles;
    // Per entry, the public fields of its arguments that name the input
    // file; the client writes the input's name into them before the call.
    FnMap<std::vector<Cell>> files;
    // §2.4 Key: the names the witnesses' indirect targets are registered
    // under. The input file may carry one as its extension.
    std::vector<std::string> keys;
    // §3.9: the union of the write covers of the witnesses that pass.
    std::vector<Function *> writers;
    // §3.9: per witness, the realization of each obligation cell.
    std::vector<WitnessPlan> witnesses;
    // §3.7: per witness, its indirect edges and how Definition D realizes
    // each, and the number left open.
    std::vector<std::string> obligations;
    // §3.7 D item 2 / H3: first input-dispatch installer per witness
    // (`input:F`). The search approaches these before the sink (Π_I gate).
    std::vector<std::string> stInstallers;
    // Per producer of a held type, the calls that can establish the state
    // it reads before it can produce.
    std::map<std::pair<Function *, std::string>, std::vector<Function *>, FnOrder> deps;
    // §3.8 정의 3.8.4: per entry, the key setter calls that realize a cell of
    // a witness that passes, in the order the may layer found them.
    FnMap<std::vector<std::pair<Function *, Keyed>>> keyed;
    // §3.8 정의 3.8.6: per entry, the named settings of the lookups its
    // witnesses' steps make on an object the entry receives.
    FnMap<std::vector<Named>> named;
  };

  // §3.8: the key setters of each witness, aligned with plan()'s witnesses.
  std::vector<std::vector<Keyed>> keyedIn;
  // 정의 R: the return obligations of each witness, aligned likewise.
  std::vector<std::vector<Ret>> retsIn;
  // §3.9 정의 E: the may layer's first satisfiable sequence, at path index
  // `from` or later in cost order, from one of the start functions to a
  // source line, or none within the path budget.
  struct Reached {
    std::vector<std::string> seq;
    std::vector<Cell> phi;
    std::vector<Keyed> keyed;
    std::vector<Ret> rets;
    int index = -1;
  };
  std::function<std::optional<Reached>(const std::string &file, unsigned line, const std::set<std::string> &starts,
                                       int from)>
      reach;
  // The same may query, three-valued: 1 a satisfiable sequence reaches the
  // line, 0 every sequence was tried and none is satisfiable, -1 unknown
  // (budget exhausted or no such line).
  std::function<int(const std::string &file, unsigned line, const std::set<std::string> &starts)> probe;
  // 정의 R: the same three-valued query from exactly the given functions,
  // internal ones included.
  std::function<int(const std::string &file, unsigned line, const std::set<std::string> &starts)> probeFrom;

  Client(Module &down, Module &up, const fs::path &dir);
  static std::set<std::string> downstreamInterface(const fs::path &dir);
  // I: exports of D that an installed header declares. The call graph and
  // midpoint test use this set. A dynamic symbol the header does not
  // declare is not in I.
  static std::set<std::string> publicInterface(llvm::Module &down, llvm::Module &up, const fs::path &dir);
  // P1 start set: members of I whose held argument types are all client-
  // producible (entryCallable). Witnesses begin only here so π₀ is a real
  // client entry and φ lands on its arguments.
  static std::set<std::string> entryInterface(llvm::Module &down, llvm::Module &up, const fs::path &dir);
  // Every symbol, function or data, exported or local, a library the closure
  // installs defines.
  static std::set<std::string> installedExports(const fs::path &dir);
  Plan plan(const Witnesses &ws) const;
  // §3.7 / P1: indirect edges of seq that Definition D cannot realize with
  // the producers and writers an empty-φ plan would install at seq[0].
  // P1 keeps a path only when this set is empty (φ SAT is not enough).
  std::vector<std::pair<std::string, std::string>> openDispatchEdges(const std::vector<std::string> &seq) const;
  void report(const Plan &P, raw_ostream &out) const;
  void emit(const Plan &P, Module &H) const;
  // Bounds of the client search: writer calls before the entry, and the
  // bytes of every input channel.
  void bounds(unsigned writers, unsigned input, unsigned depth, unsigned text) {
    writerSlots = writers;
    inputBound = input;
    objectDepth = depth;
    textBound = text;
  }

  // A shared library the closure installs: its path relative to the case
  // directory ("/"-prefixed; absolute when outside it), whether it is a
  // symbolic link, and the symbols it exports.
  struct Library {
    std::string key;
    bool link = false;
    std::set<std::string> exports;
  };

  std::vector<Param> signature(Function *F) const;
  std::vector<int> irParams(Function *F) const;
  Param result(Function *F) const;
  static const char *kindName(Kind k);

private:
  Module &down;
  Module &up;
  const DataLayout &dl;
  std::set<std::string> dsyms, usyms, headers, declared;
  std::vector<Library> installed;
  std::map<std::string, bool> defined;
  std::map<std::string, const DICompositeType *> composite;
  // The ODR identifiers (typeinfo names) the debug info of D and U carries.
  std::set<std::string> identifiers;
  std::map<std::string, Function *> bodies;
  FnSet ifaceD, ifaceU;
  FnMap<FnSet> calls;
  FnMap<std::set<std::pair<std::pair<std::string, int64_t>, std::string>>> stores;
  // Fields a function writes a value that is neither a constant nor a copy
  // of another field (§3.9 정의 E).
  FnMap<std::set<std::pair<std::string, int64_t>>> inputStores;
  // The copies a function's own stores make: destination field to sources.
  FnMap<std::map<std::pair<std::string, int64_t>, std::set<std::pair<std::string, int64_t>>>> copyStores;
  // Byte ranges memory intrinsics write: (struct, offset) and a length,
  // INT64_MAX when the length is not constant.
  FnMap<std::vector<std::tuple<std::string, int64_t, int64_t>>> ranges;
  std::set<std::pair<Function *, unsigned>> releases;
  // Fields a function may modify or reference directly: through a store or
  // load, or by passing the field's address to a call.
  FnMap<std::set<std::pair<std::string, int64_t>>> mods, refs;
  mutable std::map<std::pair<Function *, bool>, std::set<std::pair<std::string, int64_t>>> modRefOf;
  const std::set<std::pair<std::string, int64_t>> &transitive(Function *F, bool mod) const;
  // Fields a branch condition reads, per function and over its closure.
  FnMap<std::set<std::pair<std::string, int64_t>>> crefs;
  mutable FnMap<std::set<std::pair<std::string, int64_t>>> crefOf;
  const std::set<std::pair<std::string, int64_t>> &controlRefs(Function *F) const;
  // The functions whose own stores modify a field.
  mutable std::map<std::pair<std::string, int64_t>, std::vector<Function *>> modifiers;
  void buildModRef();
  // Where a pointer of a function points: *(..*(formal + p1)..+ pk) + off;
  // root -1 where it is no such pointer, -2 where only a slot or call
  // already being evaluated defines it.
  struct Position {
    int root = -1;
    std::vector<int64_t> path;
    int64_t off = 0;
    bool exact = true;
  };
  mutable FnMap<Position> returnOfFn;
  mutable FnSet returnOpen;
  Position positionOf(Value *V, std::set<AllocaInst *> &open, bool &cut) const;
  Position returnOf(Function *F, bool &cut) const;
  static Position agreed(const std::vector<Position> &vs);
  // A text read inside a call of F: formal i, then a pointer loaded at each
  // offset of path in turn.
  using TextPlace = std::tuple<Function *, unsigned, std::vector<int64_t>>;
  mutable std::map<TextPlace, std::vector<std::string>> comparedOf;
  const std::vector<std::string> &compared(Function *F, unsigned i, const std::vector<int64_t> &path = {}) const;
  std::vector<std::string> keysOf(Function *T) const;
  // §3.7 St(t): the functions that take t's address (any use but as a
  // callee), or read a constant record that holds it.
  FnSet installers(Function *T) const;
  // §3.11 Definition L: how a call of F takes the input. Passed: a formal
  // hands it over, a byte sequence F bounds by a length formal (A3) or a
  // callback whose type reads one; Named: F's closure opens or reads a file
  // of the environment (§7 FileEnv); None otherwise. The order is the
  // provenance order of the harness's choices.
  enum class Channel { Passed, Named, None };
  Channel channel(Function *F) const;
  mutable FnMap<Channel> channelOf;
  // Functions that reach fopen/read-family calls: one reverse BFS over
  // `calls`, not a fresh closureOf per channel()/readsInput() query.
  void ensureIoReach() const;
  mutable bool ioReachReady = false;
  mutable FnSet reachesOpen;
  mutable FnSet reachesRead;
  bool opensFile(Function *F) const { return channel(F) != Channel::None; }
  // The pointer formals of F that integer formal j bounds (A3).
  std::vector<unsigned> boundBy(Function *F, unsigned j) const;
  // 1 + the cost of the held inputs of a call of F (Definition 4).
  unsigned callCost(Function *F) const;
  // The values a call of F leaves to the client's choice: its formals that
  // are neither held nor out.
  unsigned freeArgs(Function *F) const;
  bool needs(const std::string &U, const std::string &T, std::set<std::string> &seen) const;
  std::vector<Function *> dependences(Function *P, const std::string &T) const;
  bool guardOf(Function *E, const Cell &c, Guard &g, bool config = false) const;
  bool place(const Cell &c, int64_t &off, Type *&field) const;
  unsigned writerSlots = 2, inputBound = 64, depSlots = 1, objectDepth = 2, textBound = 2;
  std::map<std::string, unsigned> cost;
  std::map<std::string, std::vector<Producer>> producers;
  // Types some interface function constructs (returns or writes out).
  std::set<std::string> constructed;
  bool held(const Param &p) const;
  std::set<int> loadedFrom(Function *F) const;
  bool writesThrough(Function *F, unsigned i) const;
  std::set<std::pair<Function *, unsigned>> writes;
  mutable FnMap<FnSet> closures, inner, callersOf;
  std::map<std::pair<Function *, unsigned>, FunctionType *> fnTypes;
  // The declared type of each callback formal, when the header declares one.
  std::map<std::pair<Function *, unsigned>, const DIType *> fnDecl;
  void buildCallbackTypes();
  // The IR type of a call through a pointer of declared type T, or null.
  FunctionType *fnTypeOf(const DIType *T) const;
  const FnSet &innerClosure(Function *F) const;
  // Per formal of F, from F's SSA form: whether null has a meaning (A1),
  // and the largest pointer-to-record type a variable bound to it has.
  struct Formals {
    std::vector<bool> null;
    std::vector<const DIType *> as;
    // A3, derived: the pairs (i, j) such that integer formal j bounds the
    // elements F accesses through pointer formal i.
    std::set<std::pair<unsigned, unsigned>> len;
  };
  // A call of F that passes pointer and integer formals of F on: the callee,
  // and per argument the pointer (resp. integer) formal of F it is, or -1.
  struct LenCall {
    Function *callee;
    std::vector<int> ptr, num;
  };
  // What F's own body shows: Formals with len holding only direct evidence,
  // and the calls through which Len(callee) transfers to Len(F).
  struct LocalFormals {
    Formals f;
    std::vector<LenCall> calls;
  };
  mutable FnMap<LocalFormals> localFormals;
  const LocalFormals &localFormalsOf(Function *F) const;
  mutable FnMap<Formals> formals;
  const Formals &formalsOf(Function *F) const;
  bool nullTested(Function *F, unsigned i) const;
  mutable FnMap<std::vector<Param>> sigs;
  static std::vector<int> lower(Function *F, const std::vector<Param> &sig);
  // Fields (S, off) whose value some library function compares with null:
  // A1 for the pointer fields of client-built objects.
  std::set<std::pair<std::string, int64_t>> nullFields;
  // Call_0 (§2.2): fields some function calls through without comparing
  // the field's value with null. They are not in nullFields.
  std::set<std::pair<std::string, int64_t>> unguardedCalls;
  void buildNullFields();
  // A3 for fields: (S, off of a pointer field) -> off of the integer field
  // that bounds it.
  std::map<std::pair<std::string, int64_t>, int64_t> fieldLen;
  void buildFieldLengths();

  std::string typeKey(const DIType *T) const;
  // The record an owning aggregate holds (a smart pointer: its first
  // template argument T, and a T* at offset 0), or "".
  std::string owned(const DIType *A) const;
  const DICompositeType *definition(const DIType *T) const;
  // The class F constructs (not by copy or move), or "".
  std::string constructs(Function *F) const;
  bool isPublic(const std::string &key) const;
  Kind classify(const DIType *T, std::string &key) const;
  Value *fieldAddress(Value *P) const;
  std::vector<std::pair<std::string, int64_t>> fieldsOf(Value *P) const;
  // The fields access I makes through address P: the field GEPs of P, else
  // the record and offset I's TBAA names (the byte GEPs of optimised IR).
  std::vector<std::pair<std::string, int64_t>> accessFields(const Instruction &I, Value *P) const;
  // The record a zero-fill writes whole when its address has no field: the
  // source type the address points to, from offset 0 for its length.
  static std::optional<std::tuple<std::string, int64_t, int64_t>> zeroFill(const MemSetInst &MS);
  // §3.10 the call relation the may layer resolved, read from the marks.
  klee::calls::Targets targets;
  void buildCalls();
  void buildStores();
  void buildReleases();
  void buildWrites();
  void buildProducers();
  static int formalOf(Value *V);
  static int rootOf(Value *V, std::set<AllocaInst *> &open);
  Function *body(const std::string &name) const;
  FnSet interface() const;
  FnSet closure(Function *F) const;
  const FnSet &closureOf(Function *F) const;
  bool callable(Function *F) const;
  // §P2 entry elevation: like callable, but every held argument type must be
  // in cost. A null-only opaque formal does not make a hollow π₀ the client
  // entry — that soft-accepts and skips the real E that installs φ/named.
  bool entryCallable(Function *F) const;
  std::vector<Function *> entries(Function *E) const;
  std::vector<Function *> writers(const Cell &c) const;
  // Whether any defined function stores to the field (struct type, offset).
  // A field no body writes is immutable after construction: its value is the
  // one the library's own static data (a const table, a zeroed allocation)
  // established, identical in every execution. The client neither can nor
  // needs to set it, so it is not a client obligation.
  bool everStored(const std::string &type, int64_t off) const;
  mutable std::set<std::pair<std::string, int64_t>> storedFields;
  mutable bool storedBuilt = false;

  // §3.9 facts. A field is the last (struct type, offset) step of a cell.
  using Field = std::pair<std::string, int64_t>;
  // Some function in fns' closures may store the field (a store or a memory
  // intrinsic over it, the same field abstraction as everStored).
  bool mayStore(const std::vector<Function *> &fns, const Field &f) const;
  static Field fieldOf(const Cell &c) { return {c.type, c.off}; }
  // The integer values of a cell's atom, false when one is not a constant.
  static bool intValues(const Cell &c, std::vector<int64_t> &vs);
  // §3.9 정의 M: what a function leaves in fields on every returning path.
  // A field holds the constant of fixed, else nothing known when it is a
  // hole, else the value of the last fill covering it ("*": nothing known).
  struct MustFill {
    std::string type;
    int64_t off = 0, len = 0;
    std::string val;
    bool operator==(const MustFill &o) const {
      return type == o.type && off == o.off && len == o.len && val == o.val;
    }
  };
  struct MustState {
    std::map<Field, std::string> fixed;
    std::vector<MustFill> fills;
    std::set<Field> holes;
    std::string at(const Field &f) const;
  };
  // A write through formal `formal` of len bytes (lenFormal >= 0: the
  // length is that formal) of value val ("0", "*", or "#j" for formal j).
  struct FormalWrite {
    unsigned formal = 0;
    std::string val;
    int64_t len = 0;
    int lenFormal = -1;
    bool operator==(const FormalWrite &o) const {
      return formal == o.formal && val == o.val && len == o.len && lenFormal == o.lenFormal;
    }
  };
  struct MustSummary {
    MustState post;
    std::vector<FormalWrite> writes;
    std::set<unsigned> clobbers;
  };
  mutable FnMap<MustSummary> mustOf;
  mutable FnSet mustBusy;
  // The fields F or anything it reaches may modify, one bit per field of
  // fieldAt, shared by an SCC of the call relation. Materialising closureOf
  // per callee instead holds a name-ordered set per function: OIIO, GBs.
  const llvm::BitVector &modsBelow(Function *F) const;
  mutable std::vector<Field> fieldAt;
  mutable std::map<Field, unsigned> fieldId;
  mutable std::map<std::string, std::vector<std::pair<int64_t, unsigned>>> fieldsOfType;
  mutable llvm::DenseMap<Function *, unsigned> sccOf;
  mutable std::vector<llvm::BitVector> sccMods;
  mutable std::unique_ptr<TargetLibraryInfoImpl> libImpl;
  mutable std::unique_ptr<TargetLibraryInfo> libSpec;
  const TargetLibraryInfo &libInfo() const;
  const MustSummary *mustOnReturn(Function *F) const;
  // 정의 M: W, once it returns, leaves c's field at a constant φ_c rejects.
  bool contradicts(Function *W, const Cell &c) const;
  // The held type of argument root of E, or "".
  std::string heldType(Function *E, int root) const;
  // The cell lies in a public object the client passes to E.
  bool own(Function *E, const Cell &c) const;
  // §3.6 copy map: the stores in F's inner closure of a value loaded from
  // one field into another, as destination -> sources.
  const std::map<Field, std::set<Field>> &copies(Function *F) const;
  mutable FnMap<std::map<Field, std::set<Field>>> allCopiesOf;
  // The same over F's whole closure, the scope storesInput reads.
  const std::map<Field, std::set<Field>> &allCopies(Function *F) const;
  // The fields a store copies from: those of the load its value is.
  std::set<Field> copySources(StoreInst *S) const;
  mutable FnMap<std::map<Field, std::set<Field>>> copiesOf;
  // The interface functions that set a source F copies into c's field.
  std::vector<Function *> copySetters(Function *F, const Cell &c) const;
  // §3.8 taint (iii): F returns a value derived from its formal j.
  bool returnsArg(Function *F, unsigned j) const;
  mutable std::map<std::pair<Function *, unsigned>, bool> returnsOf;
  // §3.6 lever: the fields W's closure stores a value derived from its
  // scalar, byte or text formals (only that formal when only >= 0).
  const std::set<Field> &argStores(Function *W, int only = -1) const;
  mutable std::map<std::pair<Function *, int>, std::set<Field>> argStoresOf;
  // W stores a value of its arguments to c's field or a field E copies
  // into it.
  bool carries(Function *W, const Cell &c, Function *E) const;
  // §7: F's closure calls an input primitive.
  bool readsInput(Function *F) const;
  mutable FnMap<bool> readsOf;
  // Some store F's closure executes writes to the field a value that is
  // neither a constant nor a copy of another field.
  bool storesInput(Function *F, const Field &f) const;
  bool storesSatisfying(Function *F, const Field &f, const Cell &c) const;
  // §3.5 정리 B(a): every defined function that stores to the field is in U.
  bool upOnly(const Field &f) const;
  // §3.9 realizations, in their order.
  std::vector<std::pair<Function *, Lever>> leversOf(Function *E, const Cell &c) const;
  bool realizable(Function *E, const Keyed &k) const;
  // §3.8 정의 3.8.6: the named settings of the lookups the steps make.
  std::vector<Named> named(const std::vector<std::string> &seq) const;
  Function *namedSetter(Function *G, unsigned obj, unsigned name, unsigned fallback) const;
  std::vector<Function *> writeCandidates(Function *E, const std::vector<Function *> &es, const Cell &c) const;
  // §3.9 정의 E. Whether c is established, and when a store establishes it
  // under Lemma E, the plan of the sequence reaching that store (via).
  bool establishedBy(Function *E, Function *entry, const Cell &c, const WitnessPlan *&via, std::string &at) const;
  std::vector<Function *> harnessStarts(Function *E, Function *entry, const Cell &c) const;
  const WitnessPlan *established(const std::string &file, unsigned line, const std::vector<Function *> &starts) const;
  // Key setters for fields that an establish sequence compares against a
  // constant (Φ_pre held cells may omitted when both branch sides reach).
  std::vector<Keyed> keyedGatesAlong(const std::vector<std::string> &seq, Function *E) const;
  // §3.8.4 tag-dispatch setters, and §3.8.5 tag → (field, mask) raises from
  // constant registries at bit-OR sites (TIFFSetFieldBit shape).
  // §3.7 ∘ 정의 E: T's installation is refuted from the harness calls when T
  // is installed only by stores of its address and probe proves none of
  // those stores reachable from starts.
  bool installRefuted(Function *T, const std::set<std::string> &starts) const;
  mutable std::map<std::pair<std::string, std::set<std::string>>, bool> refutedOf;
  void ensureTagSetters() const;
  void ensureRegistryRaises() const;
  mutable std::map<Field, std::vector<Keyed>> tagSettersOf;
  mutable bool tagSettersReady = false;
  mutable std::map<int64_t, std::vector<std::pair<Field, uint64_t>>> raisesOfTag;
  mutable bool registryReady = false;
  // Per query (file, line, starts): absent while computing (a cycle), then
  // the plan of the reaching sequence when it passes, else null.
  mutable std::map<std::tuple<std::string, unsigned, std::set<std::string>>, std::unique_ptr<WitnessPlan>> estOf;
  // Queries being computed, with their stack depth. estLow is the least
  // depth of a busy query met since the innermost open query began: a
  // failure that met a busy ancestor holds only under that ancestor's
  // provisional failure and is not cached.
  mutable std::map<std::tuple<std::string, unsigned, std::set<std::string>>, int> estBusy;
  mutable int estLow = INT_MAX;
  // One line per query, for the report: the position and the answer.
  mutable std::vector<std::string> estLog;
  bool fills(Function *F, const Cell &c) const;
  Function *inputFiller(Function *E, Function *entry, const Cell &c) const;
  // decide: only whether the plan passes is wanted, so realization stops at
  // the first open obligation (no later step reopens a cell as non-open).
  WitnessPlan realize(Function *E, const std::vector<Cell> &phi, const std::vector<Keyed> &keyed,
                      const std::vector<Ret> &rets, bool decide = false) const;
  int returnedBy(const Ret &r, std::string &why, std::set<std::string> &busy) const;
  mutable std::map<std::string, std::pair<int, std::string>> retOf;
  // The grammar the harness carries, and §3.7 for its indirect edges.
  void grammar(Plan &P) const;
  void dispatch(const Witnesses &ws, Plan &P) const;
  static std::string abstractValue(Value *V);
  static std::string bareName(const std::string &n);
  static bool satisfies(const std::string &v, const Cell &c);
  static std::string irName(const std::string &t);
};
