#pragma once

#include "Model.h"
#include <tuple>

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
    // §3.5: the cell lies inside a D→U crossing actual, so it is part of the
    // state the client must build and hand across the boundary (Phi_boundary).
    bool boundary = false;
    // §3.5: this witness has a D→U crossing (some resolved or unresolved
    // boundary root), so the boundary projection applies: only boundary cells
    // are client obligations. Without a crossing the projection is undefined
    // and every cell stays an obligation.
    bool crossing = false;
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
  struct Plan {
    // Per entry, a disjunction over its witnesses of the conjunction of
    // their frozen constraints. An entry with an unguarded witness has none.
    FnMap<std::vector<std::vector<Guard>>> guards;
    std::vector<Function *> firsts;
    std::vector<Function *> entries;
    std::vector<std::pair<std::string, std::vector<Producer>>> handles;
    std::vector<Cell> clientCells;
    // Per entry, the public fields of its arguments that name the input
    // file; the client writes the input's name into them before the call.
    FnMap<std::vector<Cell>> files;
    std::vector<std::pair<Cell, std::vector<Function *>>> cellWriters;
    std::vector<Function *> writers;
    // One line per witness: whether its library cells are discharged by at
    // most four interface calls that are not the entry itself.
    std::vector<std::string> verdicts;
    // Per producer of a held type, the calls that can establish the state
    // it reads before it can produce.
    std::map<std::pair<Function *, std::string>, std::vector<Function *>, FnOrder> deps;
  };

  Client(Module &down, Module &up, const fs::path &dir);
  static std::set<std::string> downstreamInterface(const fs::path &dir);
  Plan plan(const std::vector<std::pair<std::vector<std::string>, std::vector<Cell>>> &witnesses) const;
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

  std::vector<Param> signature(Function *F) const;
  std::vector<int> irParams(Function *F) const;
  Param result(Function *F) const;
  static const char *kindName(Kind k);

private:
  Module &down;
  Module &up;
  const DataLayout &dl;
  std::set<std::string> dsyms, usyms, headers, declared;
  std::map<std::string, bool> defined;
  std::map<std::string, const DICompositeType *> composite;
  // The ODR identifiers (typeinfo names) the debug info of D and U carries.
  std::set<std::string> identifiers;
  std::map<std::string, Function *> bodies;
  FnSet ifaceD, ifaceU;
  FnMap<FnSet> calls;
  FnMap<std::set<std::pair<std::pair<std::string, int64_t>, std::string>>> stores;
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
  std::map<std::pair<std::string, int64_t>, FnSet> fnField;
  Value *fieldAddress(Value *P) const;
  std::vector<std::pair<std::string, int64_t>> fieldsOf(Value *P) const;
  void constFields(Constant *C, Type *T, std::string S, int64_t at, const DIType *D);
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
  static std::string abstractValue(Value *V);
  static std::string bareName(const std::string &n);
  static bool satisfies(const std::string &v, const Cell &c);
  static std::string irName(const std::string &t);
};
