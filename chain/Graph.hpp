#pragma once

// Field- and context-sensitive points-to as CFL-reachability.
//
// A pointer p may point to a memory cell o iff some backward walk from
// p's node to o's node spells a word of the Flows grammar below. The
// grammar is a context-free bracket language: field-get and field-put
// are a matched pair, call and return are a matched pair. A standard
// result (Reps 1998, Melski-Reps 2000, Zheng-Rugina 2008) is that
// context-free reachability on a graph with n nodes answers one query
// in O(n^3) worst case, and under memoization typically O(n^2); the
// demand-driven walk explores only nodes a query can observe.
//
// The grammar (Zheng-Rugina style, field-sensitive, context-sensitive):
//
//   Flows   -> Assign | Alloc
//   Assign  -> eps
//            | Assign Assign
//            | assign
//            | store_k Alias load_k         (balanced field)
//            | gep_k   Assign gep_(-k)      (balanced shift)
//            | call_c  Assign ret_c         (balanced context)
//   Alias   -> Flows Flows^{-1}
//
// Nodes carry one of two tags:
//   Value : a pointer-typed LLVM Value (SSA register, Argument, Constant)
//   Cell  : a memory cell (object id, byte offset); offset may be Any.
//
// Edges carry one of seven labels, each with a small payload that the
// automaton reads to drive its stacks.
//
// The graph is built once from the two modules (M, U). Nothing is solved
// at build time: the solver runs demand-driven on queries.

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace chain {
namespace cfl {

// A byte offset within an object. INT64_MIN means "any offset", for
// GEPs with non-constant indices and for displacements that leave the
// known shape of the object.
using Offset = int64_t;
constexpr Offset kAny = INT64_MIN;

// A call site id. The id is dense, assigned as the Builder walks the
// modules; it indexes a side table of CallBase pointers.
using CallSiteId = uint32_t;
constexpr CallSiteId kNoCall = 0;

// A node id in the graph. Dense uint32; nodes have two kinds (Value /
// Cell), the kind is stored on the node, not encoded in the id.
using NodeId = uint32_t;
constexpr NodeId kNoNode = 0;

// An object id. 0 is reserved for "outside"; subsequent ids are per
// allocation site (Alloca, Global, allocating-call, one per Function
// for code addresses).
using ObjectId = uint32_t;
constexpr ObjectId kOutside = 0;

// Node kind. Value nodes carry an LLVM Value*; Cell nodes carry (obj, off).
enum class NodeKind : uint8_t {
  Value = 0,  // SSA value or constant, pointer-typed
  Cell  = 1,  // memory cell (object, byte offset)
};

// Edge label. The automaton reads this plus the payload to transition
// its field stack and context stack.
enum class EdgeLabel : uint8_t {
  Assign  = 0,  // u <- v     : SSA copy (bitcast, phi, select arm, ...)
  Store   = 1,  // *(u + k) <- v : StoreInst value side -> cell
  Load    = 2,  // u <- *(v + k) : LoadInst cell -> result
  Gep     = 3,  // u = v + k     : constant GEP; non-const uses k = kAny
  Call    = 4,  // formal <- actual at call site c, arg i
  Return  = 5,  // call result <- return value at call site c
  Alloc   = 6,  // v <- &cell    : alloca/global/allocating-call/function
};

struct Edge {
  NodeId   dst   = kNoNode;
  EdgeLabel label = EdgeLabel::Assign;
  // Payload. Only one of these is meaningful per label:
  //   Store, Load, Gep -> field_off
  //   Call             -> call_site, arg_idx
  //   Return           -> call_site
  //   Assign, Alloc    -> none
  Offset      field_off = 0;
  CallSiteId  call_site = kNoCall;
  uint16_t    arg_idx   = 0;
};

// A directed graph. For each node, forward edges (outgoing) and backward
// edges (incoming) are stored separately; demand-driven queries walk
// backward from the query node.
class Graph {
public:
  Graph();

  // --- Node creation ---------------------------------------------------
  // Create or look up a Value node. Idempotent per Value*. Returns kNoNode
  // when v is null.
  NodeId valueNode(const llvm::Value *v);
  // Create or look up a Cell node for (obj, off). Idempotent per key.
  NodeId cellNode(ObjectId obj, Offset off);

  // --- Edge insertion --------------------------------------------------
  // Each insertion is deduplicated: two edges with the same (dst, label,
  // field_off, call_site, arg_idx) between the same src are stored once.
  // Returns true if the edge was new.
  bool addAssign(NodeId src, NodeId dst);
  bool addStore (NodeId src, NodeId dst, Offset field_off);
  bool addLoad  (NodeId src, NodeId dst, Offset field_off);
  bool addGep   (NodeId src, NodeId dst, Offset field_off);
  bool addCall  (NodeId src, NodeId dst, CallSiteId cs, uint16_t arg_idx);
  bool addReturn(NodeId src, NodeId dst, CallSiteId cs);
  bool addAlloc (NodeId src, NodeId dst);

  // --- Adjacency reads -------------------------------------------------
  // Edges leaving (forward) or arriving at (backward) a node. The result
  // reference is invalidated by any subsequent addEdge on the same node.
  const std::vector<Edge> &forward (NodeId n) const;
  const std::vector<Edge> &backward(NodeId n) const;

  // --- Node introspection ---------------------------------------------
  NodeKind kind(NodeId n) const { return nodes_[n].kind; }
  const llvm::Value *value(NodeId n) const {
    return nodes_[n].kind == NodeKind::Value ? nodes_[n].value : nullptr;
  }
  std::pair<ObjectId, Offset> cell(NodeId n) const {
    return nodes_[n].kind == NodeKind::Cell
             ? std::make_pair(nodes_[n].cell_obj, nodes_[n].cell_off)
             : std::make_pair(ObjectId{0}, Offset{0});
  }

  // --- Call site registry ---------------------------------------------
  // Every call site in either module gets a dense CallSiteId. The id is
  // assigned on first lookup. kNoCall (0) is reserved and does not
  // correspond to any instruction.
  CallSiteId registerCallSite(const llvm::CallBase *C);
  const llvm::CallBase *callSite(CallSiteId id) const {
    return id < call_sites_.size() ? call_sites_[id] : nullptr;
  }
  size_t numCallSites() const { return call_sites_.size(); }

  // --- Object registry -------------------------------------------------
  // Object id for a syntactic allocation site. Objects are:
  //   kOutside : one for all memory outside both modules
  //   Alloca   : one per AllocaInst
  //   Global   : one per GlobalVariable
  //   Alloc    : one per allocating CallBase (malloc, calloc, custom)
  //   Func     : one per Function (for code addresses)
  // The Builder decides when to create each; this registry is dense and
  // keyed by (kind-tagged pointer).
  enum class ObjectKind : uint8_t { Outside = 0, Alloca, Global, Alloc, Func };
  ObjectId registerObject(ObjectKind k, const llvm::Value *site);
  struct ObjectInfo {
    ObjectKind kind = ObjectKind::Outside;
    const llvm::Value *site = nullptr;
    // Static byte size when known; 0 means "unknown or dynamic".
    uint64_t size = 0;
  };
  const ObjectInfo &objectInfo(ObjectId o) const { return objects_[o]; }
  void setObjectSize(ObjectId o, uint64_t bytes);
  size_t numObjects() const { return objects_.size(); }

  // --- Statistics ------------------------------------------------------
  size_t numNodes() const { return nodes_.size(); }
  size_t numEdges() const { return num_edges_; }
  std::string stats() const;

  // --- Debug ----------------------------------------------------------
  // Human-readable one-line description of a node.
  std::string describe(NodeId n) const;

private:
  struct Node {
    NodeKind kind = NodeKind::Value;
    // For Value kind:
    const llvm::Value *value = nullptr;
    // For Cell kind:
    ObjectId cell_obj = 0;
    Offset   cell_off = 0;
  };

  // Dense node storage. Index 0 is reserved as kNoNode.
  std::vector<Node> nodes_;

  // Dense edge adjacency, per node.
  std::vector<std::vector<Edge>> fwd_;
  std::vector<std::vector<Edge>> bwd_;
  size_t num_edges_ = 0;

  // Value -> NodeId. One node per Value* (sharing across contexts; the
  // automaton tracks context on edges).
  llvm::DenseMap<const llvm::Value *, NodeId> value_node_;

  // (obj, off) -> NodeId. Offsets are stored as the actual byte offset
  // (or kAny).
  struct CellKey {
    ObjectId obj;
    Offset   off;
  };
  struct CellKeyHash {
    size_t operator()(const CellKey &k) const noexcept {
      return (static_cast<size_t>(k.obj) * 0x9e3779b97f4a7c15ULL) ^
             static_cast<size_t>(k.off);
    }
  };
  struct CellKeyEq {
    bool operator()(const CellKey &a, const CellKey &b) const noexcept {
      return a.obj == b.obj && a.off == b.off;
    }
  };
  std::unordered_map<CellKey, NodeId, CellKeyHash, CellKeyEq> cell_node_;

  // Call site registry.
  std::vector<const llvm::CallBase *> call_sites_;
  llvm::DenseMap<const llvm::CallBase *, CallSiteId> call_site_id_;

  // Object registry.
  std::vector<ObjectInfo> objects_;
  struct ObjKey {
    ObjectKind kind;
    const llvm::Value *site;
    bool operator==(const ObjKey &o) const noexcept {
      return kind == o.kind && site == o.site;
    }
  };
  struct ObjKeyHash {
    size_t operator()(const ObjKey &k) const noexcept {
      size_t h = static_cast<size_t>(k.kind);
      h ^= reinterpret_cast<uintptr_t>(k.site) + 0x9e3779b97f4a7c15ULL +
           (h << 6) + (h >> 2);
      return h;
    }
  };
  std::unordered_map<ObjKey, ObjectId, ObjKeyHash> object_id_;

  // Allocate a new node and return its id. Grows fwd_, bwd_ in parallel.
  NodeId newNode(const Node &n);
};

// Return the byte size of a type, or 0 when unknown.
uint64_t typeStoreSize(const llvm::DataLayout &DL, llvm::Type *T);

} // namespace cfl
} // namespace chain
