#include "Graph.hpp"

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Type.h"

#include <sstream>

namespace chain {
namespace cfl {

uint64_t typeStoreSize(const llvm::DataLayout &DL, llvm::Type *T) {
  if (!T || !T->isSized())
    return 0;
  llvm::TypeSize s = DL.getTypeStoreSize(T);
  if (s.isScalable())
    return 0;
  return s.getFixedValue();
}

Graph::Graph() {
  // Index 0 reserved as kNoNode. Push a dummy so real nodes start at 1.
  nodes_.emplace_back();
  fwd_.emplace_back();
  bwd_.emplace_back();
  // Call site 0 reserved as kNoCall.
  call_sites_.push_back(nullptr);
  // Object 0 reserved as kOutside.
  ObjectInfo info;
  info.kind = ObjectKind::Outside;
  info.site = nullptr;
  info.size = 0;
  objects_.push_back(info);
}

NodeId Graph::newNode(const Node &n) {
  const NodeId id = static_cast<NodeId>(nodes_.size());
  nodes_.push_back(n);
  fwd_.emplace_back();
  bwd_.emplace_back();
  return id;
}

NodeId Graph::valueNode(const llvm::Value *v) {
  if (!v)
    return kNoNode;
  auto it = value_node_.find(v);
  if (it != value_node_.end())
    return it->second;
  Node n;
  n.kind = NodeKind::Value;
  n.value = v;
  const NodeId id = newNode(n);
  value_node_[v] = id;
  return id;
}

NodeId Graph::cellNode(ObjectId obj, Offset off) {
  CellKey key{obj, off};
  auto it = cell_node_.find(key);
  if (it != cell_node_.end())
    return it->second;
  Node n;
  n.kind = NodeKind::Cell;
  n.cell_obj = obj;
  n.cell_off = off;
  const NodeId id = newNode(n);
  cell_node_[key] = id;
  return id;
}

CallSiteId Graph::registerCallSite(const llvm::CallBase *C) {
  if (!C)
    return kNoCall;
  auto it = call_site_id_.find(C);
  if (it != call_site_id_.end())
    return it->second;
  const CallSiteId id = static_cast<CallSiteId>(call_sites_.size());
  call_sites_.push_back(C);
  call_site_id_[C] = id;
  return id;
}

ObjectId Graph::registerObject(Graph::ObjectKind k, const llvm::Value *site) {
  ObjKey key{k, site};
  auto it = object_id_.find(key);
  if (it != object_id_.end())
    return it->second;
  ObjectInfo info;
  info.kind = k;
  info.site = site;
  info.size = 0;
  const ObjectId id = static_cast<ObjectId>(objects_.size());
  objects_.push_back(info);
  object_id_[key] = id;
  return id;
}

void Graph::setObjectSize(ObjectId o, uint64_t bytes) {
  if (o < objects_.size())
    objects_[o].size = bytes;
}

// Edge deduplication is per (src, label, payload). The adjacency list for a
// node is kept short in practice; a linear scan is cheap and avoids the
// memory cost of a hash set per node.
static bool sameEdge(const Edge &a, const Edge &b) {
  if (a.dst != b.dst || a.label != b.label)
    return false;
  switch (a.label) {
    case EdgeLabel::Assign:
    case EdgeLabel::Alloc:
      return true;
    case EdgeLabel::Store:
    case EdgeLabel::Load:
    case EdgeLabel::Gep:
      return a.field_off == b.field_off;
    case EdgeLabel::Call:
      return a.call_site == b.call_site && a.arg_idx == b.arg_idx;
    case EdgeLabel::Return:
      return a.call_site == b.call_site;
  }
  return false;
}

static bool addEdgeTo(std::vector<Edge> &adj, const Edge &e) {
  for (const Edge &x : adj)
    if (sameEdge(x, e))
      return false;
  adj.push_back(e);
  return true;
}

bool Graph::addAssign(NodeId src, NodeId dst) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Assign;
  Edge b; b.dst = src; b.label = EdgeLabel::Assign;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addStore(NodeId src, NodeId dst, Offset field_off) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Store; f.field_off = field_off;
  Edge b; b.dst = src; b.label = EdgeLabel::Store; b.field_off = field_off;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addLoad(NodeId src, NodeId dst, Offset field_off) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Load; f.field_off = field_off;
  Edge b; b.dst = src; b.label = EdgeLabel::Load; b.field_off = field_off;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addGep(NodeId src, NodeId dst, Offset field_off) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Gep; f.field_off = field_off;
  Edge b; b.dst = src; b.label = EdgeLabel::Gep; b.field_off = field_off;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addCall(NodeId src, NodeId dst, CallSiteId cs, uint16_t arg_idx) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Call; f.call_site = cs; f.arg_idx = arg_idx;
  Edge b; b.dst = src; b.label = EdgeLabel::Call; b.call_site = cs; b.arg_idx = arg_idx;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addReturn(NodeId src, NodeId dst, CallSiteId cs) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Return; f.call_site = cs;
  Edge b; b.dst = src; b.label = EdgeLabel::Return; b.call_site = cs;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

bool Graph::addAlloc(NodeId src, NodeId dst) {
  if (!src || !dst)
    return false;
  Edge f; f.dst = dst; f.label = EdgeLabel::Alloc;
  Edge b; b.dst = src; b.label = EdgeLabel::Alloc;
  if (!addEdgeTo(fwd_[src], f))
    return false;
  addEdgeTo(bwd_[dst], b);
  ++num_edges_;
  return true;
}

const std::vector<Edge> &Graph::forward(NodeId n) const {
  return fwd_[n];
}

const std::vector<Edge> &Graph::backward(NodeId n) const {
  return bwd_[n];
}

std::string Graph::stats() const {
  std::ostringstream o;
  o << "nodes=" << (nodes_.size() - 1)      // minus the kNoNode slot
    << " edges=" << num_edges_
    << " callsites=" << (call_sites_.size() - 1)
    << " objects=" << (objects_.size() - 1);
  return o.str();
}

std::string Graph::describe(NodeId n) const {
  if (n == kNoNode || n >= nodes_.size())
    return "<none>";
  const Node &nd = nodes_[n];
  std::ostringstream o;
  o << "#" << n << " ";
  if (nd.kind == NodeKind::Value) {
    o << "V(";
    if (nd.value && nd.value->hasName())
      o << nd.value->getName().str();
    else
      o << static_cast<const void *>(nd.value);
    o << ")";
  } else {
    o << "C(obj=" << nd.cell_obj << ",off=";
    if (nd.cell_off == kAny)
      o << "ANY";
    else
      o << nd.cell_off;
    o << ")";
  }
  return o.str();
}

} // namespace cfl
} // namespace chain
