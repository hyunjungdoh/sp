#pragma once

// CFL automaton for the points-to grammar in Graph.hpp.
//
//   Flows   -> Assign | Alloc
//   Assign  -> eps | Assign Assign | assign
//            | store_k Alias load_k
//            | gep_k   Assign gep_(-k)
//            | call_c  Assign ret_c
//   Alias   -> Flows Flows^{-1}
//
// The language is context-free: `store_k Alias load_k`, `gep_k ... gep_{-k}`
// and `call_c ... ret_c` form matched brackets. The straight CFL walk
// therefore needs two stacks: one for field offsets, one for call-site
// contexts. In practice we drive the walk by a pair of partial
// derivations plus an edge direction (backward from the query).
//
// The automaton we expose below is a *configuration transition*:
//
//     Config = {direction, fieldStack, ctxStack, derivation}
//     step(Config, EdgeLabel, payload) -> {Config'} ∪ accept|reject
//
// The query engine (Query.cpp) does the actual tabling and worklist; this
// file just encodes the valid transitions and the acceptance test. By
// keeping the automaton small and allocation-free, the solver can call
// it tens of millions of times without pressure.

#include "Graph.hpp"

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace chain {
namespace cfl {

// Direction of the walk. The query starts with Backward (we want to find
// what points to the query node). When a `store_k` is popped, we flip to
// Forward through the Alias phase, then flip back to Backward on the
// matching `load_k`. Similarly for Flows^{-1} inside Alias.
enum class Direction : uint8_t { Backward = 0, Forward = 1 };

// Which part of the grammar the walk is currently in. The derivation
// controls what matched brackets are expected and what the acceptance
// test looks for.
enum class Derivation : uint8_t {
  Flows   = 0,  // outer: expecting Assign or Alloc, accept at a Cell
  Alias   = 1,  // inside store/load match: Flows Flows^{-1}
  AliasFwd = 2, // the Flows^{-1} half of Alias
};

// A single pending bracket on one of the two stacks. Field brackets are
// keyed by signed offset; call-site brackets by CallSiteId.
struct FieldFrame {
  Offset off = 0;
};
struct CtxFrame {
  CallSiteId cs = kNoCall;
};

// Full automaton configuration. Field and context stacks are small in
// practice (the grammar matches brackets in LIFO order, so depth equals
// the depth of nesting the walk has entered). For the query engine we
// hash and compare entire configurations.
struct Config {
  Direction  dir   = Direction::Backward;
  Derivation deriv = Derivation::Flows;
  std::vector<FieldFrame> fields;
  std::vector<CtxFrame>   ctxs;

  bool operator==(const Config &o) const {
    if (dir != o.dir || deriv != o.deriv)
      return false;
    if (fields.size() != o.fields.size() || ctxs.size() != o.ctxs.size())
      return false;
    for (size_t i = 0; i < fields.size(); ++i)
      if (fields[i].off != o.fields[i].off)
        return false;
    for (size_t i = 0; i < ctxs.size(); ++i)
      if (ctxs[i].cs != o.ctxs[i].cs)
        return false;
    return true;
  }
};

struct ConfigHash {
  size_t operator()(const Config &c) const noexcept {
    size_t h = (static_cast<size_t>(c.dir) << 1) ^ static_cast<size_t>(c.deriv);
    for (const FieldFrame &f : c.fields) {
      h ^= static_cast<size_t>(f.off) + 0x9e3779b97f4a7c15ULL +
           (h << 6) + (h >> 2);
    }
    for (const CtxFrame &x : c.ctxs) {
      h ^= static_cast<size_t>(x.cs) + 0x517cc1b727220a95ULL +
           (h << 6) + (h >> 2);
    }
    return h;
  }
};

// Transition result: zero, one, or several successor configs.
// A result of {} means the edge is rejected under this configuration.
using Transitions = std::vector<Config>;

// Apply one edge to a configuration and return the valid successors.
//
// Semantics (backward walk, Flows derivation):
//   backward over Assign       : stay in Flows
//   backward over Alloc        : accept if dst node is a Cell
//   backward over Store_k      : enter Alias(Backward Flows then Forward Flows^{-1})
//                                 push field k
//   backward over Load_k       : only valid if currently matching an Alias
//   backward over Gep_k        : push shift k (positive); matched by later gep_{-k}
//   backward over Call_c (arg) : push context c; stays in Flows
//   backward over Return_c     : push context c; stays in Flows but flips direction? no --
//                                 Return edges go from the ReturnInst value to the
//                                 CallBase result, so backward over Return pushes
//                                 context into the callee body
//
// The actual table is in Automaton.cpp. Returning multiple successors
// handles the case where more than one derivation is valid for the same
// edge (rare; e.g. an Assign in the Alias Flows^{-1} phase).
Transitions step(const Config &from,
                 EdgeLabel label,
                 Offset field_off,
                 CallSiteId call_site,
                 bool dst_is_cell);

// The starting configuration for a points-to query of a Value node.
// We walk backward from the query (we want to know what the query may
// point to), starting empty and in the Flows derivation.
Config initialConfig();

// Whether a configuration, having just reached a Cell node by backward
// Alloc, is accepting. For a straight points-to query the answer is:
// yes, if the field and context stacks are empty (fully balanced) and
// the derivation is Flows.
bool isAccepting(const Config &c);

// Debug / logging.
std::string show(const Config &c);
std::string show(EdgeLabel l);

} // namespace cfl
} // namespace chain
