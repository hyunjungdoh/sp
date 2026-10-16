#pragma once

#include "Entry.hpp"

#include <string>
#include <unordered_map>
#include <vector>

namespace llvm {
class Module;
}

namespace chain {

// Least fixpoint of access paths. A path is a sequence of (struct, constant
// byte offset). A struct keeps one id for its name; a loader suffix .N is
// the same id when the unsuffixed name exists and the field count matches.
// The same struct on a path collapses that step to Any and
// does not grow past it. A call result is the callee return path concatenated
// onto the actual argument. A pointer call that yields no return path keeps
// each argument path plus Any. A declaration does the same.
// The sink slice is the least set of field keys and formals that contains the
// sink instruction's operands. A sliced formal is replaced by the actual at
// each direct call and by the actual at an indirect call whose callee key
// holds that function. A write of a sliced key adds the stored value's keys.
// A function stored at a sliced key joins the slice through that call's actuals.
// An indirect call of type τ targets only functions of type τ stored at the
// same sequence of struct fields. A function passed in a formal is stored
// with the access path of the object that formal points to, and a later
// call sees it only on that path. An unnamed global whose layout equals a
// named struct is that named struct's field. An export argument whose
// declared type, after peeling pointer, reference, and typedef, is a
// string or string_view labels only fields of that string. The call
// sequence is a path in the resolved call graph from that export to the
// sink function, and it ends at the sink. Use-def selects the export and
// the chop; it does not insert an edge. Among the paths that reach one
// sink state, the walk keeps the shortest. Call sites of one function are
// tried in instruction order, and the may-targets of one site are tried in
// demangled-name order, so that shortest path is the first one in that
// order. The same rule picks each return to the export and the path from
// the chop that reaches the sink again after a function repeats. The path
// from the export back to a field writer is the shortest path in the caller
// graph under that same order. A value that denotes several slot chains
// contributes every chain to a call's target set. The one chain copied onto
// a callee as the object's identity is the lexicographically smallest,
// read as the sequence of (type name, byte offset). An unnamed struct is
// that sequence's name by its layout, not by the id assigned when it was
// first seen. Bodies that share an IR name are one function, and the path
// kept for a field of that function is the shortest path to any of them.
// Users of one value are
// walked in instruction order. An argument is the pair (function, index).
// A hash of its address is not its identity. A call
// whose operand may denote several formals targets the functions passed as
// any of them. The slots of a value in a context are the union of its
// operands' slots. A cycle adds nothing, and a finished pair is reused by
// every caller. A phi or select is that union.
// A function-pointer slot drops a byte-0 step only when that field's type
// is the struct the next step indexes. A function stored at a constant
// index of a global pointer array is a target of a call that loads that
// index from an object of the same size, including a base embedded at byte 0.
// A struct of pointers is an object, and its fields stay labeled.
// A phi takes the deps of the branch conditions that select its incoming edges.
// A store takes the deps of the branch conditions its block is control-dependent on.
// A struct whose fields are all pointers is not a path step.
// A sliced write is emitted when the address formal, or a formal the stored
// value depends on, reaches an input. One way substitutes that formal with
// the actual's formals at each caller. The other starts from a chop formal
// that use-def already roots at an input, and passes that formal on to a
// callee only when the actual is that formal. A load of a field takes the
// formals of the value stored at that field of the same formal. A call
// result takes the formals named by the callee return summary. Each function
// records that field K of formal j came from formal i. A callee that is
// passed that object and loads field K takes i, through the actual. One call
// sequence is kept for each reached input. The same struct on a path still
// collapses to Any.
struct FieldReport {
  std::vector<Cell> cells;
  // One call sequence from an export argument through the chop. No field.
  std::vector<std::string> seqs;
};

FieldReport fieldCells(llvm::Module &downstream, llvm::Module &upstream, const std::string &sinkFile,
                       unsigned sinkLine, const std::vector<std::string> &sinkFns,
                       const std::vector<std::string> &chops,
                       const std::unordered_map<std::string, std::vector<Input>> &inputs);

} // namespace chain
