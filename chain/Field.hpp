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
// sequence from that export through the chop stays a separate fact.
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
