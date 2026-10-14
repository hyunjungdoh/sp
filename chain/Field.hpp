#pragma once

#include "Entry.hpp"

#include <string>
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
// A phi takes the deps of the branch conditions that select its incoming edges.
// A store takes the deps of the branch conditions its block is control-dependent on.
std::vector<Cell> fieldCells(llvm::Module &downstream, llvm::Module &upstream, const std::string &sinkFile,
                             unsigned sinkLine, const std::vector<std::string> &sinkFns);

} // namespace chain
