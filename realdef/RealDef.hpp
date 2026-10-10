#pragma once

#include <string>
#include <vector>

namespace llvm {
class Module;
}

namespace realdef {

/// Where a sink use is first written.
/// `at` is the store (or call, or constant) that creates the value the sink
/// reads. Copies — a later load of that same value — are not defs.
struct Def {
  std::string func;
  std::string file;
  unsigned line = 0;
  std::string kind;
};

struct UseDef {
  std::string use;
  std::vector<Def> defs;
};

/// Defs of the memory values read at `file:line` in `M`.
/// A def is the store that puts the value into the object the sink loads.
/// A store of a load is a copy and is followed. A store of a new value stops.
/// `downstream`, when present, is only used to see which upstream return
/// (or out-parameter) is passed into a later upstream argument. Its body
/// is not part of the points-to fixpoint. A slot the application can write
/// — a global it can name, an argument it passes, or an object it hands in —
/// has an external def beside the library stores. A direct call exposes the
/// arguments of that upstream function. An indirect call whose target does
/// not reduce exposes the objects passed at that call. A slot that reaches
/// none of those has only the library stores. An object that does not reduce
/// is not proved unreachable, so the external def stays.
std::vector<UseDef> findDefs(llvm::Module &M, const std::string &file, unsigned line,
                             llvm::Module *downstream = nullptr);

}
