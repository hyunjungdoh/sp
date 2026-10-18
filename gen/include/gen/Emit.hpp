#pragma once

#include "gen/Place.hpp"

#include <string>

namespace llvm {
class Module;
}

namespace gen {

// A driver bitcode declares the export and defines main. For each symbolic
// pointer argument, main allocates one object per shape the placement
// produced. A shape with several structs stores the child at the pointer
// field that reached it. Each sink-slice range of an object is a call to
// klee_make_symbolic. Several shapes of one argument are a symbolic choice
// of which object the argument denotes. A pointer argument with no placed
// field is a symbolic pointer. A non-pointer argument is a symbolic value
// of its type. Every other parameter is zero.
struct Emitted {
  std::string irName;
  std::string file;
};

// `upstream` is the other module linked into the same program. A function
// the witness names is stored whether its body is in the downstream module
// or in that one.
Emitted emitDriver(const Placed &placed, llvm::Module &library, const std::string &outDir,
                   llvm::Module *upstream = nullptr);

} // namespace gen
