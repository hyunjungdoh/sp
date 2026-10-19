#pragma once

#include "gen/Driver.hpp"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace llvm {
class Module;
}

namespace gen {

// A byte range inside one allocated object.
struct Range {
  int64_t off = 0;
  int64_t len = 0;
};

// A pointer field. choice is the boundary join: the slot holds the child
// when a symbolic bit is true, and the bytes of this object when it is false.
struct Edge {
  int64_t at = 0;
  int child = -1;
  bool choice = false;
};

// One allocated object. An edge is a pointer field: the child is a separate
// allocation stored at that byte offset. A range is a sink-slice field of
// this object.
struct Object {
  std::string type;
  uint64_t size = 0;
  uint64_t align = 1;
  std::vector<Range> ranges;
  std::vector<Edge> edges;
  // Concrete integer stored at a byte offset after the symbolic ranges.
  // A string's length word is the size of the buffer its pointer denotes.
  std::vector<std::pair<int64_t, uint64_t>> words;
  // A determined branch constant, stored after the symbolic ranges.
  struct Pin {
    int64_t off = 0;
    std::string val;
    uint64_t bytes = 0;
  };
  std::vector<Pin> pins;
  // A predicate on the bytes at off. pred 32 with several values is a disjunction.
  struct Assume {
    int64_t off = 0;
    // otherAlloc >= 0 compares this load with the load at otherOff of that object.
    int otherAlloc = -1;
    int64_t otherOff = -1;
    // otherArg >= 0 compares this load with that integer argument.
    int otherArg = -1;
    uint64_t bytes = 0;
    unsigned pred = 0;
    std::vector<std::string> vals;
    std::string mask;
  };
  std::vector<Assume> assumes;
  // A function pointer stored at a byte offset. The indirect call loads it.
  struct FnPtr {
    int64_t at = 0;
    std::string name;
  };
  std::vector<FnPtr> fns;
  // A field that holds the root object of this shape.
  std::vector<int64_t> backs;
};

// One may-object of an argument. The analysis roots several structs at one
// formal; each struct is one shape, and the driver chooses among them.
struct Shape {
  std::vector<Object> objects;
  int root = 0;
};

struct PlacedArg {
  int index = -1;
  int dropped = 0;
  std::vector<Shape> shapes;
};

struct Placed {
  std::string func;
  std::vector<PlacedArg> args;
  // file is set when this export opens a file. fileBytes is the largest
  // constant read. Zero with file set means the read count is not a constant.
  bool file = false;
  int fileArg = -1;
  int64_t fileBytes = 0;
};

// A boundary step (neu) is a new object stored at the previous step's offset.
// A step without that boundary stays in the same allocation, and its offset
// is added to the current base. The last step's length is the symbolic
// range. The struct layout supplies the object's size when the bitcode has
// that struct.
std::vector<Placed> placeAll(const std::vector<Driver> &drivers, llvm::Module &library,
                             llvm::Module *upstream = nullptr);

} // namespace gen
