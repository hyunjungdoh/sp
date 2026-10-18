#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace gen {

// The analysis report, as written. An input is one export argument the
// use-def walk reduced a chop actual to. A cell is one sink-slice field.
// Its path is the sequence of (struct, constant byte offset) from a formal,
// the same sequence the analysis prints. A root names the export argument
// that reaches that field, then the call sequence, which this module does
// not replay.
struct Root {
  int arg = -1;
  std::string path;
  std::string func;
};

struct Cell {
  int64_t off = 0;
  int64_t len = -1;
  std::string path;
  std::vector<Root> roots;
};

struct Input {
  int chopArg = -1;
  int arg = -1;
  std::string func;
};

struct FileBytes {
  int arg = -1;
  int64_t len = 0;
  std::string func;
};

// An indirect call on the kept sequence. The driver stores `name` at path.
struct FnBind {
  int arg = -1;
  std::string path;
  std::string name;
  std::string func;
  // The cell holds the export argument's object.
  bool self = false;
};

struct GuardFix {
  int arg = -1;
  int otherArg = -1;
  unsigned pred = 32;
  int64_t len = 0;
  // Decimal integers of width `len` bytes.
  std::vector<std::string> vals;
  // When set, the predicate reads (cell & mask).
  std::string mask;
  std::string path;
  std::string otherPath;
  std::string func;
};

struct Report {
  std::vector<Input> inputs;
  std::vector<Cell> cells;
  std::vector<FileBytes> files;
  std::vector<GuardFix> guards;
  std::vector<FnBind> fns;
  std::string kept;
};

} // namespace gen
