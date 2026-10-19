#pragma once

#include "gen/Report.hpp"

#include <cstdint>
#include <string>
#include <vector>

namespace gen {

// One step of an access path: the struct the analysis indexed, and the
// constant byte offset of that gep. An any offset is not one constant, so
// the step is the whole object.
struct Step {
  std::string type;
  int64_t off = 0;
  // True when this step indexes a pointer loaded from the previous step.
  bool neu = false;
  // True when the step was reached both as a load and as an address.
  // Placement keeps both layouts in one object. A symbolic bit selects the
  // pointer to the child or the bytes of the parent.
  bool both = false;
  // True when the offset is not one constant. That step is not a cell.
  bool any = false;
};

// One sink-slice field rooted at an export argument. steps[0] is the object
// the argument denotes. Each later step is a gep on the preceding step.
// The path's argN prefix is the formal of the function that wrote the cell.
// The root's pass index is the export argument that formal was lifted to,
// and the field is placed on that argument.
struct Field {
  std::vector<Step> steps;
  int64_t len = 0;
  // A single EQ value is stored after the symbolic range.
  bool pin = false;
  // Decimal integer of width `len` bytes.
  std::string pinVal;
  // Any other predicate is assumed on the load of those bytes.
  // pred 32 with several values is a disjunction of equalities.
  unsigned assumePred = 0;
  std::vector<std::string> assumeVals;
  // When set, the predicate reads (cell & mask).
  std::string mask;
  // When set, this field is that function, not a symbolic range.
  std::string fn;
  // The cell holds the object this argument denotes.
  bool self = false;
};

// The symbolic arguments of one export. Two chops that name the same index
// are one argument. The fields are the cells whose root is this export and
// this index.
struct Argument {
  int index = -1;
  std::vector<Field> fields;
};

// One driver. The library already contains the call sequence from this
// export to the sink, so the driver calls the export once.
// A predicate whose operands are two access paths of one export.
struct Rel {
  int arg = -1;
  int otherArg = -1;
  unsigned pred = 0;
  int64_t len = 0;
  std::vector<Step> left;
  std::vector<Step> right;
};

struct Driver {
  std::string func;
  std::vector<Argument> args;
  std::vector<Rel> rels;
  // True when an export argument is the path of a file the kept sequence reads.
  // fileBytes is the largest constant count among those reads. Zero means the
  // count is not a constant; the runtime fills each concrete read.
  bool file = false;
  int fileArg = -1;
  int64_t fileBytes = 0;
};

// One driver per export that an input line names, in the order of the
// export's demangled name.
std::vector<Driver> driversOf(const Report &report);

} // namespace gen
