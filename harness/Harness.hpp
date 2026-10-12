#pragma once

#include "Entry.hpp"
#include "RealDef.hpp"

#include <string>
#include <vector>

namespace harness {

// One formula for one initial state of one chop.
// The initial state is a maximal strong export: the query calls that one
// function, and the bytes it chooses are that function's parameters that
// reach the chop. When the sink names a parameter of the chop, only the
// inputs that reach that parameter stay. An input is a root of the chop
// actual. An open line is an actual of that same export that did not
// reduce. A global stays only when no parameter of the export is a root of
// that actual. Writes are the stores and initializers of the sink. They
// name the object. They do not prove that the loaded value is the entry
// byte. A chop that no entry reaches is not a query.
struct Spec {
  std::string chop;
  std::vector<std::string> calls;
  std::vector<realdef::Def> symbolic;
  std::vector<realdef::Def> writes;
  std::vector<std::string> uses;
};

std::vector<Spec> specs(const std::vector<chain::EntryGroup> &groups,
                        const std::vector<realdef::UseDef> &uses);

std::vector<chain::EntryGroup> loadEntries(const std::string &text);
std::vector<realdef::UseDef> loadDefs(const std::string &text);

std::string format(const std::vector<Spec> &out);

} // namespace harness
