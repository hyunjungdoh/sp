#pragma once

#include "gen/Report.hpp"

#include <string>

namespace gen {

// Reads one entry.txt. Lines other than input, cell, and root are not part
// of a driver: an open argument did not reduce, and a seq is the call
// sequence already present in the library.
Report loadReport(const std::string &path);

} // namespace gen
