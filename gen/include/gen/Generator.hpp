#pragma once

#include "gen/Emit.hpp"

#include <string>
#include <vector>

namespace gen {

// Loads the report, builds one driver per export, and writes that driver's
// bitcode. An export the bitcode does not define is recorded with an empty
// file. The manifest lists every driver in the same order.
struct Generated {
  std::string func;
  std::string irName;
  std::string file;
  std::vector<int> args;
  int ranges = 0;
};

// upstreamPath, when set, is linked with the downstream bitcode into each
// driver so the export's call enters the library body that reaches the sink.
std::vector<Generated> generate(const std::string &reportPath, const std::string &bitcodePath,
                                const std::string &outDir, const std::string &upstreamPath = {});

} // namespace gen
