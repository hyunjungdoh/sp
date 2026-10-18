#include "gen/Generator.hpp"

#include "llvm/Support/raw_ostream.h"

#include <filesystem>

int main(int argc, char **argv) {
  if (argc != 4 && argc != 5) {
    llvm::errs() << "usage: gen <entry.txt> <downstream.bc> <out-dir> [upstream.bc]\n";
    return 1;
  }
  if (!std::filesystem::is_regular_file(argv[1]) || !std::filesystem::is_regular_file(argv[2])) {
    llvm::errs() << "missing report or bitcode\n";
    return 1;
  }
  std::string upstream = argc == 5 ? argv[4] : "";
  if (!upstream.empty() && !std::filesystem::is_regular_file(upstream)) {
    llvm::errs() << "missing upstream bitcode\n";
    return 1;
  }
  auto written = gen::generate(argv[1], argv[2], argv[3], upstream);
  if (written.empty()) {
    llvm::errs() << "no driver\n";
    return 1;
  }
  for (const gen::Generated &g : written) {
    llvm::outs() << g.func;
    if (g.file.empty())
      llvm::outs() << " missing\n";
    else
      llvm::outs() << " " << g.file << "\n";
  }
  return 0;
}
