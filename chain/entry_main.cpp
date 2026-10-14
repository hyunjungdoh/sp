#include "Chop.hpp"
#include "Entry.hpp"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <filesystem>
#include <fstream>
#include <string>

namespace fs = std::filesystem;

static bool loadSink(const fs::path &yaml, std::string &file, unsigned &line) {
  std::ifstream in(yaml);
  std::string s;
  file.clear();
  line = 0;
  while (std::getline(in, s)) {
    auto pos = s.find_first_not_of(" \t");
    if (pos == std::string::npos)
      continue;
    s = s.substr(pos);
    if (s.rfind("File:", 0) == 0) {
      auto v = s.substr(5);
      auto b = v.find_first_not_of(" \t");
      file = b == std::string::npos ? "" : v.substr(b);
    } else if (s.rfind("Line:", 0) == 0)
      line = (unsigned)std::stoul(s.substr(5));
  }
  return !file.empty() && line != 0;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    llvm::errs() << "usage: entry <cve-dir> <out-dir>\n";
    return 1;
  }
  fs::path dir = argv[1];
  fs::path outDir = argv[2];
  auto bc = dir / "upstream.bc";
  auto dsPath = dir / "se_lib" / "downstream.closure.bc";
  auto yaml = dir / "sink.yaml";
  std::string file;
  unsigned line = 0;
  if (!fs::exists(bc) || !fs::exists(dsPath) || !loadSink(yaml, file, line)) {
    llvm::errs() << "missing bitcode or sink in " << dir << "\n";
    return 1;
  }
  llvm::LLVMContext ctx;
  llvm::SMDiagnostic err;
  auto upstream = llvm::parseIRFile(bc.string(), err, ctx);
  if (!upstream) {
    err.print("entry", llvm::errs());
    return 1;
  }
  llvm::SMDiagnostic dsErr;
  auto downstream = llvm::parseIRFile(dsPath.string(), dsErr, ctx);
  if (!downstream) {
    dsErr.print("entry", llvm::errs());
    return 1;
  }
  auto chop = chain::findChops(*upstream, *downstream, file, line);
  auto groups = chain::findEntries(*downstream, *upstream, chop.chops, chop.sinkFile, chop.sinkLine,
                                   chop.sinkFns);
  std::string text = chain::formatEntries(chop, groups);
  fs::create_directories(outDir);
  std::ofstream out(outDir / "entry.txt");
  out << text;
  llvm::outs() << dir.filename().string() << "\n" << text;
  return 0;
}
