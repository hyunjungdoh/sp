#include "RealDef.hpp"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
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
    } else if (s.rfind("Line:", 0) == 0) {
      line = (unsigned)std::stoul(s.substr(5));
    }
  }
  return !file.empty() && line != 0;
}

static int runOne(const fs::path &bc, const std::string &file, unsigned line) {
  llvm::LLVMContext ctx;
  llvm::SMDiagnostic err;
  auto M = llvm::parseIRFile(bc.string(), err, ctx);
  if (!M) {
    err.print("realdef", llvm::errs());
    return 1;
  }
  std::unique_ptr<llvm::Module> ds;
  auto dsPath = bc.parent_path() / "se_lib" / "downstream.closure.bc";
  if (fs::exists(dsPath)) {
    llvm::SMDiagnostic dsErr;
    ds = llvm::parseIRFile(dsPath.string(), dsErr, ctx);
  }
  auto defs = realdef::findDefs(*M, file, line, ds.get());
  if (defs.empty()) {
    llvm::outs() << "  (no memory use on this line)\n";
    return 0;
  }
  for (const auto &u : defs) {
    llvm::outs() << "  use " << u.use << "\n";
    if (u.defs.empty())
      llvm::outs() << "    def (none in module)\n";
    for (const auto &d : u.defs) {
      llvm::outs() << "    def " << d.kind << " " << d.func;
      if (!d.file.empty())
        llvm::outs() << " " << d.file << ":" << d.line;
      if (d.arg >= 0)
        llvm::outs() << " arg " << d.arg;
      llvm::outs() << "\n";
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 4)
    return runOne(argv[1], argv[2], (unsigned)std::stoul(argv[3]));
  if (argc != 2) {
    llvm::errs() << "usage: realdef <upstream.bc> <file> <line>\n"
                 << "       realdef <dataset-dir>\n";
    return 1;
  }
  int rc = 0;
  for (const auto &ent : fs::directory_iterator(argv[1])) {
    if (!ent.is_directory())
      continue;
    auto bc = ent.path() / "upstream.bc";
    auto yaml = ent.path() / "sink.yaml";
    if (!fs::exists(bc) || !fs::exists(yaml))
      continue;
    std::string file;
    unsigned line = 0;
    if (!loadSink(yaml, file, line))
      continue;
    llvm::outs() << ent.path().filename().string() << " " << file << ":" << line << "\n";
    rc |= runOne(bc, file, line);
  }
  return rc;
}
