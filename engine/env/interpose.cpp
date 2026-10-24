// interpose IN OUT NAMES: IN with each symbol listed in NAMES (one per line)
// turned from a definition into a declaration, so that references to it bind
// to the definition an earlier module provides (ELF interposition).
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <string>
#include <vector>

using namespace llvm;

int main(int argc, char **argv) {
  if (argc != 4) {
    errs() << "usage: interpose IN OUT NAMES\n";
    return 2;
  }
  LLVMContext ctx;
  auto buf = MemoryBuffer::getFile(argv[1]);
  if (!buf) {
    errs() << argv[1] << ": " << buf.getError().message() << "\n";
    return 1;
  }
  auto mod = parseBitcodeFile(**buf, ctx);
  if (!mod) {
    errs() << argv[1] << ": " << toString(mod.takeError()) << "\n";
    return 1;
  }
  Module &M = **mod;
  std::ifstream names(argv[3]);
  std::vector<GlobalAlias *> aliases;
  for (std::string n; std::getline(names, n);) {
    GlobalValue *G = M.getNamedValue(n);
    if (!G || G->isDeclaration())
      continue;
    if (auto *F = dyn_cast<Function>(G)) {
      F->deleteBody();
      F->setComdat(nullptr);
    } else if (auto *V = dyn_cast<GlobalVariable>(G)) {
      V->setInitializer(nullptr);
      V->setLinkage(GlobalValue::ExternalLinkage);
      V->setComdat(nullptr);
    } else if (auto *A = dyn_cast<GlobalAlias>(G)) {
      aliases.push_back(A);
    }
  }
  for (GlobalAlias *A : aliases) {
    std::string n = A->getName().str();
    A->setName("");
    GlobalValue *D;
    if (auto *FT = dyn_cast<FunctionType>(A->getValueType()))
      D = Function::Create(FT, GlobalValue::ExternalLinkage, n, &M);
    else
      D = new GlobalVariable(M, A->getValueType(), false, GlobalValue::ExternalLinkage, nullptr, n);
    A->replaceAllUsesWith(D);
    A->eraseFromParent();
  }
  std::error_code ec;
  raw_fd_ostream out(argv[2], ec);
  if (ec) {
    errs() << argv[2] << ": " << ec.message() << "\n";
    return 1;
  }
  WriteBitcodeToFile(M, out);
  return 0;
}
