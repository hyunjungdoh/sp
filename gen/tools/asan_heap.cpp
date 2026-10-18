// The harness objects are the sizes the analysis already computed.
// malloc records that size in the ASan allocator, so a later copy or
// load past the object is an AddressSanitizer report.
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Bitcode/BitcodeWriter.h"

#include <vector>

using namespace llvm;

int main(int argc, char **argv) {
  if (argc != 3) {
    errs() << "usage: asan_heap <in.bc> <out.bc>\n";
    return 1;
  }
  LLVMContext ctx;
  SMDiagnostic err;
  std::unique_ptr<Module> m = parseIRFile(argv[1], err, ctx);
  if (!m) {
    err.print(argv[0], errs());
    return 1;
  }
  Function *mainFn = m->getFunction("main");
  if (!mainFn || mainFn->isDeclaration()) {
    errs() << "no main\n";
    return 1;
  }
  const DataLayout &DL = m->getDataLayout();
  Type *i64 = Type::getInt64Ty(ctx);
  FunctionCallee mallocFn = m->getOrInsertFunction(
      "malloc", PointerType::get(ctx, 0), i64);
  std::vector<AllocaInst *> allocas;
  for (Instruction &I : instructions(mainFn))
    if (auto *A = dyn_cast<AllocaInst>(&I))
      allocas.push_back(A);
  for (AllocaInst *A : allocas) {
    IRBuilder<> B(A);
    uint64_t el = DL.getTypeAllocSize(A->getAllocatedType());
    if (el == 0)
      el = 1;
    Value *n = A->getArraySize();
    Value *bytes = nullptr;
    if (auto *C = dyn_cast<ConstantInt>(n))
      bytes = ConstantInt::get(i64, C->getZExtValue() * el);
    else {
      Value *wide = n->getType()->isIntegerTy(64) ? n : B.CreateZExt(n, i64);
      bytes = B.CreateMul(wide, ConstantInt::get(i64, el));
    }
    CallInst *call = B.CreateCall(mallocFn, {bytes}, A->getName());
    A->replaceAllUsesWith(call);
    A->eraseFromParent();
  }
  if (verifyModule(*m, &errs()))
    return 1;
  std::error_code ec;
  raw_fd_ostream out(argv[2], ec);
  if (ec) {
    errs() << ec.message() << "\n";
    return 1;
  }
  WriteBitcodeToFile(*m, out);
  return 0;
}
