#include "Points.hpp"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

#include <cstdio>

int main() {
  llvm::LLVMContext ctx;
  llvm::Module M("m", ctx);
  llvm::Module U("u", ctx);
  auto *ptr = llvm::PointerType::get(ctx, 0);
  auto *fnty = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), {ptr}, false);
  auto *F = llvm::Function::Create(fnty, llvm::Function::ExternalLinkage, "f", &M);
  auto *BB = llvm::BasicBlock::Create(ctx, "e", F);
  llvm::IRBuilder<> b(BB);
  auto *slot = b.CreateAlloca(ptr, nullptr, "slot");
  b.CreateStore(F->getArg(0), slot);
  auto *ld = b.CreateLoad(ptr, slot, "ld");
  b.CreateRetVoid();

  chain::Points::Hooks h;
  chain::Points P(M, U, std::move(h));
  const auto &pts = P.of(slot);
  std::printf("of(slot) count=%u\n", pts.count());
  if (pts.count() == 0) {
    std::printf("FAIL empty of(slot)\n");
    return 1;
  }
  unsigned id = *pts.begin();
  auto loc = P.loc(id);
  std::printf("loc obj=%u off=%lld kind=%d\n", loc.obj, (long long)loc.off, (int)P.obj(loc.obj).kind);
  const auto &ws = P.writes(loc.obj);
  std::printf("writes=%zu\n", ws.size());
  for (const auto &w : ws)
    std::printf("  write off=%lld len=%lld\n", (long long)w.off, (long long)w.len);
  const auto &lp = P.of(ld);
  std::printf("of(load) count=%u\n", lp.count());
  const auto &ap = P.of(F->getArg(0));
  std::printf("of(arg) count=%u harness-free\n", ap.count());
  if (ws.empty()) {
    std::printf("FAIL no writes\n");
    return 1;
  }

  // A store of a function through one harness formal and a call through
  // another must meet: both formals contain the harness object, and the
  // store solves its address, so the call is a caller.
  llvm::LLVMContext ctx2;
  llvm::Module M2("m2", ctx2);
  llvm::Module U2("u2", ctx2);
  auto *ptr2 = llvm::PointerType::get(ctx2, 0);
  auto *st = llvm::StructType::create(ctx2, {ptr2, ptr2}, "S");
  auto *cbTy = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx2), {ptr2}, false);
  auto *cb = llvm::Function::Create(cbTy, llvm::Function::InternalLinkage, "cb", &M2);
  llvm::IRBuilder<> cbB(llvm::BasicBlock::Create(ctx2, "e", cb));
  cbB.CreateRetVoid();
  auto *init = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx2), {ptr2}, false),
      llvm::Function::ExternalLinkage, "init", &M2);
  llvm::IRBuilder<> ib(llvm::BasicBlock::Create(ctx2, "e", init));
  ib.CreateStore(cb, ib.CreateStructGEP(st, init->getArg(0), 1));
  ib.CreateRetVoid();
  auto *use = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx2), {ptr2, ptr2}, false),
      llvm::Function::ExternalLinkage, "use", &M2);
  llvm::IRBuilder<> ub(llvm::BasicBlock::Create(ctx2, "e", use));
  auto *fp = ub.CreateLoad(ptr2, ub.CreateStructGEP(st, use->getArg(0), 1));
  ub.CreateCall(cbTy, fp, {use->getArg(1)});
  ub.CreateRetVoid();
  chain::Points::Hooks h2;
  h2.harness = [](const llvm::Function *Fn) {
    return Fn && (Fn->getName() == "init" || Fn->getName() == "use");
  };
  chain::Points P2(M2, U2, std::move(h2));
  const auto &cs = P2.callers(cb);
  std::printf("callers(cb)=%zu\n", cs.size());
  if (cs.size() != 1) {
    std::printf("FAIL call inclusion\n");
    return 1;
  }
  const auto &bp = P2.of(cb->getArg(0));
  std::printf("of(cb.arg)=%u\n", bp.count());
  if (bp.count() == 0) {
    std::printf("FAIL formal did not receive the actual\n");
    return 1;
  }

  // A pointer and an integer stored through one harness formal are visible
  // through another, including when the formal is spilled to an alloca.
  llvm::LLVMContext ctx3;
  llvm::Module M3("m3", ctx3);
  llvm::Module U3("u3", ctx3);
  auto *ptr3 = llvm::PointerType::get(ctx3, 0);
  auto *i32 = llvm::Type::getInt32Ty(ctx3);
  auto *st3 = llvm::StructType::create(ctx3, {ptr3, i32}, "T");
  auto *g = new llvm::GlobalVariable(M3, ptr3, false, llvm::GlobalValue::ExternalLinkage,
                                     llvm::ConstantPointerNull::get(ptr3), "g");
  auto *init3 = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx3), {ptr3}, false),
      llvm::Function::ExternalLinkage, "init", &M3);
  llvm::IRBuilder<> ib3(llvm::BasicBlock::Create(ctx3, "e", init3));
  auto *slotI = ib3.CreateAlloca(ptr3);
  ib3.CreateStore(init3->getArg(0), slotI);
  auto *ctxI = ib3.CreateLoad(ptr3, slotI);
  ib3.CreateStore(g, ib3.CreateStructGEP(st3, ctxI, 0));
  ib3.CreateStore(llvm::ConstantInt::get(i32, 1), ib3.CreateStructGEP(st3, ctxI, 1));
  ib3.CreateRetVoid();
  auto *use3 = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx3), {ptr3}, false),
      llvm::Function::ExternalLinkage, "use", &M3);
  llvm::IRBuilder<> ub3(llvm::BasicBlock::Create(ctx3, "e", use3));
  auto *slotU = ub3.CreateAlloca(ptr3);
  ub3.CreateStore(use3->getArg(0), slotU);
  auto *ctxU = ub3.CreateLoad(ptr3, slotU);
  auto *ldp = ub3.CreateLoad(ptr3, ub3.CreateStructGEP(st3, ctxU, 0));
  auto *fld = ub3.CreateStructGEP(st3, ctxU, 1);
  ub3.CreateRetVoid();
  chain::Points::Hooks h3;
  h3.harness = [](const llvm::Function *Fn) {
    return Fn && (Fn->getName() == "init" || Fn->getName() == "use");
  };
  chain::Points P3(M3, U3, std::move(h3));
  bool sawG = false;
  for (unsigned id : P3.of(ldp))
    if (P3.obj(P3.loc(id).obj).site == g)
      sawG = true;
  std::printf("field pointer reaches other export=%d\n", sawG ? 1 : 0);
  if (!sawG) {
    std::printf("FAIL harness data cell\n");
    return 1;
  }
  bool sawFlag = false;
  for (unsigned id : P3.of(fld)) {
    auto loc = P3.loc(id);
    for (const auto &w : P3.writes(loc.obj))
      if (w.off == loc.off)
        sawFlag = true;
  }
  std::printf("field store reaches other export=%d\n", sawFlag ? 1 : 0);
  if (!sawFlag) {
    std::printf("FAIL harness flag cell\n");
    return 1;
  }

  // The call's type is not the callee's type. Points-to still binds it.
  llvm::LLVMContext ctx4;
  llvm::Module M4("m4", ctx4);
  llvm::Module U4("u4", ctx4);
  auto *ptr4 = llvm::PointerType::get(ctx4, 0);
  auto *cbTy4 = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx4), {ptr4}, false);
  auto *callTy4 = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx4), {ptr4, ptr4}, false);
  auto *cb4 = llvm::Function::Create(cbTy4, llvm::Function::InternalLinkage, "cb", &M4);
  llvm::IRBuilder<> cbB4(llvm::BasicBlock::Create(ctx4, "e", cb4));
  cbB4.CreateRetVoid();
  auto *init4 = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx4), {ptr4}, false),
      llvm::Function::ExternalLinkage, "init", &M4);
  llvm::IRBuilder<> ib4(llvm::BasicBlock::Create(ctx4, "e", init4));
  ib4.CreateStore(cb4, init4->getArg(0));
  ib4.CreateRetVoid();
  auto *use4 = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(ctx4), {ptr4}, false),
      llvm::Function::ExternalLinkage, "use", &M4);
  llvm::IRBuilder<> ub4(llvm::BasicBlock::Create(ctx4, "e", use4));
  auto *fp4 = ub4.CreateLoad(ptr4, use4->getArg(0));
  ub4.CreateCall(callTy4, fp4, {use4->getArg(0), use4->getArg(0)});
  ub4.CreateRetVoid();
  chain::Points::Hooks h4;
  h4.harness = [](const llvm::Function *Fn) {
    return Fn && (Fn->getName() == "init" || Fn->getName() == "use");
  };
  chain::Points P4(M4, U4, std::move(h4));
  const auto &cs4 = P4.callers(cb4);
  std::printf("callers(mismatched type)=%zu\n", cs4.size());
  if (cs4.size() != 1) {
    std::printf("FAIL type-mismatched indirect call\n");
    return 1;
  }
  std::printf("ok\n");
  return 0;
}
