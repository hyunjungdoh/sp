#include "Model.h"
#include "Client.h"
#include "Close.h"
#include <sstream>

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"

#include <dlfcn.h>
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>

// A library function's memory effects are part of its specification. LLVM
// records them for the functions whose prototype it recognizes; -O0 bitcode
// leaves the declarations bare.
static void annotateLibcalls(Module &M) {
  TargetLibraryInfoImpl impl{Triple(M.getTargetTriple())};
  TargetLibraryInfo tli(impl);
  for (Function &F : M)
    if (F.isDeclaration())
      inferNonMandatoryLibFuncAttrs(F, tli);
}

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

// The symbols the installed libraries of the closure define. A declaration
// among them is library code the bitcode lacks (an assembly routine, a
// library left out of the link): no engine has its body, so a call of it
// ends the path, and a global of it cannot be loaded.
static std::set<std::string> projectExports;

// Whether main reaches the sink marker along a control-flow path that passes
// only calls which can return. A call returns when its callee is a
// definition with a path from entry to a ret, an environment function (a
// declaration outside projectExports) that is not noreturn, or an indirect
// call one of whose targets returns. Least fixpoints over the call graph,
// so a function proven to return or to reach the sink has such a path. gaps
// receives the closure gaps that cut it: those called in functions that
// reach the sink only when gaps could return. An indirect call goes to
// Tgt_sig, or with refined to Tgt (§3.10, klee/Support/CallTargets.h).
static bool flowReach(Module &M, const klee::calls::Targets &tg, std::set<std::string> &gaps,
                      std::vector<std::string> &chain, bool refined) {
  std::map<const Function *, std::pair<const Function *, bool>> via;
  auto gap = [&](const Function *C) {
    return C && C->isDeclaration() && !C->isIntrinsic() && projectExports.count(C->getName().str());
  };
  auto solve = [&](bool gapsReturn, std::set<const Function *> &returns, std::set<const Function *> &sinks) {
  auto returnsFrom = [&](const Function *C) {
    if (C->isDeclaration())
      return (gapsReturn || !gap(C)) && !C->doesNotReturn() && !C->getName().starts_with("klee_silent_exit");
    return returns.count(C) > 0;
  };
  // One pass over F: whether it reaches a ret (for returns) or the marker.
  auto walk = [&](Function &F, bool toSink) {
    std::set<const BasicBlock *> done;
    std::vector<const BasicBlock *> work{&F.getEntryBlock()};
    while (!work.empty()) {
      const BasicBlock *BB = work.back();
      work.pop_back();
      if (!done.insert(BB).second)
        continue;
      bool alive = true;
      for (const Instruction &I : *BB) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || isa<DbgInfoIntrinsic>(CB))
          continue;
        // A call to an alias (Itanium C1/D1) is a direct call of its aliasee.
        const Function *C =
            dyn_cast<Function>(CB->getCalledOperand()->stripPointerCastsAndAliases());
        if (C && C->getName() == "klee_warning_once") {
          if (toSink) {
            via[&F] = {nullptr, false};
            return true;
          }
          continue;
        }
        bool passes = false;
        if (CB->isInlineAsm()) {
          passes = true;
        } else if (!C) {
          for (Function *T : refined ? tg.of(*CB) : tg.signature(*CB)) {
            if (toSink && sinks.count(T)) {
              via[&F] = {T, true};
              return true;
            }
            passes = passes || returnsFrom(T);
          }
        } else {
          if (toSink && sinks.count(C)) {
            via[&F] = {C, false};
            return true;
          }
          passes = returnsFrom(C);
        }
        if (auto *II = dyn_cast<InvokeInst>(CB)) {
          work.push_back(II->getUnwindDest());
          if (passes)
            work.push_back(II->getNormalDest());
          alive = false;
          break;
        }
        if (!passes) {
          alive = false;
          break;
        }
      }
      if (!alive)
        continue;
      const Instruction *T = BB->getTerminator();
      if (isa<ReturnInst>(T) && !toSink)
        return true;
      for (const BasicBlock *S : successors(BB))
        work.push_back(S);
    }
    return false;
  };
  for (bool toSink : {false, true})
    for (bool changed = true; changed;) {
      changed = false;
      for (Function &F : M) {
        if (F.isDeclaration() || (toSink ? sinks : returns).count(&F))
          continue;
        if (walk(F, toSink)) {
          (toSink ? sinks : returns).insert(&F);
          changed = true;
        }
      }
    }
  };
  Function *Main = M.getFunction("main");
  if (!Main)
    return false;
  std::set<const Function *> returns, sinks, returnsIf, sinksIf;
  solve(false, returns, sinks);
  auto real = via;
  solve(true, returnsIf, sinksIf);
  bool byPointer = false;
  for (const Function *F = Main; F && sinks.count(F) && chain.size() < 200;) {
    chain.push_back((byPointer ? "*" : "") + F->getName().str());
    std::tie(F, byPointer) = real[F];
  }
  for (const Function *F : sinksIf)
    if (!sinks.count(F))
      for (const Instruction &I : instructions(*F))
        if (auto *CB = dyn_cast<CallBase>(&I); CB && gap(CB->getCalledFunction()))
          gaps.insert(CB->getCalledFunction()->getName().str());
  return sinks.count(Main) > 0;
}

// The linked program a harness runs: declarations bound to the bodies the
// link renamed, environment allocators, memory intrinsics lowered with
// their locations, the closed-program check, and a marker at the sink line.
static int finish(Module &harness, LLVMContext &ctx, const fs::path &outDir, const std::string &stem,
                  const std::string &sinkFile, unsigned sinkLine) {
  // An internal definition is renamed when an external declaration of the
  // same name already exists. The cell stores that declaration; point it at
  // the definition.
  std::vector<Function *> decls;
  for (Function &F : harness)
    if (F.isDeclaration() && F.getName() != "klee_make_symbolic" && F.getName() != "klee_assume")
      decls.push_back(&F);
  for (Function *D : decls) {
    Function *body = nullptr;
    std::string prefix = (D->getName() + ".").str();
    for (Function &F : harness) {
      if (F.isDeclaration() || F.getFunctionType() != D->getFunctionType())
        continue;
      if (F.getName() == D->getName() || F.getName().starts_with(prefix)) {
        body = &F;
        break;
      }
    }
    if (!body)
      continue;
    D->replaceAllUsesWith(body);
    D->eraseFromParent();
  }
  std::vector<GlobalVariable *> gdecls;
  for (GlobalVariable &G : harness.globals())
    if (G.isDeclaration())
      gdecls.push_back(&G);
  for (GlobalVariable *D : gdecls) {
    std::string prefix = (D->getName() + ".").str();
    for (GlobalVariable &G : harness.globals()) {
      if (G.isDeclaration() || G.getValueType() != D->getValueType())
        continue;
      if (G.getName().starts_with(prefix)) {
        D->replaceAllUsesWith(&G);
        D->eraseFromParent();
        break;
      }
    }
  }
  // A call with no body whose pointer argument is the address of a pointer
  // the caller then loads stores an object of its last integer argument.
  // A function the environment defines is not body-less: its specification
  // is the environment model's (strtoul's out slot is an end pointer).
  std::map<Function *, int> allocSlot;
  std::map<Function *, int> allocSize;
  std::set<Function *> allocSkip;
  for (Function &F : harness) {
    if (F.isDeclaration())
      continue;
    for (Instruction &I : instructions(F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Function *D = CB->getCalledFunction();
      if (!D || !D->isDeclaration() || D->getName().starts_with("llvm.") || !D->getReturnType()->isIntegerTy() ||
          environmentSymbol(D->getName().str()))
        continue;
      int lastInt = -1;
      int slot = -1;
      for (unsigned a = 0; a < CB->arg_size() && a < D->arg_size(); ++a) {
        if (D->getArg(a)->getType()->isIntegerTy())
          lastInt = (int)a;
        if (!D->getArg(a)->getType()->isPointerTy())
          continue;
        auto *Al = dyn_cast<AllocaInst>(CB->getArgOperand(a)->stripPointerCasts());
        if (!Al)
          continue;
        bool loaded = false;
        for (User *U : Al->users()) {
          auto *Ld = dyn_cast<LoadInst>(U);
          if (Ld && Ld->getType()->isPointerTy() && Ld->getPointerOperand()->stripPointerCasts() == Al)
            loaded = true;
        }
        if (!loaded)
          continue;
        if (slot != -1 && slot != (int)a)
          slot = -2;
        else if (slot != -2)
          slot = (int)a;
      }
      if (slot < 0 || lastInt < 0)
        continue;
      auto sit = allocSlot.find(D);
      if (sit == allocSlot.end()) {
        allocSlot[D] = slot;
        allocSize[D] = lastInt;
      } else if (sit->second != slot || allocSize[D] != lastInt)
        allocSkip.insert(D);
    }
  }
  Function *Malloc = harness.getFunction("malloc");
  if (!Malloc)
    Malloc = Function::Create(FunctionType::get(PointerType::get(ctx, 0), {Type::getInt64Ty(ctx)}, false),
                              GlobalValue::ExternalLinkage, "malloc", &harness);
  for (const auto &kv : allocSlot) {
    Function *D = kv.first;
    if (!D->isDeclaration() || allocSkip.count(D))
      continue;
    int slot = kv.second;
    int sz = allocSize[D];
    if (slot < 0 || sz < 0 || (unsigned)slot >= D->arg_size() || (unsigned)sz >= D->arg_size())
      continue;
    auto *BB = BasicBlock::Create(ctx, "entry", D);
    IRBuilder<> IB(BB);
    Value *n = D->getArg((unsigned)sz);
    if (n->getType() != Type::getInt64Ty(ctx))
      n = n->getType()->getIntegerBitWidth() < 64 ? IB.CreateZExt(n, Type::getInt64Ty(ctx))
                                                  : IB.CreateTrunc(n, Type::getInt64Ty(ctx));
    IB.CreateStore(IB.CreateCall(Malloc, {n}), D->getArg((unsigned)slot));
    IB.CreateRet(Constant::getNullValue(D->getReturnType()));
  }
  // KLEE's IntrinsicCleaner lowers memcpy/memmove/memset with LLVM's
  // IntrinsicLowering, which emits the libc call without carrying over the
  // intrinsic's debug location. The verifier then rejects that call inside any
  // function that holds a subprogram. Perform the same lowering here while
  // preserving each intrinsic's location, so KLEE's pass finds nothing to
  // lower and the module keeps its source lines for sink reporting. A location
  // the intrinsic never had becomes a line-zero site in the enclosing
  // subprogram, which marks "no source line" rather than a wrong one.
  {
    PointerType *p0 = PointerType::get(ctx, 0);
    Type *i64 = Type::getInt64Ty(ctx);
    Type *i32 = Type::getInt32Ty(ctx);
    FunctionCallee cMemcpy = harness.getOrInsertFunction(
        "memcpy", FunctionType::get(p0, {p0, p0, i64}, false));
    FunctionCallee cMemmove = harness.getOrInsertFunction(
        "memmove", FunctionType::get(p0, {p0, p0, i64}, false));
    FunctionCallee cMemset = harness.getOrInsertFunction(
        "memset", FunctionType::get(p0, {p0, i32, i64}, false));
    for (Function &F : harness) {
      if (F.isDeclaration())
        continue;
      DISubprogram *SP = F.getSubprogram();
      std::vector<MemIntrinsic *> mems;
      for (Instruction &I : instructions(F))
        if (auto *MI = dyn_cast<MemIntrinsic>(&I))
          mems.push_back(MI);
      for (MemIntrinsic *MI : mems) {
        IRBuilder<> B(MI);
        DebugLoc dl = MI->getDebugLoc();
        if (!dl && SP)
          dl = DILocation::get(ctx, 0, 0, SP);
        B.SetCurrentDebugLocation(dl);
        Value *dst = MI->getRawDest();
        Value *len = MI->getLength();
        if (len->getType() != i64)
          len = B.CreateZExtOrTrunc(len, i64);
        if (auto *MS = dyn_cast<MemSetInst>(MI)) {
          B.CreateCall(cMemset, {dst, B.CreateZExt(MS->getValue(), i32), len});
        } else {
          Value *src = cast<MemTransferInst>(MI)->getRawSource();
          B.CreateCall(isa<MemMoveInst>(MI) ? cMemmove : cMemcpy, {dst, src, len});
        }
        MI->eraseFromParent();
      }
    }
  }
  // Sink reach is observable: a warning at each instruction of the sink line.
  {
    FunctionCallee warn = harness.getOrInsertFunction(
        "klee_warning_once", FunctionType::get(Type::getVoidTy(ctx), {PointerType::get(ctx, 0)}, false));
    std::string base = sinkFile.substr(sinkFile.find_last_of('/') == std::string::npos ? 0 : sinkFile.find_last_of('/') + 1);
    for (Function &F : harness) {
      if (F.isDeclaration())
        continue;
      for (BasicBlock &BB : F) {
        Instruction *at = nullptr;
        for (Instruction &I : BB) {
          DILocation *L = I.getDebugLoc().get();
          if (L && L->getLine() == sinkLine && !isa<PHINode>(I) &&
              L->getFilename().ends_with(base) && (L->getFilename().size() == base.size() || L->getFilename()[L->getFilename().size() - base.size() - 1] == '/')) {
            at = &I;
            break;
          }
        }
        if (!at)
          continue;
        IRBuilder<> B(at);
        B.SetCurrentDebugLocation(at->getDebugLoc());
        B.CreateCall(warn, {B.CreateGlobalStringPtr("SINK-REACHED")});
      }
    }
  }
  // Block only structural breakage. Debug-metadata defects that linking left
  // in the library bitcode (a subprogram shared by two merged definitions) are
  // reported through the separate flag and tolerated, matching how KLEE loads
  // the module.
  bool brokenDI = false;
  if (verifyModule(harness, &errs(), &brokenDI))
    return 1;
  // The harness runs a closed program: every function it calls is defined in
  // the linked bitcode or provided by the system libraries that form the
  // environment. A called function that neither defines breaks that
  // precondition; it is reported, since no execution can go past it.
  {
    std::set<const Function *> reach;
    std::set<const Value *> seen;
    std::vector<const Value *> work;
    if (Function *M = harness.getFunction("main"))
      work.push_back(M);
    if (GlobalVariable *C = harness.getGlobalVariable("llvm.global_ctors"))
      work.push_back(C);
    while (!work.empty()) {
      const Value *V = work.back();
      work.pop_back();
      if (!seen.insert(V).second)
        continue;
      if (auto *F = dyn_cast<Function>(V)) {
        reach.insert(F);
        for (const Instruction &I : instructions(*F))
          for (const Value *op : I.operands())
            if (isa<Constant>(op))
              work.push_back(op);
      } else if (auto *G = dyn_cast<GlobalVariable>(V)) {
        if (G->hasInitializer())
          work.push_back(G->getInitializer());
      } else if (auto *GA = dyn_cast<GlobalAlias>(V)) {
        work.push_back(GA->getAliasee());
      } else if (auto *C = dyn_cast<Constant>(V)) {
        for (const Value *op : C->operands())
          work.push_back(op);
      }
    }
    std::error_code ec;
    // Whether main reaches a function holding the sink marker through calls
    // and the functions whose addresses the reached code takes.
    {
      std::vector<std::string> sinks;
      for (const Function *F : reach)
        for (const Instruction &I : instructions(*F))
          if (auto *CB = dyn_cast<CallBase>(&I))
            if (const Function *C = CB->getCalledFunction(); C && C->getName() == "klee_warning_once") {
              sinks.push_back(F->getName().str());
              break;
            }
      raw_fd_ostream rs((outDir / (stem + ".reach.txt")).string(), ec);
      rs << "sink-reachable " << (sinks.empty() ? 0 : 1) << "\n";
      for (const std::string &s : sinks)
        rs << "sink-fn " << s << "\n";
      klee::calls::Targets tg;
      tg.index(harness);
      std::set<std::string> gaps;
      std::vector<std::string> chain;
      bool cfg = flowReach(harness, tg, gaps, chain, false);
      // A library global the bitcode lacks has no initial contents, and the
      // program cannot start without them.
      std::vector<std::string> missing;
      for (GlobalVariable &G : harness.globals())
        if (G.isDeclaration() && G.getName() != "__dso_handle" && projectExports.count(G.getName().str()) &&
            harness.getDataLayout().getTypeAllocSize(G.getValueType()) > 0)
          missing.push_back(G.getName().str());
      cfg = cfg && missing.empty();
      rs << "sink-reachable-cfg " << (cfg ? 1 : 0) << "\n";
      rs << "global-gaps " << missing.size() << "\n";
      for (size_t k = 0; k < missing.size() && k < 20; ++k)
        rs << "global-gap " << missing[k] << "\n";
      // '*' marks a step through an indirect call.
      for (const std::string &c : chain)
        rs << "cfg-path " << c << "\n";
      std::set<std::string> tGaps;
      std::vector<std::string> tChain;
      bool refined = flowReach(harness, tg, tGaps, tChain, true);
      unsigned sites = 0, narrowed = 0;
      for (Function &F : harness)
        for (Instruction &I : instructions(F))
          if (auto *CB = dyn_cast<CallBase>(&I); CB && klee::calls::indirect(*CB) && CB->getMetadata("sp.tgt")) {
            ++sites;
            narrowed += tg.of(*CB).size() < tg.signature(*CB).size();
          }
      rs << "indirect-sites " << sites << " narrowed " << narrowed << " empty " << tg.empty << "\n";
      rs << "sink-reachable-mlta " << (refined ? 1 : 0) << "\n";
      for (const std::string &c : tChain)
        rs << "mlta-path " << c << "\n";
      for (const std::string &g : gaps)
        rs << "closure-gap " << g << "\n";
    }
    raw_fd_ostream open((outDir / (stem == "run" ? std::string("open.txt") : stem + ".open.txt")).string(), ec);
    for (Function &F : harness) {
      if (!F.isDeclaration() || F.isIntrinsic() || !reach.count(&F) || F.getName().starts_with("klee_"))
        continue;
      std::string name = F.getName().str();
      if (environmentSymbol(name) || nativeResidue(harness, name))
        continue;
      open << name << "\n";
      errs() << "open: " << name << "\n";
    }
  }
  std::error_code bec;
  raw_fd_ostream bc((outDir / (stem + ".bc")).string(), bec);
  if (bec) {
    errs() << bec.message() << "\n";
    return 1;
  }
  {
    unsigned witMeta = 0;
    for (const Function &F : harness) {
      SmallVector<MDNode *, 2> mds;
      F.getMetadata("sp.wit", mds);
      witMeta += mds.size();
    }
    errs() << stem << ".bc sp.wit " << witMeta << "\n";
  }
  WriteBitcodeToFile(harness, bc);
  return 0;
}

namespace {

// One satisfiable sequence of the may phase: its functions and the cells
// of its residual formula.
struct Witness {
  int index = -1;
  std::vector<std::string> seq;
  std::vector<Client::Cell> phi;
  struct Ret {
    std::string callee, pred, k, caller;
    unsigned line = 0, col = 0;
    bool live = false;
  };
  std::vector<Ret> rets;
  std::vector<Client::Keyed> keyed;
};

// A run prints every sequence it tries and stops at the first satisfiable
// one, so the witness is its last block. The atoms to discharge are the
// entry formula (model lines). A model line with no fact is not an atom.
// The may cell list is the formula only when this block has no model lines.
Witness parseWitness(std::istream &st) {
  Witness w, accepted;
  std::vector<Client::Cell> may, facts;
  // §3.5 정의 3.5.2: 이 시퀀스의 경계 근 R(π). 각 근은 (export 인자, 타입 경로)다.
  std::vector<std::pair<int, std::vector<std::string>>> roots;
  // Φ_∂ applies when the path has a D↔client object boundary: resolved
  // boundary roots, or unresolved (D-allocated) roots. Then only boundary
  // and prefix cells are client obligations; D-internal residual is not.
  bool crossing = false;
  // Any non-return "model" line (including unknown). Valued atoms are those
  // take() keeps; unknown lines are free vars, not φ atoms.
  bool sawModelLine = false;
  // A sequence followed by dispatch-open is not a P1 witness — φ SAT alone
  // is not enough when Definition D leaves an indirect edge open.
  bool rejected = false;
  // §3.8: prefix cells (root, type path, last offset) and the key setter that
  // precedes its "discharges" line.
  std::vector<std::tuple<int, std::vector<std::string>, int64_t>> prefixes;
  std::optional<Client::Keyed> pendingKeyed;
  auto take = [](const std::string &s, std::vector<Client::Cell> &into) {
    std::istringstream in(s);
    std::string head, root, tok, last;
    in >> head >> root;
    std::string op;
    auto bound = [](const std::string &t) {
      return t == "ule" || t == "uge" || t == "ult" || t == "sle" || t == "sge";
    };
    auto bitOp = [](const std::string &t) { return t == "has" || t == "lacks"; };
    std::vector<std::string> path;
    while (in >> tok) {
      if (tok == "unknown")
        return;
      if (tok == "=" || tok == "!=" || tok[0] == '<' || tok[0] == '>' || bound(tok) || bitOp(tok)) {
        op = tok;
        break;
      }
      last = tok;
      auto p = tok.rfind('+');
      if (p != std::string::npos && p > 0)
        path.push_back(tok.substr(0, p));
    }
    auto plus = last.rfind('+');
    if (plus == std::string::npos || plus == 0 || op.empty())
      return;
    auto off = asI64(last.substr(plus + 1));
    if (!off)
      return;
    Client::Cell c{last.substr(0, plus), *off, s};
    if (root.rfind("arg", 0) == 0)
      c.root = std::atoi(root.c_str() + 3);
    c.path = std::move(path);
    c.op = op;
    // §3.8: a bit atom after the value constraint is a second atom on the cell.
    std::vector<std::pair<std::string, std::string>> bits;
    while (in >> tok) {
      if (tok == "file") {
        c.file = true;
        break;
      }
      if (bitOp(tok)) {
        std::string m;
        if (in >> m)
          bits.push_back({tok, m});
        continue;
      }
      if (bound(tok))
        break;
      if (!bits.empty())
        continue;
      if (tok.size() >= 2 && tok.front() == '"' && tok.back() == '"')
        tok = tok.substr(1, tok.size() - 2);
      c.values.push_back(tok);
    }
    for (const auto &[bop, m] : bits) {
      Client::Cell b = c;
      b.op = bop;
      b.values = {m};
      b.file = false;
      into.push_back(std::move(b));
    }
    if (bitOp(c.op) && !bits.empty() && c.values.empty())
      return;
    into.push_back(std::move(c));
  };
  auto finish = [&](Witness &dst) {
    // φ_π = residual entry formula. May-layer domains are not φ — use them
    // only when the run emitted no model section (legacy / no residual).
    dst.phi = sawModelLine ? facts : may;
    if (sawModelLine)
      for (const Client::Cell &m : may) {
        if (!m.file)
          continue;
        bool have = false;
        for (Client::Cell &c : dst.phi)
          if (c.root == m.root && c.off == m.off && c.path == m.path) {
            c.file = true;
            have = true;
            break;
          }
        if (!have)
          dst.phi.push_back(m);
      }
    // Φ_∂: under crossing, only boundary/prefix cells are client obligations.
    for (Client::Cell &c : dst.phi) {
      c.crossing = crossing;
      for (const auto &[root, typePath, off] : prefixes)
        if (root == c.root && off == c.off && typePath == c.path)
          c.prefix = true;
      for (const auto &r : roots)
        if (r.first == c.root && r.second.size() <= c.path.size() &&
            std::equal(r.second.begin(), r.second.end(), c.path.begin())) {
          c.boundary = true;
          break;
        }
    }
    if (dst.seq.empty())
      dst.index = -1;
  };
  auto commit = [&]() {
    if (rejected || w.index < 0 || w.seq.empty())
      return;
    finish(w);
    accepted = w;
  };
  for (std::string s; std::getline(st, s);) {
    std::istringstream in(s);
    std::string head;
    in >> head;
    if (head == "sequence") {
      commit();
      w = Witness{};
      may.clear();
      facts.clear();
      roots.clear();
      crossing = false;
      sawModelLine = false;
      rejected = false;
      prefixes.clear();
      pendingKeyed.reset();
      std::string n, absent;
      in >> n >> absent;
      if (absent.empty())
        if (auto k = asI64(n))
          w.index = (int)*k;
      continue;
    }
    if (head == "dispatch-open") {
      // P1 rejects this sequence: φ SAT ∧ open Definition-D edge.
      rejected = true;
      w = Witness{};
      continue;
    }
    if (w.index < 0)
      continue;
    if (head == "fn") {
      std::string name;
      in >> name;
      w.seq.push_back(name);
    } else if (head == "boundary") {
      // "boundary cells X of Y roots R unresolved U": Φ_∂ iff R>0 or U>0.
      for (std::string tok; in >> tok;)
        if (tok == "roots" || tok == "unresolved") {
          std::string n;
          if (in >> n)
            if (auto v = asI64(n); v && *v > 0)
              crossing = true;
        }
    } else if (head == "boundaryroot") {
      std::string root;
      in >> root;
      if (root.rfind("arg", 0) != 0)
        continue;
      std::vector<std::string> typePath;
      for (std::string tok; in >> tok;) {
        auto p = tok.rfind('+');
        typePath.push_back(p == std::string::npos ? tok : tok.substr(0, p));
      }
      roots.push_back({std::atoi(root.c_str() + 3), std::move(typePath)});
    } else if (head == "prefixcell") {
      std::string root;
      in >> root;
      if (root.rfind("arg", 0) != 0)
        continue;
      std::vector<std::string> typePath;
      int64_t off = -1;
      for (std::string tok; in >> tok;) {
        auto p = tok.rfind('+');
        if (p == std::string::npos || p == 0)
          continue;
        typePath.push_back(tok.substr(0, p));
        if (auto o = asI64(tok.substr(p + 1)))
          off = *o;
      }
      prefixes.push_back({std::atoi(root.c_str() + 3), std::move(typePath), off});
    } else if (head == "client") {
      // §3.8 정의 3.8.4: "client W argO argT = K [vararg …]".
      Client::Keyed k;
      std::string obj;
      in >> k.fn >> obj;
      if (obj.rfind("arg", 0) != 0)
        continue;
      k.obj = (unsigned)std::atoi(obj.c_str() + 3);
      std::vector<std::string> toks;
      for (std::string t; in >> t;)
        toks.push_back(t);
      bool ok = true;
      for (size_t i = 0; i < toks.size(); ++i) {
        if (toks[i].rfind("arg", 0) == 0 && i + 2 < toks.size() && toks[i + 1] == "=") {
          k.tag = std::atoi(toks[i].c_str() + 3);
          auto v = asI64(toks[i + 2]);
          ok = ok && v.has_value();
          k.tagV = v ? *v : 0;
          i += 2;
        } else if (toks[i] == "vararg" && i + 2 < toks.size()) {
          k.va = true;
          auto v = asI64(toks[i + 2]);
          if (!v)
            if (auto u = asU64(toks[i + 2]))
              v = (int64_t)*u;
          ok = ok && v.has_value();
          k.preds.push_back({toks[i + 1], v ? *v : 0});
          i += 2;
        } else
          ok = false;
      }
      pendingKeyed = ok ? std::optional<Client::Keyed>(k) : std::nullopt;
    } else if (head == "discharges") {
      std::string root;
      in >> root;
      if (pendingKeyed && root.rfind("arg", 0) == 0) {
        Client::Keyed &k = *pendingKeyed;
        k.target = s.substr(std::string("discharges").size());
        k.root = std::atoi(root.c_str() + 3);
        for (std::string tok; in >> tok;) {
          auto p = tok.rfind('+');
          if (p == std::string::npos || p == 0)
            continue;
          k.path.push_back(tok.substr(0, p));
          if (auto o = asI64(tok.substr(p + 1)))
            k.off = *o;
        }
        w.keyed.push_back(k);
      }
      pendingKeyed.reset();
    } else if (head == "cell") {
      take(s, may);
    } else if (head == "model") {
      std::string second;
      in >> second;
      if (second == "return") {
        Witness::Ret r;
        std::string at, linek, lines, colk, cols;
        in >> r.callee >> r.pred >> r.k >> at >> r.caller >> linek >> lines >> colk >> cols;
        if (linek == "line")
          r.line = (unsigned)std::atoi(lines.c_str());
        if (colk == "col")
          r.col = (unsigned)std::atoi(cols.c_str());
        std::string extra;
        while (in >> extra)
          if (extra == "live")
            r.live = true;
        if (!r.callee.empty() && !r.caller.empty() && !r.pred.empty())
          w.rets.push_back(std::move(r));
      } else {
        // φ = residual path condition on entry cells. "unknown" ⇒ free, not an atom.
        sawModelLine = true;
        take(s, facts);
      }
    }
  }
  commit();
  return accepted;
}

// The client the witnesses direct, linked with D and U into client.bc.
// A required branch compared a call's result with a constant. An integer
// lookup returns the witness. A pointer lookup that may be null returns
// null. Every other integer result is assumed. Pointer results are applied
// after the link, when a declaration is distinct from a body.
void plantReturns(Module &M, const std::vector<Witness::Ret> &rets) {
  if (rets.empty())
    return;
  LLVMContext &ctx = M.getContext();
  auto *i64 = Type::getInt64Ty(ctx);
  FunctionType *assumeTy = FunctionType::get(Type::getVoidTy(ctx), {i64}, false);
  Function *assume = M.getFunction("klee_assume");
  if (!assume)
    assume = Function::Create(assumeTy, Function::ExternalLinkage, "klee_assume", &M);
  auto predOf = [](const std::string &p) -> std::optional<ICmpInst::Predicate> {
    if (p == "==")
      return ICmpInst::ICMP_EQ;
    if (p == "!=")
      return ICmpInst::ICMP_NE;
    if (p == "ugt")
      return ICmpInst::ICMP_UGT;
    if (p == "uge")
      return ICmpInst::ICMP_UGE;
    if (p == "ult")
      return ICmpInst::ICMP_ULT;
    if (p == "ule")
      return ICmpInst::ICMP_ULE;
    if (p == "sgt")
      return ICmpInst::ICMP_SGT;
    if (p == "sge")
      return ICmpInst::ICMP_SGE;
    if (p == "slt")
      return ICmpInst::ICMP_SLT;
    if (p == "sle")
      return ICmpInst::ICMP_SLE;
    return std::nullopt;
  };
  struct SiteKey {
    std::string callee, caller;
    unsigned line = 0, col = 0;
    bool operator<(const SiteKey &o) const {
      if (callee != o.callee)
        return callee < o.callee;
      if (caller != o.caller)
        return caller < o.caller;
      if (line != o.line)
        return line < o.line;
      return col < o.col;
    }
  };
  struct SiteFact {
    std::vector<std::pair<unsigned, int64_t>> cs;
    bool live = false;
  };
  std::map<SiteKey, SiteFact> grouped;
  for (const Witness::Ret &r : rets) {
    auto pred = predOf(r.pred);
    if (!pred || !r.line)
      continue;
    int64_t k = 0;
    auto parsed = std::from_chars(r.k.data(), r.k.data() + r.k.size(), k);
    if (parsed.ec != std::errc())
      continue;
    SiteFact &fact = grouped[{r.callee, r.caller, r.line, r.col}];
    fact.cs.push_back({(unsigned)*pred, k});
    fact.live = fact.live || r.live;
  }
  auto supply = [](CallBase *CB, Value *W) {
    if (auto *II = dyn_cast<InvokeInst>(CB)) {
      BasicBlock *From = II->getParent();
      BasicBlock *Unw = II->getUnwindDest();
      II->replaceAllUsesWith(W);
      for (PHINode &Phi : Unw->phis())
        Phi.removeIncomingValue(From, false);
      BranchInst::Create(II->getNormalDest(), II);
      II->eraseFromParent();
      return;
    }
    CB->replaceAllUsesWith(W);
    CB->eraseFromParent();
  };
  for (const auto &gv : grouped) {
    Function *caller = M.getFunction(gv.first.caller);
    if (!caller || caller->isDeclaration())
      continue;
    std::vector<CallBase *> sites;
    for (Instruction &I : instructions(*caller)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      Function *Cal = CB->getCalledFunction();
      if (!Cal || Cal->getName() != gv.first.callee)
        continue;
      const DebugLoc &DL = CB->getDebugLoc();
      if (!DL || DL.getLine() != gv.first.line || (gv.first.col && DL.getCol() != gv.first.col))
        continue;
      sites.push_back(CB);
    }
    for (CallBase *CB : sites) {
      Function *D = CB->getCalledFunction();
      std::optional<int64_t> fallback;
      if (auto arg = fallbackArg(D))
        if (*arg < CB->arg_size())
          if (auto *C = dyn_cast<ConstantInt>(CB->getArgOperand(*arg)))
            fallback = C->getSExtValue();
      std::optional<int64_t> witness = satisfyingValue(gv.second.cs, fallback);
      bool asLookup = lookupOnly(D) && witness && !gv.second.live;
      Value *W = nullptr;
      if (asLookup && CB->getType()->isIntegerTy())
        W = ConstantInt::get(CB->getType(), (uint64_t)*witness, true);
      else if (asLookup && CB->getType()->isPointerTy() && *witness == 0)
        W = ConstantPointerNull::get(cast<PointerType>(CB->getType()));
      if (W) {
        supply(CB, W);
        continue;
      }
      if (!CB->getType()->isIntegerTy())
        continue;
      Instruction *ip = nullptr;
      if (auto *II = dyn_cast<InvokeInst>(CB))
        ip = II->getNormalDest()->getFirstNonPHI();
      else
        ip = CB->getNextNode();
      if (!ip)
        continue;
      IRBuilder<> B(ip);
      for (const auto &c : gv.second.cs) {
        Value *cmp = B.CreateICmp((ICmpInst::Predicate)c.first, CB, ConstantInt::get(CB->getType(), c.second, true));
        B.CreateCall(assume, {B.CreateZExt(cmp, i64)});
      }
    }
  }
}

// Bytes read or written through a pointer at constant offsets. base is the
// displacement of the pointer from the start of that region.
struct PtrExtent {
  int64_t base = 0;
  uint64_t n = 0;
};

static PtrExtent resultExtent(const CallBase *Root) {
  PtrExtent out;
  if (!Root || !Root->getFunction())
    return out;
  const DataLayout &dl = Root->getFunction()->getParent()->getDataLayout();
  struct Item {
    const Function *F;
    const Value *V;
    int64_t off;
  };
  std::vector<Item> q{{Root->getFunction(), Root, 0}};
  std::set<std::tuple<const Function *, const Value *, int64_t>> seen;
  int64_t lo = 0, hi = 0;
  bool any = false;
  auto cover = [&](int64_t o, uint64_t n) {
    if (!n || n > (1ull << 20))
      return;
    int64_t b = o + (int64_t)n;
    if (b < o)
      return;
    if (!any) {
      lo = o;
      hi = b;
      any = true;
    } else {
      lo = std::min(lo, o);
      hi = std::max(hi, b);
    }
  };
  auto sized = [&](Type *T) -> uint64_t {
    if (!T || !T->isSized())
      return 0;
    TypeSize ts = dl.getTypeStoreSize(T);
    if (ts.isScalable())
      return 0;
    return ts.getFixedValue();
  };
  for (size_t i = 0; i < q.size() && i < 8192; ++i) {
    const Function *F = q[i].F;
    const Value *V = q[i].V;
    int64_t o = q[i].off;
    if (!F || !V || !seen.insert({F, V, o}).second)
      continue;
    for (const User *U : V->users()) {
      if (q.size() >= 8192)
        break;
      if (auto *C = dyn_cast<CastInst>(U)) {
        q.push_back({C->getFunction(), C, o});
        continue;
      }
      if (auto *G = dyn_cast<GetElementPtrInst>(U)) {
        if (G->getPointerOperand() != V)
          continue;
        APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta))
          continue;
        q.push_back({G->getFunction(), G, o + (int64_t)delta.getSExtValue()});
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(U)) {
        if (L->getPointerOperand() == V)
          cover(o, sized(L->getType()));
        continue;
      }
      if (auto *S = dyn_cast<StoreInst>(U)) {
        if (S->getPointerOperand() == V)
          cover(o, sized(S->getValueOperand()->getType()));
        else if (S->getValueOperand() == V)
          for (const User *PU : S->getPointerOperand()->users())
            if (auto *RL = dyn_cast<LoadInst>(PU))
              if (RL->getPointerOperand() == S->getPointerOperand())
                q.push_back({RL->getFunction(), RL, o});
        continue;
      }
      auto *CB = dyn_cast<CallBase>(U);
      if (!CB || CB->isDebugOrPseudoInst() || CB->getCalledOperand() == V)
        continue;
      Function *Cal = CB->getCalledFunction();
      if (Cal && (Cal->getName().starts_with("llvm.memcpy") || Cal->getName().starts_with("llvm.memmove"))) {
        if (CB->arg_size() >= 3 && (CB->getArgOperand(0) == V || CB->getArgOperand(1) == V))
          if (auto *N = dyn_cast<ConstantInt>(CB->getArgOperand(2)))
            if (N->getBitWidth() <= 64)
              cover(o, N->getZExtValue());
        continue;
      }
      if (!Cal || Cal->isDeclaration())
        continue;
      for (unsigned a = 0; a < CB->arg_size() && a < Cal->arg_size(); ++a)
        if (CB->getArgOperand(a) == V)
          q.push_back({Cal, Cal->getArg(a), o});
    }
  }
  if (!any)
    return out;
  if (hi < 0)
    hi = 0;
  if (lo > 0)
    lo = 0;
  if (hi < lo)
    return out;
  out.base = -lo;
  out.n = (uint64_t)(hi - lo);
  return out;
}

// A pointer result still present after linking. A body stays and, when
// assumed is set, the comparison is assumed. A declaration with no integer
// argument cannot allocate, so a non-null result is the object the
// continuation accesses.
static void plantExternal(Module &M, const std::vector<Witness::Ret> &rets, bool assumed = true) {
  if (rets.empty())
    return;
  LLVMContext &ctx = M.getContext();
  auto *i64 = Type::getInt64Ty(ctx);
  auto *i8 = Type::getInt8Ty(ctx);
  auto *ptrTy = PointerType::getUnqual(ctx);
  FunctionType *assumeTy = FunctionType::get(Type::getVoidTy(ctx), {i64}, false);
  Function *assume = M.getFunction("klee_assume");
  if (!assume)
    assume = Function::Create(assumeTy, Function::ExternalLinkage, "klee_assume", &M);
  FunctionType *symTy = FunctionType::get(Type::getVoidTy(ctx), {ptrTy, i64, ptrTy}, false);
  Function *sym = M.getFunction("klee_make_symbolic");
  if (!sym)
    sym = Function::Create(symTy, Function::ExternalLinkage, "klee_make_symbolic", &M);
  Function *mallocFn = M.getFunction("malloc");
  if (!mallocFn)
    mallocFn = Function::Create(FunctionType::get(ptrTy, {i64}, false), Function::ExternalLinkage, "malloc", &M);
  auto predOf = [](const std::string &p) -> std::optional<ICmpInst::Predicate> {
    if (p == "==")
      return ICmpInst::ICMP_EQ;
    if (p == "!=")
      return ICmpInst::ICMP_NE;
    if (p == "ugt")
      return ICmpInst::ICMP_UGT;
    if (p == "uge")
      return ICmpInst::ICMP_UGE;
    if (p == "ult")
      return ICmpInst::ICMP_ULT;
    if (p == "ule")
      return ICmpInst::ICMP_ULE;
    if (p == "sgt")
      return ICmpInst::ICMP_SGT;
    if (p == "sge")
      return ICmpInst::ICMP_SGE;
    if (p == "slt")
      return ICmpInst::ICMP_SLT;
    if (p == "sle")
      return ICmpInst::ICMP_SLE;
    return std::nullopt;
  };
  struct SiteKey {
    std::string callee, caller;
    unsigned line = 0, col = 0;
    bool operator<(const SiteKey &o) const {
      if (callee != o.callee)
        return callee < o.callee;
      if (caller != o.caller)
        return caller < o.caller;
      if (line != o.line)
        return line < o.line;
      return col < o.col;
    }
  };
  struct SiteFact {
    std::vector<std::pair<unsigned, int64_t>> cs;
    bool live = false;
  };
  std::map<SiteKey, SiteFact> grouped;
  for (const Witness::Ret &r : rets) {
    auto pred = predOf(r.pred);
    if (!pred || !r.line)
      continue;
    int64_t k = 0;
    auto parsed = std::from_chars(r.k.data(), r.k.data() + r.k.size(), k);
    if (parsed.ec != std::errc())
      continue;
    SiteFact &fact = grouped[{r.callee, r.caller, r.line, r.col}];
    fact.cs.push_back({(unsigned)*pred, k});
    fact.live = fact.live || r.live;
  }
  auto supply = [](CallBase *CB, Value *W) {
    if (auto *II = dyn_cast<InvokeInst>(CB)) {
      BasicBlock *From = II->getParent();
      BasicBlock *Unw = II->getUnwindDest();
      II->replaceAllUsesWith(W);
      for (PHINode &Phi : Unw->phis())
        Phi.removeIncomingValue(From, false);
      BranchInst::Create(II->getNormalDest(), II);
      II->eraseFromParent();
      return;
    }
    CB->replaceAllUsesWith(W);
    CB->eraseFromParent();
  };
  unsigned nameN = 0;
  for (const auto &gv : grouped) {
    Function *caller = M.getFunction(gv.first.caller);
    if (!caller || caller->isDeclaration())
      continue;
    std::vector<CallBase *> sites;
    for (Instruction &I : instructions(*caller)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || !CB->getType()->isPointerTy())
        continue;
      Function *Cal = CB->getCalledFunction();
      if (!Cal || Cal->getName() != gv.first.callee)
        continue;
      const DebugLoc &DL = CB->getDebugLoc();
      if (!DL || DL.getLine() != gv.first.line || (gv.first.col && DL.getCol() != gv.first.col))
        continue;
      sites.push_back(CB);
    }
    for (CallBase *CB : sites) {
      bool onlyNull = true, wantObj = true;
      for (const auto &c : gv.second.cs) {
        auto pred = (ICmpInst::Predicate)c.first;
        if (c.second != 0 || (pred != ICmpInst::ICMP_EQ && pred != ICmpInst::ICMP_NE))
          onlyNull = false;
        if (!cmpHolds(pred, 1, c.second))
          wantObj = false;
      }
      Function *Cal = CB->getCalledFunction();
      bool integerArg = false;
      for (Value *A : CB->args())
        integerArg = integerArg || A->getType()->isIntegerTy();
      PtrExtent ext = resultExtent(CB);
      bool material = onlyNull && wantObj && Cal && Cal->isDeclaration() && !Cal->isIntrinsic() && !integerArg && ext.n > 0 &&
                      ext.n <= (1ull << 20) && (uint64_t)ext.base <= ext.n;
      if (material) {
        IRBuilder<> B(CB);
        Value *block = B.CreateCall(mallocFn, {ConstantInt::get(i64, ext.n)});
        B.CreateCall(sym, {block, ConstantInt::get(i64, ext.n), B.CreateGlobalString("o" + std::to_string(nameN++))});
        Value *ptr = block;
        if (ext.base)
          ptr = B.CreateGEP(i8, block, {ConstantInt::get(i64, ext.base)});
        supply(CB, ptr);
        continue;
      }
      if (!assumed)
        continue;
      Instruction *ip = nullptr;
      if (auto *II = dyn_cast<InvokeInst>(CB))
        ip = II->getNormalDest()->getFirstNonPHI();
      else
        ip = CB->getNextNode();
      if (!ip)
        continue;
      IRBuilder<> B(ip);
      for (const auto &c : gv.second.cs) {
        auto pred = (ICmpInst::Predicate)c.first;
        if (c.second != 0 || (pred != ICmpInst::ICMP_EQ && pred != ICmpInst::ICMP_NE))
          continue;
        Value *cmp = B.CreateICmp(pred, CB, ConstantPointerNull::get(cast<PointerType>(CB->getType())));
        B.CreateCall(assume, {B.CreateZExt(cmp, i64)});
      }
    }
  }
}

// Function p of witness k carries the attachment sp.wit !{k, p} (DESIGN-D
// §6b). Only definitions carry it, before linking, so a renamed local keeps it.
void markWitnesses(Module &M, const std::vector<Witness> &witnesses) {
  LLVMContext &C = M.getContext();
  Type *i32 = Type::getInt32Ty(C);
  unsigned hit = 0, miss = 0;
  for (unsigned k = 0; k < witnesses.size(); ++k)
    for (unsigned p = 0; p < witnesses[k].seq.size(); ++p) {
      Function *F = M.getFunction(witnesses[k].seq[p]);
      if (!F || F->isDeclaration()) {
        ++miss;
        continue;
      }
      F->addMetadata("sp.wit", *MDNode::get(C, {ConstantAsMetadata::get(ConstantInt::get(i32, k)),
                                                 ConstantAsMetadata::get(ConstantInt::get(i32, p))}));
      ++hit;
    }
  errs() << "markWitnesses hit " << hit << " miss " << miss << "\n";
}

// §3.7 D item 2: an input-dispatch installer F (`input:F`). The search
// approaches F before the sink so Π_I opens the gate the plan named.
void markStInstallers(Module &M, const std::vector<std::string> &names) {
  LLVMContext &C = M.getContext();
  unsigned hit = 0;
  for (const std::string &n : names) {
    Function *F = M.getFunction(n);
    if (!F || F->isDeclaration())
      continue;
    F->setMetadata("sp.st", MDNode::get(C, {}));
    ++hit;
  }
  errs() << "markStInstallers hit " << hit << " of " << names.size() << "\n";
}

int mustSide(const fs::path &dir, const fs::path &outDir, LLVMContext &ctx, const std::vector<Witness> &witnesses,
             const calls::Table &table, const std::string &file, unsigned line, int rc) {
  SMDiagnostic e2;
  auto up2 = parseIRFile((dir / "upstream.bc").string(), e2, ctx);
  auto down2 = parseIRFile((dir / "se_lib" / "downstream.closure.bc").string(), e2, ctx);
  if (!up2 || !down2)
    return 1;
  closeModules(*down2, *up2, dir);
  annotateLibcalls(*up2);
  annotateLibcalls(*down2);
  if (!calls::annotate(*down2, *up2, table))
    return 1;
  source::reset();
  source::index(*down2);
  source::index(*up2);
  Client client(*down2, *up2, dir);
  std::vector<std::pair<std::vector<std::string>, std::vector<Client::Cell>>> ws;
  for (const Witness &w : witnesses) {
    ws.push_back({w.seq, w.phi});
    client.keyedIn.push_back(w.keyed);
  }
  auto bound = [](const char *name, unsigned dflt) {
    const char *v = std::getenv(name);
    return v && *v ? (unsigned)std::atoi(v) : dflt;
  };
  client.bounds(bound("CLIENT_K", 2), bound("CLIENT_N", 64), bound("CLIENT_D", 2), bound("CLIENT_L", 2));
  // §3.9 정의 E: the same may analysis, with a store's line as the target and
  // the harness calls as the starts.
  unsigned queries = 0, reached = 0;
  const std::set<std::string> iface = Client::publicInterface(*down2, *up2, dir);
  client.reach = [&](const std::string &f, unsigned l, const std::set<std::string> &starts)
      -> std::optional<Client::Reached> {
    ++queries;
    Model m(*down2, *up2, f, l);
    m.interfaceNames = iface;
    m.startNames = starts;
    std::string buf;
    raw_string_ostream o(buf);
    m.run(0, o);
    o.flush();
    std::istringstream in(buf);
    Witness w = parseWitness(in);
    if (w.seq.empty())
      return std::nullopt;
    ++reached;
    return Client::Reached{w.seq, w.phi, w.keyed};
  };
  Client::Plan plan = client.plan(ws);
  errs() << "establish queries " << queries << " reached " << reached << "\n";
  std::error_code ec;
  {
    raw_fd_ostream cout((outDir / "client.txt").string(), ec);
    client.report(plan, cout);
  }
  // Snapshot before linkInModule moves D/U: WitnessPlan::first would dangle.
  std::vector<std::string> unrealizedLines;
  for (const auto &W : plan.witnesses)
    if (!W.realized)
      unrealizedLines.push_back("unrealized " + (W.first ? W.first->getName().str() : "-") + " iface " +
                                std::to_string(W.iface) + " pass " + std::to_string(W.pass) + " dispatch-open " +
                                std::to_string(W.dispatchOpen) + "\n");
  if (plan.witnesses.empty())
    unrealizedLines.push_back("unrealized -\n");
  auto writeUnrealized = [&]() {
    // §5 따름정리: realized = 0 is a model gap (H3 open), never a closed
    // program. No soft-accept on empty cells or a clean link alone.
    if (unrealizedLines.empty())
      return;
    std::ofstream open((outDir / "client.open.txt").string(), std::ios::app);
    for (const std::string &line : unrealizedLines)
      open << line;
    errs() << "open: no realized witness\n";
  };
  const bool anyRealized =
      std::any_of(plan.witnesses.begin(), plan.witnesses.end(), [](const auto &W) { return W.realized; });
  if (!anyRealized) {
    writeUnrealized();
    if (plan.entries.empty())
      return rc;
  } else if (plan.entries.empty()) {
    return rc;
  }
  // The client fixes no result of the library: every byte the library reads
  // is the client's (arguments, callbacks, the file), so the path's
  // comparisons are decided by those bytes, for every witness at once.
  Module ch("client", ctx);
  client.emit(plan, ch);
  if (verifyModule(ch, &errs()))
    return 1;
  markWitnesses(*down2, witnesses);
  markWitnesses(*up2, witnesses);
  markStInstallers(*down2, plan.stInstallers);
  markStInstallers(*up2, plan.stInstallers);
  Linker l2(ch);
  if (l2.linkInModule(std::move(down2)) || l2.linkInModule(std::move(up2))) {
    errs() << "link failed\n";
    return 1;
  }
  // Data the two libraries still leave undefined is filled from the installed
  // images. Function bodies were linked into the two libraries before analysis.
  closeLibrary(ch, dir);
  markStInstallers(ch, plan.stInstallers);
  if (!witnesses.empty())
    plantExternal(ch, witnesses[0].rets, false);
  if (verifyModule(ch, &errs()))
    return 1;
  int r2 = finish(ch, ctx, outDir, "client", file, line);
  // finish() rewrites client.open.txt from link reachability; re-assert the
  // H3 gap when no witness is realized so a clean link cannot soft-accept.
  if (!anyRealized)
    writeUnrealized();
  return rc ? rc : r2;
}

} // namespace

int main(int argc, char **argv) {
  // SIGUSR1 prints where the model is, for a run that takes long.
  signal(SIGUSR1, [](int) {
    void *frames[64];
    int n = backtrace(frames, 64);
    backtrace_symbols_fd(frames, n, STDERR_FILENO);
    (void)!write(STDERR_FILENO, "--\n", 3);
  });
  if (argc != 3 && argc != 4) {
    errs() << "usage: model <cve-dir> <out-dir> [sequence]\n";
    return 1;
  }
  fs::path dir = argv[1];
  fs::path outDir = argv[2];
  int seqPick = argc == 4 ? std::atoi(argv[3]) : 0;
  std::string file;
  unsigned line = 0;
  if (!loadSink(dir / "sink.yaml", file, line)) {
    errs() << "missing sink\n";
    return 1;
  }
  projectExports = Client::installedExports(dir);
  LLVMContext ctx;
  // The must side depends on the may side only through its witnesses and its
  // call relation. With MAY_REUSE set, the witnesses of an earlier run in
  // out-dir stand for the search; the call relation, which the index alone
  // determines, is recomputed so that it covers the present modules.
  if (const char *r = std::getenv("MAY_REUSE"); r && *r && fs::exists(outDir / "witnesses.txt")) {
    calls::Table table;
    {
      SMDiagnostic e;
      auto up = parseIRFile((dir / "upstream.bc").string(), e, ctx);
      auto down = parseIRFile((dir / "se_lib" / "downstream.closure.bc").string(), e, ctx);
      if (!up || !down) {
        e.print("model", errs());
        return 1;
      }
      closeModules(*down, *up, dir);
      annotateLibcalls(*up);
      annotateLibcalls(*down);
      source::index(*down);
      source::index(*up);
      Model m(*down, *up, file, line);
      m.interfaceNames = Client::publicInterface(*down, *up, dir);
      m.startNames = Client::entryInterface(*down, *up, dir);
      m.index();
      m.resolvePrecisely();
      table = m.indirectTargets();
      calls::write(table, outDir / "calls.txt");
    }
    std::vector<Witness> ws;
    {
      std::ifstream st((outDir / "state.txt").string());
      Witness w = parseWitness(st);
      if (!w.seq.empty())
        ws.push_back(w);
    }
    std::ifstream all((outDir / "witnesses.txt").string());
    std::string block;
    for (std::string s; std::getline(all, s);) {
      block += s + "\n";
      if (s != "sat")
        continue;
      std::istringstream in(block);
      Witness v = parseWitness(in);
      if (!v.seq.empty())
        ws.push_back(v);
      block.clear();
    }
    return mustSide(dir, outDir, ctx, ws, table, file, line, 0);
  }
  SMDiagnostic err;
  auto up = parseIRFile((dir / "upstream.bc").string(), err, ctx);
  if (!up) {
    err.print("model", errs());
    return 1;
  }
  SMDiagnostic derr;
  auto down = parseIRFile((dir / "se_lib" / "downstream.closure.bc").string(), derr, ctx);
  if (!down) {
    derr.print("model", errs());
    return 1;
  }
  closeModules(*down, *up, dir);
  annotateLibcalls(*up);
  annotateLibcalls(*down);
  std::error_code ec;
  fs::create_directories(outDir);
  raw_fd_ostream out((outDir / "state.txt").string(), ec);
  if (ec) {
    errs() << ec.message() << "\n";
    return 1;
  }
  source::index(*down);
  source::index(*up);
  Client client(*down, *up, dir);
  Model model(*down, *up, file, line);
  // I = header-declared exports (midpoint). I★ = entryCallable starts (P1).
  model.interfaceNames = Client::publicInterface(*down, *up, dir);
  model.startNames = Client::entryInterface(*down, *up, dir);
  // P1 feasibility = φ SAT ∧ no open Definition-D dispatch edge.
  model.openDispatch = [&](const std::vector<Function *> &fn) {
    std::vector<std::string> seq;
    seq.reserve(fn.size());
    for (Function *F : fn)
      seq.push_back(F->getName().str());
    return client.openDispatchEdges(seq);
  };
  errs() << "interface " << model.interfaceNames.size() << " entry-starts " << model.startNames.size() << "\n";
  model.run(seqPick, out);
  {
    const auto &st = source::stats();
    out << "types source " << st.source << " ir " << st.ir << " renamed " << st.renamed << "\n";
  }
  out.flush();
  errs() << dir.filename().string() << " " << (outDir / "state.txt").string() << "\n";
  // The may answer is the set of satisfiable sequences, not one of them: the
  // sink is reachable when some member is. Each is the next satisfiable
  // sequence after the previous one; the set is finite because each
  // sequence removes the edge by which it leaves the interface.
  std::vector<Witness> witnesses;
  {
    std::ifstream st((outDir / "state.txt").string());
    Witness w = parseWitness(st);
    if (!w.seq.empty())
      witnesses.push_back(w);
    raw_fd_ostream all((outDir / "witnesses.txt").string(), ec);
    for (int n = w.seq.empty() ? -1 : w.index + 1; n >= 0;) {
      Model next(*down, *up, file, line);
      next.interfaceNames = model.interfaceNames;
      next.startNames = model.startNames;
      next.openDispatch = model.openDispatch;
      std::string buf;
      raw_string_ostream o(buf);
      next.run(n, o);
      o.flush();
      std::istringstream in(buf);
      Witness v = parseWitness(in);
      if (v.seq.empty())
        break;
      all << buf;
      witnesses.push_back(v);
      n = v.index + 1;
    }
  }
  calls::Table table = model.indirectTargets();
  calls::write(table, outDir / "calls.txt");
  if (!calls::annotate(*down, *up, table))
    return 1;
  int rc = 0;
  if (model.exportFn()) {
  if (!witnesses.empty()) {
    plantReturns(*down, witnesses[0].rets);
    plantReturns(*up, witnesses[0].rets);
  }
  Module harness("harness", ctx);
  model.emit(harness);
  if (verifyModule(harness, &errs()))
    return 1;
  markWitnesses(*down, witnesses);
  markWitnesses(*up, witnesses);
  Linker linker(harness);
  if (linker.linkInModule(std::move(down)) || linker.linkInModule(std::move(up))) {
    errs() << "link failed\n";
    return 1;
  }
  if (!witnesses.empty())
    plantExternal(harness, witnesses[0].rets);
  // Same closing as the client: installed-image data and native residue.
  closeLibrary(harness, dir);
  if (verifyModule(harness, &errs()))
    return 1;
  rc = finish(harness, ctx, outDir, "run", file, line);
  }
  return mustSide(dir, outDir, ctx, witnesses, table, file, line, rc);
}
