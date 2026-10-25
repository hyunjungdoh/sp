#include "Model.h"
#include "Client.h"

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
      if (!D || !D->isDeclaration() || D->getName().starts_with("llvm.") || !D->getReturnType()->isIntegerTy())
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
    std::vector<void *> env;
    for (const char *lib : {"libc.so.6", "libm.so.6", "libstdc++.so.6", "libgcc_s.so.1"})
      if (void *h = dlopen(lib, RTLD_LAZY))
        env.push_back(h);
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
    raw_fd_ostream open((outDir / (stem == "run" ? std::string("open.txt") : stem + ".open.txt")).string(), ec);
    for (Function &F : harness) {
      if (!F.isDeclaration() || F.isIntrinsic() || !reach.count(&F) || F.getName().starts_with("klee_"))
        continue;
      std::string name = F.getName().str();
      bool provided = false;
      for (void *h : env)
        provided = provided || dlsym(h, name.c_str());
      if (provided)
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
};

// A run prints every sequence it tries and stops at the first satisfiable
// one, so the witness is its last block. The atoms to discharge are the
// entry formula (model lines). A model line with no fact is not an atom.
// The may cell list is the formula only when this block has no model lines.
Witness parseWitness(std::istream &st) {
  Witness w;
  std::vector<Client::Cell> may, facts;
  bool sawModel = false;
  auto take = [](const std::string &s, std::vector<Client::Cell> &into) {
    std::istringstream in(s);
    std::string head, root, tok, last;
    in >> head >> root;
    std::string op;
    auto bound = [](const std::string &t) {
      return t == "ule" || t == "uge" || t == "ult" || t == "sle" || t == "sge";
    };
    std::vector<std::string> path;
    while (in >> tok) {
      if (tok == "unknown")
        return;
      if (tok == "=" || tok == "!=" || tok[0] == '<' || tok[0] == '>' || bound(tok)) {
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
    while (in >> tok) {
      if (tok == "file") {
        c.file = true;
        break;
      }
      if (bound(tok))
        break;
      if (tok.size() >= 2 && tok.front() == '"' && tok.back() == '"')
        tok = tok.substr(1, tok.size() - 2);
      c.values.push_back(tok);
    }
    into.push_back(std::move(c));
  };
  for (std::string s; std::getline(st, s);) {
    std::istringstream in(s);
    std::string head;
    in >> head;
    if (head == "sequence") {
      w = Witness{};
      may.clear();
      facts.clear();
      sawModel = false;
      std::string n, absent;
      in >> n >> absent;
      if (absent.empty())
        if (auto k = asI64(n))
          w.index = (int)*k;
      continue;
    }
    if (w.index < 0)
      continue;
    if (head == "fn") {
      std::string name;
      in >> name;
      w.seq.push_back(name);
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
        sawModel = true;
        take(s, facts);
      }
    }
  }
  w.phi = sawModel ? facts : may;
  if (w.seq.empty())
    w.index = -1;
  return w;
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

// A pointer result still present after linking. A body stays and the
// comparison is assumed. A declaration with no integer argument cannot
// allocate, so a non-null result is the object the continuation accesses.
static void plantExternal(Module &M, const std::vector<Witness::Ret> &rets) {
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

int mustSide(const fs::path &dir, const fs::path &outDir, LLVMContext &ctx, const std::vector<Witness> &witnesses,
             const std::string &file, unsigned line, int rc) {
  SMDiagnostic e2;
  auto up2 = parseIRFile((dir / "upstream.bc").string(), e2, ctx);
  auto down2 = parseIRFile((dir / "se_lib" / "downstream.closure.bc").string(), e2, ctx);
  if (!up2 || !down2)
    return 1;
  annotateLibcalls(*up2);
  annotateLibcalls(*down2);
  source::reset();
  source::index(*down2);
  source::index(*up2);
  Client client(*down2, *up2, dir);
  std::vector<std::pair<std::vector<std::string>, std::vector<Client::Cell>>> ws;
  for (const Witness &w : witnesses)
    ws.push_back({w.seq, w.phi});
  auto bound = [](const char *name, unsigned dflt) {
    const char *v = std::getenv(name);
    return v && *v ? (unsigned)std::atoi(v) : dflt;
  };
  client.bounds(bound("CLIENT_K", 2), bound("CLIENT_N", 64), bound("CLIENT_D", 2), bound("CLIENT_L", 2));
  Client::Plan plan = client.plan(ws);
  std::error_code ec;
  {
    raw_fd_ostream cout((outDir / "client.txt").string(), ec);
    client.report(plan, cout);
  }
  if (plan.entries.empty())
    return rc;
  if (!witnesses.empty()) {
    plantReturns(*down2, witnesses[0].rets);
    plantReturns(*up2, witnesses[0].rets);
  }
  Module ch("client", ctx);
  client.emit(plan, ch);
  if (verifyModule(ch, &errs()))
    return 1;
  Linker l2(ch);
  if (l2.linkInModule(std::move(down2)) || l2.linkInModule(std::move(up2))) {
    errs() << "link failed\n";
    return 1;
  }
  if (!witnesses.empty())
    plantExternal(ch, witnesses[0].rets);
  if (verifyModule(ch, &errs()))
    return 1;
  int r2 = finish(ch, ctx, outDir, "client", file, line);
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
  LLVMContext ctx;
  // The must side depends on the may side only through its witnesses. With
  // MAY_REUSE set, the witnesses of an earlier run in out-dir stand for it.
  if (const char *r = std::getenv("MAY_REUSE"); r && *r && fs::exists(outDir / "witnesses.txt")) {
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
    return mustSide(dir, outDir, ctx, ws, file, line, 0);
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
  Model model(*down, *up, file, line);
  model.interfaceNames = Client::downstreamInterface(dir);
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
  // sequence removes an edge into the sink.
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
  Linker linker(harness);
  if (linker.linkInModule(std::move(down)) || linker.linkInModule(std::move(up))) {
    errs() << "link failed\n";
    return 1;
  }
  if (!witnesses.empty())
    plantExternal(harness, witnesses[0].rets);
  if (verifyModule(harness, &errs()))
    return 1;
  rc = finish(harness, ctx, outDir, "run", file, line);
  }
  return mustSide(dir, outDir, ctx, witnesses, file, line, rc);
}
