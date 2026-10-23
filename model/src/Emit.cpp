#include "Model.h"

#include "llvm/IR/IntrinsicInst.h"

Function *Model::exportFn() const { return entry; }

StructType *Model::structNamed(StringRef n) const {
    if (n.empty())
      return nullptr;
    for (StructType *S : down.getIdentifiedStructTypes())
      if (S->getName() == n)
        return S;
    for (StructType *S : up.getIdentifiedStructTypes())
      if (S->getName() == n)
        return S;
    return nullptr;
  }

bool Model::fieldIsPointer(StringRef type, int64_t off) const {
    StructType *ST = structNamed(type);
    if (!ST || ST->isOpaque() || !ST->isSized() || off < 0)
      return false;
    const StructLayout *SL = dl.getStructLayout(ST);
    for (unsigned i = 0; i < ST->getNumElements(); ++i)
      if ((int64_t)SL->getElementOffset(i) == off)
        return ST->getElementType(i)->isPointerTy();
    return false;
  }

void Model::emit(Module &H) const {
    if (!entry)
      return;
    LLVMContext &ctx = H.getContext();
    H.setDataLayout(down.getDataLayout());
    H.setTargetTriple(down.getTargetTriple());
    Type *i8 = Type::getInt8Ty(ctx);
    Type *i32 = Type::getInt32Ty(ctx);
    Type *i64 = Type::getInt64Ty(ctx);
    auto *ptrTy = PointerType::get(ctx, 0);
    auto *symTy = FunctionType::get(Type::getVoidTy(ctx), {ptrTy, i64, ptrTy}, false);
    auto *assumeTy = FunctionType::get(Type::getVoidTy(ctx), {i64}, false);
    auto *sym = Function::Create(symTy, Function::ExternalLinkage, "klee_make_symbolic", &H);
    auto *assume = Function::Create(assumeTy, Function::ExternalLinkage, "klee_assume", &H);
    auto declare = [&](Function *F) -> Function * {
      if (!F)
        return nullptr;
      if (Function *E = H.getFunction(F->getName()))
        return E;
      return Function::Create(F->getFunctionType(), Function::ExternalLinkage, F->getName(), &H);
    };
    auto fnNamed = [&](StringRef n) -> Function * {
      if (Function *F = down.getFunction(n))
        return F;
      return up.getFunction(n);
    };
    struct Piece {
      std::map<int64_t, Piece> child;
      std::map<int64_t, std::set<std::string>> word;
      std::map<int64_t, unsigned> width;
      std::map<int64_t, FunctionType *> fileAt;
      std::map<int64_t, uint64_t> fileLenAt;
      std::set<int64_t> pathPtrAt;
      std::map<int64_t, std::set<std::string>> text;
      std::map<int64_t, std::pair<std::string, uint64_t>> globAt;
      std::map<int64_t, uint64_t> symAt;
      std::map<int64_t, std::set<std::string>> ban;
      struct Ord {
        bool slo = false, shi = false, ulo = false, uhi = false;
        int64_t sloV = 0, shiV = 0;
        uint64_t uloV = 0, uhiV = 0;
      };
      std::map<int64_t, Ord> ordAt;
      // end-pointer offset -> offset of the pointer that begins the byte region
      std::map<int64_t, int64_t> boundAt;
      // Indirect-call targets that flow into this field. The stored value is
      // one of these functions, chosen by a symbolic index.
      std::map<int64_t, std::vector<Function *>> choiceAt;
      // A pointer to a constant table: the global and the byte offset inside
      // it. The stored value is one of these addresses, chosen by a symbolic
      // index.
      std::map<int64_t, std::vector<std::pair<GlobalVariable *, uint64_t>>> tableAt;
      uint64_t size = 8;
    };
    std::map<int, Piece> args;
    auto declared = [&](int arg) -> uint64_t {
      if (!entry || arg < 0 || (unsigned)arg >= entry->arg_size())
        return 0;
      Argument *A = entry->getArg((unsigned)arg);
      if (!A->hasAttribute(Attribute::Dereferenceable))
        return 0;
      return A->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
    };
    for (const auto &ex : argExtent) {
      uint64_t n = std::max(ex.second, declared(ex.first));
      args[ex.first].size = std::max(args[ex.first].size, n);
    }
    for (const Solved &s : solvedCells) {
      Piece *p = &args[s.arg];
      Suffix walked;
      int64_t acc = 0;
      bool openPtr = false;
      for (size_t i = 0; i < s.suf.size(); ++i) {
        // A pointer field holds the next object. The step's own deref bit
        // records the same fact when the load was seen directly.
        bool into = s.suf[i].deref || openPtr;
        if (into) {
          p->size = std::max(p->size, (uint64_t)acc + 8);
          p = &p->child[acc];
          acc = 0;
        }
        int64_t off = s.suf[i].off < 0 ? 0 : s.suf[i].off;
        acc += off;
        walked.push_back(s.suf[i]);
        auto rb = readBytes.find({s.arg, walked});
        bool haveLen = rb != readBytes.end() && rb->second != 0;
        uint64_t span = 8;
        if (haveLen)
          span = std::max(span, rb->second);
        p->size = std::max(p->size, (uint64_t)acc + span);
        openPtr = fieldIsPointer(s.suf[i].type, off) && i + 1 < s.suf.size();
        if (i + 1 != s.suf.size())
          continue;
        if (s.file && s.fty) {
          p->fileAt[acc] = s.fty;
          if (s.len)
            p->fileLenAt[acc] = *s.len;
        } else if (s.pathPtr) {
          p->pathPtrAt.insert(acc);
          p->size = std::max(p->size, (uint64_t)acc + 8);
        } else if (!s.text.empty()) {
          p->text[acc] = s.text;
          uint64_t n = 1;
          for (const std::string &t : s.text)
            n = std::max(n, (uint64_t)t.size() + 1);
          p->size = std::max(p->size, (uint64_t)acc + n);
        } else if (!s.glob.empty()) {
          p->globAt[acc] = {s.glob, s.gbyte};
        } else if (!s.vals.empty()) {
          p->word[acc] = s.vals;
          p->width[acc] = s.width ? s.width : 8;
        } else if (!p->child.count(acc)) {
          p->symAt[acc] = span;
          if (!s.ban.empty()) {
            p->ban[acc] = s.ban;
            if (!p->width.count(acc))
              p->width[acc] = s.width ? s.width : (unsigned)span;
          }
        }
        if (s.slo || s.shi || s.ulo || s.uhi) {
          Piece::Ord o;
          o.slo = s.slo;
          o.shi = s.shi;
          o.ulo = s.ulo;
          o.uhi = s.uhi;
          o.sloV = s.sloV;
          o.shiV = s.shiV;
          o.uloV = s.uloV;
          o.uhiV = s.uhiV;
          p->ordAt[acc] = o;
          unsigned wd = s.ordBytes ? s.ordBytes : (s.width ? s.width : 8);
          if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
            wd = 8;
          if (!p->width.count(acc))
            p->width[acc] = wd;
          if (!p->word.count(acc) && !p->child.count(acc) && !p->symAt.count(acc) && !p->text.count(acc) &&
              !p->globAt.count(acc) && !p->fileAt.count(acc) && !p->pathPtrAt.count(acc))
            p->symAt[acc] = std::max<uint64_t>(span, wd);
        }
      }
    }
    for (const PathSrc &ps : pathSrc) {
      Piece &p = args[ps.arg];
      int64_t ptrOff = 0;
      int64_t intOff = -1;
      unsigned intW = 8;
      if (StructType *ST = structNamed(ps.fieldType))
        if (ST->isSized()) {
          const StructLayout *SL = dl.getStructLayout(ST);
          int64_t found = -1;
          for (unsigned i = 0; i < ST->getNumElements() && found < 0; ++i) {
            Type *E = ST->getElementType(i);
            int64_t o = (int64_t)SL->getElementOffset(i);
            if (E->isPointerTy())
              found = o;
            else if (auto *N = dyn_cast<StructType>(E))
              if (N->isSized() && N->getNumElements() && N->getElementType(0)->isPointerTy())
                found = o + (int64_t)dl.getStructLayout(N)->getElementOffset(0);
          }
          if (found >= 0)
            ptrOff = found;
          for (unsigned i = 0; i < ST->getNumElements(); ++i) {
            Type *E = ST->getElementType(i);
            int64_t o = (int64_t)SL->getElementOffset(i);
            if (o <= ptrOff || !E->isIntegerTy())
              continue;
            intOff = o;
            intW = std::max<unsigned>(1, E->getIntegerBitWidth() / 8);
            break;
          }
        }
      p.pathPtrAt.insert(ptrOff);
      p.size = std::max(p.size, (uint64_t)ptrOff + 8);
      if (intOff > ptrOff) {
        p.word[intOff] = {"1"};
        p.width[intOff] = intW;
        p.symAt.erase(intOff);
        p.size = std::max(p.size, (uint64_t)intOff + intW);
      }
    }
    auto placeIn = [&](int arg, const Suffix &suf) -> std::pair<Piece *, int64_t> {
      auto it = args.find(arg);
      if (it == args.end())
        return {nullptr, 0};
      Piece *p = &it->second;
      int64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        bool into = suf[i].deref || open;
        if (into) {
          auto ch = p->child.find(acc);
          if (ch == p->child.end())
            return {nullptr, 0};
          p = &ch->second;
          acc = 0;
        }
        acc += suf[i].off < 0 ? 0 : suf[i].off;
        open = fieldIsPointer(suf[i].type, suf[i].off) && i + 1 < suf.size();
      }
      return {p, acc};
    };
    for (const PtrSpan &sp : ptrSpan) {
      auto b = placeIn(sp.arg, sp.begin);
      auto e = placeIn(sp.arg, sp.end);
      if (!b.first || b.first != e.first || b.second == e.second)
        continue;
      if (!b.first->child.count(b.second))
        continue;
      b.first->boundAt[e.second] = b.second;
    }
    std::function<void(Piece &)> tieLen = [&](Piece &p) {
      for (auto &ch : p.child) {
        bool bytes = ch.second.child.empty() && ch.second.symAt.count(0) && ch.second.symAt.at(0) > dl.getPointerSize(0);
        int64_t lenOff = ch.first + (int64_t)dl.getPointerSize(0);
        auto sm = p.symAt.find(lenOff);
        if (bytes && sm != p.symAt.end() && !p.word.count(lenOff) && !p.child.count(lenOff)) {
          unsigned wd = (unsigned)sm->second;
          if (wd == 4 || wd == 8) {
            p.word[lenOff] = {std::to_string(ch.second.size)};
            p.width[lenOff] = wd;
            p.symAt.erase(sm);
          }
        }
        tieLen(ch.second);
      }
    };
    for (auto &kv : args)
      tieLen(kv.second);
    std::map<int, uint64_t> tiedCount;
    auto namesArg = [&](Value *V, unsigned argNo) {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *A = dyn_cast<Argument>(V))
          return A->getParent() == entry && A->getArgNo() == argNo;
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!Al)
            return false;
          Value *st = storedOnce(Al);
          if (!st)
            return false;
          V = st;
          continue;
        }
        return false;
      }
      return false;
    };
    // The integer is the buffer's length when a write in the entry passes
    // that pointer and, immediately after it, that integer.
    auto usedAsCount = [&](unsigned ptrArg, unsigned intArg) {
      if (!entry || entry->isDeclaration())
        return false;
      for (Instruction &I : instructions(*entry)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->onlyReadsMemory())
          continue;
        if (Function *C = CB->getCalledFunction()) {
          StringRef n = C->getName();
          if (n.starts_with("llvm.dbg.") || n.starts_with("llvm.lifetime.") || n.starts_with("llvm.experimental."))
            continue;
        }
        for (unsigned k = 0; k + 1 < CB->arg_size(); ++k) {
          if (!CB->getArgOperand(k)->getType()->isPointerTy() || !CB->getArgOperand(k + 1)->getType()->isIntegerTy())
            continue;
          if (CB->onlyReadsMemory(k))
            continue;
          if (namesArg(CB->getArgOperand(k), ptrArg) && namesArg(CB->getArgOperand(k + 1), intArg))
            return true;
        }
      }
      return false;
    };
    if (entry) {
      for (unsigned i = 0; i + 1 < entry->arg_size(); ++i) {
        Argument *P = entry->getArg(i);
        Argument *N = entry->getArg(i + 1);
        if (!P->getType()->isPointerTy() || !N->getType()->isIntegerTy())
          continue;
        if (!usedAsCount(i, i + 1))
          continue;
        Piece &p = args[(int)i];
        std::unordered_set<const Function *> seenF;
        uint64_t n = pointedExtent(entry, P, seenF, 0);
        if (P->hasAttribute(Attribute::Dereferenceable))
          n = std::max(n, P->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes());
        n = std::max(n, p.size);
        if (n == 0)
          continue;
        p.size = n;
        if (p.child.empty() && p.word.empty() && p.text.empty() && p.globAt.empty() && p.fileAt.empty())
          p.symAt[0] = std::max(p.symAt.count(0) ? p.symAt[0] : 0, n);
        // The count is the length of this object. A larger integer is not a
        // defined read of the object.
        tiedCount[(int)i + 1] = p.size;
      }
    }
    Function *exp = declare(entry);
    auto *mainTy = FunctionType::get(i32, false);
    auto *mainF = Function::Create(mainTy, Function::ExternalLinkage, "main", &H);
    auto *BB = BasicBlock::Create(ctx, "entry", mainF);
    IRBuilder<> B(BB);
    auto *fdg = new GlobalVariable(H, i32, false, GlobalValue::PrivateLinkage, ConstantInt::get(i32, -1), "filefd");
    auto *openTy = FunctionType::get(i32, {ptrTy, i32}, true);
    auto *readTy = FunctionType::get(i64, {i32, ptrTy, i64}, false);
    auto *openF = Function::Create(openTy, Function::ExternalLinkage, "open", &H);
    auto *readF = Function::Create(readTy, Function::ExternalLinkage, "read", &H);
    auto *fileObj = new GlobalVariable(H, i8, false, GlobalValue::PrivateLinkage, ConstantInt::get(i8, 0), "fileobj");
    for (const FileIO &io : fileIO) {
      if (H.getFunction(io.name))
        continue;
      Function *Src = down.getFunction(io.name);
      if (!Src)
        Src = up.getFunction(io.name);
      if (!Src || !Src->isDeclaration())
        continue;
      FunctionType *FT = Src->getFunctionType();
      unsigned nArg = FT->getNumParams();
      auto inRange = [&](int i) { return i >= 0 && (unsigned)i < nArg; };
      if (io.opener && !inRange(io.pathArg))
        continue;
      if (!io.opener && (!inRange(io.bufArg) || !inRange(io.countArg)))
        continue;
      Function *F = Function::Create(FT, Function::ExternalLinkage, io.name, &H);
      auto *e = BasicBlock::Create(ctx, "e", F);
      IRBuilder<> IB(e);
      auto pathIsF = [&](Value *path) -> Value * {
        Value *c0 = IB.CreateLoad(i8, path);
        Value *c1 = IB.CreateLoad(i8, IB.CreateGEP(i8, path, {ConstantInt::get(i64, 1)}));
        return IB.CreateAnd(IB.CreateICmpEQ(c0, ConstantInt::get(i8, 'f')),
                             IB.CreateICmpEQ(c1, ConstantInt::get(i8, 0)));
      };
      if (io.opener) {
        Value *ok = pathIsF(F->getArg((unsigned)io.pathArg));
        if (io.retPtr)
          IB.CreateRet(IB.CreateSelect(ok, fileObj, Constant::getNullValue(ptrTy)));
        else if (F->getReturnType()->isIntegerTy())
          IB.CreateRet(IB.CreateSelect(ok, ConstantInt::get(F->getReturnType(), 3),
                                        ConstantInt::getSigned(F->getReturnType(), -1)));
        else
          IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      if (io.bufArg < 0 || io.countArg < 0 || (unsigned)io.bufArg >= F->arg_size() ||
          (unsigned)io.countArg >= F->arg_size()) {
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      Value *n = F->getArg((unsigned)io.countArg);
      if (!n->getType()->isIntegerTy()) {
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
        continue;
      }
      if (n->getType() != i64)
        n = IB.CreateZExt(n, i64);
      if (io.count2 >= 0 && (unsigned)io.count2 < F->arg_size() &&
          F->getArg((unsigned)io.count2)->getType()->isIntegerTy()) {
        Value *m = F->getArg((unsigned)io.count2);
        if (m->getType() != i64)
          m = IB.CreateZExt(m, i64);
        n = IB.CreateMul(n, m);
      }
      auto *nm = IB.CreateGlobalString("f");
      IB.CreateCall(sym, {F->getArg((unsigned)io.bufArg), n, nm});
      Value *ret = io.count2 >= 0 ? F->getArg((unsigned)io.count2) : F->getArg((unsigned)io.countArg);
      if (!F->getReturnType()->isIntegerTy())
        IB.CreateRet(Constant::getNullValue(F->getReturnType()));
      else if (ret->getType() == F->getReturnType())
        IB.CreateRet(ret);
      else
        IB.CreateRet(IB.CreateZExtOrTrunc(ret, F->getReturnType()));
    }
    {
      auto *e = BasicBlock::Create(ctx, "e", openF);
      IRBuilder<> IB(e);
      Value *path = openF->getArg(0);
      Value *c0 = IB.CreateLoad(i8, path);
      Value *c1 = IB.CreateLoad(i8, IB.CreateGEP(i8, path, {ConstantInt::get(i64, 1)}));
      Value *ok = IB.CreateAnd(IB.CreateICmpEQ(c0, ConstantInt::get(i8, 'f')),
                                IB.CreateICmpEQ(c1, ConstantInt::get(i8, 0)));
      IB.CreateRet(IB.CreateSelect(ok, ConstantInt::get(i32, 3), ConstantInt::get(i32, -1)));
    }
    {
      auto *e = BasicBlock::Create(ctx, "e", readF);
      auto *yes = BasicBlock::Create(ctx, "file", readF);
      auto *no = BasicBlock::Create(ctx, "other", readF);
      IRBuilder<> IB(e);
      IB.CreateCondBr(IB.CreateICmpEQ(readF->getArg(0), ConstantInt::get(i32, 3)), yes, no);
      IB.SetInsertPoint(yes);
      auto *nm = IB.CreateGlobalString("f");
      IB.CreateCall(sym, {readF->getArg(1), readF->getArg(2), nm});
      IB.CreateRet(readF->getArg(2));
      IB.SetInsertPoint(no);
      IB.CreateRet(ConstantInt::get(i64, (uint64_t)-1));
    }
    std::map<std::pair<FunctionType *, uint64_t>, Function *> readers;
    auto readerFor = [&](FunctionType *FT, uint64_t len) -> Function * {
      auto it = readers.find({FT, len});
      if (it != readers.end())
        return it->second;
      auto *F = Function::Create(FT, Function::ExternalLinkage, "fileread", &H);
      auto *e = BasicBlock::Create(ctx, "e", F);
      auto *op = BasicBlock::Create(ctx, "op", F);
      auto *rd = BasicBlock::Create(ctx, "rd", F);
      IRBuilder<> IB(e);
      Value *buf = nullptr;
      Value *n = nullptr;
      for (Argument &A : F->args()) {
        if (!buf && A.getType()->isPointerTy())
          buf = &A;
        if (!n && A.getType()->isIntegerTy())
          n = &A;
      }
      if (!buf || !n) {
        IB.CreateRet(Constant::getNullValue(FT->getReturnType()));
        readers[{FT, len}] = F;
        return F;
      }
      auto *path = IB.CreateGlobalString("f");
      Value *cur = IB.CreateLoad(i32, fdg);
      IB.CreateCondBr(IB.CreateICmpSLT(cur, ConstantInt::get(i32, 0)), op, rd);
      IB.SetInsertPoint(op);
      Value *opened = IB.CreateCall(openF, {path, ConstantInt::get(i32, 0)});
      IB.CreateStore(opened, fdg);
      IB.CreateBr(rd);
      IB.SetInsertPoint(rd);
      auto *phi = IB.CreatePHI(i32, 2);
      phi->addIncoming(cur, e);
      phi->addIncoming(opened, op);
      Value *count = n;
      if (n->getType() != i64)
        count = IB.CreateZExtOrTrunc(n, i64);
      if (len != ~uint64_t{0}) {
        Value *eq = IB.CreateICmpEQ(count, ConstantInt::get(i64, len));
        IB.CreateCall(assume, {IB.CreateZExt(eq, i64)});
      }
      Value *got = IB.CreateCall(readF, {phi, buf, count});
      if (FT->getReturnType()->isVoidTy())
        IB.CreateRetVoid();
      else if (FT->getReturnType() == i64)
        IB.CreateRet(got);
      else if (FT->getReturnType()->isIntegerTy())
        IB.CreateRet(IB.CreateZExtOrTrunc(got, FT->getReturnType()));
      else
        IB.CreateRet(Constant::getNullValue(FT->getReturnType()));
      readers[{FT, len}] = F;
      return F;
    };
    unsigned ai = 0;
    for (Argument &A : entry->args()) {
      if (ai < callActs.size()) {
        const Act &a = callActs[ai];
        if (A.getType()->isPointerTy() && a.loc && a.address && a.loc->suf.empty()) {
          Piece &p = args[a.loc->arg];
          uint64_t n = 0;
          if (A.hasAttribute(Attribute::Dereferenceable))
            n = A.getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
          if (A.hasStructRetAttr()) {
            Type *T = A.getAttribute(Attribute::StructRet).getValueAsType();
            if (T && T->isSized())
              n = std::max(n, (uint64_t)dl.getTypeAllocSize(T).getFixedValue());
          }
          p.size = std::max(p.size, std::max<uint64_t>(n, 8));
        }
      }
      ++ai;
    }
    struct Built {
      Value *base = nullptr;
      uint64_t size = 0;
      std::map<int64_t, Built> child;
    };
    int nameN = 0;
    // A witness for an indirect call is an assignment of named functions to the
    // export cell the call loads. targetsOf supplies that set when it names
    // definitions. An empty result abstains: the cell then takes the functions
    // the solved frontier already named, and if it named none the cell holds no
    // function. No type is filled with every function of that type. The model
    // claims nothing about a callee that is not an export cell. Containment is
    // checked when the call executes: a callee value that can be anything other
    // than a defined function ends that execution as uncertain.
    // Each function is summarized once. A binding is the export cell a formal
    // stands for, extended by the suffix walked inside the function. A step
    // that already occurs in that suffix is a cycle, so the binding is not
    // inserted. A pointer cell the code dereferences and that has no object
    // becomes an object whose size is the constant offset and width of the
    // accesses. The same bytes read as an integer, two call types, or an empty
    // intersection are uncertain.
    struct Acc {
      bool bad = false;
      FunctionType *ty = nullptr;
      bool have = false;
      bool open = false;
      std::set<Function *> fns;
      std::vector<CallBase *> sites;
    };
    auto locKey = [](const Loc &L) {
      std::string k = std::to_string(L.arg);
      for (const Step &s : L.suf) {
        k.push_back('|');
        k += s.type;
        k.push_back('@');
        k += std::to_string(s.off);
        k.push_back(s.deref ? '*' : '.');
      }
      return k;
    };
    std::map<std::string, Acc> accs;
    std::map<std::string, Loc> locOfKey;
    std::map<int, Acc> argAcc;
    std::set<std::string> dataKeys;
    std::set<int> argData;
    struct Form {
      bool ok = false;
      int formal = -1;
      Suffix suf;
      bool pointee = false;
    };
    auto formalOf = [&](Function *F, Value *V) -> Form {
      std::unordered_set<const Value *> seen;
      std::function<Form(Value *)> go = [&](Value *V) -> Form {
        Form bad;
        if (!V || !seen.insert(V).second)
          return bad;
        if (auto *C = dyn_cast<CastInst>(V))
          return go(C->getOperand(0));
        if (auto *CE = dyn_cast<ConstantExpr>(V))
          if (CE->isCast())
            return go(CE->getOperand(0));
        if (auto *G = dyn_cast<GEPOperator>(V)) {
          Step st;
          if (!constStep(dl, G, st))
            return bad;
          Form b = go(G->getPointerOperand());
          if (!b.ok)
            return bad;
          st.deref = b.pointee;
          if (movesAddress(st)) {
            b.suf.push_back(st);
            b.pointee = false;
          }
          return b;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
            Value *st = storedOnce(A);
            return st ? go(st) : bad;
          }
          if (!L->getType()->isPointerTy())
            return bad;
          Form b = go(L->getPointerOperand());
          if (!b.ok)
            return bad;
          b.pointee = true;
          return b;
        }
        if (auto *P = dyn_cast<PHINode>(V)) {
          Value *one = nullptr;
          for (Value *in : P->incoming_values()) {
            if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
              continue;
            if (one && one != in)
              return bad;
            one = in;
          }
          return one ? go(one) : bad;
        }
        if (auto *A = dyn_cast<Argument>(V)) {
          if (A->getParent() != F)
            return bad;
          Form f;
          f.ok = true;
          f.formal = (int)A->getArgNo();
          return f;
        }
        return bad;
      };
      return go(V);
    };
    auto sufKey = [](const Suffix &s) {
      std::string k;
      for (const Step &st : s) {
        k.push_back('|');
        k += st.type;
        k.push_back('@');
        k += std::to_string(st.off);
        k.push_back(st.deref ? '*' : '.');
      }
      return k;
    };
    auto repeats = [](const Suffix &s) {
      for (size_t i = 0; i < s.size(); ++i)
        for (size_t j = 0; j < i; ++j)
          if (s[i] == s[j])
            return true;
      return false;
    };
    struct Bind {
      int arg = -1;
      Suffix suf;
    };
    auto compose = [&](const Bind &base, const Suffix &extra, bool extraPointee, Bind &out) -> bool {
      out.arg = base.arg;
      out.suf = base.suf;
      out.suf.insert(out.suf.end(), extra.begin(), extra.end());
      if (extraPointee)
        out.suf.push_back(Step{"", 0, true});
      return !repeats(out.suf);
    };
    struct Use {
      int formal = -1;
      Suffix suf;
      CallBase *cb = nullptr;
      FunctionType *ty = nullptr;
      std::vector<Function *> tg;
      bool open = false;
      bool argLevel = false;
      bool mixed = false;
    };
    struct Edge {
      Function *to = nullptr;
      int toArg = -1;
      int formal = -1;
      Suffix suf;
      bool pointee = false;
    };
    struct Need {
      int formal = -1;
      Suffix suf;
      uint64_t width = 0;
    };
    struct Sum {
      std::vector<Use> uses;
      std::vector<Edge> edges;
      std::vector<Need> needs;
    };
    auto bodyOf = [&](Function *T) -> Function * {
      if (!T)
        return nullptr;
      if (!T->isDeclaration())
        return T;
      return define(T->getName());
    };
    std::unordered_map<Function *, Sum> sum;
    std::unordered_set<Function *> summarized;
    std::deque<Function *> fq;
    struct Item {
      Function *F = nullptr;
      int formal = -1;
      Bind b;
    };
    std::deque<Item> bq;
    std::unordered_map<Function *, std::vector<std::vector<Bind>>> binds;
    std::unordered_map<Function *, std::vector<std::unordered_set<std::string>>> seenBind;
    auto bindKey = [&](const Bind &b) {
      std::string k = std::to_string(b.arg);
      k += sufKey(b.suf);
      return k;
    };
    auto remember = [&](Function *F, int formal, const Bind &b) -> bool {
      if (!F || formal < 0 || (unsigned)formal >= F->arg_size() || b.arg < 0)
        return false;
      auto &slot = seenBind[F];
      if (slot.size() < F->arg_size())
        slot.resize(F->arg_size());
      if (!slot[(unsigned)formal].insert(bindKey(b)).second)
        return false;
      auto &held = binds[F];
      if (held.size() < F->arg_size())
        held.resize(F->arg_size());
      held[(unsigned)formal].push_back(b);
      bq.push_back(Item{F, formal, b});
      return true;
    };
    auto build = [&](Function *F) {
      Sum s;
      auto noteDeref = [&](Value *ptr, uint64_t width) {
        if (!ptr || width == 0)
          return;
        Form f = formalOf(F, ptr);
        if (!f.ok)
          return;
        bool deref = f.pointee;
        for (const Step &st : f.suf)
          if (st.deref)
            deref = true;
        if (!deref)
          return;
        Need n;
        n.formal = f.formal;
        n.suf = f.suf;
        if (f.pointee)
          n.suf.push_back(Step{"", 0, true});
        if (repeats(n.suf))
          return;
        n.width = width;
        s.needs.push_back(std::move(n));
      };
      for (Instruction &I : instructions(*F)) {
        if (auto *L = dyn_cast<LoadInst>(&I)) {
          if (L->getType()->isSized())
            noteDeref(L->getPointerOperand(), dl.getTypeStoreSize(L->getType()).getFixedValue());
          if (!L->getType()->isPointerTy()) {
            Form f = formalOf(F, L->getPointerOperand());
            if (f.ok && !f.pointee)
              dataKeys.insert(std::to_string(reinterpret_cast<uintptr_t>(F)) + "#" + std::to_string(f.formal) + sufKey(f.suf));
          }
        } else if (auto *ST = dyn_cast<StoreInst>(&I)) {
          if (ST->getValueOperand()->getType()->isSized())
            noteDeref(ST->getPointerOperand(), dl.getTypeStoreSize(ST->getValueOperand()->getType()).getFixedValue());
        }
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *direct = CB->getCalledFunction();
        if (direct && ignorable(direct))
          continue;
        if (direct && (direct->getName().starts_with("llvm.memcpy") || direct->getName().starts_with("llvm.memmove") ||
                       direct->getName().starts_with("llvm.memset"))) {
          if (CB->arg_size() >= 3)
            if (auto *N = dyn_cast<ConstantInt>(CB->getArgOperand(2))) {
              uint64_t len = N->getZExtValue();
              noteDeref(CB->getArgOperand(0), len);
              if (!direct->getName().starts_with("llvm.memset") && CB->arg_size() >= 2)
                noteDeref(CB->getArgOperand(1), len);
            }
          continue;
        }
        auto addEdge = [&](Function *D) {
          Function *B = bodyOf(D);
          if (!B)
            return;
          for (unsigned i = 0; i < CB->arg_size() && i < B->arg_size(); ++i) {
            Form f = formalOf(F, CB->getArgOperand(i));
            if (!f.ok)
              continue;
            Edge e;
            e.to = B;
            e.toArg = (int)i;
            e.formal = f.formal;
            e.suf = f.suf;
            e.pointee = f.pointee;
            s.edges.push_back(std::move(e));
          }
          if (!summarized.count(B))
            fq.push_back(B);
        };
        if (!direct) {
          Value *V = CB->getCalledOperand();
          std::unordered_set<const Value *> seenV;
          while (V && seenV.insert(V).second) {
            if (auto *C = dyn_cast<CastInst>(V)) {
              V = C->getOperand(0);
              continue;
            }
            if (auto *CE = dyn_cast<ConstantExpr>(V))
              if (CE->isCast()) {
                V = CE->getOperand(0);
                continue;
              }
            break;
          }
          Use u;
          u.cb = CB;
          u.ty = CB->getFunctionType();
          for (Function *T : targetsOf(CB)) {
            Function *B = bodyOf(T);
            if (!B)
              continue;
            if (u.ty && B->getFunctionType() != u.ty)
              continue;
            u.tg.push_back(B);
          }
          std::sort(u.tg.begin(), u.tg.end());
          u.tg.erase(std::unique(u.tg.begin(), u.tg.end()), u.tg.end());
          u.open = u.tg.empty();
          Form slot;
          bool addressed = false;
          if (auto *L = dyn_cast<LoadInst>(V)) {
            slot = formalOf(F, L->getPointerOperand());
            addressed = true;
          } else
            slot = formalOf(F, V);
          if (!slot.ok) {
            for (Function *T : u.tg)
              addEdge(T);
            continue;
          }
          u.formal = slot.formal;
          u.suf = slot.suf;
          if (slot.pointee)
            u.suf.push_back(Step{"", 0, true});
          u.argLevel = !addressed && u.suf.empty();
          s.uses.push_back(std::move(u));
          for (Function *T : s.uses.back().tg)
            addEdge(T);
          continue;
        }
        addEdge(direct);
      }
      for (Use &u : s.uses) {
        Suffix addr = u.suf;
        if (!addr.empty() && addr.back().type.empty() && addr.back().off == 0 && addr.back().deref)
          addr.pop_back();
        if (dataKeys.count(std::to_string(reinterpret_cast<uintptr_t>(F)) + "#" + std::to_string(u.formal) + sufKey(addr)))
          u.mixed = true;
      }
      sum[F] = std::move(s);
      summarized.insert(F);
    };
    auto drainFuncs = [&]() {
      while (!fq.empty()) {
        Function *F = fq.front();
        fq.pop_front();
        if (!F || F->isDeclaration() || summarized.count(F))
          continue;
        build(F);
      }
    };
    auto drainBinds = [&]() {
      while (!bq.empty()) {
        Item it = std::move(bq.front());
        bq.pop_front();
        auto sit = sum.find(it.F);
        if (sit == sum.end())
          continue;
        for (const Edge &e : sit->second.edges) {
          if (e.formal != it.formal || !e.to)
            continue;
          Bind nb;
          if (!compose(it.b, e.suf, e.pointee, nb))
            continue;
          remember(e.to, e.toArg, nb);
        }
      }
    };
    if (entry && !entry->isDeclaration())
      fq.push_back(entry);
    drainFuncs();
    if (entry && !entry->isDeclaration()) {
      for (unsigned i = 0; i < entry->arg_size(); ++i) {
        Bind b;
        b.arg = (int)i;
        remember(entry, (int)i, b);
      }
    }
    drainBinds();
    auto wordFns = [&](const Bind &cell, FunctionType *ty) {
      std::vector<Function *> v;
      auto pl = placeIn(cell.arg, cell.suf);
      if (!pl.first || !pl.first->word.count(pl.second))
        return v;
      for (const std::string &name : pl.first->word.at(pl.second)) {
        Function *B = bodyOf(fnNamed(name));
        if (!B || (ty && B->getFunctionType() != ty))
          continue;
        v.push_back(B);
      }
      return v;
    };
    bool grew = true;
    while (grew) {
      grew = false;
      for (auto &sk : sum) {
        Function *caller = sk.first;
        for (const Use &u : sk.second.uses) {
          if (!u.open || u.formal < 0)
            continue;
          auto bit = binds.find(caller);
          if (bit == binds.end() || (unsigned)u.formal >= bit->second.size())
            continue;
          for (const Bind &b : bit->second[(unsigned)u.formal]) {
            Bind cell;
            if (!compose(b, u.suf, false, cell))
              continue;
            for (Function *D : wordFns(cell, u.ty)) {
              if (!summarized.count(D)) {
                fq.push_back(D);
                grew = true;
              }
              if (!u.cb)
                continue;
              for (unsigned i = 0; i < u.cb->arg_size() && i < D->arg_size(); ++i) {
                Form f = formalOf(caller, u.cb->getArgOperand(i));
                if (!f.ok)
                  continue;
                auto cit = binds.find(caller);
                if (cit == binds.end() || (unsigned)f.formal >= cit->second.size())
                  continue;
                for (const Bind &ab : cit->second[(unsigned)f.formal]) {
                  Bind nb;
                  if (compose(ab, f.suf, f.pointee, nb) && remember(D, (int)i, nb))
                    grew = true;
                }
              }
            }
          }
        }
      }
      drainFuncs();
      drainBinds();
    }
    auto note = [&](Acc &a, const Use &u) {
      if (u.cb)
        a.sites.push_back(u.cb);
      if (u.mixed)
        a.bad = true;
      if (a.bad)
        return;
      if (!u.ty || (a.ty && a.ty != u.ty)) {
        a.bad = true;
        return;
      }
      a.ty = u.ty;
      if (u.open) {
        a.open = true;
        return;
      }
      std::set<Function *> s(u.tg.begin(), u.tg.end());
      if (s.empty()) {
        a.open = true;
        return;
      }
      if (!a.have) {
        a.have = true;
        a.fns = std::move(s);
        return;
      }
      std::set<Function *> both;
      std::set_intersection(a.fns.begin(), a.fns.end(), s.begin(), s.end(), std::inserter(both, both.end()));
      if (both.empty())
        a.bad = true;
      else
        a.fns.swap(both);
    };
    for (auto &sk : sum) {
      Function *F = sk.first;
      for (const Use &u : sk.second.uses) {
        auto bit = binds.find(F);
        if (bit == binds.end() || u.formal < 0 || (unsigned)u.formal >= bit->second.size() ||
            bit->second[(unsigned)u.formal].empty())
          continue;
        for (const Bind &b : bit->second[(unsigned)u.formal]) {
          Bind cell;
          if (!compose(b, u.suf, false, cell))
            continue;
          if (u.argLevel && cell.suf.empty()) {
            note(argAcc[cell.arg], u);
            continue;
          }
          Loc loc;
          loc.arg = cell.arg;
          loc.suf = cell.suf;
          std::string k = locKey(loc);
          locOfKey[k] = loc;
          note(accs[k], u);
        }
      }
    }
    auto ensureObj = [&](int arg, const Suffix &suf, uint64_t width) {
      if (arg < 0 || width == 0)
        return;
      if (!args.count(arg))
        args[arg] = Piece{};
      Piece *p = &args[arg];
      int64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        bool into = suf[i].deref || open;
        if (into) {
          if (!p->child.count(acc)) {
            Piece ch;
            ch.size = std::max<uint64_t>(width, 8);
            p->child.emplace(acc, std::move(ch));
          }
          p->symAt.erase(acc);
          p->size = std::max(p->size, (uint64_t)(acc < 0 ? 0 : acc) + dl.getPointerSize(0));
          p = &p->child[acc];
          acc = 0;
        }
        acc += suf[i].off < 0 ? 0 : suf[i].off;
        open = fieldIsPointer(suf[i].type, suf[i].off) && i + 1 < suf.size();
      }
      p->size = std::max(p->size, (uint64_t)(acc < 0 ? 0 : acc) + width);
    };
    for (auto &sk : sum) {
      Function *F = sk.first;
      auto bit = binds.find(F);
      if (bit == binds.end())
        continue;
      for (const Need &n : sk.second.needs) {
        if (n.formal < 0 || (unsigned)n.formal >= bit->second.size())
          continue;
        for (const Bind &b : bit->second[(unsigned)n.formal]) {
          Bind cell;
          if (!compose(b, n.suf, false, cell))
            continue;
          ensureObj(cell.arg, cell.suf, n.width);
        }
      }
    }
    auto realize = [&](Acc &a) -> std::vector<Function *> {
      std::vector<Function *> fns;
      if (a.bad || !a.have)
        return fns;
      for (Function *F : a.fns)
        if (F && (!a.ty || F->getFunctionType() == a.ty))
          fns.push_back(F);
      std::sort(fns.begin(), fns.end(), [](Function *A, Function *B) { return A->getName() < B->getName(); });
      fns.erase(std::unique(fns.begin(), fns.end()), fns.end());
      return fns;
    };
    std::map<int, std::vector<Function *>> argChoice;
    for (auto &kv : accs) {
      Acc &a = kv.second;
      std::vector<Function *> may = realize(a);
      std::vector<Function *> fns;
      // One named target determines the cell. A larger set is every function
      // that call could reach, which is not a value of the cell. It becomes a
      // witness only when the solved frontier names a function inside that set.
      if (may.size() == 1)
        fns = may;
      if (a.bad) {
        continue;
      }
      auto it = locOfKey.find(kv.first);
      if (it == locOfKey.end()) {
        continue;
      }
      const Loc &loc = it->second;
      if (!args.count(loc.arg))
        args[loc.arg] = Piece{};
      auto pl = placeIn(loc.arg, loc.suf);
      if (!pl.first) {
        continue;
      }
      if (pl.first->child.count(pl.second)) {
        continue;
      }
      Piece *p = pl.first;
      int64_t off = pl.second;
      if (p->word.count(off)) {
        std::vector<Function *> pinned;
        bool ok = true;
        for (const std::string &v : p->word[off]) {
          Function *B = bodyOf(fnNamed(v));
          if (!B) {
            ok = false;
            break;
          }
          if (a.ty && B->getFunctionType() != a.ty)
            continue;
          if (!may.empty() && std::find(may.begin(), may.end(), B) == may.end())
            continue;
          pinned.push_back(B);
        }
        if (!ok || pinned.empty()) {
          continue;
        }
        fns = std::move(pinned);
        p->word.erase(off);
      }
      if (fns.empty()) {
        continue;
      }
      p->symAt.erase(off);
      p->choiceAt[off] = std::move(fns);
      p->size = std::max(p->size, (uint64_t)off + dl.getPointerSize(0));
    }
    // A callee cell inside the pointee of a pointer cell constrains that
    // pointer: the slot at its offset holds a function of the call's set.
    // The values the program gives such a pointer are the constant tables it
    // stores at that field, at the address point it stores. The domain of
    // the pointer is every stored table whose slots meet all constraints.
    // An empty domain leaves the pointee an object built from its cells.
    {
      indexVtables();
      // A slot the residual calls holds a defined function of the call's
      // type; a named set narrows it further.
      struct Slot {
        int64_t at = 0;
        FunctionType *ty = nullptr;
        std::set<std::string> fns;
      };
      struct Table {
        int arg = -1;
        Suffix prefix;
        std::vector<Slot> slots;
      };
      std::map<std::string, Table> tables;
      for (auto &kv : accs) {
        Acc &a = kv.second;
        auto it = locOfKey.find(kv.first);
        if (a.bad || it == locOfKey.end())
          continue;
        const Loc &loc = it->second;
        size_t j = loc.suf.size();
        while (j > 0 && !loc.suf[j - 1].deref)
          --j;
        if (j == 0)
          continue;
        --j;
        Slot s;
        s.ty = a.ty;
        for (size_t i = j; i < loc.suf.size(); ++i)
          s.at += loc.suf[i].off;
        auto pl = placeIn(loc.arg, loc.suf);
        if (pl.first && pl.first->choiceAt.count(pl.second))
          for (Function *F : pl.first->choiceAt.at(pl.second))
            s.fns.insert(F->getName().str());
        else
          for (Function *F : realize(a))
            s.fns.insert(F->getName().str());
        if (s.fns.empty() && a.have)
          continue;
        Suffix prefix(loc.suf.begin(), loc.suf.begin() + (long)j);
        Table &t = tables[std::to_string(loc.arg) + sufKey(prefix)];
        t.arg = loc.arg;
        t.prefix = prefix;
        t.slots.push_back(std::move(s));
      }
      for (auto &kv : tables) {
        const Table &t = kv.second;
        auto pl = placeIn(t.arg, t.prefix);
        if (!pl.first)
          continue;
        std::vector<std::pair<GlobalVariable *, uint64_t>> dom;
        uint64_t extent = 0;
        for (const VTab &vt : vtAll) {
          if (!vt.last || !vt.g || !vt.g->hasInitializer() || vt.field != pl.second)
            continue;
          bool ok = true;
          for (const Slot &s : t.slots) {
            if (s.at < 0) {
              ok = false;
              break;
            }
            Function *F = functionAt(vt.g->getInitializer(), 0, vt.base + (uint64_t)s.at);
            if (!F || F->isDeclaration() || (s.ty && F->getFunctionType() != s.ty) ||
                (!s.fns.empty() && !s.fns.count(F->getName().str()))) {
              ok = false;
              break;
            }
          }
          if (!ok)
            continue;
          extent = std::max(extent, vt.extent);
          if (std::find(dom.begin(), dom.end(), std::make_pair(vt.g, vt.base)) == dom.end())
            dom.push_back({vt.g, vt.base});
        }
        if (dom.empty())
          continue;
        Piece *p = pl.first;
        int64_t off = pl.second;
        // The table fixes the object's layout, so the object spans the
        // largest layout among the tables it may hold.
        p->size = std::max(p->size, extent);
        p->child.erase(off);
        p->symAt.erase(off);
        p->word.erase(off);
        p->choiceAt.erase(off);
        p->tableAt[off] = std::move(dom);
        p->size = std::max(p->size, (uint64_t)off + dl.getPointerSize(0));
      }
    }
    for (auto &kv : argAcc) {
      Acc &a = kv.second;
      std::vector<Function *> fns = realize(a);
      if (fns.size() != 1)
        fns.clear();
      bool object = false;
      if (args.count(kv.first)) {
        const Piece &p = args[kv.first];
        object = !p.child.empty() || !p.symAt.empty() || !p.word.empty() || !p.text.empty() || !p.globAt.empty() ||
                 !p.fileAt.empty() || !p.pathPtrAt.empty() || !p.choiceAt.empty() || !p.tableAt.empty();
      }
      if (fns.empty() || object) {
        continue;
      }
      argChoice[kv.first] = std::move(fns);
    }
    auto pick = [&](IRBuilder<> &IB, const std::vector<Constant *> &elems) -> Value * {
      if (elems.empty())
        return nullptr;
      if (elems.size() == 1)
        return elems[0];
      auto *arrTy = ArrayType::get(ptrTy, elems.size());
      auto *table = new GlobalVariable(H, arrTy, true, GlobalValue::PrivateLinkage, ConstantArray::get(arrTy, elems),
                                      "callee.tab." + std::to_string(nameN++));
      Value *mem = IB.CreateAlloca(i32);
      auto *nm = IB.CreateGlobalString("c" + std::to_string(nameN++));
      IB.CreateCall(sym, {mem, ConstantInt::get(i64, 4), nm});
      Value *k = IB.CreateLoad(i32, mem);
      Value *inRange = IB.CreateICmpULT(k, ConstantInt::get(i32, elems.size()));
      IB.CreateCall(assume, {IB.CreateZExt(inRange, i64)});
      Value *slot = IB.CreateInBoundsGEP(arrTy, table, {ConstantInt::get(i64, 0), k});
      return IB.CreateLoad(ptrTy, slot);
    };
    auto choose = [&](IRBuilder<> &IB, const std::vector<Function *> &fns) -> Value * {
      std::vector<Constant *> decls;
      for (Function *F : fns)
        if (Function *D = declare(F))
          decls.push_back(D);
      return pick(IB, decls);
    };
    auto chooseTable = [&](IRBuilder<> &IB, const std::vector<std::pair<GlobalVariable *, uint64_t>> &dom) -> Value * {
      std::vector<Constant *> addrs;
      for (const auto &t : dom) {
        GlobalVariable *g = H.getNamedGlobal(t.first->getName());
        if (!g)
          g = new GlobalVariable(H, t.first->getValueType(), true, GlobalValue::ExternalLinkage, nullptr,
                                 t.first->getName());
        addrs.push_back(ConstantExpr::getGetElementPtr(i8, g, ConstantInt::get(i64, t.second)));
      }
      return pick(IB, addrs);
    };
    std::function<Built(const Piece &)> mat = [&](const Piece &p) -> Built {
      // A determined cell is a byte range [off, off + width) whose value a
      // fact fixes. The object holds every determined cell, and its symbolic
      // bytes are the ranges no determined cell covers.
      const uint64_t ptrW = dl.getPointerSize(0);
      std::vector<std::pair<int64_t, uint64_t>> fixed;
      auto wordWidth = [&](int64_t off) -> uint64_t {
        unsigned wd = p.width.count(off) ? p.width.at(off) : 8;
        return wd == 1 || wd == 2 || wd == 4 || wd == 8 ? wd : 8;
      };
      for (const auto &kv : p.child)
        fixed.push_back({kv.first, ptrW});
      for (const auto &kv : p.choiceAt)
        fixed.push_back({kv.first, ptrW});
      for (const auto &kv : p.tableAt)
        fixed.push_back({kv.first, ptrW});
      for (const auto &kv : p.boundAt)
        fixed.push_back({kv.first, ptrW});
      for (const auto &kv : p.globAt)
        fixed.push_back({kv.first, ptrW});
      for (const auto &kv : p.fileAt)
        fixed.push_back({kv.first, ptrW});
      for (int64_t off : p.pathPtrAt)
        fixed.push_back({off, ptrW});
      for (const auto &kv : p.word)
        if (!p.child.count(kv.first))
          fixed.push_back({kv.first, wordWidth(kv.first)});
      for (const auto &kv : p.text) {
        uint64_t n = 0;
        for (const std::string &s : kv.second)
          n = std::max<uint64_t>(n, s.size() + 1);
        if (n && !p.child.count(kv.first))
          fixed.push_back({kv.first, n});
      }
      uint64_t nbytes = p.size ? p.size : 8;
      for (const auto &c : fixed)
        if (c.first >= 0)
          nbytes = std::max(nbytes, (uint64_t)c.first + c.second);
      std::vector<bool> owned(nbytes, false);
      for (const auto &c : fixed)
        for (uint64_t i = 0; c.first >= 0 && i < c.second; ++i)
          owned[(uint64_t)c.first + i] = true;
      // The program may take ownership of an entry object and free it, so
      // every object lives on the heap.
      FunctionCallee mallocF = H.getOrInsertFunction("malloc", FunctionType::get(ptrTy, {i64}, false));
      Value *base = B.CreateCall(mallocF, {ConstantInt::get(i64, nbytes)});
      B.CreateMemSet(base, ConstantInt::get(i8, 0), nbytes, MaybeAlign(1));
      Built built;
      built.base = base;
      built.size = nbytes;
      for (const auto &ch : p.choiceAt) {
        if (ch.first < 0 || (uint64_t)ch.first + dl.getPointerSize(0) > nbytes || p.child.count(ch.first))
          continue;
        Value *chosen = choose(B, ch.second);
        if (!chosen)
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)ch.first)});
        B.CreateStore(chosen, slot);
      }
      for (const auto &t : p.tableAt) {
        if (t.first < 0 || p.child.count(t.first))
          continue;
        Value *chosen = chooseTable(B, t.second);
        if (!chosen)
          continue;
        B.CreateStore(chosen, B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)t.first)}));
      }
      for (const auto &sm : p.symAt) {
        if (p.child.count(sm.first) || p.word.count(sm.first) || p.text.count(sm.first) ||
            p.pathPtrAt.count(sm.first) || p.fileAt.count(sm.first) || p.globAt.count(sm.first) ||
            p.choiceAt.count(sm.first))
          continue;
        if ((uint64_t)sm.first >= nbytes)
          continue;
        uint64_t end = std::min<uint64_t>(nbytes, (uint64_t)sm.first + sm.second);
        for (uint64_t at = (uint64_t)sm.first; at < end;) {
          if (owned[at]) {
            ++at;
            continue;
          }
          uint64_t stop = at;
          while (stop < end && !owned[stop])
            ++stop;
          uint64_t n = stop - at;
          Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, at)});
          // klee_make_symbolic names one whole object. These bytes are a range
          // of the cell, so they are a separate object copied into that range.
          Value *tmp = B.CreateAlloca(ArrayType::get(i8, n));
          auto *nm = B.CreateGlobalString("a" + std::to_string(nameN++));
          B.CreateCall(sym, {tmp, ConstantInt::get(i64, n), nm});
          B.CreateMemCpy(slot, MaybeAlign(1), tmp, MaybeAlign(1), ConstantInt::get(i64, n));
          at = stop;
        }
      }
      for (const auto &b : p.ban) {
        auto sit = p.symAt.find(b.first);
        if (sit == p.symAt.end() || b.second.empty())
          continue;
        unsigned wd = p.width.count(b.first) ? p.width.at(b.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        if (sit->second < wd)
          continue;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)b.first)});
        Value *got = B.CreateLoad(ty, slot);
        Value *ok = ConstantInt::getTrue(ctx);
        for (const std::string &v : b.second)
          ok = B.CreateAnd(ok, B.CreateICmpNE(got, ConstantInt::get(ty, (uint64_t)std::stoll(v), true)));
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      for (const auto &o : p.ordAt) {
        auto sit = p.symAt.find(o.first);
        if (sit == p.symAt.end())
          continue;
        unsigned wd = p.width.count(o.first) ? p.width.at(o.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        if (sit->second < wd)
          continue;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)o.first)});
        Value *got = B.CreateLoad(ty, slot);
        Value *ok = ConstantInt::getTrue(ctx);
        const Piece::Ord &b = o.second;
        if (b.slo)
          ok = B.CreateAnd(ok, B.CreateICmpSGE(got, ConstantInt::get(ty, (uint64_t)b.sloV, true)));
        if (b.shi)
          ok = B.CreateAnd(ok, B.CreateICmpSLE(got, ConstantInt::get(ty, (uint64_t)b.shiV, true)));
        if (b.ulo)
          ok = B.CreateAnd(ok, B.CreateICmpUGE(got, ConstantInt::get(ty, b.uloV, false)));
        if (b.uhi)
          ok = B.CreateAnd(ok, B.CreateICmpULE(got, ConstantInt::get(ty, b.uhiV, false)));
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      for (const auto &f : p.fileAt) {
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)f.first)});
        uint64_t len = ~uint64_t{0};
        auto lit = p.fileLenAt.find(f.first);
        if (lit != p.fileLenAt.end())
          len = lit->second;
        B.CreateStore(readerFor(f.second, len), slot);
      }
      for (const auto &g : p.globAt) {
        GlobalVariable *src = down.getNamedGlobal(g.second.first);
        if (!src)
          src = up.getNamedGlobal(g.second.first);
        if (src && !p.child.count(g.first)) {
          GlobalVariable *gv = H.getNamedGlobal(src->getName());
          if (!gv)
            gv = new GlobalVariable(H, src->getValueType(), false, GlobalValue::ExternalLinkage, nullptr, src->getName());
          Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)g.first)});
          Value *addr = B.CreateGEP(i8, gv, {ConstantInt::get(i64, g.second.second)});
          B.CreateStore(addr, slot);
        }
      }
      for (int64_t off : p.pathPtrAt) {
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)off)});
        auto *bytes = B.CreateGlobalString("f");
        B.CreateStore(bytes, slot);
      }
      for (const auto &t : p.text) {
        if (p.child.count(t.first) || t.second.empty())
          continue;
        std::vector<std::string> opts(t.second.begin(), t.second.end());
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)t.first)});
        auto *kmem = B.CreateAlloca(i32);
        auto *kn = B.CreateGlobalString("k" + std::to_string(nameN++));
        B.CreateCall(sym, {kmem, ConstantInt::get(i64, 4), kn});
        Value *k = B.CreateLoad(i32, kmem);
        Value *inRange = B.CreateICmpULT(k, ConstantInt::get(i32, opts.size()));
        B.CreateCall(assume, {B.CreateZExt(inRange, i64)});
        Function *mf = B.GetInsertBlock()->getParent();
        auto *cont = BasicBlock::Create(ctx, "kcont", mf);
        auto *def = BasicBlock::Create(ctx, "kdef", mf);
        auto *sw = B.CreateSwitch(k, def, opts.size());
        auto storeText = [&](BasicBlock *bb, const std::string &str) {
          IRBuilder<> IB(bb);
          for (size_t i = 0; i <= str.size(); ++i) {
            Value *at = IB.CreateGEP(i8, slot, {ConstantInt::get(i64, i)});
            IB.CreateStore(ConstantInt::get(i8, i == str.size() ? 0 : (unsigned char)str[i]), at);
          }
          IB.CreateBr(cont);
        };
        for (unsigned i = 0; i < opts.size(); ++i) {
          BasicBlock *bb = i == 0 ? def : BasicBlock::Create(ctx, "kcase", mf);
          if (i != 0)
            sw->addCase(cast<ConstantInt>(ConstantInt::get(i32, i)), bb);
          storeText(bb, opts[i]);
        }
        B.SetInsertPoint(cont);
      }
      for (const auto &ch : p.child) {
        Built inner = mat(ch.second);
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)ch.first)});
        B.CreateStore(inner.base, slot);
        built.child.emplace(ch.first, std::move(inner));
      }
      for (const auto &bd : p.boundAt) {
        auto cit = built.child.find(bd.second);
        auto pit = p.child.find(bd.second);
        if (cit == built.child.end() || pit == p.child.end())
          continue;
        Value *end = B.CreateGEP(i8, cit->second.base, {ConstantInt::get(i64, cit->second.size)});
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)bd.first)});
        B.CreateStore(end, slot);
      }
      for (const auto &w : p.word) {
        if (p.child.count(w.first))
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)w.first)});
        unsigned wd = p.width.count(w.first) ? p.width.at(w.first) : 8;
        if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
          wd = 8;
        Type *ty = Type::getIntNTy(ctx, wd * 8);
        bool allFn = true;
        for (const std::string &v : w.second)
          if (!fnNamed(v))
            allFn = false;
        if (w.second.size() == 1) {
          if (allFn)
            B.CreateStore(declare(fnNamed(*w.second.begin())), slot);
          else
            B.CreateStore(ConstantInt::get(ty, (uint64_t)std::stoll(*w.second.begin()), true), slot);
          continue;
        }
        auto *nm = B.CreateGlobalString("c" + std::to_string(nameN++));
        Value *tmp = B.CreateAlloca(ArrayType::get(i8, wd));
        B.CreateCall(sym, {tmp, ConstantInt::get(i64, wd), nm});
        B.CreateMemCpy(slot, MaybeAlign(1), tmp, MaybeAlign(1), ConstantInt::get(i64, wd));
        Value *got = B.CreateLoad(allFn ? ptrTy : ty, slot);
        Value *ok = ConstantInt::get(Type::getInt1Ty(ctx), 0);
        for (const std::string &v : w.second) {
          Value *want = nullptr;
          if (Function *F = fnNamed(v))
            want = declare(F);
          else
            want = ConstantInt::get(ty, (uint64_t)std::stoll(v), true);
          ok = B.CreateOr(ok, B.CreateICmpEQ(got, want));
        }
        B.CreateCall(assume, {B.CreateZExt(ok, i64)});
      }
      return built;
    };
    std::map<int, Built> roots;
    auto rootFor = [&](int arg) -> Built {
      auto it = roots.find(arg);
      if (it != roots.end())
        return it->second;
      Piece p = args.count(arg) ? args[arg] : Piece{};
      if (p.size < 8)
        p.size = 8;
      Built b = mat(p);
      roots.emplace(arg, b);
      return b;
    };
    auto place = [&](const Built &root, const Suffix &suf) -> std::pair<Value *, uint64_t> {
      const Built *cur = &root;
      Value *at = root.base;
      uint64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        const Step &s = suf[i];
        if (s.deref || open) {
          auto it = cur->child.find((int64_t)acc);
          if (it == cur->child.end())
            break;
          cur = &it->second;
          at = cur->base;
          acc = 0;
        }
        acc += (uint64_t)(s.off < 0 ? 0 : s.off);
        open = fieldIsPointer(s.type, s.off) && i + 1 < suf.size();
      }
      return {at, acc};
    };
    auto addressOf = [&](const Built &root, const Suffix &suf) -> Value * {
      auto at = place(root, suf);
      if (!at.second)
        return at.first;
      return B.CreateGEP(i8, at.first, {ConstantInt::get(i64, at.second)});
    };
    auto valueOf = [&](const Built &root, const Suffix &suf) -> Value * {
      const Built *cur = &root;
      uint64_t acc = 0;
      bool open = false;
      for (size_t i = 0; i < suf.size(); ++i) {
        const Step &s = suf[i];
        if (s.deref || open) {
          auto it = cur->child.find((int64_t)acc);
          if (it == cur->child.end())
            break;
          cur = &it->second;
          acc = 0;
        }
        acc += (uint64_t)(s.off < 0 ? 0 : s.off);
        open = fieldIsPointer(s.type, s.off) && i + 1 < suf.size();
      }
      auto it = cur->child.find((int64_t)acc);
      if (it != cur->child.end())
        return it->second.base;
      if (suf.empty())
        return root.base;
      return B.CreateLoad(ptrTy, addressOf(root, suf));
    };
    auto symInt = [&](Type *ty) -> Value * {
      unsigned bits = ty->getIntegerBitWidth();
      uint64_t n = std::max<uint64_t>(1, (bits + 7) / 8);
      Value *mem = B.CreateAlloca(ty);
      auto *nm = B.CreateGlobalString("i" + std::to_string(nameN++));
      B.CreateCall(sym, {mem, ConstantInt::get(i64, n), nm});
      return B.CreateLoad(ty, mem);
    };
    std::vector<Value *> acts;
    ai = 0;
    for (Argument &A : entry->args()) {
      Act a = ai < callActs.size() ? callActs[ai] : Act{};
      ++ai;
      Value *act = nullptr;
      if (a.nullPtr) {
        act = Constant::getNullValue(A.getType());
      } else if (!a.fn.empty()) {
        Function *F = fnNamed(a.fn);
        act = F ? declare(F) : Constant::getNullValue(A.getType());
      } else if (argChoice.count((int)acts.size()) && A.getType()->isPointerTy()) {
        act = choose(B, argChoice[(int)acts.size()]);
      } else if (A.getType()->isIntegerTy()) {
        auto tc = tiedCount.find((int)acts.size());
        if (tc != tiedCount.end())
          act = ConstantInt::get(A.getType(), tc->second);
        else if (a.haveInt)
          act = ConstantInt::get(A.getType(), (uint64_t)a.ival, true);
        else if (a.loc && !a.address)
          act = B.CreateLoad(A.getType(), addressOf(rootFor(a.loc->arg), a.loc->suf));
        else
          act = symInt(A.getType());
      } else if (A.getType()->isPointerTy() && a.loc) {
        Built root = rootFor(a.loc->arg);
        act = a.address || a.loc->suf.empty() ? addressOf(root, a.loc->suf) : valueOf(root, a.loc->suf);
      } else if (A.getType()->isPointerTy()) {
        Piece p;
        uint64_t n = 8;
        if (A.hasAttribute(Attribute::Dereferenceable))
          n = std::max(n, A.getAttribute(Attribute::Dereferenceable).getDereferenceableBytes());
        if (A.hasStructRetAttr()) {
          Type *T = A.getAttribute(Attribute::StructRet).getValueAsType();
          if (T && T->isSized())
            n = std::max(n, (uint64_t)dl.getTypeAllocSize(T).getFixedValue());
        }
        p.size = n;
        act = mat(p).base;
      } else {
        act = Constant::getNullValue(A.getType());
      }
      acts.push_back(act);
    }
    for (const Rel &r : rels) {
      unsigned wd = r.bytes;
      if (wd != 1 && wd != 2 && wd != 4 && wd != 8)
        wd = 8;
      Type *ty = Type::getIntNTy(ctx, wd * 8);
      auto loadAt = [&](int arg, const Suffix &suf) -> Value * {
        Built root = rootFor(arg);
        auto at = place(root, suf);
        Value *slot = at.second ? B.CreateGEP(i8, at.first, {ConstantInt::get(i64, at.second)}) : at.first;
        return B.CreateLoad(ty, slot);
      };
      Value *cmp = B.CreateICmp((ICmpInst::Predicate)r.pred, loadAt(r.a, r.asuf), loadAt(r.b, r.bsuf));
      B.CreateCall(assume, {B.CreateZExt(cmp, i64)});
    }
    B.CreateCall(exp, acts);
    B.CreateRet(ConstantInt::get(i32, 0));
  }
