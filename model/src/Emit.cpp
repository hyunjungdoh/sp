#include "Model.h"

#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"

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
      // The struct type whose first field sits at this object's base, used to
      // find the function-pointer members that must hold a valid target.
      std::string type;
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
        if (p->type.empty() && !s.suf[i].type.empty())
          p->type = s.suf[i].type;
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
        bool bare = p.child.empty() && p.symAt.empty() && p.text.empty() && p.word.empty() && p.pathPtrAt.empty() &&
                    p.fileAt.empty() && p.globAt.empty();
        if (!bare)
          continue;
        std::unordered_set<const Function *> seenF;
        uint64_t n = pointedExtent(entry, P, seenF, 0);
        if (P->hasAttribute(Attribute::Dereferenceable))
          n = std::max(n, P->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes());
        if (n == 0)
          continue;
        p.size = std::max(p.size, n);
        p.symAt[0] = n;
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
      std::map<int64_t, Built> child;
    };
    int nameN = 0;
    // Debug info records each struct member's real type, which survives LLVM's
    // opaque pointers. A member whose type is a pointer to a subroutine is a
    // function pointer: control-plane scaffolding set by initialization, not a
    // value read from attacker input. The harness fills those with a benign
    // type-correct stub so an uninitialized handler does not abort execution
    // before the sink, and never leaves one symbolic or null.
    std::map<std::string, std::set<int64_t>> fnPtrOff;
    {
      std::function<DIType *(DIType *)> strip = [&](DIType *T) -> DIType * {
        while (auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
          unsigned tag = D->getTag();
          if (tag == dwarf::DW_TAG_typedef || tag == dwarf::DW_TAG_const_type ||
              tag == dwarf::DW_TAG_volatile_type || tag == dwarf::DW_TAG_atomic_type ||
              tag == dwarf::DW_TAG_restrict_type)
            T = D->getBaseType();
          else
            break;
        }
        return T;
      };
      auto isFnPtr = [&](DIType *T) -> bool {
        T = strip(T);
        auto *D = dyn_cast_or_null<DIDerivedType>(T);
        if (!D || D->getTag() != dwarf::DW_TAG_pointer_type)
          return false;
        return isa_and_nonnull<DISubroutineType>(strip(D->getBaseType()));
      };
      DebugInfoFinder finder;
      finder.processModule(down);
      finder.processModule(up);
      for (DIType *T : finder.types()) {
        auto *CT = dyn_cast<DICompositeType>(T);
        if (!CT || CT->getName().empty())
          continue;
        unsigned tag = CT->getTag();
        if (tag != dwarf::DW_TAG_structure_type && tag != dwarf::DW_TAG_class_type &&
            tag != dwarf::DW_TAG_union_type)
          continue;
        for (DINode *E : CT->getElements()) {
          auto *M = dyn_cast_or_null<DIDerivedType>(E);
          if (!M || M->getTag() != dwarf::DW_TAG_member)
            continue;
          if (isFnPtr(M->getBaseType()))
            fnPtrOff[CT->getName().str()].insert((int64_t)(M->getOffsetInBits() / 8));
        }
      }
    }
    auto bareName = [](StringRef n) -> std::string {
      n.consume_front("struct.");
      n.consume_front("class.");
      n.consume_front("union.");
      size_t dot = n.rfind('.');
      if (dot != StringRef::npos && !n.substr(dot + 1).empty() &&
          n.substr(dot + 1).find_first_not_of("0123456789") == StringRef::npos)
        n = n.substr(0, dot);
      return n.str();
    };
    // One benign stub serves every unresolved function pointer. It takes any
    // signature and returns zero, so a handler call neither crashes nor steers
    // a branch on uninitialized control state.
    Function *stub = H.getFunction("__scaffold_stub");
    if (!stub) {
      auto *stubTy = FunctionType::get(i64, {}, true);
      stub = Function::Create(stubTy, GlobalValue::InternalLinkage, "__scaffold_stub", &H);
      auto *sb = BasicBlock::Create(ctx, "e", stub);
      IRBuilder<> SB(sb);
      SB.CreateRet(ConstantInt::get(i64, 0));
    }
    std::function<Built(const Piece &)> mat = [&](const Piece &p) -> Built {
      uint64_t nbytes = p.size ? p.size : 8;
      auto *arr = ArrayType::get(i8, nbytes);
      Value *base = B.CreateAlloca(arr);
      B.CreateMemSet(base, ConstantInt::get(i8, 0), nbytes, MaybeAlign(1));
      Built built;
      built.base = base;
      std::set<int64_t> fptr;
      if (!p.type.empty()) {
        auto it = fnPtrOff.find(bareName(p.type));
        if (it != fnPtrOff.end())
          fptr = it->second;
      }
      for (int64_t off : fptr) {
        if (off < 0 || (uint64_t)off + dl.getPointerSize(0) > nbytes)
          continue;
        if (p.word.count(off) || p.child.count(off))
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)off)});
        B.CreateStore(stub, slot);
      }
      for (const auto &sm : p.symAt) {
        if (p.child.count(sm.first) || p.word.count(sm.first) || p.text.count(sm.first) ||
            p.pathPtrAt.count(sm.first) || p.fileAt.count(sm.first) || p.globAt.count(sm.first) ||
            fptr.count(sm.first))
          continue;
        if ((uint64_t)sm.first >= nbytes)
          continue;
        uint64_t n = sm.second;
        if ((uint64_t)sm.first + n > nbytes)
          n = nbytes - (uint64_t)sm.first;
        if (n == 0)
          continue;
        Value *slot = B.CreateGEP(i8, base, {ConstantInt::get(i64, (uint64_t)sm.first)});
        // klee_make_symbolic names one whole object. These bytes are a range
        // of the cell, so they are a separate object copied into that range.
        Value *tmp = B.CreateAlloca(ArrayType::get(i8, n));
        auto *nm = B.CreateGlobalString("a" + std::to_string(nameN++));
        B.CreateCall(sym, {tmp, ConstantInt::get(i64, n), nm});
        B.CreateMemCpy(slot, MaybeAlign(1), tmp, MaybeAlign(1), ConstantInt::get(i64, n));
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
        Value *end = B.CreateGEP(i8, cit->second.base, {ConstantInt::get(i64, pit->second.size)});
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
