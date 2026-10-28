#include "Model.h"

void Model::run(int seqPick, raw_ostream &out) {
    sinks = findSinks();
    if (sinks.empty()) {
      out << "sink none\n";
      return;
    }
    // Experiment gate: when set, resolve local-held pointers eagerly during the
    // index passes too, so one binary can show the index output is identical
    // with or without the staging. Off by default.
    if (const char *e = std::getenv("SP_EAGER_HELD"); e && *e)
      resolveHeld = true;
    indexFunctions();
    exports = findExports();
    buildCallers();
    cone = reachSink();
    starts = findStarts();
    out << "starts " << starts.size() << "\n";
    // Indexing is done. Resolve local-held pointers precisely from here on.
    resolveHeld = true;
    for (int n = seqPick;; ++n) {
      auto paths = sequences(n);
      if ((int)paths.size() <= n) {
        out << "sequence " << n << " absent\n";
        out << "paths " << paths.size() << "\n";
        entry = nullptr;
        solvedCells.clear();
        return;
      }
      const auto &path = paths[(size_t)n];
      out << "sequence " << n << "\n";
      for (Function *F : path.fn)
        out << "fn " << F->getName() << " " << pretty(F->getName()) << "\n";
      inputs(path.fn, out);
      if (solve(path.fn, out))
        return;
    }
  }

Function *Model::define(StringRef name) const {
    auto body = [&](Module &M) -> Function * {
      if (Function *F = M.getFunction(name))
        if (!F->isDeclaration())
          return F;
      if (GlobalAlias *A = M.getNamedAlias(name))
        if (Constant *Ali = A->getAliasee())
          if (auto *F = dyn_cast<Function>(Ali->stripPointerCasts()))
            if (!F->isDeclaration())
              return F;
      return nullptr;
    };
    if (Function *D = body(down))
      return D;
    return body(up);
  }

bool Model::noBody(CallBase *CB) {
    if (Function *C = CB->getCalledFunction())
      return define(C->getName()) == nullptr;
    for (Function *T : targetsOf(CB))
      if (!T->isDeclaration() || define(T->getName()))
        return false;
    return true;
  }

std::vector<Function *> Model::findSinks() {
    std::vector<Function *> found;
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        found.push_back(&F);
        break;
      }
    });
    std::sort(found.begin(), found.end(), [](Function *A, Function *B) { return A->getName() < B->getName(); });
    found.erase(std::unique(found.begin(), found.end()), found.end());
    return found;
  }

Suffix Model::suffix(Value *V) const {
    Suffix s;
    std::unordered_set<const Value *> seen;
    if (!V)
      return s;
    {
      Value *U = V;
      while (auto *C = dyn_cast<CastInst>(U))
        U = C->getOperand(0);
      if (auto *L = dyn_cast<LoadInst>(U))
        V = L->getPointerOperand();
    }
    while (V && seen.insert(V).second) {
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      auto *G = dyn_cast<GEPOperator>(V);
      if (G) {
        if (!G->hasAllConstantIndices()) {
          // A variable index of an array is one element cell. A variable
          // field of a struct is not a cell.
          if (isa<StructType>(G->getSourceElementType()))
            return {};
          V = G->getPointerOperand();
          continue;
        }
        APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (!G->accumulateConstantOffset(dl, off))
          return {};
        std::string k = source::container(G, dl);
        if (!k.empty())
          s.insert(s.begin(), Step{k, off.getSExtValue()});
        V = G->getPointerOperand();
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        if (!s.empty())
          break;
        V = L->getPointerOperand();
        continue;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        Value *one = nullptr;
        bool bad = false;
        for (Value *in : P->incoming_values()) {
          if (isa<UndefValue>(in) || isa<ConstantPointerNull>(in))
            continue;
          if (one && one != in) {
            bad = true;
            break;
          }
          one = in;
        }
        if (bad || !one)
          return {};
        V = one;
        continue;
      }
      break;
    }
    return s;
  }

std::vector<Model::InitSite> Model::initializers(const std::string &type, const std::set<int64_t> &cells) const {
    auto memo = initMemo.find({type, cells});
    if (memo != initMemo.end())
      return memo->second;
    auto callers = [&](Function *F) -> const std::vector<Function *> & {
      static const std::vector<Function *> none;
      auto it = callersOf.find(F);
      return it == callersOf.end() ? none : it->second;
    };
    // Methods: the functions the struct's fields hold, and the helpers only
    // they call.
    std::set<Function *> methods;
    for (const auto &kv : initSites)
      if (kv.first.first == type && cells.count(kv.first.second))
        for (const InitSite &s : kv.second)
          methods.insert(s.stored);
    for (const auto &[field, fns] : fieldFns)
      if (field.first == type && cells.count(field.second))
        methods.insert(fns.begin(), fns.end());
    std::set<Function *> callbacks;
    for (const auto &kv : initSites)
      if (kv.first.first == type)
        for (const InitSite &s : kv.second)
          callbacks.insert(s.stored);
    for (const auto &[field, fns] : fieldFns)
      if (field.first == type)
        callbacks.insert(fns.begin(), fns.end());
    for (bool grew = true; grew;) {
      grew = false;
      eachBody([&](Function &F) {
        if (methods.count(&F))
          return;
        const auto &cs = callers(&F);
        if (cs.empty())
          return;
        for (Function *C : cs)
          if (!methods.count(C))
            return;
        methods.insert(&F);
        grew = true;
      });
    }
    std::map<Function *, unsigned> site;
    for (const auto &kv : initSites)
      if (kv.first.first == type && cells.count(kv.first.second))
        for (const InitSite &s : kv.second)
          if (!methods.count(s.fn))
            site.emplace(s.fn, s.arg);
    auto formalOf = [](Value *V) -> int {
      V = V->stripPointerCasts();
      if (auto *A = dyn_cast<Argument>(V))
        return (int)A->getArgNo();
      auto *L = dyn_cast<LoadInst>(V);
      auto *Al = L ? dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
      if (!Al)
        return -1;
      int at = -1;
      for (User *U : Al->users())
        if (auto *S = dyn_cast<StoreInst>(U))
          if (S->getPointerOperand()->stripPointerCasts() == Al) {
            auto *A = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
            if (!A || (at != -1 && at != (int)A->getArgNo()))
              return -1;
            at = (int)A->getArgNo();
          }
      return at;
    };
    auto scalarsBut = [](Function *F, unsigned obj) {
      for (Argument &A : F->args())
        if (A.getArgNo() != obj && !A.getType()->isIntegerTy())
          return false;
      return true;
    };
    // The formal whose object a pointer lies in.
    auto rootOf = [&](Value *V) -> int {
      for (int n = 0; n < 32 && V; ++n) {
        V = V->stripPointerCasts();
        if (auto *A = dyn_cast<Argument>(V))
          return (int)A->getArgNo();
        if (auto *G = dyn_cast<GEPOperator>(V)) {
          V = G->getPointerOperand();
          continue;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          if (isa<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
            return formalOf(L);
          V = L->getPointerOperand();
          continue;
        }
        return -1;
      }
      return -1;
    };
    // Deallocators: free, and the functions that pass a formal's object to a
    // deallocator.
    std::set<std::pair<Function *, unsigned>> frees;
    for (bool grew = true; grew;) {
      grew = false;
      eachBody([&](Function &F) {
        for (Instruction &I : instructions(F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          Function *C = CB ? CB->getCalledFunction() : nullptr;
          if (!C)
            continue;
          if (Function *D = define(C->getName()))
            C = D;
          for (unsigned i = 0; i < CB->arg_size(); ++i) {
            if (C->getName() != "free" && !frees.count({C, i}))
              continue;
            int k = formalOf(CB->getArgOperand(i));
            if (k >= 0 && frees.insert({&F, (unsigned)k}).second)
              grew = true;
          }
        }
      });
    }
    // A site that releases memory of its object ends that object's state
    // rather than establishing it.
    auto releases = [&](Function *S, unsigned obj) {
      for (Instruction &I : instructions(*S)) {
        auto *CB = dyn_cast<CallBase>(&I);
        Function *C = CB ? CB->getCalledFunction() : nullptr;
        if (!C)
          continue;
        if (Function *D = define(C->getName()))
          C = D;
        for (unsigned i = 0; i < CB->arg_size(); ++i)
          if ((C->getName() == "free" || frees.count({C, i})) && rootOf(CB->getArgOperand(i)) == (int)obj)
            return true;
      }
      return false;
    };
    for (auto it = site.begin(); it != site.end();)
      it = callbacks.count(it->first) || releases(it->first, it->second) ? site.erase(it) : std::next(it);
    // A site whose scalars its caller passes from its own formals is run
    // through that caller, which chooses them as the program does.
    std::vector<Function *> work;
    for (const auto &kv : site)
      work.push_back(kv.first);
    while (!work.empty()) {
      Function *S = work.back();
      work.pop_back();
      unsigned obj = site[S];
      if (scalarsBut(S, obj) && S->arg_size() <= 1)
        continue;
      bool hasScalar = false;
      for (Argument &A : S->args())
        hasScalar = hasScalar || (A.getArgNo() != obj && A.getType()->isIntegerTy());
      if (!hasScalar)
        continue;
      for (Function *P : callers(S)) {
        if (site.count(P) || methods.count(P) || callbacks.count(P) || P->isDeclaration())
          continue;
        for (Instruction &I : instructions(*P)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->arg_size() <= obj)
            continue;
          auto ts = targetsOf(CB);
          if (std::find(ts.begin(), ts.end(), S) == ts.end())
            continue;
          int k = formalOf(CB->getArgOperand(obj));
          if (k < 0 || !scalarsBut(P, (unsigned)k))
            continue;
          bool through = true;
          for (unsigned i = 0; i < CB->arg_size(); ++i) {
            if (i == obj)
              continue;
            Value *A = CB->getArgOperand(i);
            if (!isa<ConstantInt>(A) && formalOf(A) < 0 && !isa<Argument>(A) && !isa<LoadInst>(A))
              through = false;
          }
          if (!through || releases(P, (unsigned)k))
            continue;
          site.emplace(P, (unsigned)k);
          work.push_back(P);
          break;
        }
      }
    }
    std::vector<InitSite> out;
    auto runs = [&](Function *F) {
      auto it = site.find(F);
      return it != site.end() && scalarsBut(F, it->second);
    };
    // Functions run only within initializers or methods: what every caller
    // of one does is part of a larger initializer.
    std::set<Function *> within;
    for (bool grew = true; grew;) {
      grew = false;
      eachBody([&](Function &F) {
        if (within.count(&F))
          return;
        const auto &cs = callers(&F);
        if (cs.empty())
          return;
        for (Function *C : cs)
          if (!runs(C) && !methods.count(C) && !within.count(C))
            return;
        within.insert(&F);
        grew = true;
      });
    }
    for (const auto &kv : site) {
      if (!runs(kv.first))
        continue;
      bool inner = within.count(kv.first);
      if (!inner)
        out.push_back(InitSite{kv.first, kv.second, nullptr});
    }
    std::sort(out.begin(), out.end(),
              [](const InitSite &a, const InitSite &b) { return a.fn->getName() < b.fn->getName(); });
    initMemo[{type, cells}] = out;
    return out;
  }

std::string Model::dec(const ConstantInt *CI) {
    SmallVector<char, 32> buf;
    CI->getValue().toString(buf, 10, true);
    return std::string(buf.begin(), buf.end());
  }

void Model::noteScalar(const Suffix &suf, const std::string &v) {
    if (!suf.empty())
      facts[suf].insert(v);
  }

std::string Model::shape(Type *T) {
    auto it = shapeMemo.find(T);
    if (it != shapeMemo.end())
      return it->second;
    shapeMemo[T] = "?";
    std::string s;
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) {
        s = "opaque";
      } else {
        const StructLayout *SL = dl.getStructLayout(ST);
        s = "{";
        for (unsigned i = 0; i < ST->getNumElements(); ++i) {
          s += std::to_string(SL->getElementOffset(i));
          s += ":";
          s += shape(ST->getElementType(i));
          s += ";";
        }
        s += "}";
      }
    } else if (auto *AT = dyn_cast<ArrayType>(T)) {
      s = "[" + std::to_string(AT->getNumElements()) + "x" + shape(AT->getElementType()) + "]";
    } else {
      s = std::to_string(dl.getTypeAllocSize(T).getFixedValue());
    }
    shapeMemo[T] = s;
    return s;
  }

void Model::ensureShapes() {
    if (shapesReady)
      return;
    shapesReady = true;
    for (Module *M : {&down, &up})
      for (StructType *ST : M->getIdentifiedStructTypes())
        if (ST->hasName() && !ST->isOpaque())
          namedByShape[shape(ST)].push_back(ST);
  }

std::vector<StructType *> Model::namesFor(StructType *ST) {
    ensureShapes();
    if (!ST || ST->isOpaque())
      return {};
    if (ST->hasName())
      return {ST};
    auto it = namedByShape.find(shape(ST));
    if (it == namedByShape.end())
      return {};
    std::vector<StructType *> out;
    std::set<std::string> seen;
    for (StructType *N : it->second)
      if (seen.insert(N->getName().str()).second)
        out.push_back(N);
    return out;
  }

void Model::noteZero(Type *Ty, const Suffix &suf) {
    if (!Ty)
      return;
    if (Ty->isIntegerTy() || Ty->isPointerTy()) {
      noteScalar(suf, "0");
      return;
    }
    if (auto *ST = dyn_cast<StructType>(Ty)) {
      for (StructType *N : namesFor(ST)) {
        const StructLayout *SL = dl.getStructLayout(N);
        for (unsigned i = 0; i < N->getNumElements(); ++i) {
          Suffix n = suf;
          n.push_back(Step{source::key(nullptr, N, dl), (int64_t)SL->getElementOffset(i)});
          noteZero(N->getElementType(i), n);
        }
      }
      return;
    }
    if (auto *AT = dyn_cast<ArrayType>(Ty)) {
      uint64_t es = dl.getTypeAllocSize(AT->getElementType()).getFixedValue();
      for (uint64_t i = 0; i < AT->getNumElements(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        noteZero(AT->getElementType(), n);
      }
    }
  }

// The leaves of a constant, a function or an integer, each with the path
// of the struct fields it lies at. D is the source type of the object C
// initializes, when DWARF declares it.
void Model::eachLeaf(Constant *C, Type *Ty, const Suffix &suf, const DIType *D,
                     const std::function<void(Constant *, const Suffix &)> &leaf) {
    if (!C)
      return;
    if (isa<ConstantPointerNull>(C) || isa<ConstantAggregateZero>(C))
      return;
    if (isa<Function>(C->stripPointerCasts()) || isa<ConstantInt>(C)) {
      leaf(C, suf);
      return;
    }
    if (auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
      Type *ET = CDS->getElementType();
      uint64_t es = dl.getTypeAllocSize(ET).getFixedValue();
      for (unsigned i = 0; i < CDS->getNumElements(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        eachLeaf(CDS->getElementAsConstant(i), ET, n, source::element(D), leaf);
      }
      return;
    }
    if (auto *S = dyn_cast<ConstantStruct>(C)) {
      auto *ST = dyn_cast<StructType>(Ty ? Ty : C->getType());
      auto named = namesFor(ST);
      if (named.empty()) {
        for (unsigned i = 0; i < S->getNumOperands(); ++i)
          eachLeaf(S->getOperand(i), S->getOperand(i)->getType(), suf, nullptr, leaf);
        return;
      }
      // A declared source type names the one struct the constant is; the
      // IR shape stands for every struct it may be only when DWARF is silent.
      if (D && !source::name(D).empty())
        named.resize(1);
      for (StructType *N : named) {
        const StructLayout *SL = dl.getStructLayout(N);
        std::string k = source::key(D, N, dl);
        for (unsigned i = 0; i < S->getNumOperands() && i < N->getNumElements(); ++i) {
          Suffix n = suf;
          uint64_t o = SL->getElementOffset(i);
          n.push_back(Step{k, (int64_t)o});
          Type *E = N->getElementType(i);
          eachLeaf(S->getOperand(i), E, n,
                   D ? source::member(D, o, E->isSized() ? dl.getTypeAllocSize(E).getFixedValue() : 0) : nullptr, leaf);
        }
      }
      return;
    }
    if (auto *A = dyn_cast<ConstantArray>(C)) {
      auto *AT = dyn_cast<ArrayType>(Ty ? Ty : C->getType());
      Type *ET = AT ? AT->getElementType() : nullptr;
      uint64_t es = ET ? dl.getTypeAllocSize(ET).getFixedValue() : 0;
      for (unsigned i = 0; i < A->getNumOperands(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        eachLeaf(A->getOperand(i), ET, n, source::element(D), leaf);
      }
    }
  }

void Model::walkInit(Constant *C, Type *Ty, const Suffix &suf, bool scalars, const DIType *D) {
    eachLeaf(C, Ty, suf, D, [&](Constant *L, const Suffix &at) {
      if (auto *F = dyn_cast<Function>(L->stripPointerCasts())) {
        if (Function *B = define(F->getName()))
          F = B;
        noteScalar(at, F->getName().str());
      } else if (scalars) {
        noteScalar(at, dec(cast<ConstantInt>(L)));
      }
    });
  }

bool Model::typeNameMatches(StringRef llvmName, StringRef access) {
    StringRef n = llvmName;
    if (!n.consume_front("struct.") && !n.consume_front("class."))
      return false;
    if (n == access)
      return true;
    return n.starts_with(access) && n.size() > access.size() && n[access.size()] == '.';
  }

void Model::ensureAccess() const {
    if (accessReady)
      return;
    accessReady = true;
    for (Module *M : {&down, &up}) {
      for (StructType *ST : M->getIdentifiedStructTypes()) {
        if (!ST->hasName())
          continue;
        StringRef n = ST->getName();
        if (!n.consume_front("struct.") && !n.consume_front("class."))
          continue;
        accessNames[n.str()].push_back(ST->getName().str());
        auto dot = n.rfind('.');
        if (dot != StringRef::npos && n.drop_front(dot + 1).find_if_not([](char c) { return c >= '0' && c <= '9'; }) == StringRef::npos)
          accessNames[n.substr(0, dot).str()].push_back(ST->getName().str());
      }
    }
  }

Suffix Model::suffixFromAccess(const StoreInst *S) const {
    const MDNode *TB = S->getMetadata(LLVMContext::MD_tbaa);
    if (!TB || TB->getNumOperands() < 3)
      return {};
    auto *Base = dyn_cast<MDNode>(TB->getOperand(0).get());
    auto *Off = dyn_cast<ConstantAsMetadata>(TB->getOperand(2).get());
    if (!Base || Base->getNumOperands() < 1 || !Off)
      return {};
    auto *Name = dyn_cast<MDString>(Base->getOperand(0).get());
    auto *CI = dyn_cast<ConstantInt>(Off->getValue());
    if (!Name || !CI)
      return {};
    ensureAccess();
    auto it = accessNames.find(Name->getString().str());
    if (it == accessNames.end() || it->second.empty())
      return {};
    StructType *ST = structNamed(it->second.front());
    return {Step{ST ? source::key(nullptr, ST, dl) : it->second.front(), CI->getSExtValue()}};
  }

void Model::indexFunctions() {
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *C = dyn_cast<Constant>(S->getValueOperand());
        if (!C)
          continue;
        Suffix suf = suffix(S->getPointerOperand());
        if (suf.empty())
          suf = suffixFromAccess(S);
        walkInit(C, C->getType(), suf, false, source::pointee(S->getPointerOperand()));
      }
    });
    for (Module *M : {&down, &up})
      for (GlobalVariable &G : M->globals()) {
      if (!G.hasInitializer())
        continue;
      walkInit(G.getInitializer(), G.getValueType(), {}, true, source::ofGlobal(G));
    }
    buildResolve();
    indexKeys();
  }

std::string Model::cstring(Value *V) {
    if (!V)
      return {};
    V = V->stripPointerCasts();
    if (auto *G = dyn_cast<GEPOperator>(V)) {
      if (G->hasAllZeroIndices())
        V = G->getPointerOperand()->stripPointerCasts();
    }
    auto *GV = dyn_cast<GlobalVariable>(V);
    if (!GV || !GV->hasInitializer())
      return {};
    auto *C = dyn_cast<ConstantDataSequential>(GV->getInitializer());
    if (!C || !C->isString())
      return {};
    StringRef s = C->getAsString();
    if (!s.empty() && s.back() == '\0')
      s = s.drop_back();
    if (s.empty() || s.find('\0') != StringRef::npos)
      return {};
    return s.str();
  }

std::map<unsigned, int64_t> Model::argOffsets(Function *F) {
    auto it = keyArgCache.find(F);
    if (it != keyArgCache.end())
      return it->second;
    std::map<unsigned, int64_t> args;
    std::unordered_set<const Value *> base;
    for (BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        break;
      }
      if (V)
        base.insert(V);
    }
    auto placed = [&](Value *P, int64_t &off) {
      off = 0;
      std::unordered_set<const Value *> seen;
      while (P && seen.insert(P).second) {
        if (auto *C = dyn_cast<CastInst>(P)) {
          P = C->getOperand(0);
          continue;
        }
        if (auto *G = dyn_cast<GEPOperator>(P)) {
          if (!G->hasAllConstantIndices())
            return false;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, delta))
            return false;
          off += delta.getSExtValue();
          P = G->getPointerOperand();
          continue;
        }
        break;
      }
      return P && base.count(P);
    };
    for (Instruction &I : instructions(*F)) {
      auto *S = dyn_cast<StoreInst>(&I);
      if (!S)
        continue;
      int64_t off = 0;
      if (!placed(S->getPointerOperand(), off))
        continue;
      Value *V = S->getValueOperand();
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *CB = dyn_cast<CallBase>(V)) {
          if (CB->arg_size() == 1) {
            V = CB->getArgOperand(0);
            continue;
          }
        }
        break;
      }
      if (auto *A = dyn_cast<Argument>(V))
        args[A->getArgNo()] = off;
    }
    keyArgCache[F] = args;
    return keyArgCache[F];
  }

std::map<std::string, std::set<int64_t>> Model::keyFields() {
    std::map<std::string, std::set<int64_t>> out;
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Op = CB->getArgOperand(i);
          while (auto *C = dyn_cast<CastInst>(Op))
            Op = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(Op);
          if (!L)
            continue;
          Value *Ptr = L->getPointerOperand();
          while (auto *C = dyn_cast<CastInst>(Ptr))
            Ptr = C->getOperand(0);
          auto *G = dyn_cast<GEPOperator>(Ptr);
          if (!G || !G->hasAllConstantIndices())
            continue;
          auto *ST = dyn_cast<StructType>(G->getSourceElementType());
          if (!ST || !ST->hasName())
            continue;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, delta))
            continue;
          Value *base = G->getPointerOperand()->stripPointerCasts();
          for (unsigned j = 0; j < CB->arg_size(); ++j) {
            if (i == j)
              continue;
            if (CB->getArgOperand(j)->stripPointerCasts() == base)
              out[source::container(G, dl)].insert(delta.getSExtValue());
          }
        }
      }
    });
    return out;
  }

std::string Model::bareType(StringRef n) {
    if (!n.consume_front("struct.") && !n.consume_front("class."))
      return n.str();
    auto dot = n.rfind('.');
    if (dot != StringRef::npos && n.drop_front(dot + 1).find_if_not([](char c) { return c >= '0' && c <= '9'; }) == StringRef::npos)
      return n.substr(0, dot).str();
    return n.str();
  }

void Model::indexKeys() {
    auto fields = keyFields();
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts());
        if (!Fn)
          continue;
        Value *P = S->getPointerOperand();
        std::unordered_set<const Value *> seen;
        while (P && seen.insert(P).second) {
          if (auto *C = dyn_cast<CastInst>(P)) {
            P = C->getOperand(0);
            continue;
          }
          if (auto *G = dyn_cast<GEPOperator>(P)) {
            P = G->getPointerOperand();
            continue;
          }
          break;
        }
        auto *CB = dyn_cast<CallBase>(P);
        if (!CB)
          continue;
        if (Function *D = define(Fn->getName()))
          Fn = D;
        Function *Alloc = CB->getCalledFunction();
        if (Alloc)
          if (Function *AD = define(Alloc->getName()))
            Alloc = AD;
        if (!Alloc)
          continue;
        std::string structName;
        Suffix where = suffix(S->getPointerOperand());
        if (!where.empty())
          structName = bareType(where.front().type);
        std::set<int64_t> keys;
        for (const auto &kf : fields)
          if (bareType(kf.first) == structName)
            keys.insert(kf.second.begin(), kf.second.end());
        auto placed = argOffsets(Alloc);
        for (const auto &ao : placed) {
          if (!keys.empty() && !keys.count(ao.second))
            continue;
          if (keys.empty())
            continue;
          if (ao.first >= CB->arg_size())
            continue;
          std::string s = cstring(CB->getArgOperand(ao.first));
          if (!s.empty())
            regKeys[Fn].insert(std::move(s));
        }
      }
    });
    indexArgFns();
  }

void Model::addUnique(std::vector<Function *> &v, Function *F) {
    if (F && std::find(v.begin(), v.end(), F) == v.end())
      v.push_back(F);
  }

void Model::indexArgFns() {
    struct Stored {
      Function *fn;
      unsigned arg;
      Suffix suf;
    };
    std::vector<Stored> stored;
    eachBody([&](Function &F) {
      Mem m;
      std::vector<std::optional<Loc>> roots(F.arg_size());
      for (unsigned i = 0; i < F.arg_size(); ++i)
        roots[i] = Loc{(int)i, {}};
      bindFormals(m, &F, roots);
      propagate(m, &F);
      auto argOf = [&](Value *V) -> int {
        Loc L;
        if (!locOf(m, V, L) || !L.suf.empty())
          return -1;
        return L.arg;
      };
      for (Instruction &I : instructions(F)) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          int arg = argOf(S->getValueOperand());
          if (arg < 0) {
            Value *Sv = S->getValueOperand()->stripPointerCasts();
            if (auto *Ld = dyn_cast<LoadInst>(Sv)) {
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              if (Al)
                for (Instruction &SI : instructions(F)) {
                  auto *St = dyn_cast<StoreInst>(&SI);
                  if (!St || St->getPointerOperand()->stripPointerCasts() != Al)
                    continue;
                  if (auto *A = dyn_cast<Argument>(St->getValueOperand()->stripPointerCasts()))
                    arg = (int)A->getArgNo();
                }
            }
          }
          if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
            Loc L;
            if (locOf(m, S->getPointerOperand(), L) && L.arg >= 0 && L.suf.size() == 1 && !L.suf[0].deref &&
                !L.suf[0].type.empty()) {
              if (Function *D = define(Fn->getName()))
                Fn = D;
              auto &v = initSites[{L.suf[0].type, L.suf[0].off}];
              bool have = false;
              for (const InitSite &s : v)
                have = have || (s.fn == &F && s.stored == Fn);
              if (!have)
                v.push_back(InitSite{&F, (unsigned)L.arg, Fn});
            }
          }
          Suffix suf = suffix(S->getPointerOperand());
          if (arg >= 0 && !suf.empty())
            stored.push_back(Stored{&F, (unsigned)arg, std::move(suf)});
        }
      }
    });
    for (const Stored &s : stored)
      argStored[s.fn].push_back({s.arg, s.suf});
    for (const Stored &s : stored) {
      if (fnsOf(s.fn->getArg(s.arg)).empty())
        continue;
      for (const Stored &o : stored) {
        if (o.fn != s.fn || o.arg == s.arg)
          continue;
        auto &v = besidePtr[s.suf];
        if (std::find(v.begin(), v.end(), o.suf) == v.end())
          v.push_back(o.suf);
      }
    }
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *C = CB->getCalledFunction();
        if (!C)
          continue;
        if (Function *D = define(C->getName()))
          C = D;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Act = CB->getArgOperand(i)->stripPointerCasts();
          if (auto *Ld = dyn_cast<LoadInst>(Act)) {
            auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
            if (Al)
              for (Instruction &SI : instructions(F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (S && S->getPointerOperand()->stripPointerCasts() == Al)
                  Act = S->getValueOperand()->stripPointerCasts();
              }
          }
          auto *Inner = dyn_cast<CallBase>(Act);
          if (!Inner)
            continue;
          Function *H = Inner->getCalledFunction();
          if (!H)
            continue;
          if (Function *HD = define(H->getName()))
            H = HD;
          for (const auto &st : argStored[C]) {
            if (st.first != i)
              continue;
            auto &v = builderOf[st.second];
            if (std::find(v.begin(), v.end(), H) == v.end())
              v.push_back(H);
          }
        }
      }
    });
  }

Suffix Model::returnsOf(const Function *F) const {
    if (!F || F->isDeclaration())
      return {};
    auto it = retCache.find(F);
    if (it != retCache.end())
      return it->second;
    bool saw = false;
    bool bad = false;
    Suffix s;
    for (const BasicBlock &BB : *F) {
      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      Value *V = R->getReturnValue();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
        continue;
      Suffix t = suffix(V);
      if (t.empty()) {
        bad = true;
        break;
      }
      if (!saw) {
        s = std::move(t);
        saw = true;
      } else if (s != t) {
        bad = true;
        break;
      }
    }
    if (!saw || bad)
      s.clear();
    retCache[F] = s;
    return retCache[F];
  }

Function *Model::functionAt(Constant *C, uint64_t base, uint64_t want) const {
    if (!C)
      return nullptr;
    if (auto *CE = dyn_cast<ConstantExpr>(C)) {
      if (CE->isCast())
        return functionAt(CE->getOperand(0), base, want);
      return nullptr;
    }
    if (auto *F = dyn_cast<Function>(C)) {
      if (base != want)
        return nullptr;
      if (Function *D = define(F->getName()))
        return D;
      return F;
    }
    if (auto *CS = dyn_cast<ConstantStruct>(C)) {
      const StructLayout *SL = dl.getStructLayout(CS->getType());
      for (unsigned i = 0; i < CS->getNumOperands(); ++i)
        if (Function *Fn = functionAt(CS->getOperand(i), base + SL->getElementOffset(i), want))
          return Fn;
      return nullptr;
    }
    if (auto *CA = dyn_cast<ConstantArray>(C)) {
      uint64_t es = dl.getTypeAllocSize(CA->getType()->getElementType()).getFixedValue();
      for (unsigned i = 0; i < CA->getNumOperands(); ++i)
        if (Function *Fn = functionAt(CA->getOperand(i), base + (uint64_t)i * es, want))
          return Fn;
      return nullptr;
    }
    return nullptr;
  }

void Model::indexVtables() const {
    if (vtReady)
      return;
    vtReady = true;
    eachBody([&](Function &F) {
      bool any = false;
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *VG = dyn_cast<GEPOperator>(S->getValueOperand()->stripPointerCasts());
        if (VG && dyn_cast<GlobalVariable>(VG->getPointerOperand()->stripPointerCasts()))
          any = true;
      }
      if (!any || F.arg_empty())
        return;
      std::unordered_set<const Value *> th{F.getArg(0)};
      std::unordered_set<const AllocaInst *> boxes;
      for (size_t before = SIZE_MAX; before != th.size() + boxes.size();) {
        before = th.size() + boxes.size();
        for (Instruction &I : instructions(F)) {
          if (auto *C = dyn_cast<CastInst>(&I))
            if (th.count(C->getOperand(0)))
              th.insert(&I);
          if (auto *S = dyn_cast<StoreInst>(&I))
            if (th.count(S->getValueOperand()->stripPointerCasts()))
              if (auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
                boxes.insert(Al);
          if (auto *L = dyn_cast<LoadInst>(&I))
            if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
              if (boxes.count(Al))
                th.insert(&I);
        }
      }
      std::set<std::string> types;
      uint64_t extent = 0;
      for (Instruction &I : instructions(F)) {
        auto *G = dyn_cast<GetElementPtrInst>(&I);
        if (!G || !th.count(G->getPointerOperand()->stripPointerCasts()))
          continue;
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName()) {
            types.insert(source::container(cast<GEPOperator>(G), dl));
            if (ST->isSized())
              extent = std::max<uint64_t>(extent, dl.getTypeAllocSize(ST).getFixedValue());
          }
      }
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        Value *Val = S->getValueOperand()->stripPointerCasts();
        auto *VG = dyn_cast<GEPOperator>(Val);
        if (!VG || !VG->hasAllConstantIndices())
          continue;
        APInt bo(dl.getIndexSizeInBits(VG->getPointerAddressSpace()), 0);
        if (!VG->accumulateConstantOffset(dl, bo))
          continue;
        auto *GV = dyn_cast<GlobalVariable>(VG->getPointerOperand()->stripPointerCasts());
        if (!GV || !GV->hasInitializer())
          continue;
        Value *P = S->getPointerOperand()->stripPointerCasts();
        int64_t field = 0;
        if (auto *G = dyn_cast<GEPOperator>(P)) {
          if (!G->hasAllConstantIndices())
            continue;
          APInt fo(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->accumulateConstantOffset(dl, fo))
            continue;
          field = fo.getSExtValue();
          P = G->getPointerOperand()->stripPointerCasts();
        }
        if (!th.count(P))
          continue;
        VTab vt{GV, (uint64_t)bo.getSExtValue(), field, &F, extent};
        vtAll.push_back(vt);
        for (const std::string &ty : types)
          vtOf[ty].push_back(vt);
      }
    });
    // A table is overwritten in every construction when each caller of the
    // storing function itself stores a table into the same field.
    std::map<int64_t, std::set<const Function *>> storers;
    for (const VTab &vt : vtAll)
      storers[vt.field].insert(vt.by);
    std::function<void(const Value *, const std::set<const Function *> &, bool &, std::set<const Value *> &)> callers =
        [&](const Value *V, const std::set<const Function *> &st, bool &last, std::set<const Value *> &seen) {
          if (!seen.insert(V).second)
            return;
          for (const User *U : V->users()) {
            if (last)
              return;
            if (auto *GA = dyn_cast<GlobalAlias>(U)) {
              callers(GA, st, last, seen);
              continue;
            }
            auto *CB = dyn_cast<CallBase>(U);
            if (!CB || CB->getCalledOperand()->stripPointerCasts() != V || !st.count(CB->getFunction()))
              last = true;
          }
        };
    for (VTab &vt : vtAll) {
      bool last = false;
      std::set<const Value *> seen;
      callers(vt.by, storers[vt.field], last, seen);
      if (vt.by->use_empty())
        last = true;
      vt.last = last;
    }
  }

Model::VSlot Model::vslot(CallBase *CB) const {
    VSlot s;
    auto *fnLoad = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
    if (!fnLoad)
      return s;
    // The slot is the vtable pointer advanced by a constant, by none for the
    // first slot (whose all-zero GEP stripPointerCasts removes).
    Value *vt = fnLoad->getPointerOperand()->stripPointerCasts();
    APInt slot(dl.getIndexSizeInBits(fnLoad->getPointerAddressSpace()), 0);
    if (auto *slotG = dyn_cast<GEPOperator>(vt)) {
      if (!slotG->hasAllConstantIndices() || !slotG->accumulateConstantOffset(dl, slot))
        return s;
      vt = slotG->getPointerOperand()->stripPointerCasts();
    }
    auto *vLoad = dyn_cast<LoadInst>(vt);
    if (!vLoad)
      return s;
    Value *obj = vLoad->getPointerOperand()->stripPointerCasts();
    int64_t field = 0;
    if (auto *OG = dyn_cast<GEPOperator>(obj)) {
      if (!OG->hasAllConstantIndices())
        return s;
      APInt fo(dl.getIndexSizeInBits(OG->getPointerAddressSpace()), 0);
      if (!OG->accumulateConstantOffset(dl, fo))
        return s;
      field = fo.getSExtValue();
      obj = OG->getPointerOperand()->stripPointerCasts();
    }
    // A virtual call reads its slot through the vtable pointer of an object
    // whose source class is polymorphic; a C function pointer field read
    // through a struct pointer has the same IR shape.
    if (field < 0 || !source::vptrAt(source::pointee(obj), (uint64_t)field))
      return s;
    s.ok = true;
    s.obj = obj;
    s.field = field;
    s.slot = (uint64_t)slot.getSExtValue();
    return s;
  }

std::vector<Function *> Model::fromVtabs(const std::vector<Model::VTab> &tabs, int64_t field, uint64_t slot) const {
    std::vector<Function *> out;
    for (const VTab &vt : tabs) {
      if (vt.field != field)
        continue;
      if (Function *Fn = functionAt(vt.g->getInitializer(), 0, vt.base + slot))
        if (std::find(out.begin(), out.end(), Fn) == out.end())
          out.push_back(Fn);
    }
    return out;
  }

bool Model::containsRead(Function *F) const {
    auto it = readBody.find(F);
    if (it != readBody.end())
      return it->second;
    bool yes = false;
    if (F && !F->isDeclaration()) {
      for (Instruction &I : instructions(*F)) {
        auto *C = dyn_cast<CallBase>(&I);
        if (!C)
          continue;
        Function *Cal = C->getCalledFunction();
        if (!Cal || define(Cal->getName()))
          continue;
        if (asRead(*C).ok) {
          yes = true;
          break;
        }
      }
    }
    readBody[F] = yes;
    return yes;
  }

bool Model::reachesFn(Function *From, Function *To) const {
    if (!From || !To)
      return false;
    Function *Dst = define(To->getName());
    if (!Dst)
      Dst = To;
    auto it = reachFrom.find(From);
    if (it == reachFrom.end()) {
      std::unordered_set<const Function *> seen;
      std::vector<Function *> work{From};
      seen.insert(From);
      for (size_t i = 0; i < work.size(); ++i) {
        if (work[i]->isDeclaration())
          continue;
        for (Instruction &I : instructions(*work[i])) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          for (Function *T : targetsOf(CB)) {
            if (!T)
              continue;
            Function *D = define(T->getName());
            if (!D)
              D = T;
            if (seen.insert(D).second)
              work.push_back(D);
          }
        }
      }
      it = reachFrom.emplace(From, std::move(seen)).first;
    }
    return it->second.count(Dst) != 0;
  }

std::set<std::string> Model::storedBeside(const Suffix &cell, Function *Next) const {
    std::set<std::string> out;
    if (!Next || cell.empty())
      return out;
    auto key = std::make_pair(static_cast<const Function *>(Next), cell);
    if (auto it = besideCache.find(key); it != besideCache.end())
      return it->second;
    auto same = [&](const Suffix &s) {
      if (s.size() != cell.size())
        return false;
      for (size_t i = 0; i < s.size(); ++i)
        if (s[i].type != cell[i].type || s[i].off != cell[i].off)
          return false;
      return true;
    };
    eachBody([&](Function &F) {
      bool writes = false;
      std::vector<std::string> here;
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts());
        if (!Fn)
          continue;
        if (Function *D = define(Fn->getName()))
          Fn = D;
        if (Fn == Next)
          writes = true;
        if (same(suffix(S->getPointerOperand())))
          here.push_back(Fn->getName().str());
      }
      if (writes)
        out.insert(here.begin(), here.end());
    });
    besideCache[key] = out;
    return besideCache[key];
  }

std::vector<Function *> Model::vtableTargets(CallBase *CB) const {
    auto hit = vtableCache.find(CB);
    if (hit != vtableCache.end())
      return hit->second;
    std::vector<Function *> out;
    VSlot s = vslot(CB);
    if (!s.ok) {
      vtableCache[CB] = out;
      return out;
    }
    // Class hierarchy analysis: the receiver's dynamic class is its static
    // class or one derived from it. A class's own table (_ZTV, Itanium ABI)
    // is installed by its constructors at the vtable pointer of every
    // subobject; the class is the one of the storing member function's this.
    // The call reads the slot of the table at the receiver's subobject.
    indexVtables();
    auto classes = source::derived(source::pointee(s.obj));
    for (const VTab &vt : vtAll) {
      if (!vt.g->getName().starts_with("_ZTV") || vt.by->arg_empty())
        continue;
      auto it = classes.find(source::name(source::pointee(vt.by->getArg(0))));
      if (it == classes.end())
        continue;
      bool at = std::any_of(it->second.begin(), it->second.end(), [&](const std::optional<uint64_t> &o) {
        return !o || vt.field == (int64_t)*o + s.field;
      });
      if (!at)
        continue;
      if (Function *Fn = functionAt(vt.g->getInitializer(), 0, vt.base + s.slot)) {
        Function *B = define(Fn->getName());
        Function *T = B ? B : Fn;
        if (T->getFunctionType() == CB->getFunctionType() && std::find(out.begin(), out.end(), T) == out.end())
          out.push_back(T);
      }
    }
    vtableCache[CB] = out;
    return out;
  }

uint64_t Model::objectBytes(Value *O, Function *F) const {
    std::unordered_set<const Value *> seen;
    while (O && seen.insert(O).second) {
      if (auto *C = dyn_cast<CastInst>(O)) {
        O = C->getOperand(0);
        continue;
      }
      auto *L = dyn_cast<LoadInst>(O);
      if (!L || !F)
        break;
      auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      if (!Al)
        break;
      Value *stored = nullptr;
      for (Instruction &I : instructions(*F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
          continue;
        Value *sv = S->getValueOperand()->stripPointerCasts();
        if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
          continue;
        stored = sv;
      }
      if (!stored)
        return 0;
      O = stored;
    }
    if (!O)
      return 0;
    auto *A = dyn_cast<Argument>(O);
    if (!A || !A->hasAttribute(Attribute::Dereferenceable))
      return 0;
    return A->getAttribute(Attribute::Dereferenceable).getDereferenceableBytes();
  }

uint64_t Model::typeBytes(const std::string &name) const {
    auto it = typeSize.find(name);
    if (it != typeSize.end())
      return it->second;
    uint64_t n = 0;
    for (Module *M : {&down, &up})
      for (StructType *ST : M->getIdentifiedStructTypes())
        if (ST->hasName() && ST->getName() == name && !ST->isOpaque() && ST->isSized()) {
          n = dl.getTypeAllocSize(ST).getFixedValue();
          break;
        }
    typeSize[name] = n;
    return n;
  }

std::vector<Function *> Model::vtableReads(CallBase *CB) const {
    auto hit = readCache.find(CB);
    if (hit != readCache.end())
      return hit->second;
    std::vector<Function *> out;
    VSlot s = vslot(CB);
    if (!s.ok) {
      readCache[CB] = out;
      return out;
    }
    indexVtables();
    for (Function *Fn : fromVtabs(vtAll, s.field, s.slot))
      if (containsRead(Fn))
        out.push_back(Fn);
    readCache[CB] = out;
    return out;
  }

std::vector<Function *> Model::targetsOf(CallBase *CB) const {
    if (const Function *C = klee::calls::callee(*CB)) {
      if (Function *D = define(C->getName()))
        return {D};
      return {};
    }
    auto it = resolved.find(CB);
    return it == resolved.end() ? std::vector<Function *>{} : it->second;
  }

static std::unordered_set<const BasicBlock *> blocksToReturn(Function &F, const std::function<bool(CallBase *)> &returns) {
    auto alive = [&](const BasicBlock *B) {
      for (const Instruction &I : *B)
        if (auto *CB = dyn_cast<CallBase>(&I); CB && !returns(const_cast<CallBase *>(CB)))
          return false;
      return !isa<UnreachableInst>(B->getTerminator());
    };
    std::unordered_set<const BasicBlock *> fwd, out;
    std::vector<const BasicBlock *> work{&F.getEntryBlock()};
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!alive(B) || !fwd.insert(B).second)
        continue;
      for (const BasicBlock *S : successors(B))
        work.push_back(S);
    }
    for (const BasicBlock *B : fwd)
      if (isa<ReturnInst>(B->getTerminator()))
        work.push_back(B);
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!fwd.count(B) || !out.insert(B).second)
        continue;
      for (const BasicBlock *P : predecessors(B))
        work.push_back(P);
    }
    return out;
  }

bool Model::callReturns(CallBase *CB) const {
    if (!returningBuilt) {
      returningBuilt = true;
      std::vector<Function *> fs;
      for (Module *M : {&down, &up})
        for (Function &F : *M)
          if (!F.isDeclaration())
            fs.push_back(&F);
      for (bool changed = true; changed;) {
        changed = false;
        for (Function *F : fs)
          if (!returning.count(F) && !blocksToReturn(*F, [&](CallBase *C) { return callReturns(C); }).empty()) {
            returning.insert(F);
            changed = true;
          }
      }
    }
    if (CB->doesNotReturn())
      return false;
    if (const Function *C = klee::calls::callee(*CB)) {
      if (Function *D = define(C->getName()))
        return returning.count(D) > 0;
      return !C->doesNotReturn();
    }
    auto ts = targetsOf(CB);
    if (ts.empty())
      return true;
    for (Function *T : ts)
      if (T->isDeclaration() ? !T->doesNotReturn() : returning.count(T) > 0)
        return true;
    return false;
  }

std::unordered_set<const BasicBlock *> Model::returnBlocks(Function *F) const {
    return blocksToReturn(*F, [&](CallBase *C) { return callReturns(C); });
  }

// §3.10 Res: the least solution of one inclusion system in which function
// constants and abstract objects flow. A cell is an SSA value, the return of
// a function, an access path, the contents of an object, or the variadic
// area. Every constraint is monotone, so a worklist that sends each token
// along each edge once reaches the least solution.
void Model::buildResolve() {
    using Node = unsigned;
    std::vector<std::vector<Node>> succ;
    std::vector<SmallPtrSet<Value *, 4>> pt;
    std::vector<std::pair<Node, Value *>> work;
    auto fresh = [&]() {
      succ.emplace_back();
      pt.emplace_back();
      return (Node)(succ.size() - 1);
    };
    auto token = [&](Function *F) {
      Function *B = define(F->getName());
      return B ? B : F;
    };
    // An object is a local or global whose type can hold a function pointer
    // (H_mlta: without type punning a data-only object holds none), or the
    // result of a call to an external function. IR without source type is
    // treated as able to hold one (C void * slots).
    std::function<bool(Type *)> holdsIR = [&](Type *T) {
      if (T->isPointerTy())
        return true;
      if (auto *ST = dyn_cast<StructType>(T))
        return std::any_of(ST->element_begin(), ST->element_end(), holdsIR);
      if (auto *AT = dyn_cast<ArrayType>(T))
        return holdsIR(AT->getElementType());
      return false;
    };
    auto object = [&](Value *V) -> Value * {
      if (auto *A = dyn_cast<AllocaInst>(V)) {
        if (const DIType *D = source::pointee(A))
          return source::holdsFn(D) ? V : nullptr;
        return holdsIR(A->getAllocatedType()) ? V : nullptr;
      }
      if (auto *G = dyn_cast<GlobalVariable>(V)) {
        if (const DIType *D = source::ofGlobal(*G))
          return source::holdsFn(D) ? V : nullptr;
        return holdsIR(G->getValueType()) ? V : nullptr;
      }
      return nullptr;
    };
    // The token a value is: a function, or the object a constant address is in.
    auto tokenOf = [&](Value *V) -> Value * {
      V = V->stripPointerCastsAndAliases();
      while (isa<Constant>(V) && isa<GEPOperator>(V))
        V = cast<GEPOperator>(V)->getPointerOperand()->stripPointerCastsAndAliases();
      if (auto *F = dyn_cast<Function>(V))
        return token(F);
      return object(V);
    };

    std::unordered_map<const Value *, Node> valN, elemN;
    std::unordered_map<const Function *, Node> retN;
    std::map<Suffix, Node> stN, ldN;
    auto val = [&](Value *V) {
      V = V->stripPointerCastsAndAliases();
      auto [it, added] = valN.try_emplace(V, 0);
      if (added) {
        it->second = fresh();
        if (Value *T = tokenOf(V))
          work.push_back({it->second, T});
      }
      return it->second;
    };
    auto node = [&](auto &m, const auto &k) {
      auto [it, added] = m.try_emplace(k, 0);
      if (added)
        it->second = fresh();
      return it->second;
    };
    auto edge = [&](Node a, Node b) {
      if (a != b)
        succ[a].push_back(b);
    };
    auto link = [&](Node a, Node b) {
      edge(a, b);
      for (Value *t : pt[a])
        if (!pt[b].count(t))
          work.push_back({b, t});
    };
    // A path stored at is read at every path one of whose layers sequences is
    // a suffix of the other's: the same field, named from an outer or an inner
    // struct. A cell is joined to the others when it is first named.
    std::map<Step, std::vector<std::pair<Suffix, Node>>> stLeaf, ldLeaf;
    auto tail = [](const Suffix &a, const Suffix &b) {
      return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.end() - (long)a.size());
    };
    auto cell = [&](bool store, const Suffix &p) {
      auto &m = store ? stN : ldN;
      auto [it, added] = m.try_emplace(p, 0);
      if (!added)
        return it->second;
      Node n = it->second = fresh();
      for (const auto &[q, o] : (store ? ldLeaf : stLeaf)[p.back()])
        if (tail(p, q) || tail(q, p))
          store ? link(n, o) : link(o, n);
      (store ? stLeaf : ldLeaf)[p.back()].push_back({p, n});
      return n;
    };

    // The access path of an address: the struct layers holding it, outer to
    // inner, each the layer's source type and the address's offset in it, up
    // to the last loaded pointer. Layers outside an unknown offset (a variable
    // array index) are not named; the layers inside it are. An address with no
    // layer is into the objects its base pointer points to.
    struct Addr {
      Suffix path;
      Value *base = nullptr;
      bool va = false;
    };
    auto layers = [&](GEPOperator *G, Suffix &inner, std::optional<int64_t> &acc) {
      Type *T = G->getSourceElementType();
      const DIType *D = source::pointee(G->getPointerOperand());
      std::vector<std::optional<int64_t>> c;
      std::vector<std::pair<std::string, size_t>> lv;
      auto idx = G->idx_begin();
      if (idx != G->idx_end()) {
        auto *CI = dyn_cast<ConstantInt>(*idx);
        if (CI && T->isSized())
          c.push_back(CI->getSExtValue() * (int64_t)dl.getTypeAllocSize(T).getFixedValue());
        else
          c.push_back(std::nullopt);
        ++idx;
      }
      for (bool open = true; open;) {
        auto *ST = dyn_cast<StructType>(T);
        if (ST && ST->hasName())
          lv.push_back({source::key(D, ST, dl), c.size()});
        if (idx == G->idx_end())
          break;
        auto *CI = dyn_cast<ConstantInt>(*idx);
        if (ST && CI && ST->isSized() && CI->getZExtValue() < ST->getNumElements()) {
          unsigned i = (unsigned)CI->getZExtValue();
          uint64_t o = dl.getStructLayout(ST)->getElementOffset(i);
          c.push_back((int64_t)o);
          T = ST->getElementType(i);
          D = D ? source::member(D, o, T->isSized() ? dl.getTypeAllocSize(T).getFixedValue() : 0) : nullptr;
        } else if (auto *AT = dyn_cast<ArrayType>(T)) {
          int64_t es = (int64_t)dl.getTypeAllocSize(AT->getElementType()).getFixedValue();
          c.push_back(CI ? std::optional<int64_t>(CI->getSExtValue() * es) : std::nullopt);
          T = AT->getElementType();
          D = D ? source::element(D) : nullptr;
        } else {
          c.push_back(std::nullopt);
          open = false;
        }
        ++idx;
      }
      // Offset of the address from the start of contribution k onward.
      auto from = [&](size_t k) -> std::optional<int64_t> {
        if (!acc)
          return std::nullopt;
        int64_t s = *acc;
        for (size_t j = k; j < c.size(); ++j) {
          if (!c[j])
            return std::nullopt;
          s += *c[j];
        }
        return s;
      };
      // A struct the GEP only ends at is the layer the next access enters.
      Suffix add;
      for (const auto &[key, k] : lv)
        if (k < c.size() || inner.empty())
          if (auto o = from(k))
            add.push_back(Step{key, *o});
      inner.insert(inner.begin(), add.begin(), add.end());
      acc = from(0);
    };
    // The variadic arguments lie in untyped storage that va_list values
    // carry between functions, so they are one cell Va. A va_arg reads
    // through a pointer loaded from a __va_list_tag field.
    auto vaArea = [&](const LoadInst &L) {
      const Value *P = L.getPointerOperand()->stripPointerCasts();
      if (auto *G = dyn_cast<GEPOperator>(P))
        if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()); ST && ST->hasName())
          if (ST->getName().starts_with("struct.__va_list_tag"))
            return true;
      const MDNode *T = L.getMetadata(LLVMContext::MD_tbaa);
      auto *B = T && T->getNumOperands() ? dyn_cast<MDNode>(T->getOperand(0)) : nullptr;
      auto *N = B && B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
      return N && N->getString() == "__va_list_tag";
    };
    auto addrs = [&](Value *A) {
      std::vector<Addr> out;
      struct Item {
        Value *v;
        Suffix inner;
        std::optional<int64_t> acc;
      };
      std::vector<Item> items{{A, {}, 0}};
      std::unordered_set<const Value *> phis;
      while (!items.empty()) {
        Item it = std::move(items.back());
        items.pop_back();
        Value *V = it.v;
        while (V) {
          if (auto *O = dyn_cast<Operator>(V);
              O && (O->getOpcode() == Instruction::BitCast || O->getOpcode() == Instruction::AddrSpaceCast)) {
            V = O->getOperand(0);
          } else if (auto *GA = dyn_cast<GlobalAlias>(V)) {
            V = GA->getAliasee();
          } else if (auto *G = dyn_cast<GEPOperator>(V)) {
            layers(G, it.inner, it.acc);
            V = G->getPointerOperand();
          } else if (auto *P = dyn_cast<PHINode>(V)) {
            if (phis.insert(P).second)
              for (Value *in : P->incoming_values())
                items.push_back({in, it.inner, it.acc});
            break;
          } else if (auto *S = dyn_cast<SelectInst>(V)) {
            items.push_back({S->getTrueValue(), it.inner, it.acc});
            items.push_back({S->getFalseValue(), it.inner, it.acc});
            break;
          } else {
            if (!it.inner.empty())
              out.push_back({it.inner, nullptr});
            else if (auto *L = dyn_cast<LoadInst>(V); L && vaArea(*L))
              out.push_back({{}, nullptr, true});
            else
              out.push_back({{}, V});
            break;
          }
        }
      }
      return out;
    };
    // An access whose address carries no layer (a byte GEP of optimized IR)
    // still names its struct path in its TBAA tag (base type, offset): the
    // compiler's statement of the lvalue's type (C11 6.5p7). The path descends
    // from the base type into the member types holding the offset.
    ensureAccess();
    auto tbaaStruct = [&](const MDNode *B) -> StructType * {
      auto *N = B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
      if (!N)
        return nullptr;
      std::string n = N->getString().str();
      if (StringRef(n).starts_with("_ZTS")) {
        n = llvm::demangle(n);
        StringRef r(n);
        if (!r.consume_front("typeinfo name for "))
          return nullptr;
        n = r.str();
      }
      auto it = accessNames.find(n);
      return it == accessNames.end() || it->second.empty() ? nullptr : structNamed(it->second.front());
    };
    auto tbaa = [&](const Instruction &I) {
      Suffix s;
      const MDNode *T = I.getMetadata(LLVMContext::MD_tbaa);
      if (!T || T->getNumOperands() < 3)
        return s;
      const MDNode *B = dyn_cast<MDNode>(T->getOperand(0));
      auto *O = mdconst::dyn_extract<ConstantInt>(T->getOperand(2));
      if (!O)
        return s;
      int64_t off = O->getSExtValue();
      while (B) {
        StructType *ST = tbaaStruct(B);
        if (!ST)
          break;
        s.push_back(Step{source::key(nullptr, ST, dl), off});
        const MDNode *in = nullptr;
        int64_t at = -1;
        for (unsigned i = 1; i + 1 < B->getNumOperands(); i += 2) {
          auto *mo = mdconst::dyn_extract<ConstantInt>(B->getOperand(i + 1));
          if (mo && mo->getSExtValue() <= off && mo->getSExtValue() >= at) {
            in = dyn_cast<MDNode>(B->getOperand(i));
            at = mo->getSExtValue();
          }
        }
        if (!in)
          break;
        off -= at;
        B = in;
      }
      return s;
    };
    // An access that names a struct field, by its address or by its tag, is
    // into the field's cell only.
    auto access = [&](const Instruction &I, Value *A) {
      auto at = addrs(A);
      if (std::none_of(at.begin(), at.end(), [](const Addr &a) { return !a.path.empty(); }))
        if (Suffix s = tbaa(I); !s.empty())
          return std::vector<Addr>{{std::move(s), nullptr}};
      return at;
    };
    std::optional<Node> vaN;
    auto va = [&]() {
      if (!vaN)
        vaN = fresh();
      return *vaN;
    };
    // Through a base pointer the object is known only when one reaches it:
    // the constraint waits at the pointer's cell. A local or global base is
    // its own object.
    struct Deref {
      Node n;
      bool load;
      Value *token;
    };
    std::unordered_map<Node, std::vector<Deref>> derefs;
    auto elem = [&](Value *O) { return node(elemN, O); };
    auto known = [](Value *B) { return isa<AllocaInst>(B) || isa<GlobalVariable>(B); };
    auto writes = [&](const Addr &a, Node src) {
      if (a.va)
        edge(src, va());
      else if (!a.base)
        edge(src, cell(true, a.path));
      else if (known(a.base))
        edge(src, elem(a.base));
      else
        derefs[val(a.base)].push_back({src, false, nullptr});
    };
    auto reads = [&](const Addr &a, Node dst) {
      if (a.va)
        edge(va(), dst);
      else if (!a.base)
        edge(cell(false, a.path), dst);
      else if (known(a.base))
        edge(elem(a.base), dst);
      else
        derefs[val(a.base)].push_back({dst, true, nullptr});
    };
    // A path of the struct-field walk names each field by its offset in its
    // own struct; the offset of the leaf in a layer is the sum from it inward.
    auto inward = [](Suffix s) {
      int64_t sum = 0;
      for (size_t i = s.size(); i-- > 0;) {
        sum += s[i].off;
        s[i].off = sum;
      }
      return s;
    };
    // A constant placed at an address: each token leaf at its path, and
    // every one of them in the objects of the base.
    auto place = [&](Constant *C, Type *Ty, const DIType *D, const std::vector<Addr> &at) {
      eachLeaf(C, Ty, {}, D, [&](Constant *L, const Suffix &rel) {
        Value *T = tokenOf(L);
        if (!T)
          return;
        Suffix r = inward(rel);
        int64_t d = r.empty() ? 0 : r.front().off;
        for (const Addr &a : at) {
          if (a.va)
            continue;
          if (a.base) {
            if (known(a.base))
              work.push_back({elem(a.base), T});
            else
              derefs[val(a.base)].push_back({0, false, T});
          }
          Suffix p = a.path;
          for (Step &s : p)
            s.off += d;
          p.insert(p.end(), r.begin(), r.end());
          if (!p.empty())
            work.push_back({cell(true, p), T});
        }
      });
    };

    for (Module *M : {&down, &up})
      for (GlobalVariable &G : M->globals())
        if (G.hasInitializer())
          place(G.getInitializer(), G.getValueType(), source::ofGlobal(G), {Addr{{}, &G}});

    std::unordered_map<Node, std::vector<CallBase *>> sitesAt;
    std::vector<CallBase *> sites;
    // A call through a C++ vtable slot calls, by the language's typing, a
    // function the receiver's classes place at that slot: V(c). The flow does
    // not decide it, since an object's cell holds its vptr with its data.
    std::unordered_map<CallBase *, std::vector<Function *>> virtuals;
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          Value *U = S->getValueOperand();
          auto at = access(*S, S->getPointerOperand());
          if (U->getType()->isPointerTy()) {
            for (const Addr &a : at)
              writes(a, val(U));
          } else if (auto *C = dyn_cast<Constant>(U)) {
            place(C, C->getType(), source::pointee(S->getPointerOperand()), at);
          }
        } else if (auto *L = dyn_cast<LoadInst>(&I)) {
          if (L->getType()->isPointerTy())
            for (const Addr &a : access(*L, L->getPointerOperand()))
              reads(a, val(L));
        } else if (auto *VA = dyn_cast<VAArgInst>(&I)) {
          if (VA->getType()->isPointerTy())
            edge(va(), val(VA));
        } else if (auto *P = dyn_cast<PHINode>(&I)) {
          if (P->getType()->isPointerTy())
            for (Value *in : P->incoming_values())
              edge(val(in), val(P));
        } else if (auto *Sel = dyn_cast<SelectInst>(&I)) {
          if (Sel->getType()->isPointerTy()) {
            edge(val(Sel->getTrueValue()), val(Sel));
            edge(val(Sel->getFalseValue()), val(Sel));
          }
        } else if (auto *Cast = dyn_cast<CastInst>(&I)) {
          if (Cast->getType()->isPointerTy() || Cast->getOperand(0)->getType()->isPointerTy())
            edge(val(Cast->getOperand(0)), val(Cast));
        } else if (auto *G = dyn_cast<GetElementPtrInst>(&I)) {
          edge(val(G->getPointerOperand()), val(G));
        } else if (auto *R = dyn_cast<ReturnInst>(&I)) {
          if (Value *V = R->getReturnValue(); V && V->getType()->isPointerTy())
            edge(val(V), node(retN, &F));
        } else if (auto *MT = dyn_cast<MemTransferInst>(&I)) {
          Node bytes = fresh();
          for (const Addr &s : addrs(MT->getSource()))
            if (s.base)
              reads(s, bytes);
          for (const Addr &d : addrs(MT->getDest()))
            if (d.base)
              writes(d, bytes);
        } else if (auto *CB = dyn_cast<CallBase>(&I)) {
          if (isa<IntrinsicInst>(CB) || CB->isInlineAsm())
            continue;
          if (const Function *C = klee::calls::callee(*CB)) {
            Function *B = define(C->getName());
            for (unsigned i = 0; i < CB->arg_size(); ++i)
              if (CB->getArgOperand(i)->getType()->isPointerTy())
                edge(val(CB->getArgOperand(i)), !B ? val(CB) : i < B->arg_size() ? val(B->getArg(i)) : va());
            if (!B && CB->getType()->isPointerTy())
              work.push_back({val(CB), CB});
            else if (B && CB->getType()->isPointerTy())
              edge(node(retN, B), val(CB));
            continue;
          }
          sites.push_back(CB);
          if (vslot(CB).ok) {
            auto &v = virtuals[CB];
            for (Function *T : vtableTargets(CB))
              v.push_back(token(T));
          } else {
            sitesAt[val(CB->getCalledOperand())].push_back(CB);
          }
        }
      }
    });

    // An indirect call passes its actuals to, and takes the return of, each
    // function of its type the callee comes to hold; an external one returns
    // one of its pointer actuals or an object of its own.
    std::set<std::pair<const CallBase *, const Function *>> wired;
    auto wire = [&](CallBase *CB, Function *T) {
      if (T->getFunctionType() != CB->getFunctionType() || !wired.insert({CB, T}).second)
        return;
      bool ext = T->isDeclaration();
      for (unsigned i = 0; i < CB->arg_size(); ++i)
        if (CB->getArgOperand(i)->getType()->isPointerTy())
          link(val(CB->getArgOperand(i)), ext ? val(CB) : i < T->arg_size() ? val(T->getArg(i)) : va());
      if (CB->getType()->isPointerTy()) {
        if (ext)
          work.push_back({val(CB), CB});
        else
          link(node(retN, T), val(CB));
      }
    };
    for (const auto &[CB, ts] : virtuals)
      for (Function *T : ts)
        wire(CB, T);
    while (!work.empty()) {
      auto [n, t] = work.back();
      work.pop_back();
      if (!pt[n].insert(t).second)
        continue;
      for (size_t i = 0; i < succ[n].size(); ++i)
        if (!pt[succ[n][i]].count(t))
          work.push_back({succ[n][i], t});
      if (auto *F = dyn_cast<Function>(t)) {
        if (auto it = sitesAt.find(n); it != sitesAt.end())
          for (CallBase *CB : it->second)
            wire(CB, F);
      } else if (auto it = derefs.find(n); it != derefs.end()) {
        Node e = elem(t);
        for (const Deref &d : it->second)
          if (d.token)
            work.push_back({e, d.token});
          else if (d.load)
            link(e, d.n);
          else
            link(d.n, e);
      }
    }

    auto defined = [&](const auto &from, FunctionType *T) {
      std::vector<Function *> ts;
      for (Value *t : from)
        if (auto *f = dyn_cast<Function>(t); f && !f->isDeclaration() && (!T || f->getFunctionType() == T) &&
                                             std::find(ts.begin(), ts.end(), f) == ts.end())
          ts.push_back(f);
      std::sort(ts.begin(), ts.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
      return ts;
    };
    for (CallBase *CB : sites) {
      auto v = virtuals.find(CB);
      resolved[CB] = v != virtuals.end() ? defined(v->second, CB->getFunctionType())
                                         : defined(pt[val(CB->getCalledOperand())], CB->getFunctionType());
    }
    for (const auto &[V, n] : valN)
      if (auto *A = dyn_cast<Argument>(V))
        if (auto ts = defined(pt[n], nullptr); !ts.empty())
          formalFns[A] = std::move(ts);
    for (const auto &[p, n] : stN) {
      auto &v = fieldFns[{p.back().type, p.back().off}];
      for (Function *f : defined(pt[n], nullptr))
        if (std::find(v.begin(), v.end(), f) == v.end())
          v.push_back(f);
    }
  }

const std::vector<Function *> &Model::fnsOf(const Argument *A) const {
    static const std::vector<Function *> none;
    auto it = formalFns.find(A);
    return it == formalFns.end() ? none : it->second;
  }

calls::Table Model::indirectTargets() const {
    calls::Table t;
    for (Module *M : {&down, &up}) {
      char side = M == &down ? 'D' : 'U';
      for (Function &F : *M) {
        if (F.isDeclaration())
          continue;
        std::vector<std::vector<calls::Fn>> sites;
        for (Instruction &I : instructions(F))
          if (auto *CB = dyn_cast<CallBase>(&I); CB && klee::calls::indirect(*CB)) {
            std::vector<calls::Fn> ts;
            for (Function *T : targetsOf(CB))
              ts.push_back({T->getParent() == &down ? 'D' : 'U', T->getName().str()});
            sites.push_back(ts);
          }
        if (!sites.empty())
          t[{side, F.getName().str()}] = sites;
      }
    }
    return t;
  }

bool Model::exported(const Function &F) {
    switch (F.getLinkage()) {
    case GlobalValue::ExternalLinkage:
    case GlobalValue::AvailableExternallyLinkage:
    case GlobalValue::WeakAnyLinkage:
    case GlobalValue::WeakODRLinkage:
    case GlobalValue::LinkOnceAnyLinkage:
    case GlobalValue::LinkOnceODRLinkage:
      return true;
    default:
      return false;
    }
  }

std::vector<Function *> Model::findExports() {
    std::vector<Function *> v;
    for (Function &F : down)
      if (!F.isDeclaration() && exported(F) && (interfaceNames.empty() || interfaceNames.count(F.getName().str())))
        v.push_back(&F);
    std::sort(v.begin(), v.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    return v;
  }

void Model::buildCallers() {
    eachBody([&](Function &F) {
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (Function *T : targetsOf(CB))
          callersOf[T].push_back(&F);
      }
    });
  }

std::unordered_set<Function *> Model::reachSink() {
    std::unordered_set<Function *> can(sinks.begin(), sinks.end());
    std::vector<Function *> work = sinks;
    for (size_t i = 0; i < work.size(); ++i) {
      auto it = callersOf.find(work[i]);
      if (it == callersOf.end())
        continue;
      for (Function *C : it->second)
        if (can.insert(C).second)
          work.push_back(C);
    }
    return can;
  }

std::vector<Function *> Model::findStarts() {
    std::vector<Function *> v;
    for (Function *E : exports) {
      if (!cone.count(E) || (!startNames.empty() && !startNames.count(E->getName().str())))
        continue;
      bool inside = false;
      auto it = interfaceNames.empty() ? callersOf.find(E) : callersOf.end();
      if (it != callersOf.end())
        for (Function *C : it->second)
          if (cone.count(C))
            inside = true;
      if (!inside)
        v.push_back(E);
    }
    std::sort(v.begin(), v.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    return v;
  }

std::vector<Model::Path> Model::sequences(int seqPick) {
    struct Item {
      int indirect = 0;
      size_t length = 0;
      uint64_t ord = 0;
      std::vector<Function *> fn;
      bool operator>(const Item &o) const {
        return std::tie(indirect, length, ord) > std::tie(o.indirect, o.length, o.ord);
      }
    };
    using Hop = std::pair<Function *, Function *>;
    std::set<Hop> banned;
    std::vector<Path> found;
    for (int n = 0; n <= seqPick; ++n) {
      uint64_t ticket = 0;
      std::priority_queue<Item, std::vector<Item>, std::greater<Item>> q;
      for (Function *E : starts)
        q.push(Item{0, 1, ticket++, {E}});
      std::unordered_set<Function *> expanded;
      Path best;
      bool got = false;
      while (!q.empty()) {
        Item cur = q.top();
        q.pop();
        Function *At = cur.fn.back();
        if (!expanded.insert(At).second)
          continue;
        if (std::find(sinks.begin(), sinks.end(), At) != sinks.end()) {
          best = Path{cur.fn, cur.indirect};
          got = true;
          break;
        }
        for (Instruction &I : instructions(*At)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          auto ts = targetsOf(CB);
          bool indirect = CB->getCalledFunction() == nullptr;
          for (Function *T : ts) {
            if (!cone.count(T) || T->isDeclaration())
              continue;
            if (banned.count({At, T}))
              continue;
            if (std::find(cur.fn.begin(), cur.fn.end(), T) != cur.fn.end())
              continue;
            Item nxt = cur;
            nxt.fn.push_back(T);
            nxt.length = nxt.fn.size();
            if (indirect)
              ++nxt.indirect;
            nxt.ord = ticket++;
            q.push(std::move(nxt));
          }
        }
      }
      if (!got)
        break;
      found.push_back(best);
      if (best.fn.size() >= 2)
        banned.insert({best.fn[best.fn.size() - 2], best.fn.back()});
    }
    return found;
  }
