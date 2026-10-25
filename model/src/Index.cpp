#include "Model.h"

void Model::run(int seqPick, raw_ostream &out) {
    sinks = findSinks();
    if (sinks.empty()) {
      out << "sink none\n";
      return;
    }
    indexFunctions();
    exports = findExports();
    buildCallers();
    cone = reachSink();
    starts = findStarts();
    out << "starts " << starts.size() << "\n";
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

void Model::ensureSlots() const {
    if (slotReady)
      return;
    slotReady = true;
    for (const auto &kv : fnAt) {
      auto put = [&](const Suffix &key, Function *F) {
        auto &v = slotAt[key];
        if (std::find(v.begin(), v.end(), F) == v.end())
          v.push_back(F);
      };
      for (Function *F : kv.second)
        put(kv.first, F);
      for (size_t n = 1; n < kv.first.size(); ++n) {
        bool zero = true;
        for (size_t i = 0; i < n; ++i)
          if (kv.first[i].off != 0)
            zero = false;
        if (!zero)
          continue;
        Suffix tail(kv.first.begin() + (long)n, kv.first.end());
        for (Function *F : kv.second)
          put(tail, F);
      }
    }
  }

std::vector<Function *> Model::storedAt(const Suffix &s) const {
    ensureSlots();
    size_t from = 0;
    for (size_t i = 0; i < s.size(); ++i)
      if (s[i].deref)
        from = i;
    Suffix in(s.begin() + (long)from, s.end());
    if (!in.empty())
      in.front().deref = false;
    for (size_t n = 0; n < in.size(); ++n) {
      if (in[n].type.empty())
        continue;
      auto it = slotAt.find(Suffix(in.begin() + (long)n, in.end()));
      if (it != slotAt.end() && !it->second.empty())
        return it->second;
    }
    return {};
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
    for (const auto &kv : fnAt)
      if (!kv.first.empty() && kv.first.back().type == type && cells.count(kv.first.back().off))
        methods.insert(kv.second.begin(), kv.second.end());
    std::set<Function *> callbacks;
    for (const auto &kv : initSites)
      if (kv.first.first == type)
        for (const InitSite &s : kv.second)
          callbacks.insert(s.stored);
    for (const auto &kv : fnAt)
      if (!kv.first.empty() && kv.first.back().type == type)
        callbacks.insert(kv.second.begin(), kv.second.end());
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

void Model::addFn(const Suffix &s, Function *F) {
    if (!F || s.empty())
      return;
    auto &v = fnAt[s];
    if (std::find(v.begin(), v.end(), F) == v.end())
      v.push_back(F);
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

// D is the source type of the object C initializes, when DWARF declares it.
void Model::walkInit(Constant *C, Type *Ty, const Suffix &suf, bool scalars, const DIType *D) {
    if (!C)
      return;
    if (isa<ConstantPointerNull>(C) || isa<ConstantAggregateZero>(C))
      return;
    if (auto *F = dyn_cast<Function>(C->stripPointerCasts())) {
      if (Function *D = define(F->getName()))
        F = D;
      addFn(suf, F);
      noteScalar(suf, F->getName().str());
      return;
    }
    if (auto *CI = dyn_cast<ConstantInt>(C)) {
      if (scalars)
        noteScalar(suf, dec(CI));
      return;
    }
    if (auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
      Type *ET = CDS->getElementType();
      uint64_t es = dl.getTypeAllocSize(ET).getFixedValue();
      for (unsigned i = 0; i < CDS->getNumElements(); ++i) {
        Suffix n = suf;
        if (!n.empty() && es)
          n.back().off += (int64_t)i * (int64_t)es;
        walkInit(CDS->getElementAsConstant(i), ET, n, scalars, source::element(D));
      }
      return;
    }
    if (auto *S = dyn_cast<ConstantStruct>(C)) {
      auto *ST = dyn_cast<StructType>(Ty ? Ty : C->getType());
      auto named = namesFor(ST);
      if (named.empty()) {
        for (unsigned i = 0; i < S->getNumOperands(); ++i)
          walkInit(S->getOperand(i), S->getOperand(i)->getType(), suf, scalars);
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
          walkInit(S->getOperand(i), E, n, scalars,
                   D ? source::member(D, o, E->isSized() ? dl.getTypeAllocSize(E).getFixedValue() : 0) : nullptr);
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
        walkInit(A->getOperand(i), ET, n, scalars, source::element(D));
      }
    }
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
    for (auto &kv : fnAt) {
      std::sort(kv.second.begin(), kv.second.end(), [](Function *A, Function *B) { return pretty(A->getName()) < pretty(B->getName()); });
    }
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
    struct Site {
      Function *caller = nullptr;
      Function *callee = nullptr;
      unsigned index = 0;
      int from = -1;
    };
    std::vector<Site> sites;
    std::vector<std::pair<const CallBase *, unsigned>> indirect;
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
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *C = CB->getCalledFunction();
        if (C) {
          if (Function *D = define(C->getName()))
            C = D;
        }
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          Value *Op = CB->getArgOperand(i);
          if (auto *Fn = dyn_cast<Function>(Op->stripPointerCasts())) {
            if (Function *D = define(Fn->getName()))
              Fn = D;
            if (C)
              addUnique(argFn[std::make_pair(C, i)], Fn);
            continue;
          }
          int arg = argOf(Op);
          if (C && arg >= 0)
            sites.push_back(Site{&F, C, i, arg});
        }
        if (!C) {
          int arg = argOf(CB->getCalledOperand());
          if (arg >= 0)
            indirect.push_back({CB, (unsigned)arg});
        }
      }
    });
    bool grew = true;
    while (grew) {
      grew = false;
      for (const Site &s : sites) {
        if (s.from < 0 || !s.callee)
          continue;
        for (Function *Fn : argFn[std::make_pair(s.caller, (unsigned)s.from)]) {
          auto &dst = argFn[std::make_pair(s.callee, s.index)];
          if (std::find(dst.begin(), dst.end(), Fn) == dst.end()) {
            dst.push_back(Fn);
            grew = true;
          }
        }
      }
    }
    for (const auto &c : indirect)
      argCallTargets[c.first] = argFn[std::make_pair(const_cast<Function *>(c.first->getFunction()), c.second)];
    for (const Stored &s : stored) {
      for (Function *Fn : argFn[std::make_pair(s.fn, s.arg)])
        addFn(s.suf, Fn);
      argStored[s.fn].push_back({s.arg, s.suf});
    }
    for (const Stored &s : stored) {
      if (argFn[std::make_pair(s.fn, s.arg)].empty())
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
    indexVtables();
    std::unordered_set<const Value *> objs{s.obj};
    for (Instruction &I : instructions(*CB->getFunction()))
      if (auto *C = dyn_cast<CastInst>(&I))
        if (objs.count(C->getOperand(0)))
          objs.insert(&I);
    std::set<std::string> types;
    for (Instruction &I : instructions(*CB->getFunction())) {
      auto *G = dyn_cast<GetElementPtrInst>(&I);
      if (!G)
        continue;
      if (!objs.count(G->getPointerOperand()->stripPointerCasts()))
        continue;
      std::string k = source::container(cast<GEPOperator>(G), dl);
      if (!k.empty())
        types.insert(k);
    }
    for (const std::string &ty : types) {
      auto it = vtOf.find(ty);
      if (it == vtOf.end())
        continue;
      for (Function *Fn : fromVtabs(it->second, s.field, s.slot))
        if (std::find(out.begin(), out.end(), Fn) == out.end())
          out.push_back(Fn);
    }
    // Without the receiver's type, class hierarchy analysis by slot: every
    // vtable's function at this slot whose type is the call's.
    if (out.empty())
      for (const auto &kv : vtOf)
        for (Function *Fn : fromVtabs(kv.second, s.field, s.slot)) {
          Function *B = define(Fn->getName());
          Function *T = B ? B : Fn;
          if (T->getFunctionType() == CB->getFunctionType() && std::find(out.begin(), out.end(), T) == out.end())
            out.push_back(T);
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
    Value *Cal = CB->getCalledOperand()->stripPointerCasts();
    if (auto *A = dyn_cast<GlobalAlias>(Cal))
      if (Constant *Ali = A->getAliasee())
        Cal = Ali->stripPointerCasts();
    if (auto *F = dyn_cast<Function>(Cal)) {
      if (Function *D = define(F->getName()))
        return {D};
      return {};
    }
    Suffix s = suffix(CB->getCalledOperand());
    if (s.empty()) {
      Value *V = CB->getCalledOperand();
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        if (auto *G = dyn_cast<GEPOperator>(V)) {
          V = G->getPointerOperand();
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
            break;
          V = one;
          continue;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (!A) {
            V = L->getPointerOperand();
            continue;
          }
          Value *stored = nullptr;
          for (Instruction &I : instructions(*CB->getFunction())) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || S->getPointerOperand()->stripPointerCasts() != A)
              continue;
            Value *W = S->getValueOperand();
            std::unordered_set<const Value *> walk;
            while (W && walk.insert(W).second) {
              if (auto *C = dyn_cast<CastInst>(W)) {
                W = C->getOperand(0);
                continue;
              }
              if (auto *GE = dyn_cast<GEPOperator>(W)) {
                W = GE->getPointerOperand();
                continue;
              }
              break;
            }
            if (isa<CallBase>(W))
              stored = W;
          }
          if (!stored)
            break;
          V = stored;
          continue;
        }
        if (auto *Call = dyn_cast<CallBase>(V)) {
          if (Function *C = Call->getCalledFunction())
            if (Function *D = define(C->getName()))
              s = returnsOf(D);
        }
        break;
      }
    }
    ensureSlots();
    auto it = slotAt.find(s);
    if (it != slotAt.end())
      return it->second;
    // A field of type T at offset o holds what the program places in any
    // field of T at o, whatever object encloses it: a struct copy carries
    // the source's fields into the destination's.
    for (size_t n = 1; n < s.size(); ++n) {
      if (s[n].type.empty())
        continue;
      auto tl = slotAt.find(Suffix(s.begin() + (long)n, s.end()));
      if (tl != slotAt.end() && !tl->second.empty())
        return tl->second;
    }
    auto at = argCallTargets.find(CB);
    // A formal that callers pass a function through is that function.
    // An empty list is a call through the object, which a vtable may name.
    if (at != argCallTargets.end() && !at->second.empty())
      return at->second;
    return vtableTargets(CB);
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
      if (!cone.count(E))
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
