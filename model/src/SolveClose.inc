    // A function that returns a pointer loaded from a field of an argument
    // returns that field. The caller's actual argument is the object.
    struct RetF {
      unsigned arg = 0;
      Suffix suf;
      bool pointer = false;
    };
    std::unordered_map<const Function *, std::optional<RetF>> retMemo;
    std::unordered_set<const Function *> retSeen;
    std::function<std::optional<RetF>(Function *, Value *)> asField;
    std::function<std::optional<RetF>(Function *)> retField;
    asField = [&](Function *F, Value *V) -> std::optional<RetF> {
      std::unordered_set<const Value *> seen;
      std::function<std::optional<RetF>(Value *)> go = [&](Value *V) -> std::optional<RetF> {
        while (V) {
          if (auto *C = dyn_cast<CastInst>(V)) {
            V = C->getOperand(0);
            continue;
          }
          break;
        }
        if (!V || !seen.insert(V).second)
          return std::nullopt;
        if (auto *L = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (Al) {
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              if (auto got = go(sv))
                return got;
            }
            return std::nullopt;
          }
          auto *A = dyn_cast<Argument>(rootOf(L->getPointerOperand()));
          if (!A)
            return std::nullopt;
          RetF r;
          r.arg = A->getArgNo();
          r.suf = suffix(L->getPointerOperand());
          r.pointer = L->getType()->isPointerTy();
          return r;
        }
        if (auto *A = dyn_cast<Argument>(V)) {
          RetF r;
          r.arg = A->getArgNo();
          return r;
        }
        auto *Call = dyn_cast<CallBase>(V);
        if (!Call)
          return std::nullopt;
        Function *Cal = Call->getCalledFunction();
        if (!Cal)
          return std::nullopt;
        Function *D = define(Cal->getName());
        if (!D)
          return std::nullopt;
        auto inner = retField(D);
        if (!inner || inner->arg >= Call->arg_size())
          return std::nullopt;
        auto sub = go(Call->getArgOperand(inner->arg));
        if (!sub)
          return std::nullopt;
        sub->suf.insert(sub->suf.end(), inner->suf.begin(), inner->suf.end());
        sub->pointer = sub->pointer || inner->pointer;
        return sub;
      };
      return go(V);
    };
    retField = [&](Function *F) -> std::optional<RetF> {
      if (!F || F->isDeclaration())
        return std::nullopt;
      if (auto it = retMemo.find(F); it != retMemo.end())
        return it->second;
      if (!retSeen.insert(F).second)
        return std::nullopt;
      std::optional<RetF> got;
      bool bad = false;
      for (const BasicBlock &BB : *F) {
        auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!R || !R->getReturnValue())
          continue;
        Value *rv = R->getReturnValue();
        if (isa<ConstantPointerNull>(rv) || isa<UndefValue>(rv))
          continue;
        auto one = asField(F, rv);
        if (!one) {
          bad = true;
          break;
        }
        if (!got)
          got = one;
        else if (got->arg != one->arg || got->suf != one->suf || got->pointer != one->pointer) {
          bad = true;
          break;
        }
      }
      retSeen.erase(F);
      if (bad)
        got.reset();
      retMemo[F] = got;
      return got;
    };
    auto flatten = [](const Suffix &in, bool pointee) {
      Suffix flat;
      int64_t acc = 0;
      std::string ty;
      bool any = false;
      auto flush = [&]() {
        if (!any)
          return;
        flat.push_back(Step{ty, acc, false});
        acc = 0;
        ty.clear();
        any = false;
      };
      for (const Step &s : in) {
        if (s.deref) {
          flush();
          flat.push_back(s);
          continue;
        }
        if (!any && !s.type.empty())
          ty = s.type;
        acc += s.off;
        any = true;
      }
      flush();
      if (pointee)
        flat.push_back(Step{"", 0, true});
      return flat;
    };
    std::map<std::pair<int, Suffix>, std::pair<std::string, uint64_t>> vptrAt;
    for (size_t si = 0; si < seq.size(); ++si) {
      Mem &m = memAt(si);
      auto reach = sliceReach(seq[si], seq);
      for (Instruction &I : instructions(*seq[si])) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        bool held = false;
        for (Value *Op : CB->args()) {
          if (!Op->getType()->isPointerTy())
            continue;
          Loc L;
          if (cellLoc(m, Op, L) && !L.suf.empty() && cells.count({L.arg, L.suf}))
            held = true;
        }
        if (held)
          for (unsigned i = 0; i + 1 < CB->arg_size(); ++i) {
            Value *Buf = CB->getArgOperand(i);
            Value *Cnt = CB->getArgOperand(i + 1);
            if (!Buf->getType()->isPointerTy() || !Cnt->getType()->isIntegerTy())
              continue;
            auto *Call = dyn_cast<CallBase>(Buf->stripPointerCasts());
            if (!Call || !Call->getCalledFunction())
              continue;
            Function *D = define(Call->getCalledFunction()->getName());
            auto rf = retField(D);
            if (!rf || !rf->pointer || rf->arg >= Call->arg_size())
              continue;
            Loc base;
            if (!cellLoc(m, Call->getArgOperand(rf->arg), base) || base.suf.empty())
              continue;
            Suffix both = base.suf;
            both.insert(both.end(), rf->suf.begin(), rf->suf.end());
            Suffix flat = flatten(both, true);
            if (flat.empty())
              continue;
            cells.insert({base.arg, flat});
            if (auto *CI = dyn_cast<ConstantInt>(Cnt))
              if (CI->getBitWidth() <= 64 && !CI->isNegative() && CI->getZExtValue())
                readBytes[{base.arg, flat}] = CI->getZExtValue();
          }
        if (CB->getCalledFunction())
          continue;
        if (!reach.count(CB->getParent()))
          continue;
        VSlot vs = vslot(CB);
        if (!vs.ok)
          continue;
        Loc objL;
        if (!cellLoc(m, vs.obj, objL))
          continue;
        auto ts = targetsOf(CB);
        Function *want = nullptr;
        Function *next = si + 1 < seq.size() ? seq[si + 1] : nullptr;
        if (next && std::find(ts.begin(), ts.end(), next) != ts.end())
          want = next;
        else if (ts.size() == 1)
          want = ts[0];
        indexVtables();
        std::unordered_set<const Value *> objs{vs.obj};
        for (Instruction &GI : instructions(*seq[si]))
          if (auto *C = dyn_cast<CastInst>(&GI))
            if (objs.count(C->getOperand(0)))
              objs.insert(&GI);
        std::set<std::string> types;
        for (Instruction &GI : instructions(*seq[si])) {
          auto *G = dyn_cast<GetElementPtrInst>(&GI);
          if (!G || !objs.count(G->getPointerOperand()->stripPointerCasts()))
            continue;
          std::string k = source::container(cast<GEPOperator>(G), dl);
          if (!k.empty())
            types.insert(k);
        }
        std::vector<const VTab *> hits;
        std::set<std::tuple<GlobalVariable *, uint64_t, int64_t>> seenVt;
        auto consider = [&](const VTab &vt) {
          if (vt.field != vs.field || !vt.g || !vt.g->hasInitializer())
            return;
          if (!seenVt.insert({vt.g, vt.base, vt.field}).second)
            return;
          hits.push_back(&vt);
        };
        if (want) {
          for (const VTab &vt : vtAll)
            if (vt.g && vt.g->hasInitializer() &&
                functionAt(vt.g->getInitializer(), 0, vt.base + vs.slot) == want)
              consider(vt);
        }
        if (hits.empty())
          for (const std::string &ty : types) {
            auto it = vtOf.find(ty);
            if (it == vtOf.end())
              continue;
            for (const VTab &vt : it->second)
              consider(vt);
          }
        if (hits.empty() && next)
          for (const VTab &vt : vtAll) {
            if (!vt.g || !vt.g->hasInitializer())
              continue;
            Function *slotFn = functionAt(vt.g->getInitializer(), 0, vt.base + vs.slot);
            if (slotFn && reachesFn(slotFn, next))
              consider(vt);
          }
        // Every slot this slice calls through the same object is a defined
        // function. A declaration in one slot is not that vtable.
        std::vector<uint64_t> needSlots{vs.slot};
        {
          std::unordered_set<const Function *> seenFn;
          std::function<void(Function *, const std::vector<std::optional<Loc>> &)> slotsOf;
          slotsOf = [&](Function *SF, const std::vector<std::optional<Loc>> &sargs) {
            if (!SF || SF->isDeclaration() || !seenFn.insert(SF).second)
              return;
            Mem mm;
            bindFormals(mm, SF, sargs);
            propagateObject(mm, SF);
            auto sreach = sliceReach(SF, seq);
            for (const BasicBlock *BB : sreach)
              for (Instruction &JI : *const_cast<BasicBlock *>(BB)) {
                auto *O = dyn_cast<CallBase>(&JI);
                if (!O)
                  continue;
                if (!O->getCalledFunction()) {
                  VSlot os = vslot(O);
                  if (os.ok) {
                    Loc oL;
                    if (cellLoc(mm, os.obj, oL) && oL.arg == objL.arg && oL.suf == objL.suf)
                      needSlots.push_back(os.slot);
                  }
                  continue;
                }
                Function *D = define(O->getCalledFunction()->getName());
                if (!D || D->isDeclaration() || ignorable(O->getCalledFunction()))
                  continue;
                std::vector<std::optional<Loc>> down;
                bool touch = false;
                for (Value *Op : O->args()) {
                  Loc L;
                  if (objectLoc(mm, Op, L)) {
                    down.push_back(L);
                    touch = true;
                  } else
                    down.push_back(std::nullopt);
                }
                if (touch)
                  slotsOf(D, down);
              }
          };
          std::vector<std::optional<Loc>> top(seq[si]->arg_size());
          for (unsigned a = 0; a < top.size(); ++a)
            top[a] = Loc{(int)a, {}};
          if (si < frames.size())
            top = frames[si];
          slotsOf(seq[si], top);
        }
        auto definedAt = [&](const VTab *vt, uint64_t slot) {
          if (!vt->g || !vt->g->hasInitializer())
            return false;
          Function *Fn = functionAt(vt->g->getInitializer(), 0, vt->base + slot);
          return Fn && !Fn->isDeclaration();
        };
        std::vector<const VTab *> covered;
        for (const VTab *vt : hits) {
          bool ok = true;
          for (uint64_t slot : needSlots)
            if (!definedAt(vt, slot)) {
              ok = false;
              break;
            }
          if (ok)
            covered.push_back(vt);
        }
        hits.swap(covered);
        const VTab *hit = nullptr;
        if (hits.size() == 1)
          hit = hits[0];
        else if (!hits.empty()) {
          uint64_t wantN = objectBytes(vs.obj, seq[si]);
          std::vector<const VTab *> sized;
          for (const VTab *vt : hits)
            for (const auto &kv : vtOf) {
              if (!wantN || typeBytes(kv.first) != wantN)
                continue;
              for (const VTab &x : kv.second)
                if (x.g == vt->g && x.base == vt->base && x.field == vt->field)
                  sized.push_back(vt);
            }
          std::set<const VTab *> one(sized.begin(), sized.end());
          if (one.size() == 1)
            hit = *one.begin();
        }
        if (!hit)
          continue;
        std::string ty;
        for (const auto &kv : vtOf)
          for (const VTab &x : kv.second)
            if (x.g == hit->g && x.base == hit->base && x.field == hit->field)
              ty = kv.first;
        Suffix suf = objL.suf;
        suf.push_back(Step{ty, vs.field, false});
        vptrAt[{objL.arg, suf}] = {hit->g->getName().str(), hit->base};
        cells.insert({objL.arg, suf});
      }
    }
    // The value of a load is the store to that address. The value of a call
    // is what it returns, or the pointer it stores into an object it was
    // given. A value already followed is a cycle.
    {
      struct Frame {
        Function *fn = nullptr;
        std::vector<std::optional<Loc>> args;
      };
      std::map<std::string, std::optional<Loc>> knownV;
      std::set<std::string> stackV;
      auto argKey = [](const std::vector<std::optional<Loc>> &args) {
        std::string k;
        for (const auto &a : args) {
          if (!a) {
            k += "-;";
            continue;
          }
          k += std::to_string(a->arg);
          for (const Step &s : a->suf) {
            k.push_back('|');
            k += s.type;
            k.push_back('@');
            k += std::to_string(s.off);
            k.push_back(s.deref ? 'd' : 'n');
          }
          k.push_back(';');
        }
        return k;
      };
      std::function<std::optional<Loc>(Function *, Value *, const std::vector<std::optional<Loc>> &, bool)> origin;
      auto locate = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args, bool &loaded) -> std::optional<Loc> {
        loaded = false;
        Suffix pre;
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            if (!G->hasAllConstantIndices()) {
              if (isa<StructType>(G->getSourceElementType()))
                return std::nullopt;
              V = G->getPointerOperand();
              continue;
            }
            Step st;
            if (!constStep(dl, G, st))
              return std::nullopt;
            if (movesAddress(st))
              pre.insert(pre.begin(), st);
            V = G->getPointerOperand();
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!Al) {
              if (!L->getType()->isPointerTy())
                return std::nullopt;
              loaded = true;
              if (!pre.empty())
                pre.back().deref = true;
              V = L->getPointerOperand();
              continue;
            }
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            if (!st)
              return std::nullopt;
            V = st;
            continue;
          }
          auto *A = dyn_cast<Argument>(V);
          if (!A || A->getArgNo() >= args.size() || !args[A->getArgNo()])
            return std::nullopt;
          Loc out = *args[A->getArgNo()];
          out.suf.insert(out.suf.end(), pre.begin(), pre.end());
          return out;
        }
        return std::nullopt;
      };
      origin = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args, bool asPtr) -> std::optional<Loc> {
        if (!F || !V)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        std::string key = std::to_string(reinterpret_cast<uintptr_t>(F)) + ":" + std::to_string(reinterpret_cast<uintptr_t>(V)) +
                          ":" + (asPtr ? "1:" : "0:") + argKey(args);
        if (auto it = knownV.find(key); it != knownV.end())
          return it->second;
        if (!stackV.insert(key).second)
          return std::nullopt;
        struct Leave {
          std::set<std::string> &stack;
          std::map<std::string, std::optional<Loc>> &known;
          std::string key;
          std::optional<Loc> result;
          ~Leave() {
            stack.erase(key);
            known.emplace(key, result);
          }
        } leave{stackV, knownV, key, {}};
        bool loaded = false;
        if (auto L = locate(F, V, args, loaded)) {
          if (!L->suf.empty() && (asPtr || loaded))
            L->suf.push_back(Step{"", 0, true});
          leave.result = L;
          return L;
        }
        if (auto *L = dyn_cast<LoadInst>(V)) {
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || S->getPointerOperand()->stripPointerCasts() != L->getPointerOperand()->stripPointerCasts())
              continue;
            if (isa<ConstantPointerNull>(S->getValueOperand()) || isa<UndefValue>(S->getValueOperand()))
              continue;
            if (auto got = origin(F, S->getValueOperand(), args, L->getType()->isPointerTy())) {
              leave.result = got;
              return got;
            }
          }
          leave.result = origin(F, L->getPointerOperand(), args, false);
          return leave.result;
        }
        if (auto *P = dyn_cast<PHINode>(V)) {
          for (Value *in : P->incoming_values())
            if (auto got = origin(F, in, args, asPtr)) {
              leave.result = got;
              return got;
            }
          return std::nullopt;
        }
        auto *CB = dyn_cast<CallBase>(V);
        if (!CB)
          return std::nullopt;
        Function *Cal = CB->getCalledFunction();
        if (!Cal)
          return std::nullopt;
        Function *D = define(Cal->getName());
        if (!D || D->isDeclaration())
          return std::nullopt;
        std::vector<std::optional<Loc>> inner(D->arg_size());
        unsigned n = 0;
        for (Value *Op : CB->args()) {
          if (n >= inner.size())
            break;
          bool ld = false;
          if (auto L = locate(F, Op, args, ld))
            inner[n] = L;
          else if (Op->getType()->isPointerTy())
            inner[n] = origin(F, Op, args, false);
          ++n;
        }
        std::optional<Loc> ret;
        for (const BasicBlock &BB : *D) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue())
            continue;
          if (isa<ConstantPointerNull>(R->getReturnValue()) || isa<UndefValue>(R->getReturnValue()))
            continue;
          if (auto got = origin(D, R->getReturnValue(), inner, asPtr))
            ret = got;
        }
        for (Instruction &I : instructions(*D)) {
          auto *S = dyn_cast<StoreInst>(&I);
          if (!S || !S->getValueOperand()->getType()->isPointerTy())
            continue;
          bool ld = false;
          if (!locate(D, S->getPointerOperand(), inner, ld))
            continue;
          if (auto got = origin(D, S->getValueOperand(), inner, true))
            ret = got;
        }
        leave.result = ret;
        return ret;
      };
      auto rooted = [&](Function *F, Value *V, unsigned arg) {
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            V = G->getPointerOperand();
            continue;
          }
          if (auto *Al = dyn_cast<AllocaInst>(V)) {
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            V = st;
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!Al)
              return false;
            Value *st = nullptr;
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              st = sv;
            }
            V = st;
            continue;
          }
          auto *A = dyn_cast<Argument>(V);
          return A && A->getArgNo() == arg;
        }
        return false;
      };
      std::function<bool(Function *, unsigned, std::unordered_set<const Function *> &)> copied;
      copied = [&](Function *F, unsigned src, std::unordered_set<const Function *> &seen) -> bool {
        if (!F || F->isDeclaration() || !seen.insert(F).second)
          return false;
        auto samePtr = [&](Value *V) {
          std::unordered_set<const Value *> local;
          while (V && local.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            if (auto *Al = dyn_cast<AllocaInst>(V)) {
              Value *st = nullptr;
              for (Instruction &SI : instructions(*F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                  continue;
                Value *sv = S->getValueOperand();
                if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                  continue;
                st = sv;
              }
              V = st;
              continue;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (!Al)
                return false;
              Value *st = nullptr;
              for (Instruction &SI : instructions(*F)) {
                auto *S = dyn_cast<StoreInst>(&SI);
                if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                  continue;
                Value *sv = S->getValueOperand();
                if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                  continue;
                st = sv;
              }
              V = st;
              continue;
            }
            auto *A = dyn_cast<Argument>(V);
            return A && A->getArgNo() == src;
          }
          return false;
        };
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          Copy cp = fixedCopy(*CB);
          auto pointerMove = [&](const CallBase &Call) {
            if (Call.arg_size() < 3 || !Call.getArgOperand(2)->getType()->isIntegerTy())
              return false;
            auto *N = dyn_cast<ConstantInt>(Call.getArgOperand(2));
            return N && N->getZExtValue() <= dl.getPointerSize(0) * 2;
          };
          auto restInt = [&](const CallBase &Call) {
            for (unsigned k = 3; k < Call.arg_size(); ++k)
              if (!Call.getArgOperand(k)->getType()->isIntegerTy())
                return false;
            return true;
          };
          if (cp.ok && !pointerMove(*CB) && restInt(*CB) && samePtr(CB->getArgOperand(cp.src)))
            return true;
          if (CB->arg_size() >= 3 && CB->getArgOperand(0)->getType()->isPointerTy() &&
              CB->getArgOperand(1)->getType()->isPointerTy() && CB->getArgOperand(2)->getType()->isIntegerTy() &&
              restInt(*CB) && !pointerMove(*CB) && samePtr(CB->getArgOperand(1)))
            return true;
          Function *Cal = CB->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D && !Cal)
            for (Function *T : targetsOf(CB))
              if (T && !T->isDeclaration()) {
                D = T;
                break;
              }
          if (!D || D->isDeclaration())
            continue;
          for (unsigned i = 0; i < CB->arg_size() && i < D->arg_size(); ++i)
            if (CB->getArgOperand(i)->getType()->isPointerTy() && samePtr(CB->getArgOperand(i)))
              if (copied(D, i, seen))
                return true;
        }
        return false;
      };
      std::function<std::optional<Loc>(Function *, Value *, const std::vector<std::optional<Loc>> &,
                                       std::unordered_set<const Value *> &)>
          filled;
      filled = [&](Function *F, Value *V, const std::vector<std::optional<Loc>> &args,
                   std::unordered_set<const Value *> &seen) -> std::optional<Loc> {
        if (!F || !V || !seen.insert(V).second)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (auto *L = dyn_cast<LoadInst>(V))
          return filled(F, L->getPointerOperand(), args, seen);
        if (auto *CB = dyn_cast<CallBase>(V)) {
          for (Value *Op : CB->args())
            if (Op->getType()->isPointerTy())
              if (auto got = filled(F, Op, args, seen))
                return got;
          return std::nullopt;
        }
        auto *Al = dyn_cast<AllocaInst>(V);
        if (!Al)
          return std::nullopt;
        for (Instruction &I : instructions(*F)) {
          auto *Call = dyn_cast<CallBase>(&I);
          if (!Call)
            continue;
          int slot = -1;
          for (unsigned i = 0; i < Call->arg_size(); ++i)
            if (Call->getArgOperand(i)->stripPointerCasts() == Al)
              slot = (int)i;
          if (slot < 0)
            continue;
          Function *Cal = Call->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D || D->isDeclaration())
            continue;
          std::vector<std::optional<Loc>> inner(D->arg_size());
          unsigned n = 0;
          for (Value *Op : Call->args()) {
            if (n >= inner.size())
              break;
            bool ld = false;
            if (auto loc = locate(F, Op, args, ld))
              inner[n] = loc;
            ++n;
          }
          for (Instruction &SI : instructions(*D)) {
            auto *S = dyn_cast<StoreInst>(&SI);
            if (!S || !S->getValueOperand()->getType()->isPointerTy())
              continue;
            if (!rooted(D, S->getPointerOperand(), (unsigned)slot))
              continue;
            if (auto got = origin(D, S->getValueOperand(), inner, true))
              return got;
          }
          for (Instruction &SI : instructions(*D)) {
            auto *Sub = dyn_cast<CallBase>(&SI);
            if (!Sub)
              continue;
            for (unsigned i = 0; i < Sub->arg_size(); ++i)
              if (rooted(D, Sub->getArgOperand(i), (unsigned)slot))
                if (auto got = filled(D, Sub->getArgOperand(i), inner, seen))
                  return got;
          }
        }
        return std::nullopt;
      };
      const auto roots = cells;
      auto sameStep = [](const Step &a, const Step &b) { return a.type == b.type && a.off == b.off; };
      auto insideRoot = [&](const Loc &L) {
        for (const auto &c : roots)
          if (c.first == L.arg && !c.second.empty() && L.suf.size() >= c.second.size() &&
              std::equal(c.second.begin(), c.second.end(), L.suf.begin(), sameStep))
            return true;
        return false;
      };
      auto keep = [&](const Loc &L) {
        if (L.suf.empty() || insideRoot(L))
          return;
        if (L.suf.size() == 1 && L.suf[0].type.empty())
          return;
        cells.insert({L.arg, L.suf});
      };
      std::vector<Frame> work;
      std::unordered_set<Function *> seenF;
      for (size_t si = 0; si < seq.size(); ++si) {
        Frame fr;
        fr.fn = seq[si];
        fr.args = frames[si];
        if (fr.args.size() < seq[si]->arg_size())
          fr.args.resize(seq[si]->arg_size());
        if (si == 0)
          for (unsigned i = 0; i < seq[si]->arg_size(); ++i)
            if (!fr.args[i])
              fr.args[i] = Loc{(int)i, {}};
        seenF.insert(seq[si]);
        work.push_back(std::move(fr));
      }
      for (size_t wi = 0; wi < work.size(); ++wi) {
        Function *F = work[wi].fn;
        std::vector<std::optional<Loc>> args = work[wi].args;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          std::vector<std::optional<Loc>> at(CB->arg_size());
          bool fromExport = false;
          std::vector<unsigned> fresh;
          for (unsigned i = 0; i < CB->arg_size(); ++i) {
            bool ld = false;
            auto L = locate(F, CB->getArgOperand(i), args, ld);
            if (!L)
              continue;
            at[i] = L;
            fromExport = true;
          }
          if (fromExport)
            for (unsigned i = 0; i < CB->arg_size(); ++i) {
              if (at[i] || !CB->getArgOperand(i)->getType()->isPointerTy())
                continue;
              at[i] = origin(F, CB->getArgOperand(i), args, true);
              if (!at[i]) {
                std::unordered_set<const Value *> seen;
                at[i] = filled(F, CB->getArgOperand(i), args, seen);
              }
              if (at[i])
                fresh.push_back(i);
            }
          Function *Cal = CB->getCalledFunction();
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D && !Cal)
            for (Function *T : targetsOf(CB))
              if (T && !T->isDeclaration()) {
                D = T;
                break;
              }
          if (D && !D->isDeclaration() && fromExport)
            for (unsigned i : fresh) {
              if (i >= D->arg_size())
                continue;
              std::unordered_set<const Function *> copiedSeen;
              if (!copied(D, i, copiedSeen))
                continue;
              keep(*at[i]);
            }
          if (D && !D->isDeclaration() && fromExport && seenF.insert(D).second) {
            Frame fr;
            fr.fn = D;
            fr.args.resize(D->arg_size());
            for (unsigned i = 0; i < at.size() && i < fr.args.size(); ++i)
              fr.args[i] = at[i];
            work.push_back(std::move(fr));
          }
        }
      }
      // A store replaces a cell's entry value only when every execution of
      // the sequence runs it before the goal: in a sequence function it
      // precedes that step's goal, and in a callee it precedes every return
      // of a call that is itself always run. A store on another branch, or
      // after the goal, leaves the entry value the one the goal reads.
      constexpr size_t inCallee = std::numeric_limits<size_t>::max();
      auto always = [&](size_t si, Instruction *I) {
        if (si == inCallee)
          return dominatesReturns(I);
        if (si >= seq.size())
          return false;
        if (si < stepGoal.size() && stepGoal[si])
          return dominatesBefore(I, stepGoal[si]);
        for (Instruction &G : instructions(*seq[si]))
          if (sinkHere(G, sinkFile, sinkLine) && dominatesBefore(I, &G))
            return true;
        return false;
      };
      std::vector<std::pair<int, Suffix>> drop;
      for (const auto &c : cells) {
        if (!indexed.count(c))
          continue;
        bool named = false;
        for (const auto &kv : facts)
          if (tail(c.second, kv.first) && !kv.second.empty())
            named = true;
        if (named)
          continue;
        auto fieldOf = [&](Function *F, Value *V) {
          Suffix s;
          std::unordered_set<const Value *> seen;
          while (V && seen.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            auto *G = dyn_cast<GEPOperator>(V);
            if (!G)
              break;
            if (!G->hasAllConstantIndices()) {
              if (isa<StructType>(G->getSourceElementType()))
                return Suffix{};
              V = G->getPointerOperand();
              continue;
            }
            Step st;
            if (!constStep(dl, G, st))
              return Suffix{};
            if (movesAddress(st))
              s.insert(s.begin(), st);
            V = G->getPointerOperand();
          }
          return s;
        };
        std::function<bool(Function *, size_t, std::unordered_set<Function *> &)> written;
        written = [&](Function *F, size_t si, std::unordered_set<Function *> &seen) {
          if (!F || F->isDeclaration())
            return false;
          if (si == inCallee && !seen.insert(F).second)
            return false;
          for (Instruction &I : instructions(*F)) {
            if (!always(si, &I))
              continue;
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              if (isa<Constant>(S->getValueOperand()))
                continue;
              Suffix got = fieldOf(F, S->getPointerOperand());
              if (!got.empty() && c.second.size() >= got.size() &&
                  std::equal(got.begin(), got.end(), c.second.end() - (long)got.size(), sameStep))
                return true;
              continue;
            }
            auto *CB = dyn_cast<CallBase>(&I);
            if (CB) {
              Function *Cal = CB->getCalledFunction();
              Function *Callee = Cal ? define(Cal->getName()) : nullptr;
              for (unsigned a = 0; Callee && a < CB->arg_size() && a < Callee->arg_size(); ++a) {
                if (!CB->getArgOperand(a)->getType()->isPointerTy())
                  continue;
                Suffix at = fieldOf(F, CB->getArgOperand(a));
                if (at.empty() || c.second.size() < at.size() ||
                    !std::equal(at.begin(), at.end(), c.second.end() - (long)at.size(), sameStep))
                  continue;
                for (Instruction &SI : instructions(*Callee)) {
                  auto *St = dyn_cast<StoreInst>(&SI);
                  if (!St || isa<Constant>(St->getValueOperand()) || !dominatesReturns(St))
                    continue;
                  Value *P = St->getPointerOperand();
                  std::unordered_set<const Value *> local;
                  while (P && local.insert(P).second) {
                    while (auto *C = dyn_cast<CastInst>(P))
                      P = C->getOperand(0);
                    if (auto *G = dyn_cast<GEPOperator>(P)) {
                      P = G->getPointerOperand();
                      continue;
                    }
                    auto *Al = dyn_cast<AllocaInst>(P->stripPointerCasts());
                    if (!Al && isa<LoadInst>(P))
                      Al = dyn_cast<AllocaInst>(cast<LoadInst>(P)->getPointerOperand()->stripPointerCasts());
                    if (Al) {
                      Value *st = nullptr;
                      for (Instruction &AI : instructions(*Callee)) {
                        auto *WS = dyn_cast<StoreInst>(&AI);
                        if (!WS || WS->getPointerOperand()->stripPointerCasts() != Al)
                          continue;
                        if (isa<ConstantPointerNull>(WS->getValueOperand()) || isa<UndefValue>(WS->getValueOperand()))
                          continue;
                        st = WS->getValueOperand();
                      }
                      P = st;
                      continue;
                    }
                    break;
                  }
                  auto *Arg = dyn_cast<Argument>(P);
                  if (Arg && Arg->getArgNo() == a)
                    return true;
                }
              }
            }
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            Function *D = Cal ? define(Cal->getName()) : nullptr;
            if (written(D, inCallee, seen))
              return true;
          }
          return false;
        };
        bool hit = false;
        std::unordered_set<Function *> seenFn;
        for (size_t si = 0; si < seq.size(); ++si)
          if (written(seq[si], si, seenFn)) {
            hit = true;
            break;
          }
        if (hit)
          drop.push_back(c);
      }
      for (const auto &c : drop)
        cells.erase(c);
      // A call that stores a fresh pointer into a slot, and does not copy
      // the bytes that pointer used to address, replaces the slot. The
      // caller's pointer is not the object the sink reads.
      auto freshPtr = [&](Value *V) {
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *CB = dyn_cast<CallBase>(V);
          if (!CB || !CB->getType()->isPointerTy())
            return false;
          for (Value *Op : CB->args())
            if (!Op->getType()->isIntegerTy())
              return false;
          Function *Cal = CB->getCalledFunction();
          if (!Cal)
            return false;
          Function *D = define(Cal->getName());
          return !D || D->isDeclaration();
        }
        return false;
      };
      auto slotOf = [&](Function *F, Value *V) {
        Suffix s;
        std::unordered_set<const Value *> seen;
        while (V && seen.insert(V).second) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *G = dyn_cast<GEPOperator>(V);
          if (!G)
            break;
          if (!G->hasAllConstantIndices()) {
            if (isa<StructType>(G->getSourceElementType()))
              return Suffix{};
            V = G->getPointerOperand();
            continue;
          }
          Step st;
          if (!constStep(dl, G, st))
            return Suffix{};
          if (movesAddress(st))
            s.insert(s.begin(), st);
          V = G->getPointerOperand();
        }
        return s;
      };
      // A value comes from an argument when casts, field addresses, the
      // alloca the argument was saved in, or a call that returns an address
      // inside that argument, lead back to it.
      auto fromArg = [](Function *Callee, Value *P, int argNo) {
        std::function<bool(Value *, std::unordered_set<const Value *> &)> go;
        go = [&](Value *V, std::unordered_set<const Value *> &local) -> bool {
          while (V && local.insert(V).second) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            if (auto *G = dyn_cast<GEPOperator>(V)) {
              V = G->getPointerOperand();
              continue;
            }
            if (auto *CB = dyn_cast<CallBase>(V)) {
              if (!CB->getType()->isPointerTy())
                return false;
              for (Value *Op : CB->args())
                if (Op->getType()->isPointerTy() && go(Op, local))
                  return true;
              return false;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              V = L->getPointerOperand();
              continue;
            }
            auto *Al = dyn_cast<AllocaInst>(V->stripPointerCasts());
            if (!Al)
              break;
            Value *st = nullptr;
            for (Instruction &AI : instructions(*Callee)) {
              auto *WS = dyn_cast<StoreInst>(&AI);
              if (!WS || WS->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              if (isa<ConstantPointerNull>(WS->getValueOperand()) || isa<UndefValue>(WS->getValueOperand()))
                continue;
              st = WS->getValueOperand();
            }
            V = st;
          }
          auto *Arg = dyn_cast<Argument>(V);
          return Arg && (int)Arg->getArgNo() == argNo;
        };
        std::unordered_set<const Value *> local;
        return go(P, local);
      };
      std::function<bool(Function *, int, int, std::unordered_set<Function *> &)> replaced;
      replaced = [&](Function *Callee, int slotArg, int freshArg, std::unordered_set<Function *> &seen) -> bool {
        if (!Callee || Callee->isDeclaration() || !seen.insert(Callee).second)
          return false;
        bool storesFresh = false;
        bool copies = false;
        bool deeper = false;
        for (Instruction &SI : instructions(*Callee)) {
          if (auto *St = dyn_cast<StoreInst>(&SI)) {
            if (!isa<Constant>(St->getValueOperand()) && dominatesReturns(St) &&
                fromArg(Callee, St->getValueOperand(), freshArg) &&
                fromArg(Callee, St->getPointerOperand(), slotArg))
              storesFresh = true;
          }
          auto *Call = dyn_cast<CallBase>(&SI);
          if (!Call)
            continue;
          if (Call->arg_size() >= 3 && Call->getArgOperand(0)->getType()->isPointerTy() &&
              Call->getArgOperand(1)->getType()->isPointerTy() &&
              Call->getArgOperand(2)->getType()->isIntegerTy() &&
              (fromArg(Callee, Call->getArgOperand(0), slotArg) ||
               fromArg(Callee, Call->getArgOperand(1), slotArg)))
            copies = true;
          Function *InnerCal = Call->getCalledFunction();
          Function *Inner = InnerCal ? define(InnerCal->getName()) : nullptr;
          if (!Inner || Inner->isDeclaration())
            continue;
          int slot2 = -1;
          int made2 = -1;
          for (unsigned a = 0; a < Call->arg_size() && a < Inner->arg_size(); ++a) {
            Value *Op = Call->getArgOperand(a);
            if (!Op->getType()->isPointerTy())
              continue;
            if (fromArg(Callee, Op, slotArg))
              slot2 = (int)a;
            if (fromArg(Callee, Op, freshArg))
              made2 = (int)a;
          }
          if (slot2 >= 0 && made2 >= 0 && slot2 != made2 && dominatesReturns(Call) && replaced(Inner, slot2, made2, seen))
            deeper = true;
        }
        return !copies && (storesFresh || deeper);
      };
      drop.clear();
      for (const auto &c : cells) {
        if (calleeAt.count(c) || pathAt.count(c) || keyCell.count(c) || pathCell.count(c))
          continue;
        bool named = false;
        for (const auto &kv : facts)
          if (tail(c.second, kv.first) && !kv.second.empty())
            named = true;
        if (named)
          continue;
        bool parent = false;
        for (const auto &o : cells)
          if (o.first == c.first && o.second.size() > c.second.size() &&
              std::equal(c.second.begin(), c.second.end(), o.second.begin(), sameStep))
            parent = true;
        if (parent)
          continue;
        bool hit = false;
        for (size_t si = 0; si < seq.size(); ++si) {
          Function *F = seq[si];
          if (hit)
            break;
          if (!F || F->isDeclaration())
            continue;
          for (Instruction &I : instructions(*F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB || !always(si, CB))
              continue;
            Function *Cal = CB->getCalledFunction();
            Function *Callee = Cal ? define(Cal->getName()) : nullptr;
            if (!Callee || Callee->isDeclaration())
              continue;
            int slotArg = -1;
            int made = -1;
            for (unsigned a = 0; a < CB->arg_size() && a < Callee->arg_size(); ++a) {
              Value *Op = CB->getArgOperand(a);
              if (!Op->getType()->isPointerTy())
                continue;
              Suffix at = slotOf(F, Op);
              if (!at.empty() && c.second.size() >= at.size() &&
                  std::equal(at.begin(), at.end(), c.second.end() - (long)at.size(), sameStep))
                slotArg = (int)a;
              if (freshPtr(Op))
                made = (int)a;
            }
            if (slotArg < 0 || made < 0 || slotArg == made)
              continue;
            std::unordered_set<Function *> seenFn;
            if (replaced(Callee, slotArg, made, seenFn))
              hit = true;
          }
        }
        if (hit)
          drop.push_back(c);
      }
      for (const auto &c : drop)
        cells.erase(c);
    }
    // A call that returns its first pointer and takes the cell plus another
    // object assigns that object into the cell. The sink reads the object.
    auto sameSuf = [](const Suffix &a, const Suffix &b) {
      if (a.size() != b.size())
        return false;
      for (size_t i = 0; i < a.size(); ++i)
        if (a[i].type != b[i].type || a[i].off != b[i].off)
          return false;
      return true;
    };
    auto loadedPtr = [](Value *V) -> Value * {
      while (auto *C = dyn_cast<CastInst>(V))
        V = C->getOperand(0);
      auto *L = dyn_cast<LoadInst>(V);
      if (!L || !L->getType()->isPointerTy())
        return nullptr;
      return L->getPointerOperand();
    };
    for (const auto &c : pathAt) {
      if (!pathPtr.count(c))
        continue;
      for (size_t si = 0; si < seq.size(); ++si) {
        Function *F = seq[si];
        if (!F || F->isDeclaration())
          continue;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->arg_size() != 2 || !CB->getType()->isPointerTy())
            continue;
          if (!CB->getArgOperand(0)->getType()->isPointerTy() || !CB->getArgOperand(1)->getType()->isPointerTy())
            continue;
          Loc dest, src;
          if (!cellLoc(memAt(si), CB->getArgOperand(0), dest))
            continue;
          if (dest.arg != c.first || !sameSuf(dest.suf, c.second))
            continue;
          if (!cellLoc(memAt(si), CB->getArgOperand(1), src) || src.arg < 0)
            continue;
          if (src.arg == dest.arg && sameSuf(src.suf, dest.suf))
            continue;
          if (!src.suf.empty())
            continue;
          std::string ty;
          if (!c.second.empty())
            if (StructType *ST = structNamed(c.second.back().type))
              if (Type *E = [&]() -> Type * {
                    if (!ST->isSized())
                      return nullptr;
                    const StructLayout *SL = dl.getStructLayout(ST);
                    for (unsigned i = 0; i < ST->getNumElements(); ++i)
                      if ((int64_t)SL->getElementOffset(i) == c.second.back().off)
                        return ST->getElementType(i);
                    return nullptr;
                  }())
                if (auto *FT = dyn_cast<StructType>(E))
                  if (FT->hasName())
                    ty = FT->getName().str();
          pathSrc.push_back(PathSrc{src.arg, ty});
        }
      }
    }
    auto underByte = [&](const Loc &L) {
      for (const auto &c : cells) {
        if (c.first != L.arg || c.second.empty() || !c.second.back().type.empty())
          continue;
        if (c.second.size() < L.suf.size())
          continue;
        bool pre = true;
        for (size_t i = 0; i < L.suf.size(); ++i)
          if (c.second[i].type != L.suf[i].type || c.second[i].off != L.suf[i].off)
            pre = false;
        if (pre)
          return true;
      }
      return false;
    };
    std::deque<Mem> owned;
    struct Job {
      Function *F = nullptr;
      Mem *m = nullptr;
    };
    std::vector<Job> jobs;
    std::set<Function *> seqFn(seq.begin(), seq.end());
    std::set<std::string> seenCallee;
    for (size_t si = 0; si < seq.size(); ++si) {
      Function *F = seq[si];
      if (!F || F->isDeclaration())
        continue;
      jobs.push_back(Job{F, &memAt(si)});
    }
    for (size_t qi = 0; qi < jobs.size(); ++qi) {
      Function *F = jobs[qi].F;
      Mem &m = *jobs[qi].m;
      for (Instruction &I : instructions(*F)) {
        Value *lhs = nullptr;
        Value *rhs = nullptr;
        if (auto *Sub = dyn_cast<BinaryOperator>(&I)) {
          if (Sub->getOpcode() == Instruction::Sub) {
            lhs = loadedPtr(Sub->getOperand(0));
            rhs = loadedPtr(Sub->getOperand(1));
          }
        } else if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
          lhs = loadedPtr(Cmp->getOperand(0));
          rhs = loadedPtr(Cmp->getOperand(1));
        }
        auto locate = [&](Value *P, Loc &L) {
          Loc c;
          if (cellLoc(m, P, c) && !c.suf.empty()) {
            L = c;
            return true;
          }
          if (auto v = valueAt(F, P, m))
            if (!v->suf.empty()) {
              L = *v;
              return true;
            }
          return false;
        };
        if (lhs && rhs) {
          Loc a, b;
          if (locate(lhs, a) && locate(rhs, b) && a.arg == b.arg && a.suf.size() == b.suf.size()) {
            bool prefix = true;
            for (size_t i = 0; i + 1 < a.suf.size(); ++i)
              if (a.suf[i].type != b.suf[i].type || a.suf[i].off != b.suf[i].off)
                prefix = false;
            if (prefix && a.suf.back().off != b.suf.back().off && fieldIsPointer(a.suf.back().type, a.suf.back().off) &&
                fieldIsPointer(b.suf.back().type, b.suf.back().off)) {
              if (a.suf.back().off < b.suf.back().off)
                ptrSpan.push_back(PtrSpan{a.arg, a.suf, b.suf});
              else
                ptrSpan.push_back(PtrSpan{a.arg, b.suf, a.suf});
            }
          }
        }
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        for (Function *Callee : targetsOf(CB)) {
          if (!Callee || Callee->isDeclaration() || seqFn.count(Callee))
            continue;
          std::vector<std::optional<Loc>> args(Callee->arg_size());
          bool hit = false;
          for (unsigned i = 0; i < CB->arg_size() && i < Callee->arg_size(); ++i) {
            if (!CB->getArgOperand(i)->getType()->isPointerTy())
              continue;
            Loc L;
            bool got = cellLoc(m, CB->getArgOperand(i), L);
            if (!got || L.suf.empty()) {
              if (auto v = valueAt(F, CB->getArgOperand(i), m)) {
                L = *v;
                got = true;
              }
            }
            if (!got || !underByte(L))
              continue;
            args[i] = L;
            hit = true;
          }
          if (!hit)
            continue;
          std::string key = Callee->getName().str();
          for (const auto &L : args) {
            key.push_back('|');
            if (!L)
              continue;
            key += std::to_string(L->arg);
            for (const Step &s : L->suf)
              key += ":" + s.type + "@" + std::to_string(s.off);
          }
          if (!seenCallee.insert(key).second)
            continue;
          owned.emplace_back();
          bindFormals(owned.back(), Callee, args);
          propagate(owned.back(), Callee);
          jobs.push_back(Job{Callee, &owned.back()});
        }
      }
    }
    // A cast's vptr is a constraint of the witness when the cast's result is
    // an actual of a sequence edge. Two such casts of one object that need
    // different tables have no common dynamic type, so neither is kept.
    std::map<std::pair<int, Suffix>, std::set<std::pair<std::string, uint64_t>>> tablesAt;
    for (const std::string &k : framePins) {
      auto it = vptrPins.find(k);
      if (it == vptrPins.end() || vptrBad.count(k) || it->second.suf.empty())
        continue;
      Suffix obj(it->second.suf.begin(), it->second.suf.end() - 1);
      tablesAt[{it->second.arg, obj}].insert({it->second.g, it->second.byte});
    }
    for (const std::string &k : framePins) {
      auto it = vptrPins.find(k);
      if (it == vptrPins.end() || vptrBad.count(k) || it->second.suf.empty())
        continue;
      const VptrPin &p = it->second;
      Suffix obj(p.suf.begin(), p.suf.end() - 1);
      if (tablesAt[{p.arg, obj}].size() != 1)
        continue;
      auto key = std::make_pair(p.arg, p.suf);
      cells.insert(key);
      if (!vptrAt.count(key))
        vptrAt[key] = {p.g, p.byte};
    }
    // §3.5 경계 셀: 어떤 교차 근의 접두에 놓인 셀. 근 자신(suffix 동일)도 포함.
    auto isBoundary = [&](const std::pair<int, Suffix> &c) {
      for (const auto &r : boundaryRoots) {
        if (r.first != c.first || r.second.size() > c.second.size())
          continue;
        if (std::equal(r.second.begin(), r.second.end(), c.second.begin()))
          return true;
      }
      return false;
    };
    size_t boundaryCells = 0;
    for (const auto &c : cells) {
      out << "cell arg" << c.first;
      for (const Step &s : c.second)
        out << " " << s.type << "+" << s.off;
      std::set<std::string> vals;
      size_t best = 0;
      for (const auto &kv : facts) {
        if (!tail(c.second, kv.first) || kv.first.size() < best)
          continue;
        best = kv.first.size();
        vals = kv.second;
      }
      auto narrow = [&](const std::set<std::string> &keep) {
        if (keep.empty())
          return;
        if (vals.empty()) {
          vals = keep;
          return;
        }
        std::set<std::string> both;
        std::set_intersection(keep.begin(), keep.end(), vals.begin(), vals.end(), std::inserter(both, both.end()));
        vals.swap(both);
      };
      std::set<std::string> must;
      size_t bestNeed = 0;
      for (const auto &kv : need) {
        if (!tail(c.second, kv.first) || kv.first.size() < bestNeed)
          continue;
        bestNeed = kv.first.size();
        must = kv.second;
      }
      if (indirectAt.count(c)) {
        vals.clear();
        if (auto callIt = calleeAt.find(c); callIt != calleeAt.end())
          vals = callIt->second;
      } else {
        narrow(must);
        auto callIt = calleeAt.find(c);
        if (callIt != calleeAt.end())
          narrow(callIt->second);
      }
      auto sit = seqStore.find(c);
      if (sit != seqStore.end() && !sit->second.empty()) {
        bool numeric = true;
        for (const std::string &v : vals) {
          size_t i = !v.empty() && v[0] == '-' ? 1 : 0;
          if (i >= v.size())
            numeric = false;
          for (; numeric && i < v.size(); ++i)
            if (v[i] < '0' || v[i] > '9')
              numeric = false;
        }
        if (numeric)
          vals = sit->second;
      }
      auto cit = cmps.find(c);
      if (cit != cmps.end())
        narrow(cit->second);
      std::set<std::string> text;
      bool path = pathAt.count(c) != 0;
      bool asPtr = pathPtr.count(c) != 0;
      if (path && !asPtr && text.empty() && vals.empty())
        text.insert("f");
      bool hasChild = false;
      for (const auto &o : cells) {
        if (o.first == c.first && o.second.size() > c.second.size() &&
            std::equal(c.second.begin(), c.second.end(), o.second.begin()))
          hasChild = true;
      }
      if (hasChild && vals.size() == 1 && *vals.begin() == "0")
        vals.clear();
      auto fit = fileCell.find(c);
      bool nullOnly = vals.size() == 1 && *vals.begin() == "0";
      bool asFile = fit != fileCell.end() && text.empty() && (vals.empty() || nullOnly);
      if (asFile)
        vals.clear();
      std::optional<uint64_t> flen;
      if (asFile) {
        auto lit = fileLen.find(c);
        if (lit != fileLen.end())
          flen = lit->second;
      }
      auto vit = vptrAt.find(c);
      if (vit != vptrAt.end() && text.empty()) {
        out << " = " << vit->second.first << "+" << vit->second.second;
        vals.clear();
      } else if (!text.empty()) {
        out << " =";
        for (const std::string &t : text)
          out << " \"" << t << "\"";
      } else if (!vals.empty()) {
        out << " =";
        for (const std::string &v : vals)
          out << " " << v;
      } else if (neq.count(c)) {
        out << " !=";
        for (const std::string &v : neq[c])
          out << " " << v;
      }
      if (asFile || path) {
        out << " file";
        if (flen)
          out << " " << *flen;
      }
      if (isBoundary(c))
        ++boundaryCells;
      out << "\n";
      // The same path with each dereference marked, which the cell line's
      // spelling leaves implicit.
      out << "steps arg" << c.first;
      for (const Step &s : c.second)
        out << " " << s.type << "+" << s.off << (s.deref ? "*" : "");
      out << "\n";
      Solved s;
      s.arg = c.first;
      s.suf = c.second;
      s.vals = std::move(vals);
      if (s.vals.empty())
        if (auto nit = neq.find(c); nit != neq.end())
          s.ban = nit->second;
      s.text = std::move(text);
      s.file = asFile || (path && asPtr);
      s.pathPtr = path && asPtr;
      if (vit != vptrAt.end()) {
        s.glob = vit->second.first;
        s.gbyte = vit->second.second;
        s.vals.clear();
      }
      s.len = flen;
      if (asFile)
        s.fty = fit->second;
      auto w = wide.find(c);
      if (w != wide.end() && w->second)
        s.width = w->second;
      s.code = calleeAt.count(c) != 0;
      solvedCells.push_back(std::move(s));
    }
    out << "boundary cells " << boundaryCells << " of " << cells.size()
        << " roots " << boundaryRoots.size() << " unresolved " << boundaryUnresolved << "\n";
    // R(π): resolved boundary roots (export-arg access paths). Φ_∂ projects
    // residual onto cells under some r∈R only when |R|>0. unresolved counts
    // are diagnostic; they do not enable that projection by themselves.
    for (const auto &r : boundaryRoots) {
      out << "boundaryroot arg" << r.first;
      for (const Step &s : r.second)
        out << " " << s.type << "+" << s.off;
      out << "\n";
    }
    Transition tr;
    using Cell = std::pair<int, Suffix>;
    std::map<Cell, SlotVal> mem;
    auto writeCell = [&](const Cell &c) {
      out << " arg" << c.first;
      for (const Step &st : c.second)
        out << " " << st.type << "+" << st.off;
    };
    // Φ_pre (§3.5 정리 B 보정): Loc 판정된 셀 중, 첫 교차 이하 D 경로 조건이
    // 읽은 것. Loc 합성(프레임·팩·GEP/load)으로 cells/stepEv에 오른 뒤, 여기서
    // 클라이언트 의무로 올린다. Lemma W: 엔트리 클로저가 교차 전에 그 셀을
    // must-constant store로 확립한 경우만 제외한다. kind 'd'는 값이 비는
    // 추상 define이라 자기 확립이 아니다 — 넣으면 φ 제약(≠0 등)이 Φ_pre에서
    // 떨어져 realize가 open으로 남는다.
    {
      std::set<Cell> pre, selfWritten;
      for (const auto &[si, evs] : stepEv) {
        if (si > crossStep)
          continue;
        for (const Ev &e : evs) {
          if (!e.fn || e.fn->getParent() != &down)
            continue;
          if (e.kind == 'e' || e.kind == 'n' || e.kind == 'r' || e.kind == 'b' || e.kind == 'g')
            pre.insert(e.cell);
          else if (e.kind == 'p') {
            pre.insert(e.cell);
            pre.insert(e.src);
          } else if (e.kind == 's' && e.mustExit && e.callMust) {
            selfWritten.insert(e.cell);
          }
        }
      }
      for (const Cell &c : pre) {
        if (selfWritten.count(c))
          continue;
        out << "prefixcell";
        writeCell(c);
        out << "\n";
      }
    }
    auto rankOf = [&](Instruction *I) {
      int level = 0;
      int idx = 0;
      if (I) {
        if (auto *N = domTree(I->getFunction()).getNode(I->getParent()))
          level = (int)N->getLevel();
        for (Instruction &J : *I->getParent()) {
          if (&J == I)
            break;
          ++idx;
        }
      }
      return std::make_pair(level, idx);
    };
    auto readNode = [](auto &nodes, auto &find, int id) {
      id = find(id);
      SlotVal s;
      s.known = nodes[id].has;
      s.val = nodes[id].val;
      s.any = nodes[id].any;
      s.ban = nodes[id].ban;
      s.slo = nodes[id].slo;
      s.shi = nodes[id].shi;
      s.ulo = nodes[id].ulo;
      s.uhi = nodes[id].uhi;
      s.sloV = nodes[id].sloV;
      s.shiV = nodes[id].shiV;
      s.uloV = nodes[id].uloV;
      s.uhiV = nodes[id].uhiV;
      s.ordBytes = nodes[id].ordBytes;
      s.oneBits = nodes[id].oneBits;
      s.zeroBits = nodes[id].zeroBits;
      return s;
    };
    struct Node {
      int parent = 0;
      bool has = false;
      std::string val;
      std::set<std::string> any;
      std::set<std::string> ban;
      bool slo = false, shi = false, ulo = false, uhi = false;
      int64_t sloV = 0, shiV = 0;
      uint64_t uloV = 0, uhiV = 0;
      unsigned ordBytes = 0;
      uint64_t oneBits = 0, zeroBits = 0;
    };
    std::vector<Node> nodes;
    auto make = [&]() {
      int id = (int)nodes.size();
      nodes.push_back(Node{id, false, {}, {}, {}});
      return id;
    };
    std::function<int(int)> find = [&](int x) {
      if (nodes[x].parent != x)
        nodes[x].parent = find(nodes[x].parent);
      return nodes[x].parent;
    };
    std::function<void(int)> violate;
    auto pin = [&](int x, const std::string &v) {
      x = find(x);
      if (nodes[x].has && nodes[x].val != v)
        tr.conflict = true;
      if (nodes[x].ban.count(v))
        tr.conflict = true;
      if (!nodes[x].any.empty() && !nodes[x].any.count(v))
        tr.conflict = true;
      nodes[x].has = true;
      nodes[x].val = v;
      nodes[x].any.clear();
      if (violate)
        violate(x);
    };
    auto forbid = [&](int x, const std::set<std::string> &vs) {
      x = find(x);
      nodes[x].ban.insert(vs.begin(), vs.end());
      if (nodes[x].has && nodes[x].ban.count(nodes[x].val))
        tr.conflict = true;
    };
    auto allow = [&](int x, const std::set<std::string> &vs) {
      if (vs.empty())
        return;
      if (vs.size() == 1) {
        pin(x, *vs.begin());
        return;
      }
      x = find(x);
      if (nodes[x].has) {
        if (!vs.count(nodes[x].val))
          tr.conflict = true;
        return;
      }
      if (nodes[x].any.empty())
        nodes[x].any = vs;
      else {
        std::set<std::string> both;
        std::set_intersection(nodes[x].any.begin(), nodes[x].any.end(), vs.begin(), vs.end(), std::inserter(both, both.end()));
        if (both.empty())
          tr.conflict = true;
        nodes[x].any.swap(both);
      }
    };
    violate = [&](int x) {
      x = find(x);
      Node &n = nodes[x];
      if (n.slo && n.shi && n.sloV > n.shiV)
        tr.conflict = true;
      if (n.ulo && n.uhi && n.uloV > n.uhiV)
        tr.conflict = true;
      if (n.oneBits & n.zeroBits)
        tr.conflict = true;
      if (!n.has)
        return;
      if (n.oneBits || n.zeroBits) {
        auto u = asU64(n.val);
        auto s = asI64(n.val);
        uint64_t k = u ? *u : s ? (uint64_t)*s : 0;
        if ((!u && !s) || (k & n.oneBits) != n.oneBits || (k & n.zeroBits))
          tr.conflict = true;
      }
      if (n.slo || n.shi) {
        auto s = asI64(n.val);
        if (!s || (n.slo && *s < n.sloV) || (n.shi && *s > n.shiV))
          tr.conflict = true;
      }
      if (n.ulo || n.uhi) {
        auto u = asU64(n.val);
        if (!u || (n.ulo && *u < n.uloV) || (n.uhi && *u > n.uhiV))
          tr.conflict = true;
      }
    };
    auto loS = [&](int x, int64_t v) {
      x = find(x);
      if (!nodes[x].slo || v > nodes[x].sloV) {
        nodes[x].slo = true;
        nodes[x].sloV = v;
      }
      violate(x);
    };
    auto hiS = [&](int x, int64_t v) {
      x = find(x);
      if (!nodes[x].shi || v < nodes[x].shiV) {
        nodes[x].shi = true;
        nodes[x].shiV = v;
      }
      violate(x);
    };
    auto loU = [&](int x, uint64_t v) {
      x = find(x);
      if (!nodes[x].ulo || v > nodes[x].uloV) {
        nodes[x].ulo = true;
        nodes[x].uloV = v;
      }
      violate(x);
    };
    auto hiU = [&](int x, uint64_t v) {
      x = find(x);
      if (!nodes[x].uhi || v < nodes[x].uhiV) {
        nodes[x].uhi = true;
        nodes[x].uhiV = v;
      }
      violate(x);
    };
    auto boundConst = [&](int x, unsigned pred, const std::string &k, unsigned bytes) {
      x = find(x);
      if (bytes == 1 || bytes == 2 || bytes == 4 || bytes == 8)
        nodes[x].ordBytes = bytes;
      auto fail = [&] { tr.conflict = true; };
      switch (pred) {
      case ICmpInst::ICMP_SLT: {
        auto s = asI64(k);
        if (!s || *s == std::numeric_limits<int64_t>::min())
          return fail();
        hiS(x, *s - 1);
        break;
      }
      case ICmpInst::ICMP_SLE: {
        auto s = asI64(k);
        if (!s)
          return fail();
        hiS(x, *s);
        break;
      }
      case ICmpInst::ICMP_SGT: {
        auto s = asI64(k);
        if (!s || *s == std::numeric_limits<int64_t>::max())
          return fail();
        loS(x, *s + 1);
        break;
      }
      case ICmpInst::ICMP_SGE: {
        auto s = asI64(k);
        if (!s)
          return fail();
        loS(x, *s);
        break;
      }
      case ICmpInst::ICMP_ULT: {
        auto u = asU64(k);
        if (!u || *u == 0)
          return fail();
        hiU(x, *u - 1);
        break;
      }
      case ICmpInst::ICMP_ULE: {
        auto u = asU64(k);
        if (!u)
          return fail();
        hiU(x, *u);
        break;
      }
      case ICmpInst::ICMP_UGT: {
        auto u = asU64(k);
        if (!u || *u == std::numeric_limits<uint64_t>::max())
          return fail();
        loU(x, *u + 1);
        break;
      }
      case ICmpInst::ICMP_UGE: {
        auto u = asU64(k);
        if (!u)
          return fail();
        loU(x, *u);
        break;
      }
      default:
        break;
      }
    };
    auto holds = [&](unsigned pred, const std::string &a, const std::string &b) {
      if (pred == ICmpInst::ICMP_EQ)
        return a == b;
      if (pred == ICmpInst::ICMP_NE)
        return a != b;
      auto sa = asI64(a);
      auto sb = asI64(b);
      auto ua = asU64(a);
      auto ub = asU64(b);
      switch (pred) {
      case ICmpInst::ICMP_SLT:
        return sa && sb && *sa < *sb;
      case ICmpInst::ICMP_SLE:
        return sa && sb && *sa <= *sb;
      case ICmpInst::ICMP_SGT:
        return sa && sb && *sa > *sb;
      case ICmpInst::ICMP_SGE:
        return sa && sb && *sa >= *sb;
      case ICmpInst::ICMP_ULT:
        return ua && ub && *ua < *ub;
      case ICmpInst::ICMP_ULE:
        return ua && ub && *ua <= *ub;
      case ICmpInst::ICMP_UGT:
        return ua && ub && *ua > *ub;
      case ICmpInst::ICMP_UGE:
        return ua && ub && *ua >= *ub;
      default:
        return true;
      }
    };
    struct Live {
      unsigned pred = 0;
      int na = 0;
      int nb = 0;
      Cell a;
      Cell b;
      unsigned bytes = 8;
    };
    std::vector<Live> live;
    std::map<Cell, int> cur;
    std::map<Cell, int> entry;
    std::map<Cell, int> residNode;
    bool sawResidual = false;
    auto ensure = [&](const Cell &c) {
      if (cur.count(c))
        return;
      int id = make();
      cur[c] = entry[c] = id;
      if (sawResidual)
        residNode.emplace(c, id);
    };
    auto unite = [&](const Cell &dst, const Cell &src) {
      ensure(dst);
      ensure(src);
      int a = find(cur[dst]);
      int b = find(cur[src]);
      if (a == b)
        return;
      if (nodes[b].has)
        pin(a, nodes[b].val);
      else if (!nodes[b].any.empty())
        allow(a, nodes[b].any);
      forbid(a, nodes[b].ban);
      if (nodes[b].slo)
        loS(a, nodes[b].sloV);
      if (nodes[b].shi)
        hiS(a, nodes[b].shiV);
      if (nodes[b].ulo)
        loU(a, nodes[b].uloV);
      if (nodes[b].uhi)
        hiU(a, nodes[b].uhiV);
      if (nodes[b].ordBytes && !nodes[a].ordBytes)
        nodes[a].ordBytes = nodes[b].ordBytes;
      nodes[a].oneBits |= nodes[b].oneBits;
      nodes[a].zeroBits |= nodes[b].zeroBits;
      violate(a);
      auto retarget = [&](int &id) {
        if (id == b)
          id = a;
      };
      for (auto &kv : cur)
        retarget(kv.second);
      for (auto &kv : entry)
        retarget(kv.second);
      for (auto &kv : residNode)
        retarget(kv.second);
      for (Live &L : live) {
        retarget(L.na);
        retarget(L.nb);
      }
    };
    auto cmpBytes = [](unsigned bits) {
      unsigned bytes = bits >= 8 ? bits / 8 : 8;
      if (bytes != 1 && bytes != 2 && bytes != 4 && bytes != 8)
        bytes = 8;
      return bytes;
    };
    auto strict = [](unsigned p) {
      return p == ICmpInst::ICMP_NE || p == ICmpInst::ICMP_SLT || p == ICmpInst::ICMP_SGT ||
             p == ICmpInst::ICMP_ULT || p == ICmpInst::ICMP_UGT;
    };
    // A definition of a pointer cell replaces the object behind it. A cell
    // reached through that pointer, c . (s, deref) . t, then names a field of
    // the new object; its entry value is no longer what a later read sees, so
    // the read is not upward-exposed. The cells are the ones the events name.
    std::map<int, std::vector<Cell>> named;
    for (const auto &kv : stepEv)
      for (const Ev &e : kv.second) {
        named[e.cell.first].push_back(e.cell);
        if (e.kind == 'c')
          named[e.src.first].push_back(e.src);
      }
    for (auto &kv : named) {
      std::sort(kv.second.begin(), kv.second.end());
      kv.second.erase(std::unique(kv.second.begin(), kv.second.end()), kv.second.end());
    }
    auto killBelow = [&](const Cell &c) {
      auto it = named.find(c.first);
      if (it == named.end())
        return;
      size_t n = c.second.size();
      for (const Cell &d : it->second) {
        if (d.second.size() <= n || !d.second[n].deref)
          continue;
        if (!std::equal(c.second.begin(), c.second.end(), d.second.begin()))
          continue;
        cur[d] = make();
      }
    };
    for (size_t si = 0; si < mapped && si < seq.size(); ++si) {
      Function *SF = seq[si];
      std::vector<Instruction *> goals;
      if (si < stepGoal.size() && stepGoal[si])
        goals.push_back(stepGoal[si]);
      else {
        for (Instruction &I : instructions(*SF))
          if (sinkHere(I, sinkFile, sinkLine))
            goals.push_back(&I);
        if (goals.empty())
          for (BasicBlock &BB : *SF)
            if (auto *R = dyn_cast<ReturnInst>(BB.getTerminator()))
              goals.push_back(R);
      }
      if (si == residual) {
        sawResidual = true;
        for (const auto &kv : cur)
          residNode.emplace(kv.first, kv.second);
      }
      if (goals.empty())
        continue;
      std::unordered_set<Instruction *> gset(goals.begin(), goals.end());
      auto blocks = chosenPath(SF, gset);
      if (auto sp = stepPath.find(si); sp != stepPath.end() &&
          std::all_of(goals.begin(), goals.end(), [&](Instruction *g) { return sp->second.count(g->getParent()); }))
        blocks = sp->second;
      // An event is on the witness when its instruction lies on the chosen
      // path and executes before the goal. Domination would keep only the
      // facts common to every path, which is how a store on this path was
      // left as an entry obligation.
      auto beforeGoal = [&](Instruction *I, Instruction *G) {
        if (!I || !G || I->getFunction() != G->getFunction())
          return false;
        if (I == G)
          return true;
        if (blocks.empty() || !blocks.count(I->getParent()) || !blocks.count(G->getParent()))
          return dominatesBefore(I, G);
        if (I->getParent() == G->getParent()) {
          for (Instruction &J : *I->getParent()) {
            if (&J == G)
              return false;
            if (&J == I)
              return true;
          }
          return false;
        }
        std::unordered_set<const BasicBlock *> seen;
        std::vector<const BasicBlock *> st{G->getParent()};
        while (!st.empty()) {
          const BasicBlock *BB = st.back();
          st.pop_back();
          if (!BB || !seen.insert(BB).second)
            continue;
          if (BB == I->getParent())
            return true;
          for (const BasicBlock *P : predecessors(BB))
            if (blocks.count(P))
              st.push_back(P);
        }
        return false;
      };
      std::vector<const Ev *> kept;
      for (const Ev &e : stepEv[si]) {
        if (!e.at)
          continue;
        bool all = true;
        for (Instruction *goal : goals) {
          if (e.anchor == goal) {
            all = false;
            break;
          }
          bool seqEv = e.fn == SF || !e.anchor;
          if (seqEv) {
            if (!beforeGoal(e.at, goal))
              all = false;
          } else if (!(e.callMust && e.anchor && beforeGoal(e.anchor, goal)))
            all = false;
          if (!all)
            break;
        }
        if (all)
          kept.push_back(&e);
      }
      // Dominator rank alone leaves ties between blocks of one depth; the
      // position in the function's block list makes the order total. Events
      // at one instruction keep the order the walk made them; return facts
      // change no cell, so they go after the rest, ordered by content.
      std::map<const BasicBlock *, unsigned> blockNo;
      auto posOf = [&](Instruction *I) {
        BasicBlock *BB = I->getParent();
        if (!blockNo.count(BB)) {
          unsigned n = 0;
          for (BasicBlock &B : *BB->getParent())
            blockNo[&B] = n++;
        }
        return std::make_tuple(I->getFunction()->getName(), blockNo[BB], rankOf(I).second);
      };
      std::stable_sort(kept.begin(), kept.end(), [&](const Ev *a, const Ev *b) {
        auto left = a->anchor ? rankOf(a->anchor) : rankOf(a->at);
        auto right = b->anchor ? rankOf(b->anchor) : rankOf(b->at);
        if (left != right)
          return left < right;
        int nestA = a->anchor ? 1 : 0;
        int nestB = b->anchor ? 1 : 0;
        if (nestA != nestB)
          return nestA < nestB;
        if (rankOf(a->at) != rankOf(b->at))
          return rankOf(a->at) < rankOf(b->at);
        Instruction *outA = a->anchor ? a->anchor : a->at, *outB = b->anchor ? b->anchor : b->at;
        if (posOf(outA) != posOf(outB))
          return posOf(outA) < posOf(outB);
        if (posOf(a->at) != posOf(b->at))
          return posOf(a->at) < posOf(b->at);
        if ((a->kind == 'q') != (b->kind == 'q'))
          return b->kind == 'q';
        if (a->kind == 'q')
          return std::tie(a->pred, a->vals, a->words) < std::tie(b->pred, b->vals, b->words);
        return false;
      });
      struct CallFact {
        std::vector<std::pair<unsigned, int64_t>> cs;
        std::optional<int64_t> fallback;
        std::optional<int64_t> witness;
        bool lookup = false;
        bool live = false;
      };
      std::map<const Instruction *, CallFact> callFact;
      for (const Ev *e : kept) {
        if (e->kind != 'q' || e->vals.empty() || !e->at)
          continue;
        int64_t k = 0;
        const std::string &text = *e->vals.begin();
        auto parsed = std::from_chars(text.data(), text.data() + text.size(), k);
        if (parsed.ec != std::errc())
          continue;
        callFact[e->at].cs.push_back({(unsigned)e->pred, k});
        callFact[e->at].live = callFact[e->at].live || e->live;
      }
      for (auto &kv : callFact) {
        auto *CB = dyn_cast<CallBase>(kv.first);
        if (!CB)
          continue;
        Function *Cal = CB->getCalledFunction();
        Function *D = Cal ? define(Cal->getName()) : nullptr;
        if (!D)
          D = Cal;
        if (auto arg = fallbackArg(D))
          if (*arg < CB->arg_size())
            if (auto *C = dyn_cast<ConstantInt>(CB->getArgOperand(*arg)))
              kv.second.fallback = C->getSExtValue();
        kv.second.lookup = lookupOnly(D) && !kv.second.live;
        kv.second.witness = satisfyingValue(kv.second.cs, kv.second.fallback);
      }
      for (const Ev *e : kept) {
        if (e->kind == 'q') {
          if (!e->words.empty() && !e->vals.empty() && e->fn) {
            out << "model return " << e->words[0] << " " << icmpName((unsigned)e->pred) << " " << *e->vals.begin();
            out << " at " << e->fn->getName();
            if (const DebugLoc &DL = e->at->getDebugLoc())
              out << " line " << DL.getLine() << " col " << DL.getCol();
            for (size_t w = 1; w < e->words.size(); ++w)
              out << " \"" << e->words[w] << "\"";
            if (auto it = callFact.find(e->at); it != callFact.end()) {
              if (it->second.fallback)
                out << " fallback " << *it->second.fallback;
              if (it->second.witness)
                out << " witness " << *it->second.witness;
              if (it->second.lookup)
                out << " lookup";
              if (it->second.live)
                out << " live";
            }
            out << "\n";
          }
        } else if (e->kind == 'c') {
          out << "copy " << si;
          writeCell(e->src);
          out << " ->";
          writeCell(e->cell);
          out << "\n";
          ensure(e->src);
          ensure(e->cell);
          cur[e->cell] = find(cur[e->src]);
          killBelow(e->cell);
        } else if (e->kind == 's') {
          out << "store " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          int id = make();
          cur[e->cell] = id;
          allow(id, e->vals);
          killBelow(e->cell);
        } else if (e->kind == 'd') {
          out << "define " << si;
          writeCell(e->cell);
          out << "\n";
          ensure(e->cell);
          cur[e->cell] = make();
          killBelow(e->cell);
        } else if (e->kind == 'e') {
          out << "pre " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          for (const std::string &v : e->vals)
            pin(cur[e->cell], v);
        } else if (e->kind == 'n') {
          out << "pre " << si;
          writeCell(e->cell);
          out << " !=";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          forbid(cur[e->cell], e->vals);
        } else if (e->kind == 'g') {
          out << "edge " << si;
          writeCell(e->cell);
          out << " =";
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          allow(cur[e->cell], e->vals);
        } else if (e->kind == 'b') {
          out << "bits " << si;
          writeCell(e->cell);
          out << (e->pred ? " has" : " lacks");
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          int x = find(cur[e->cell]);
          for (const std::string &v : e->vals)
            if (auto m = asU64(v))
              (e->pred ? nodes[x].oneBits : nodes[x].zeroBits) |= *m;
          violate(x);
        } else if (e->kind == 'r') {
          out << "bound " << si;
          writeCell(e->cell);
          out << " " << icmpName((unsigned)e->pred);
          for (const std::string &v : e->vals)
            out << " " << v;
          out << "\n";
          ensure(e->cell);
          unsigned bytes = cmpBytes(e->bits);
          for (const std::string &v : e->vals)
            boundConst(cur[e->cell], (unsigned)e->pred, v, bytes);
        } else if (e->kind == 'p') {
          out << "rel " << si;
          writeCell(e->cell);
          out << " " << icmpName((unsigned)e->pred);
          writeCell(e->src);
          out << "\n";
          unsigned pred = (unsigned)e->pred;
          if (e->cell == e->src) {
            if (strict(pred))
              tr.conflict = true;
            continue;
          }
          ensure(e->cell);
          ensure(e->src);
          unsigned bytes = cmpBytes(e->bits);
          if (pred == ICmpInst::ICMP_EQ) {
            unite(e->cell, e->src);
            continue;
          }
          int na = find(cur[e->cell]);
          int nb = find(cur[e->src]);
          if (pred == ICmpInst::ICMP_NE) {
            if (nodes[na].has && nodes[nb].has) {
              if (nodes[na].val == nodes[nb].val)
                tr.conflict = true;
            } else if (nodes[na].has)
              forbid(nb, {nodes[na].val});
            else if (nodes[nb].has)
              forbid(na, {nodes[nb].val});
            else
              live.push_back(Live{pred, na, nb, e->cell, e->src, bytes});
            continue;
          }
          if (nodes[na].has && nodes[nb].has) {
            if (!holds(pred, nodes[na].val, nodes[nb].val))
              tr.conflict = true;
          } else if (nodes[na].has)
            boundConst(nb, (unsigned)ICmpInst::getSwappedPredicate((ICmpInst::Predicate)pred), nodes[na].val, bytes);
          else if (nodes[nb].has)
            boundConst(na, pred, nodes[nb].val, bytes);
          else
            live.push_back(Live{pred, na, nb, e->cell, e->src, bytes});
        }
      }
    }
    for (const Live &L : live) {
      if (L.na < 0 || L.nb < 0 || L.na >= (int)nodes.size() || L.nb >= (int)nodes.size())
        continue;
      Node &na = nodes[L.na];
      Node &nb = nodes[L.nb];
      if (L.na == L.nb) {
        if (strict(L.pred))
          tr.conflict = true;
        continue;
      }
      if (na.has && nb.has) {
        if (!holds(L.pred, na.val, nb.val))
          tr.conflict = true;
        continue;
      }
      if (na.has && !nb.has) {
        boundConst(L.nb, (unsigned)ICmpInst::getSwappedPredicate((ICmpInst::Predicate)L.pred), na.val, L.bytes);
        continue;
      }
      if (!na.has && nb.has) {
        boundConst(L.na, L.pred, nb.val, L.bytes);
        continue;
      }
      // The witness formula is the value at entry of the sequence. A store on
      // the path replaces the cell, so a use after that store constrains the
      // stored value and is not an obligation on the client.
      auto onEntry = [&](const Cell &c, int id) {
        auto it = entry.find(c);
        return it != entry.end() && it->second == id;
      };
      if (!onEntry(L.a, L.na) || !onEntry(L.b, L.nb))
        continue;
      Rel r;
      r.pred = L.pred;
      r.a = L.a.first;
      r.asuf = L.a.second;
      r.b = L.b.first;
      r.bsuf = L.b.second;
      r.bytes = L.bytes ? L.bytes : 8;
      rels.push_back(r);
      out << "model";
      writeCell(L.a);
      out << " " << icmpName(L.pred);
      writeCell(L.b);
      out << "\n";
    }
    // A count an upstream call reads that many bytes by is at most the bytes
    // the harness holds behind the paired pointer. It is a bound on the
    // count at entry, like any comparison the path makes with a constant.
    for (const auto &[c, cap] : countCap) {
      int id;
      if (auto it = entry.find(c); it != entry.end()) {
        id = it->second;
      } else {
        id = make();
        entry[c] = id;
        if (!cur.count(c))
          cur[c] = id;
      }
      if (!nodes[find(id)].ordBytes)
        nodes[find(id)].ordBytes = cap.bytes;
      hiU(id, cap.most);
    }
    for (const auto &kv : entry)
      mem[kv.first] = readNode(nodes, find, kv.second);
    for (Solved &s : solvedCells) {
      auto it = mem.find({s.arg, s.suf});
      if (it == mem.end()) {
        if (s.glob.empty())
          s.vals.clear();
        s.ban.clear();
        continue;
      }
      s.slo = it->second.slo;
      s.shi = it->second.shi;
      s.ulo = it->second.ulo;
      s.uhi = it->second.uhi;
      s.sloV = it->second.sloV;
      s.shiV = it->second.shiV;
      s.uloV = it->second.uloV;
      s.uhiV = it->second.uhiV;
      s.ordBytes = it->second.ordBytes;
      if (!s.glob.empty())
        continue;
      if (it->second.known) {
        s.vals = {it->second.val};
        s.ban.clear();
        s.text.clear();
      } else if (!it->second.any.empty()) {
        s.vals = it->second.any;
        s.ban = it->second.ban;
        s.text.clear();
      } else {
        s.vals.clear();
        s.ban = it->second.ban;
      }
    }
    auto bounded = [](const SlotVal &s) { return s.slo || s.shi || s.ulo || s.uhi || s.oneBits || s.zeroBits; };
    auto writeOrd = [&](const SlotVal &s) {
      if (s.slo)
        out << " sge " << s.sloV;
      if (s.shi)
        out << " sle " << s.shiV;
      if (s.ulo)
        out << " uge " << s.uloV;
      if (s.uhi)
        out << " ule " << s.uhiV;
      if (s.oneBits)
        out << " has " << s.oneBits;
      if (s.zeroBits)
        out << " lacks " << s.zeroBits;
    };
    auto inRel = [&](const Cell &c) {
      for (const Rel &r : rels)
        if ((r.a == c.first && r.asuf == c.second) || (r.b == c.first && r.bsuf == c.second))
          return true;
      return false;
    };
    for (const auto &kv : mem) {
      if (!kv.second.known && kv.second.any.empty() && kv.second.ban.empty() && !bounded(kv.second))
        continue;
      out << "model";
      writeCell(kv.first);
      if (kv.second.known) {
        out << " = " << kv.second.val;
      } else if (!kv.second.any.empty()) {
        out << " =";
        for (const std::string &v : kv.second.any)
          out << " " << v;
      }
      if (!kv.second.ban.empty() && !kv.second.known) {
        out << " !=";
        for (const std::string &v : kv.second.ban)
          out << " " << v;
      }
      writeOrd(kv.second);
      out << "\n";
    }
    for (const auto &c : cells) {
      auto it = mem.find(c);
      if (it != mem.end() && (it->second.known || !it->second.any.empty() || !it->second.ban.empty() || bounded(it->second)))
        continue;
      if (inRel(c))
        continue;
      out << "model";
      writeCell(c);
      out << " unknown\n";
    }
    // A library cell still in the entry formula is defined, when it is, by an
    // earlier interface call. The call that stores it under a switch on one
    // of its integer arguments has that argument as the tag and, when the
    // stored bits are the caller's variadic value, that value as the client
    // atom. The cell is then the image of those arguments, not an obligation
    // the client writes by hand.
    if (!tr.conflict) {
      auto oneFormal = [&](Value *V) -> Argument * {
        std::vector<Value *> st{V};
        std::unordered_set<const Value *> seen;
        std::unordered_set<Argument *> args;
        while (!st.empty()) {
          Value *X = st.back();
          st.pop_back();
          if (!X || !seen.insert(X).second)
            continue;
          if (auto *A = dyn_cast<Argument>(X->stripPointerCasts())) {
            args.insert(A);
            continue;
          }
          if (auto *C = dyn_cast<CastInst>(X)) {
            st.push_back(C->getOperand(0));
            continue;
          }
          if (auto *P = dyn_cast<PHINode>(X)) {
            for (Value *in : P->incoming_values())
              st.push_back(in);
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(X)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (!Al)
              continue;
            for (User *U : Al->users()) {
              auto *S = dyn_cast<StoreInst>(U);
              if (S && S->getPointerOperand()->stripPointerCasts() == Al)
                st.push_back(S->getValueOperand());
            }
            continue;
          }
          if (auto *G = dyn_cast<GEPOperator>(X))
            st.push_back(G->getPointerOperand());
        }
        return args.size() == 1 ? *args.begin() : nullptr;
      };
      auto viaVa = [](Value *V) {
        std::vector<Value *> st{V};
        std::unordered_set<const Value *> seen;
        while (!st.empty()) {
          Value *X = st.back();
          st.pop_back();
          if (!X || !seen.insert(X).second)
            continue;
          if (auto *C = dyn_cast<CastInst>(X)) {
            st.push_back(C->getOperand(0));
            continue;
          }
          if (auto *P = dyn_cast<PHINode>(X)) {
            for (Value *in : P->incoming_values())
              st.push_back(in);
            continue;
          }
          if (auto *L = dyn_cast<LoadInst>(X)) {
            auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            if (Al) {
              for (User *U : Al->users()) {
                auto *St = dyn_cast<StoreInst>(U);
                if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                  st.push_back(St->getValueOperand());
              }
              continue;
            }
            st.push_back(L->getPointerOperand());
            continue;
          }
          if (auto *A = dyn_cast<AllocaInst>(X)) {
            for (User *U : A->users()) {
              auto *St = dyn_cast<StoreInst>(U);
              if (St && St->getPointerOperand()->stripPointerCasts() == A)
                st.push_back(St->getValueOperand());
            }
            continue;
          }
          if (auto *G = dyn_cast<GEPOperator>(X)) {
            std::string ty;
            raw_string_ostream os(ty);
            G->getSourceElementType()->print(os);
            if (ty.find("va_list") != std::string::npos)
              return true;
            st.push_back(G->getPointerOperand());
          }
        }
        return false;
      };
      auto callsFn = [&](CallBase *CB, Function *callee) {
        if (Function *C = CB->getCalledFunction()) {
          if (Function *D = define(C->getName()))
            C = D;
          return C == callee;
        }
        for (Function *T : targetsOf(CB))
          if (T == callee)
            return true;
        return false;
      };
      auto liftArg = [&](Function *caller, Function *callee, Argument *a) -> Argument * {
        if (!a)
          return nullptr;
        for (Instruction &I : instructions(*caller)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || a->getArgNo() >= CB->arg_size() || !callsFn(CB, callee))
            continue;
          Argument *up = oneFormal(CB->getArgOperand(a->getArgNo()));
          if (up && up->getParent() == caller)
            return up;
        }
        return nullptr;
      };
      for (const auto &kv : mem) {
        const SlotVal &fact = kv.second;
        if (inRel(kv.first))
          continue;
        if (!fact.known && fact.any.empty() && fact.ban.empty() && !bounded(fact))
          continue;
        const Cell &want = kv.first;
        if (want.second.empty())
          continue;
        const Step &last = want.second.back();
        auto fits = [&](const ConstantInt *CI) {
          if (CI->getBitWidth() > 64)
            return false;
          std::string d = dec(CI);
          if (fact.known && fact.val != d)
            return false;
          if (!fact.any.empty() && !fact.any.count(d))
            return false;
          if (fact.ban.count(d))
            return false;
          int64_t v = CI->getSExtValue();
          uint64_t u = CI->getZExtValue();
          if (fact.slo && v < fact.sloV)
            return false;
          if (fact.shi && v > fact.shiV)
            return false;
          if (fact.ulo && u < fact.uloV)
            return false;
          if (fact.uhi && u > fact.uhiV)
            return false;
          if ((u & fact.oneBits) != fact.oneBits || (u & fact.zeroBits))
            return false;
          return true;
        };
        bool done = false;
        int nOff = 0, nVal = 0, nObj = 0, nSw = 0, nClimb = 0;
        std::string climbFn;
        eachBody([&](Function &F) {
          if (done)
            return;
          std::optional<DominatorTree> DT;
          auto domRets = [&](Instruction *S) {
            if (!DT)
              DT.emplace(F);
            bool any = false;
            for (BasicBlock &BB : F) {
              auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
              if (!R)
                continue;
              any = true;
              if (!DT->dominates(S, R))
                return false;
            }
            return any;
          };
          for (Instruction &I : instructions(F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || done)
              continue;
            auto *G = dyn_cast<GEPOperator>(S->getPointerOperand()->stripPointerCasts());
            if (!G || !G->hasAllConstantIndices())
              continue;
            APInt off(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->accumulateConstantOffset(dl, off) || off.getSExtValue() != last.off)
              continue;
            std::string irTy;
            if (auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
              if (ST->hasName())
                irTy = ST->getName().str();
            if (source::container(G, dl) != last.type && irTy != last.type)
              continue;
            ++nOff;
            auto *CI = dyn_cast<ConstantInt>(S->getValueOperand());
            bool isNull = isa<ConstantPointerNull>(S->getValueOperand()->stripPointerCasts());
            bool va = !CI && !isNull && viaVa(S->getValueOperand());
            if (CI) {
              if (!fits(CI))
                continue;
            } else if (isNull) {
              if (fact.known && fact.val != "0")
                continue;
              if (!fact.any.empty() && !fact.any.count("0"))
                continue;
              if (fact.ban.count("0"))
                continue;
            } else if (!va) {
              continue;
            }
            ++nVal;
            Argument *obj = oneFormal(S->getPointerOperand());
            if (!obj || obj->getParent() != &F)
              continue;
            std::string outer;
            {
              std::vector<Value *> ost{S->getPointerOperand()};
              std::unordered_set<const Value *> oseen;
              while (!ost.empty()) {
                Value *X = ost.back();
                ost.pop_back();
                if (!X || !oseen.insert(X).second)
                  continue;
                if (isa<Argument>(X->stripPointerCasts()))
                  continue;
                if (auto *C = dyn_cast<CastInst>(X)) {
                  ost.push_back(C->getOperand(0));
                  continue;
                }
                if (auto *P = dyn_cast<PHINode>(X)) {
                  for (Value *in : P->incoming_values())
                    ost.push_back(in);
                  continue;
                }
                if (auto *L = dyn_cast<LoadInst>(X)) {
                  auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
                  if (Al) {
                    for (User *U : Al->users()) {
                      auto *St = dyn_cast<StoreInst>(U);
                      if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                        ost.push_back(St->getValueOperand());
                    }
                    continue;
                  }
                  ost.push_back(L->getPointerOperand());
                  continue;
                }
                if (auto *GG = dyn_cast<GEPOperator>(X)) {
                  if (auto *ST = dyn_cast<StructType>(GG->getSourceElementType()))
                    if (ST->hasName())
                      outer = ST->getName().str();
                  ost.push_back(GG->getPointerOperand());
                }
              }
            }
            if (outer != want.second.front().type)
              continue;
            ++nObj;
            std::unordered_set<const BasicBlock *> reach{S->getParent()};
            std::unordered_map<const BasicBlock *, int> dist;
            std::vector<const BasicBlock *> st{S->getParent()};
            dist[S->getParent()] = 0;
            while (!st.empty()) {
              const BasicBlock *BB = st.back();
              st.pop_back();
              int d = dist[BB];
              for (const BasicBlock *P : predecessors(BB))
                if (reach.insert(P).second) {
                  dist[P] = d + 1;
                  st.push_back(P);
                }
            }
            Argument *tag = nullptr;
            int64_t tagV = 0;
            int bestDist = 0;
            for (const BasicBlock *BB : reach) {
              auto *Sw = dyn_cast<SwitchInst>(BB->getTerminator());
              if (!Sw || reach.count(Sw->getDefaultDest()))
                continue;
              int hits = 0;
              int64_t one = 0;
              for (auto &C : Sw->cases()) {
                if (!reach.count(C.getCaseSuccessor()))
                  continue;
                if (C.getCaseValue()->getBitWidth() > 64)
                  continue;
                ++hits;
                one = C.getCaseValue()->getSExtValue();
              }
              if (hits != 1)
                continue;
              Argument *A = oneFormal(Sw->getCondition());
              if (!A || A->getParent() != &F)
                continue;
              int d = dist[BB];
              if (tag && d >= bestDist)
                continue;
              tag = A;
              tagV = one;
              bestDist = d;
            }
            if (!tag && !domRets(S))
              continue;
            ++nSw;
            struct Node {
              Function *f;
              Argument *obj;
              Argument *tag;
            };
            std::queue<Node> q;
            std::unordered_set<Function *> seenFn;
            q.push({&F, obj, tag});
            Function *iface = nullptr;
            Argument *ifaceObj = nullptr;
            Argument *ifaceTag = nullptr;
            while (!q.empty() && !iface) {
              Node n = q.front();
              q.pop();
              if (!seenFn.insert(n.f).second)
                continue;
              bool face = interfaceNames.count(n.f->getName().str()) != 0;
              if (face && n.obj && (unsigned)want.first == n.obj->getArgNo() && (!va || n.f->isVarArg())) {
                iface = n.f;
                ifaceObj = n.obj;
                ifaceTag = n.tag;
                break;
              }
              auto it = callersOf.find(n.f);
              if (it == callersOf.end())
                continue;
              for (Function *C : it->second) {
                Argument *upObj = liftArg(C, n.f, n.obj);
                if (!upObj)
                  continue;
                Argument *upTag = n.tag ? liftArg(C, n.f, n.tag) : nullptr;
                if (n.tag && !upTag)
                  continue;
                q.push({C, upObj, upTag});
              }
            }
            if (!iface) {
              ++nClimb;
              climbFn = F.getName().str();
              continue;
            }
            out << "client " << iface->getName() << " arg" << ifaceObj->getArgNo();
            if (ifaceTag)
              out << " arg" << ifaceTag->getArgNo() << " = " << tagV;
            if (va) {
              if (fact.known)
                out << " vararg = " << fact.val;
              else {
                for (const std::string &b : fact.ban)
                  out << " vararg != " << b;
                for (const std::string &a : fact.any)
                  out << " vararg any " << a;
                if (fact.slo)
                  out << " vararg sge " << fact.sloV;
                if (fact.shi)
                  out << " vararg sle " << fact.shiV;
                if (fact.ulo)
                  out << " vararg uge " << fact.uloV;
                if (fact.uhi)
                  out << " vararg ule " << fact.uhiV;
                if (fact.oneBits)
                  out << " vararg has " << fact.oneBits;
                if (fact.zeroBits)
                  out << " vararg lacks " << fact.zeroBits;
              }
            }
            out << "\n";
            out << "discharges";
            writeCell(want);
            out << "\n";
            done = true;
          }
        });
        auto baseOf = [&](Value *V) -> Value * {
          std::vector<Value *> st{V};
          std::unordered_set<const Value *> seen;
          Value *found = nullptr;
          while (!st.empty()) {
            Value *X = st.back();
            st.pop_back();
            if (!X || !seen.insert(X).second)
              continue;
            if (isa<ConstantPointerNull>(X) || isa<UndefValue>(X))
              continue;
            Value *S = X->stripPointerCasts();
            if (isa<Argument>(S) || isa<GlobalValue>(S) || isa<CallBase>(X)) {
              Value *Id = isa<CallBase>(X) ? X : S;
              if (found && found != Id)
                return nullptr;
              found = Id;
              continue;
            }
            if (auto *C = dyn_cast<CastInst>(X)) {
              st.push_back(C->getOperand(0));
              continue;
            }
            if (auto *P = dyn_cast<PHINode>(X)) {
              for (Value *in : P->incoming_values())
                st.push_back(in);
              continue;
            }
            if (auto *L = dyn_cast<LoadInst>(X)) {
              auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (Al) {
                for (User *U : Al->users()) {
                  auto *St = dyn_cast<StoreInst>(U);
                  if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                    st.push_back(St->getValueOperand());
                }
                continue;
              }
              st.push_back(L->getPointerOperand());
              continue;
            }
            if (auto *G = dyn_cast<GEPOperator>(X))
              st.push_back(G->getPointerOperand());
          }
          return found;
        };
        int64_t absOff = 0;
        bool inlineField = true;
        for (const Step &s : want.second) {
          if (s.deref) {
            inlineField = false;
            break;
          }
          absOff += s.off;
        }
        bool zeroOk = inlineField && fact.ban.count("0") == 0 && (!fact.known || fact.val == "0") &&
                      (fact.any.empty() || fact.any.count("0")) && !(fact.slo && fact.sloV > 0) &&
                      !(fact.shi && fact.shiV < 0) && !(fact.ulo && fact.uloV > 0) &&
                      (fact.known || !fact.any.empty() || !fact.ban.empty() || bounded(fact));
        int nMem = 0, nSize = 0, nRoot = 0, nRet = 0, nWrite = 0, nFace = 0;
        std::string wrote;
        if (!done && zeroOk) {
          eachBody([&](Function &F) {
            if (done)
              return;
            for (Instruction &I : instructions(F)) {
              auto *CB = dyn_cast<CallBase>(&I);
              if (!CB || done)
                continue;
              Function *Cal = CB->getCalledFunction();
              if (!Cal || Cal->getName().find("memset") == StringRef::npos)
                continue;
              if (CB->arg_size() < 3)
                continue;
              ++nMem;
              Value *dest = CB->getArgOperand(0);
              auto *zero = dyn_cast<ConstantInt>(CB->getArgOperand(1));
              auto *len = dyn_cast<ConstantInt>(CB->getArgOperand(2));
              if (!zero || !len || !zero->isZero() || len->getBitWidth() > 64)
                continue;
              if (len->getZExtValue() < (uint64_t)absOff + 1)
                continue;
              ++nSize;
              Value *obj = baseOf(dest);
              if (!obj)
                continue;
              auto *alloc = dyn_cast<CallBase>(obj);
              if (!alloc)
                continue;
              ++nRoot;
              DominatorTree DT(F);
              bool anyRet = false;
              bool covered = true;
              for (BasicBlock &BB : F) {
                auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
                if (!R || !R->getReturnValue())
                  continue;
                Value *RV = R->getReturnValue();
                if (baseOf(RV) != obj)
                  continue;
                auto *Ld = dyn_cast<LoadInst>(RV->stripPointerCasts());
                auto *Slot = Ld ? dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts()) : nullptr;
                if (!Slot) {
                  anyRet = true;
                  if (!DT.dominates(CB, R))
                    covered = false;
                  continue;
                }
                for (User *U : Slot->users()) {
                  auto *St = dyn_cast<StoreInst>(U);
                  if (!St || St->getPointerOperand()->stripPointerCasts() != Slot)
                    continue;
                  if (isa<ConstantPointerNull>(St->getValueOperand()->stripPointerCasts()))
                    continue;
                  if (baseOf(St->getValueOperand()) != obj)
                    continue;
                  anyRet = true;
                  if (!DT.dominates(CB, St))
                    covered = false;
                }
              }
              if (!anyRet || !covered)
                continue;
              ++nRet;
              std::unordered_set<Function *> visiting;
              std::function<bool(Function *)> writes = [&](Function *G) {
                if (!visiting.insert(G).second)
                  return false;
                for (Instruction &J : instructions(*G)) {
                  if (auto *S = dyn_cast<StoreInst>(&J)) {
                    auto *GG = dyn_cast<GEPOperator>(S->getPointerOperand()->stripPointerCasts());
                    if (!GG || !GG->hasAllConstantIndices())
                      continue;
                    APInt o(dl.getIndexSizeInBits(GG->getPointerAddressSpace()), 0);
                    if (!GG->accumulateConstantOffset(dl, o) || o.getSExtValue() != last.off)
                      continue;
                    std::string ty;
                    if (auto *ST = dyn_cast<StructType>(GG->getSourceElementType()))
                      if (ST->hasName())
                        ty = ST->getName().str();
                    if (source::container(GG, dl) == last.type || ty == last.type) {
                      Value *V = S->getValueOperand();
                      if (auto *C = dyn_cast<ConstantInt>(V))
                        if (C->isZero())
                          continue;
                      if (isa<ConstantPointerNull>(V->stripPointerCasts()))
                        continue;
                      wrote = G->getName().str();
                      return true;
                    }
                  }
                  auto *Call = dyn_cast<CallBase>(&J);
                  if (!Call || Call->getCalledFunction() == Cal)
                    continue;
                  if (Function *D = Call->getCalledFunction()) {
                    if (Function *Def = define(D->getName()))
                      D = Def;
                    if (D && !D->isDeclaration() && writes(D))
                      return true;
                  } else {
                    for (Value *A : Call->args())
                      if (baseOf(A) == obj) {
                        wrote = G->getName().str();
                        return true;
                      }
                  }
                }
                return false;
              };
              if (writes(&F)) {
                ++nWrite;
                continue;
              }
              std::queue<Function *> cq;
              std::unordered_set<Function *> cseen;
              cq.push(&F);
              Function *iface = nullptr;
              while (!cq.empty() && !iface) {
                Function *G = cq.front();
                cq.pop();
                if (!cseen.insert(G).second)
                  continue;
                if (interfaceNames.count(G->getName().str())) {
                  iface = G;
                  break;
                }
                auto it = callersOf.find(G);
                if (it == callersOf.end())
                  continue;
                for (Function *C : it->second) {
                  bool passes = false;
                  for (Instruction &J : instructions(*C)) {
                    auto *Call = dyn_cast<CallBase>(&J);
                    if (!Call || !callsFn(Call, G))
                      continue;
                    for (BasicBlock &BB : *C) {
                      auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
                      if (R && R->getReturnValue() && baseOf(R->getReturnValue()) == Call)
                        passes = true;
                    }
                  }
                  if (passes)
                    cq.push(C);
                }
              }
              if (!iface) {
                ++nFace;
                continue;
              }
              out << "client " << iface->getName() << " result arg" << want.first << "\n";
              out << "discharges";
              writeCell(want);
              out << "\n";
              done = true;
            }
          });
        }
        (void)nOff;
        (void)nVal;
        (void)nObj;
        (void)nSw;
        (void)nClimb;
        (void)climbFn;
        (void)nMem;
        (void)nSize;
        (void)nRoot;
        (void)nRet;
        (void)nWrite;
        (void)nFace;
        (void)wrote;
      }
    }
    out << (tr.conflict ? "unsat\n" : "sat\n");
    return !tr.conflict;
  