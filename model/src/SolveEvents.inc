
    solvedCells.clear();
    rels.clear();
    readBytes.clear();
    fileLen.clear();
    argFileLen.clear();
    argExtent.clear();
    pathSrc.clear();
    ptrSpan.clear();
    size_t residual = seq.size() - 1;
    std::vector<std::vector<std::optional<Loc>>> frames(seq.size());
    frames[0].resize(seq[0]->arg_size());
    for (unsigned i = 0; i < seq[0]->arg_size(); ++i)
      frames[0][i] = Loc{(int)i, {}};
    size_t mapped = 1;
    bool failed = false;
    std::set<int> files;
    std::map<Suffix, std::set<std::string>> need;
    std::map<std::pair<int, Suffix>, std::set<std::string>> keyCell;
    std::map<std::pair<int, Suffix>, std::set<std::string>> calleeAt;
    std::set<std::pair<int, Suffix>> indirectAt;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepEq;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepNe;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepStore;
    std::map<size_t, std::map<std::pair<int, Suffix>, std::set<std::string>>> stepEdge;
    struct Ev {
      Instruction *at = nullptr;
      Instruction *anchor = nullptr;
      Function *fn = nullptr;
      char kind = 0;
      bool callMust = true;
      bool mustExit = true;
      std::pair<int, Suffix> cell;
      std::pair<int, Suffix> src;
      std::set<std::string> vals;
      int pred = 0;
      unsigned bits = 0;
    };
    std::map<size_t, std::vector<Ev>> stepEv;
    std::unordered_map<const Function *, std::unique_ptr<DominatorTree>> dts;
    Instruction *evAnchor = nullptr;
    bool evCallMust = true;
    std::vector<Instruction *> stepGoal(seq.size(), nullptr);
    size_t curStep = 0;
    auto domTree = [&](Function *F) -> DominatorTree & {
      auto &p = dts[F];
      if (!p)
        p = std::make_unique<DominatorTree>(*F);
      return *p;
    };
    auto dominatesBefore = [&](Instruction *I, Instruction *G) {
      if (!I || !G || I->getFunction() != G->getFunction())
        return false;
      if (I == G)
        return true;
      DominatorTree &DT = domTree(I->getFunction());
      if (!DT.dominates(I->getParent(), G->getParent()))
        return false;
      if (I->getParent() != G->getParent())
        return true;
      for (Instruction &J : *I->getParent()) {
        if (&J == G)
          return false;
        if (&J == I)
          return true;
      }
      return false;
    };
    auto dominatesReturns = [&](Instruction *I) {
      if (!I)
        return false;
      bool any = false;
      for (BasicBlock &BB : *I->getFunction()) {
        auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
        if (!R)
          continue;
        any = true;
        if (!dominatesBefore(I, R))
          return false;
      }
      return any;
    };
    std::vector<std::vector<Act>> atAct(seq.size());
    std::unordered_map<std::string, bool> sumCache;
    std::unordered_set<std::string> sumStack;

    for (size_t si = 0; si + 1 < seq.size(); ++si) {
      Function *F = seq[si];
      Function *Next = seq[si + 1];
      const std::vector<std::optional<Loc>> &at = frames[si];
      Mem m;
      bindFormals(m, F, at);
      propagate(m, F);
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        if (!noBody(CB))
          continue;
        Read rd = asRead(*CB);
        if (!rd.ok)
          continue;
        auto claim = [&](Value *V) {
          while (auto *Cast = dyn_cast<CastInst>(V))
            V = Cast->getOperand(0);
          if (auto *Open = dyn_cast<CallBase>(V)) {
            for (unsigned i = 0; i < Open->arg_size(); ++i) {
              Value *Op = Open->getArgOperand(i);
              if (!Op->getType()->isPointerTy())
                continue;
              Loc L;
              if (locOf(m, Op, L) && L.suf.empty()) {
                files.insert(L.arg);
                if (rd.len)
                  argFileLen[L.arg] = *rd.len;
              }
            }
            return;
          }
          Loc L;
          if (locOf(m, V, L) && L.suf.empty()) {
            files.insert(L.arg);
            if (rd.len)
              argFileLen[L.arg] = *rd.len;
          }
        };
        if (rd.file >= 0)
          claim(CB->getArgOperand((unsigned)rd.file));
        if (rd.handle >= 0)
          claim(CB->getArgOperand((unsigned)rd.handle));
      }
      CallBase *edge = nullptr;
      std::vector<std::optional<Loc>> nextArgs;
      std::vector<Act> nextActs;
      bool edgeLocated = false;
      bool edgeConcrete = false;
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto ts = targetsOf(CB);
        if (std::find(ts.begin(), ts.end(), Next) == ts.end())
          continue;
        if (!CB->getCalledFunction()) {
          Suffix s = suffix(CB->getCalledOperand());
          if (!s.empty())
            need[s].insert(Next->getName().str());
          Loc calleeLoc;
          if (locOf(m, CB->getCalledOperand(), calleeLoc) && !calleeLoc.suf.empty()) {
            calleeAt[{calleeLoc.arg, calleeLoc.suf}].insert(Next->getName().str());
            stepEdge[si][{calleeLoc.arg, calleeLoc.suf}].insert(Next->getName().str());
          }
          auto kit = regKeys.find(Next);
          if (kit != regKeys.end()) {
            std::vector<Value *> stack{CB->getCalledOperand()};
            std::unordered_set<Value *> seen;
            while (!stack.empty()) {
              Value *V = stack.back();
              stack.pop_back();
              if (!V || !seen.insert(V).second)
                continue;
              Loc L;
              if (locOf(m, V, L) && !L.suf.empty()) {
                keyCell[{L.arg, L.suf}].insert(kit->second.begin(), kit->second.end());
                if (kit->second.size() == 1)
                  stepEq[si][{L.arg, L.suf}].insert(*kit->second.begin());
                continue;
              }
              if (auto *C = dyn_cast<CastInst>(V)) {
                stack.push_back(C->getOperand(0));
                continue;
              }
              if (auto *P = dyn_cast<PHINode>(V)) {
                for (Value *in : P->incoming_values())
                  stack.push_back(in);
                continue;
              }
              if (auto *Ld = dyn_cast<LoadInst>(V)) {
                stack.push_back(Ld->getPointerOperand());
                continue;
              }
              if (auto *Call = dyn_cast<CallBase>(V))
                for (Value *Op : Call->args())
                  stack.push_back(Op);
            }
          }
        }
        std::vector<std::optional<Loc>> got;
        std::vector<Act> gotActs;
        bool any = false;
        bool concrete = true;
        for (Value *Op : CB->args()) {
          Act a;
          Value *bare = Op->stripPointerCasts();
          Loc L;
          if (auto *Fn = dyn_cast<Function>(bare)) {
            a.fn = Fn->getName().str();
            a.address = false;
            a.missing = false;
          } else if (auto *CI = dyn_cast<ConstantInt>(bare)) {
            if (CI->getBitWidth() <= 64) {
              a.haveInt = true;
              a.ival = CI->getSExtValue();
              a.ibits = CI->getBitWidth();
              a.address = false;
              a.missing = false;
            }
          } else if (isa<ConstantPointerNull>(bare)) {
            a.nullPtr = true;
            a.address = false;
            a.missing = false;
          } else if (locOf(m, Op, L)) {
            a.loc = L;
            auto *Ld = dyn_cast<LoadInst>(bare);
            a.address = !(Ld && Ld->getType()->isPointerTy());
            a.missing = false;
            any = true;
          }
          if (a.missing)
            concrete = false;
          got.push_back(a.loc);
          gotActs.push_back(std::move(a));
        }
        int rank = (concrete ? 2 : 0) + (any ? 1 : 0);
        int best = (edgeConcrete ? 2 : 0) + (edgeLocated ? 1 : 0);
        if (!edge || rank > best) {
          edge = CB;
          nextArgs = std::move(got);
          nextActs = std::move(gotActs);
          edgeLocated = any;
          edgeConcrete = concrete;
        }
        if (edgeConcrete && edgeLocated)
          break;
      }
      if (edge)
        stepGoal[si] = edge;
      // Fold only when the call into the next function passes cells or
      // constants and this function is a bundle of constant-offset stores.
      bool bundle = edge && edgeConcrete && summarizes(F, at, sumCache, sumStack, Next);
      if (!bundle && !failed) {
        residual = si;
        failed = true;
      }
      if (bundle && !failed) {
        out << "bundle " << F->getName() << " " << Next->getName() << "\n";
        residual = si + 1;
      }
      if (!edge)
        break;
      frames[si + 1].assign(Next->arg_size(), std::nullopt);
      for (size_t i = 0; i < nextArgs.size() && i < frames[si + 1].size(); ++i)
        frames[si + 1][i] = nextArgs[i];
      atAct[si + 1] = std::move(nextActs);
      if (atAct[si + 1].size() < Next->arg_size())
        atAct[si + 1].resize(Next->arg_size());
      mapped = si + 2;
    }
    entry = seq[residual];
    callActs.clear();
    if (residual == 0) {
      unsigned ai = 0;
      for (Argument &A : entry->args()) {
        Act a;
        if (A.getType()->isPointerTy()) {
          a.loc = Loc{(int)ai, {}};
          a.address = true;
          a.missing = false;
        } else if (A.getType()->isIntegerTy()) {
          a.address = false;
        } else {
          a.nullPtr = true;
          a.address = false;
          a.missing = false;
        }
        callActs.push_back(std::move(a));
        ++ai;
      }
    } else {
      callActs = atAct[residual];
      if (callActs.size() < entry->arg_size())
        callActs.resize(entry->arg_size());
    }
    if (residual < seq.size())
      out << "residual " << seq[residual]->getName() << " " << pretty(seq[residual]->getName()) << "\n";
    for (int a : files) {
      out << "file arg" << a;
      auto it = argFileLen.find(a);
      if (it != argFileLen.end())
        out << " " << it->second;
      out << "\n";
    }
    Mem top;
    bindFormals(top, seq[0], {});
    for (unsigned i = 0; i < seq[0]->arg_size(); ++i)
      top.loc[seq[0]->getArg(i)] = Loc{(int)i, {}};
    propagate(top, seq[0]);
    std::set<std::pair<int, Suffix>> cells;
    std::set<std::pair<int, Suffix>> pathCell;
    std::set<std::pair<int, Suffix>> ptrHold;
    std::set<std::pair<int, Suffix>> pathAt;
    std::set<std::pair<int, Suffix>> pathPtr;
    std::map<std::pair<int, Suffix>, unsigned> wide;
    std::map<std::pair<int, Suffix>, FunctionType *> fileCell;
    std::map<std::pair<int, Suffix>, std::set<std::string>> cmps;
    std::map<std::pair<int, Suffix>, std::set<std::string>> neq;
    std::map<std::pair<int, Suffix>, std::set<std::string>> seqStore;
    std::unordered_set<std::string> walked;
    std::function<void(Function *, const std::vector<std::optional<Loc>> &)> walk = [&](Function *F, const std::vector<std::optional<Loc>> &args) {
      Mem m;
      bindFormals(m, F, args);
      propagate(m, F);
      auto reach = sliceReach(F, seq);
      for (Instruction &I : instructions(*F)) {
        if (!reach.count(I.getParent()))
          continue;
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          Loc cell;
          if (locOf(m, S->getPointerOperand(), cell) && !cell.suf.empty()) {
            cells.insert({cell.arg, cell.suf});
            Ev ev;
            ev.at = S;
            ev.fn = F;
            ev.kind = 's';
            ev.cell = {cell.arg, cell.suf};
            if (auto *CI = dyn_cast<ConstantInt>(S->getValueOperand())) {
              seqStore[{cell.arg, cell.suf}].insert(dec(CI));
              stepStore[curStep][{cell.arg, cell.suf}].insert(dec(CI));
              ev.vals.insert(dec(CI));
              stepEv[curStep].push_back(std::move(ev));
            } else if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
              if (Function *D = define(Fn->getName()))
                Fn = D;
              if (!Fn->isDeclaration()) {
                stepStore[curStep][{cell.arg, cell.suf}].insert(Fn->getName().str());
                ev.vals.insert(Fn->getName().str());
                stepEv[curStep].push_back(std::move(ev));
              }
            } else if (auto *Ld = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts())) {
              Loc src;
              if (locOf(m, Ld->getPointerOperand(), src) && !src.suf.empty()) {
                cells.insert({src.arg, src.suf});
                ev.kind = 'c';
                ev.src = {src.arg, src.suf};
                stepEv[curStep].push_back(std::move(ev));
              }
            }
          }
        }
        if (auto *L = dyn_cast<LoadInst>(&I)) {
          Loc cell;
          if (locOf(m, L->getPointerOperand(), cell) && !cell.suf.empty() && cells.count({cell.arg, cell.suf}))
            wide[{cell.arg, cell.suf}] = (unsigned)dl.getTypeStoreSize(L->getType()).getFixedValue();
        }
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          Copy copied = fixedCopy(*CB);
          if (copied.ok && !CB->getType()->isIntegerTy() && copied.len > dl.getPointerSize(0) * 2) {
            Loc dst, src;
            if (locOf(m, CB->getArgOperand(copied.dst), dst) && locOf(m, CB->getArgOperand(copied.src), src) &&
                !dst.suf.empty() && !src.suf.empty()) {
              cells.insert({dst.arg, dst.suf});
              cells.insert({src.arg, src.suf});
              Ev ev;
              ev.at = CB;
              ev.fn = F;
              ev.kind = 'c';
              ev.cell = {dst.arg, dst.suf};
              ev.src = {src.arg, src.suf};
              stepEv[curStep].push_back(std::move(ev));
            }
          }
          Read rd = asRead(*CB);
          if (rd.ok && noBody(CB) && !CB->getCalledFunction()) {
            Loc cell;
            if (locOf(m, CB->getCalledOperand(), cell) && !cell.suf.empty() && cells.count({cell.arg, cell.suf})) {
              fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
              if (rd.len)
                fileLen[{cell.arg, cell.suf}] = *rd.len;
            }
          }
        }
      }
    };
    for (const auto &kv : keyCell)
      cells.insert(kv.first);
    for (const auto &kv : calleeAt)
      cells.insert(kv.first);
    std::vector<Mem> mems(seq.size());
    std::vector<char> memReady(seq.size(), 0);
    auto memAt = [&](size_t si) -> Mem & {
      if (!memReady[si]) {
        bindFormals(mems[si], seq[si], frames[si]);
        propagate(mems[si], seq[si]);
        memReady[si] = 1;
      }
      return mems[si];
    };
    std::set<std::pair<int, Suffix>> indexed;
    auto varIndex = [](Value *V) {
      std::unordered_set<const Value *> seen;
      while (V && seen.insert(V).second) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        auto *G = dyn_cast<GEPOperator>(V);
        if (!G) {
          if (auto *L = dyn_cast<LoadInst>(V)) {
            V = L->getPointerOperand();
            continue;
          }
          break;
        }
        if (!G->hasAllConstantIndices() && !isa<StructType>(G->getSourceElementType()))
          return true;
        V = G->getPointerOperand();
      }
      return false;
    };
    std::vector<std::unordered_set<const Value *>> seen(seq.size());
    std::function<void(size_t, Value *)> trace = [&](size_t si, Value *V) {
      if (!V || si >= seq.size() || !seen[si].insert(V).second)
        return;
      if (auto *G = dyn_cast<GEPOperator>(V))
        for (Value *Idx : G->indices())
          if (!isa<Constant>(Idx))
            trace(si, Idx);
      Loc cell;
      if (cellLoc(memAt(si), V, cell) && !cell.suf.empty()) {
        cells.insert({cell.arg, cell.suf});
        if (varIndex(V))
          indexed.insert({cell.arg, cell.suf});
        return;
      }
      if (auto *C = dyn_cast<CastInst>(V)) {
        trace(si, C->getOperand(0));
        return;
      }
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        trace(si, G->getPointerOperand());
        return;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        trace(si, L->getPointerOperand());
        return;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        for (Value *in : P->incoming_values())
          trace(si, in);
        return;
      }
      if (auto *A = dyn_cast<Argument>(V)) {
        unsigned ai = A->getArgNo();
        if (ai < frames[si].size() && frames[si][ai] && !frames[si][ai]->suf.empty()) {
          cells.insert({frames[si][ai]->arg, frames[si][ai]->suf});
          if (varIndex(V))
            indexed.insert({frames[si][ai]->arg, frames[si][ai]->suf});
          return;
        }
        if (si == 0)
          return;
        for (Instruction &I : instructions(*seq[si - 1])) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          auto ts = targetsOf(CB);
          if (std::find(ts.begin(), ts.end(), seq[si]) == ts.end())
            continue;
          if (ai < CB->arg_size())
            trace(si - 1, CB->getArgOperand(ai));
        }
        return;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        if (noBody(CB)) {
          Read rd = asRead(*CB);
          if (rd.ok && rd.file >= 0) {
            Loc L;
            if (cellLoc(memAt(si), CB->getArgOperand((unsigned)rd.file), L) && L.suf.empty())
              files.insert(L.arg);
          }
        }
        Function *C = CB->getCalledFunction();
        if (C) {
          if (Function *D = define(C->getName())) {
            auto a = carryArg(D);
            if (a && *a >= 0 && *a < (int)CB->arg_size())
              trace(si, CB->getArgOperand((unsigned)*a));
          }
        }
        for (Value *Op : CB->args())
          if (Op->getType()->isPointerTy())
            trace(si, Op);
      }
    };
    for (size_t si = 0; si < seq.size(); ++si) {
      bool hasSink = false;
      for (Instruction &I : instructions(*seq[si]))
        if (sinkHere(I, sinkFile, sinkLine))
          hasSink = true;
      if (!hasSink)
        continue;
      for (Instruction &I : instructions(*seq[si])) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        for (Value *Op : I.operands())
          trace(si, Op);
      }
    }
    // The sink address may be a buffer filled by a read on the sequence.
    // That read's bytes are this cell. The file argument, or the callee of
    // an indirect read, is the input.
    std::set<std::pair<size_t, const Value *>> bufs;
    std::vector<std::unordered_set<const Value *>> bufSeen(seq.size());
    auto putCell = [&](int arg, Suffix suf, const std::vector<Step> &towardUse, Value *from) {
      suf.insert(suf.end(), towardUse.begin(), towardUse.end());
      if (suf.empty())
        return;
      cells.insert({arg, suf});
      if (varIndex(from))
        indexed.insert({arg, suf});
    };
    bool holdPtr = false;
    std::function<void(size_t, Value *, std::vector<Step>)> buffers =
        [&](size_t si, Value *V, std::vector<Step> towardUse) {
          if (!V || si >= seq.size() || !bufSeen[si].insert(V).second)
            return;
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *G = dyn_cast<GEPOperator>(V)) {
            Loc cell;
            if (cellLoc(memAt(si), V, cell) && !cell.suf.empty()) {
              if (holdPtr)
                ptrHold.insert({cell.arg, cell.suf});
              putCell(cell.arg, cell.suf, towardUse, V);
              return;
            }
            std::vector<Step> next = towardUse;
            if (G->hasAllConstantIndices()) {
              Step st;
              if (constStep(dl, G, st) && movesAddress(st))
                next.insert(next.begin(), st);
            } else if (isa<StructType>(G->getSourceElementType())) {
              return;
            }
            buffers(si, G->getPointerOperand(), next);
            return;
          }
          if (auto *L = dyn_cast<LoadInst>(V)) {
            std::vector<Step> next = towardUse;
            if (L->getType()->isPointerTy() && !next.empty())
              next[0].deref = true;
            Loc cell;
            if (cellLoc(memAt(si), L->getPointerOperand(), cell) && !cell.suf.empty()) {
              if (L->getType()->isPointerTy() && next.empty())
                ptrHold.insert({cell.arg, cell.suf});
              putCell(cell.arg, cell.suf, next, V);
              return;
            }
            bool prevHold = holdPtr;
            if (L->getType()->isPointerTy() && next.empty())
              holdPtr = true;
            buffers(si, L->getPointerOperand(), next);
            holdPtr = prevHold;
            return;
          }
          if (auto *P = dyn_cast<PHINode>(V)) {
            for (Value *in : P->incoming_values())
              buffers(si, in, towardUse);
            return;
          }
          if (auto *Al = dyn_cast<AllocaInst>(V)) {
            bufs.insert({si, Al});
            bool stored = false;
            for (Instruction &SI : instructions(*seq[si])) {
              auto *S = dyn_cast<StoreInst>(&SI);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              Value *sv = S->getValueOperand();
              if (isa<ConstantPointerNull>(sv) || isa<UndefValue>(sv))
                continue;
              stored = true;
              buffers(si, sv, towardUse);
            }
            if (stored)
              return;
            // The call wrote the object through this pointer. The object's
            // bytes are the call's other pointer arguments, at their own address.
            for (Instruction &SI : instructions(*seq[si])) {
              auto *CB = dyn_cast<CallBase>(&SI);
              if (!CB)
                continue;
              bool outp = false;
              for (Value *Op : CB->args())
                if (Op->stripPointerCasts() == Al)
                  outp = true;
              if (!outp)
                continue;
              for (Value *Op : CB->args()) {
                if (!Op->getType()->isPointerTy() || Op->stripPointerCasts() == Al)
                  continue;
                buffers(si, Op, {});
              }
            }
            return;
          }
          if (auto *A = dyn_cast<Argument>(V)) {
            bufs.insert({si, A});
            if (si == 0) {
              putCell((int)A->getArgNo(), {}, towardUse, V);
              return;
            }
            if (A->getArgNo() < frames[si].size() && frames[si][A->getArgNo()]) {
              const Loc &base = *frames[si][A->getArgNo()];
              putCell(base.arg, base.suf, towardUse, V);
              return;
            }
            for (Instruction &I : instructions(*seq[si - 1])) {
              auto *CB = dyn_cast<CallBase>(&I);
              if (!CB)
                continue;
              auto ts = targetsOf(CB);
              if (std::find(ts.begin(), ts.end(), seq[si]) == ts.end())
                continue;
              if (A->getArgNo() < CB->arg_size())
                buffers(si - 1, CB->getArgOperand(A->getArgNo()), towardUse);
            }
            return;
          }
          if (auto *CB = dyn_cast<CallBase>(V)) {
            for (Value *Op : CB->args())
              if (Op->getType()->isPointerTy())
                buffers(si, Op, {});
            return;
          }
          bufs.insert({si, V});
        };
    for (size_t si = 0; si < seq.size(); ++si) {
      for (Instruction &I : instructions(*seq[si])) {
        if (!sinkHere(I, sinkFile, sinkLine))
          continue;
        for (Value *Op : I.operands())
          buffers(si, Op, {});
      }
    }
    auto bare = [](Value *V) {
      while (V) {
        if (auto *C = dyn_cast<CastInst>(V)) {
          V = C->getOperand(0);
          continue;
        }
        auto *G = dyn_cast<GEPOperator>(V);
        if (!G)
          break;
        V = G->getPointerOperand();
      }
      return V;
    };
    for (size_t si = 0; si < seq.size(); ++si) {
      for (Instruction &I : instructions(*seq[si])) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto hit = [&](unsigned arg) {
          if (arg >= CB->arg_size() || !CB->getArgOperand(arg)->getType()->isPointerTy())
            return false;
          const Value *B = bare(CB->getArgOperand(arg));
          return B && bufs.count({si, B});
        };
        Copy copied = fixedCopy(*CB);
        if (copied.ok) {
          if (hit(copied.dst))
            buffers(si, CB->getArgOperand(copied.src), {});
          continue;
        }
        if (!noBody(CB))
          continue;
        Read rd = asRead(*CB);
        if (!rd.ok || !hit(rd.buf))
          continue;
        auto keepLen = [&](const std::pair<int, Suffix> &key) {
          if (!rd.len)
            return;
          auto it = fileLen.find(key);
          if (it != fileLen.end() && it->second != *rd.len)
            fileLen.erase(it);
          else
            fileLen[key] = *rd.len;
        };
        if (!CB->getCalledFunction()) {
          Loc cell;
          if (!cellLoc(memAt(si), CB->getCalledOperand(), cell) || cell.suf.empty())
            continue;
          cells.insert({cell.arg, cell.suf});
          fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
          keepLen({cell.arg, cell.suf});
          continue;
        }
        if (rd.file >= 0) {
          Loc L;
          if (cellLoc(memAt(si), CB->getArgOperand((unsigned)rd.file), L)) {
            if (L.suf.empty()) {
              files.insert(L.arg);
              if (rd.len)
                argFileLen[L.arg] = *rd.len;
            } else {
              cells.insert({L.arg, L.suf});
              keepLen({L.arg, L.suf});
            }
          }
        }
      }
    }
    // The path condition of this sequence. A branch outcome is required when
    // it is the only successor that reaches the next call, or the sink. The
    // equality of a constant-offset load and a constant is that cell's
    // equation. A direct callee reached with the export object contributes
    // the outcomes that are the only successor of a return. A pointer the
    // path dereferences is a cell; its pointee stays symbolic.
    {
      std::unordered_set<const Function *> didCallee;
      std::function<void(Function *, const std::vector<std::optional<Loc>> &, const std::unordered_set<Instruction *> &, bool, Function *)>
          pathFacts;
      pathFacts = [&](Function *F, const std::vector<std::optional<Loc>> &args, const std::unordered_set<Instruction *> &goals,
                      bool enterCallee, Function *reachTo) {
        if (!F || F->isDeclaration() || goals.empty())
          return;
        // The branch condition of one path, not the intersection of every
        // path that can still reach the goal.
        auto reach = chosenPath(F, goals);
        Mem m;
        bindFormals(m, F, args);
        propagateObject(m, F);
        auto locate = [&](Value *V, Loc &cell) -> bool {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(V);
          if (!L)
            return false;
          return objectLoc(m, L->getPointerOperand(), cell) && !cell.suf.empty();
        };
        auto keep = [&](const Loc &cell) { pathCell.insert({cell.arg, cell.suf}); cells.insert({cell.arg, cell.suf}); };
        Instruction *factAt = nullptr;
        Instruction *myAnchor = evAnchor;
        bool myMust = evCallMust;
        auto noteFact = [&](const Loc &cell, char kind, const std::string &v) {
          if (!factAt)
            return;
          Ev ev;
          ev.at = factAt;
          ev.fn = F;
          ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
          ev.callMust = myMust;
          ev.mustExit = F == seq[curStep] || dominatesReturns(factAt);
          ev.kind = kind;
          ev.cell = {cell.arg, cell.suf};
          ev.vals.insert(v);
          stepEv[curStep].push_back(std::move(ev));
        };
        auto equation = [&](const Loc &cell, std::string v) {
          keep(cell);
          noteFact(cell, 'e', v);
          stepEq[curStep][{cell.arg, cell.suf}].insert(v);
          cmps[{cell.arg, cell.suf}].insert(std::move(v));
        };
        auto pointee = [&](const Loc &cell) {
          auto it = cmps.find({cell.arg, cell.suf});
          if (it != cmps.end() && it->second.size() == 1 && it->second.count("0"))
            return;
          keep(cell);
          Loc child = cell;
          child.suf.push_back(Step{"", 0, true});
          keep(child);
        };
        auto onCmp = [&](ICmpInst *Cmp, ICmpInst::Predicate pred) {
          Value *lhs = Cmp->getOperand(0);
          Value *rhs = Cmp->getOperand(1);
          while (auto *C = dyn_cast<CastInst>(lhs))
            lhs = C->getOperand(0);
          while (auto *C = dyn_cast<CastInst>(rhs))
            rhs = C->getOperand(0);
          Loc L, R;
          bool lc = locate(lhs, L);
          bool rc = locate(rhs, R);
          Constant *CL = nullptr;
          Constant *CR = nullptr;
          if (isa<ConstantInt>(lhs) || isa<ConstantPointerNull>(lhs))
            CL = cast<Constant>(lhs);
          if (isa<ConstantInt>(rhs) || isa<ConstantPointerNull>(rhs))
            CR = cast<Constant>(rhs);
          unsigned bits = 64;
          if (auto *IT = dyn_cast<IntegerType>(Cmp->getOperand(0)->getType()))
            bits = IT->getBitWidth();
          auto push = [&](const Loc &cell, char kind, ICmpInst::Predicate p, const std::string &k, const Loc *other) {
            if (!factAt)
              return;
            keep(cell);
            if (other)
              keep(*other);
            Ev ev;
            ev.at = factAt;
            ev.fn = F;
            ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
            ev.callMust = myMust;
            ev.mustExit = F == seq[curStep] || dominatesReturns(factAt);
            ev.kind = kind;
            ev.pred = (int)p;
            ev.bits = bits;
            ev.cell = {cell.arg, cell.suf};
            if (other)
              ev.src = {other->arg, other->suf};
            else if (!k.empty())
              ev.vals.insert(k);
            stepEv[curStep].push_back(std::move(ev));
          };
          if (lc && rc && !CL && !CR) {
            push(L, 'p', pred, "", &R);
            return;
          }
          Loc cell;
          Constant *C = nullptr;
          ICmpInst::Predicate use = pred;
          if (CR && lc) {
            cell = L;
            C = CR;
          } else if (CL && rc) {
            cell = R;
            C = CL;
            use = ICmpInst::getSwappedPredicate(pred);
          } else
            return;
          if (isa<ConstantPointerNull>(C)) {
            if (use == ICmpInst::ICMP_EQ)
              equation(cell, "0");
            else if (use == ICmpInst::ICMP_NE)
              pointee(cell);
            else
              push(cell, 'r', use, "0", nullptr);
            return;
          }
          std::string k = dec(cast<ConstantInt>(C));
          if (use == ICmpInst::ICMP_EQ)
            equation(cell, k);
          else if (use == ICmpInst::ICMP_NE) {
            keep(cell);
            noteFact(cell, 'n', k);
            stepNe[curStep][{cell.arg, cell.suf}].insert(k);
            neq[{cell.arg, cell.suf}].insert(k);
          } else
            push(cell, 'r', use, k, nullptr);
        };
        for (const BasicBlock *CBB : reach) {
          BasicBlock *BB = const_cast<BasicBlock *>(CBB);
          Instruction *Term = BB->getTerminator();
          auto *BR = dyn_cast<BranchInst>(Term);
          if (BR && BR->isConditional()) {
            BasicBlock *only = nullptr;
            int n = 0;
            for (BasicBlock *S : successors(BR))
              if (reach.count(S)) {
                ++n;
                only = S;
              }
            if (n == 1) {
              factAt = BR;
              bool takenTrue = only == BR->getSuccessor(0);
              std::function<void(Value *, bool)> req = [&](Value *V, bool need) {
                while (auto *C = dyn_cast<CastInst>(V))
                  V = C->getOperand(0);
                if (auto *BO = dyn_cast<BinaryOperator>(V)) {
                  if (BO->getOpcode() == Instruction::Xor)
                    if (auto *One = dyn_cast<ConstantInt>(BO->getOperand(1)))
                      if (One->isOne()) {
                        req(BO->getOperand(0), !need);
                        return;
                      }
                  if (need && BO->getOpcode() == Instruction::And) {
                    req(BO->getOperand(0), true);
                    req(BO->getOperand(1), true);
                    return;
                  }
                  if (!need && BO->getOpcode() == Instruction::Or) {
                    req(BO->getOperand(0), false);
                    req(BO->getOperand(1), false);
                    return;
                  }
                }
                if (auto *Cmp = dyn_cast<ICmpInst>(V)) {
                  auto pred = Cmp->getPredicate();
                  if (!need)
                    pred = Cmp->getInversePredicate();
                  onCmp(Cmp, pred);
                }
              };
              req(BR->getCondition(), takenTrue);
            }
          }
          if (auto *SW = dyn_cast<SwitchInst>(Term)) {
            ConstantInt *onlyV = nullptr;
            int n = 0;
            bool def = reach.count(SW->getDefaultDest());
            if (def)
              ++n;
            for (auto &Case : SW->cases())
              if (reach.count(Case.getCaseSuccessor())) {
                ++n;
                onlyV = Case.getCaseValue();
              }
            Loc cell;
            if (n == 1 && onlyV && !def && locate(SW->getCondition(), cell)) {
              factAt = SW;
              equation(cell, dec(onlyV));
            }
          }
        }
        // An indirect call on the slice reads one cell. The value is the one
        // function that call can reach the next sequence function through.
        // A vtable call is the vtable, recorded where the object is loaded.
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB || CB->getCalledFunction() || !vtableTargets(CB).empty())
              continue;
            Loc cell;
            if (!cellLoc(m, CB->getCalledOperand(), cell) || cell.suf.empty())
              continue;
            keep(cell);
            indirectAt.insert({cell.arg, cell.suf});
            auto &slot = calleeAt[{cell.arg, cell.suf}];
            bool edge = false;
            std::vector<Function *> reachHits;
            for (Function *T : targetsOf(CB)) {
              if (!T || T->isDeclaration())
                continue;
              if (reachTo && T == reachTo)
                edge = true;
              else if (reachTo && reachesFn(T, reachTo))
                reachHits.push_back(T);
            }
            if (edge && reachTo)
              slot.insert(reachTo->getName().str());
            else if (!reachHits.empty()) {
              for (Function *T : reachHits)
                slot.insert(T->getName().str());
            }
            if (!slot.empty()) {
              stepEdge[curStep][{cell.arg, cell.suf}] = slot;
              Ev ev;
              ev.at = CB;
              ev.fn = F;
              ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
              ev.callMust = myMust;
              ev.mustExit = F == seq[curStep] || dominatesReturns(CB);
              ev.kind = 'g';
              ev.cell = {cell.arg, cell.suf};
              ev.vals = slot;
              stepEv[curStep].push_back(std::move(ev));
            }
          }
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *L = dyn_cast<LoadInst>(&I);
            if (!L || !L->getType()->isPointerTy())
              continue;
            auto asAddr = [](const User *U, const Value *P) {
              if (auto *Ld = dyn_cast<LoadInst>(U))
                return Ld->getPointerOperand() == P;
              if (auto *S = dyn_cast<StoreInst>(U))
                return S->getPointerOperand() == P;
              if (auto *G = dyn_cast<GetElementPtrInst>(U))
                return G->getPointerOperand() == P;
              return false;
            };
            bool used = false;
            bool passed = false;
            for (const User *U : L->users()) {
              if (asAddr(U, L))
                used = true;
              if (isa<CallBase>(U))
                passed = true;
              if (auto *C = dyn_cast<CastInst>(U))
                for (const User *U2 : C->users()) {
                  if (asAddr(U2, C))
                    used = true;
                  if (isa<CallBase>(U2))
                    passed = true;
                }
            }
            if (!used && !passed)
              continue;
            Loc cell;
            if (!cellLoc(m, L, cell) || cell.suf.empty())
              continue;
            std::unordered_set<const Function *> seenF;
            uint64_t n = pointedExtent(F, L, seenF, 0);
            if (!used && n == 0)
              continue;
            pointee(cell);
            if (n == 0)
              continue;
            Loc child = cell;
            child.suf.push_back(Step{"", 0, true});
            auto key = std::make_pair(child.arg, child.suf);
            auto it = readBytes.find(key);
            if (it == readBytes.end() || it->second < n)
              readBytes[key] = n;
          }
        if (!enterCallee)
          return;
        for (const BasicBlock *CBB : reach)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            if (!Cal || ignorable(Cal))
              continue;
            Function *D = define(Cal->getName());
            if (!D || D->isDeclaration())
              continue;
            std::vector<std::optional<Loc>> down;
            bool touch = false;
            for (Value *Op : CB->args()) {
              Loc L;
              if (objectLoc(m, Op, L)) {
                down.push_back(L);
                touch = true;
              } else
                down.push_back(std::nullopt);
            }
            if (!touch || !didCallee.insert(D).second)
              continue;
            std::unordered_set<Instruction *> rets;
            for (BasicBlock &RBB : *D)
              if (auto *R = dyn_cast<ReturnInst>(RBB.getTerminator()))
                rets.insert(R);
            Instruction *savedA = evAnchor;
            bool savedM = evCallMust;
            if (F == seq[curStep]) {
              evAnchor = CB;
              evCallMust = true;
            } else
              evCallMust = myMust && dominatesReturns(CB);
            pathFacts(D, down, rets, true, reachTo);
            evAnchor = savedA;
            evCallMust = savedM;
          }
      };
      for (size_t si = 0; si < mapped && si < seq.size(); ++si) {
        std::unordered_set<Instruction *> goals;
        if (si + 1 < seq.size())
          for (Instruction &I : instructions(*seq[si])) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            auto ts = targetsOf(CB);
            if (std::find(ts.begin(), ts.end(), seq[si + 1]) != ts.end())
              goals.insert(&I);
          }
        for (Instruction &I : instructions(*seq[si]))
          if (sinkHere(I, sinkFile, sinkLine))
            goals.insert(&I);
        curStep = si;
        evAnchor = nullptr;
        evCallMust = true;
        Function *reachTo = si + 1 < seq.size() ? seq[si + 1] : seq[si];
        pathFacts(seq[si], frames[si], goals, true, reachTo);
      }
    }
    for (size_t i = 0; i < mapped && i < seq.size(); ++i) {
      curStep = i;
      walk(seq[i], frames[i]);
    }
    std::set<std::string> demandedFn;
    for (const auto &kv : stepEdge)
      for (const auto &cell : kv.second)
        demandedFn.insert(cell.second.begin(), cell.second.end());
    std::unordered_map<const Function *, char> demandedReach;
    std::function<bool(Function *)> mayStoreDemanded = [&](Function *T) -> bool {
      if (!T)
        return false;
      if (Function *D = define(T->getName()))
        T = D;
      if (!T || T->isDeclaration())
        return false;
      if (auto it = demandedReach.find(T); it != demandedReach.end())
        return it->second == 2;
      demandedReach[T] = 1;
      bool yes = false;
      for (Instruction &I : instructions(*T)) {
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
            if (Function *D = define(Fn->getName()))
              Fn = D;
            if (demandedFn.count(Fn->getName().str()))
              yes = true;
          }
        }
        if (yes)
          break;
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          Function *C = CB->getCalledFunction();
          if (C) {
            if (Function *D = define(C->getName()))
              C = D;
            if (C && !C->isDeclaration() && mayStoreDemanded(C))
              yes = true;
          } else {
            for (Function *Tgt : targetsOf(CB))
              if (mayStoreDemanded(Tgt))
                yes = true;
          }
        }
      }
      demandedReach[T] = yes ? 2 : 0;
      return yes;
    };
    // A direct callee reached with the export object contributes its
    // constant stores. Its constant-offset reads set the object size.
    // A store through a loaded pointer writes the cell those bytes belong to.
    // The bundle still folds only constant-offset stores of the export object.
    // The callee walk follows the call graph to find the stores inside one
    // interface call. The graph has cycles; a function reached through a
    // pointer whose spelling grows each turn around a cycle keeps producing
    // a new `walked` signature, so signature dedup alone does not terminate.
    // A function already active on the current path is its own ancestor: it
    // is a recursive cycle, and re-entering walks the same body again, which
    // adds no store the acyclic visit did not already record. Cutting the
    // cycle leaves the walk acyclic over a finite graph, so it terminates.
    std::set<Function *> onPath;
    std::function<void(Function *, const std::vector<std::optional<Loc>> &, Instruction *, bool)> noteCallee =
        [&](Function *F, const std::vector<std::optional<Loc>> &args, Instruction *anchor, bool callMust) {
          if (!onPath.insert(F).second)
            return;
          struct PathGuard {
            std::set<Function *> &s;
            Function *f;
            ~PathGuard() { s.erase(f); }
          } pathGuard{onPath, F};
          Mem m;
          bindFormals(m, F, args);
          propagateObject(m, F);
          // Uses are located by cellLoc, so a store defines a use only when it
          // is named the same way. objectLoc drops the dereference mark a load
          // leaves, and the store then misses the cell the use named.
          auto located = [&](Value *Ptr, Loc &cell) {
            return cellLoc(m, Ptr, cell) && !cell.suf.empty();
          };
          auto sameBytes = [](const Suffix &a, const Suffix &b) {
            // An offset of zero does not move the address. A cast through an
            // empty prefix, or the first field of an embedded struct, is that
            // step. Its dereference belongs to the next byte offset.
            auto norm = [](Suffix in) {
              Suffix out;
              for (size_t i = 0; i < in.size(); ++i) {
                if (in[i].off == 0 && i + 1 < in.size()) {
                  in[i + 1].deref = in[i + 1].deref || in[i].deref;
                  continue;
                }
                out.push_back(in[i]);
              }
              return out;
            };
            Suffix x = norm(a), y = norm(b);
            if (x.size() != y.size())
              return false;
            for (size_t i = 0; i < x.size(); ++i) {
              if (x[i].off != y[i].off || x[i].deref != y[i].deref)
                return false;
              if (!x[i].deref && x[i].type != y[i].type)
                return false;
            }
            return true;
          };
          // A use recorded on this sequence demands v at cell. A store of v on
          // the call's return path defines that use, so the entry formula must
          // not keep it. The store is emitted on the use's own suffix.
          auto demandedAt = [&](const Loc &cell, const std::string &v, Loc &as) {
            for (size_t k = curStep; k < seq.size(); ++k) {
              for (const auto *tab : {&stepEq[k], &stepEdge[k]}) {
                for (const auto &kv : *tab) {
                  if (!kv.second.count(v) || kv.first.first != cell.arg || !sameBytes(kv.first.second, cell.suf))
                    continue;
                  as = cell;
                  as.suf = kv.first.second;
                  return true;
                }
              }
            }
            return false;
          };
          auto demanded = [&](const Loc &cell, const std::string &v) {
            Loc as;
            return demandedAt(cell, v, as);
          };
          auto wantStore = [&](const Loc &cell, const std::set<std::string> &vals, Loc &as) {
            if (F == seq[curStep])
              return false;
            for (const std::string &v : vals)
              if (demandedAt(cell, v, as))
                return true;
            return false;
          };
          auto grow = [&](Value *Ptr, uint64_t n) {
            Loc cell;
            if (!located(Ptr, cell) || n == 0)
              return;
            auto it = readBytes.find({cell.arg, cell.suf});
            if (it == readBytes.end() || it->second < n)
              readBytes[{cell.arg, cell.suf}] = n;
            if (cell.suf.size() == 1) {
              uint64_t end = (uint64_t)cell.suf[0].off + n;
              auto at = argExtent.find(cell.arg);
              if (at == argExtent.end() || at->second < end)
                argExtent[cell.arg] = end;
            }
          };
          // A sequence function is cut at the next call. A callee returns to
          // that path, so every block that reaches a return can run before
          // the caller continues. The shortest path to a return is often the
          // error return, which is not the path that stores the demanded value.
          auto reach = sliceReach(F, seq);
          if (F != seq[curStep]) {
            std::unordered_set<const BasicBlock *> back;
            std::vector<const BasicBlock *> st;
            for (BasicBlock &BB : *F)
              if (isa<ReturnInst>(BB.getTerminator()))
                st.push_back(&BB);
            while (!st.empty()) {
              const BasicBlock *BB = st.back();
              st.pop_back();
              if (!BB || !back.insert(BB).second)
                continue;
              for (const BasicBlock *P : predecessors(BB))
                st.push_back(P);
            }
            if (!back.empty())
              reach = std::move(back);
          }
          // An allocated object published into a cell carries the constant
          // and function stores of its fields. The first field step is a
          // dereference: the cell holds the pointer, the field is in the
          // object.
          std::unordered_map<const Value *, const Value *> rootOf;
          struct Graft {
            Suffix steps;
            std::set<std::string> vals;
          };
          std::unordered_map<const Value *, std::vector<Graft>> fields;
          std::unordered_map<const Value *, Loc> published;
          auto peel = [](Value *V) {
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            return V;
          };
          auto asRoot = [&](Value *V) -> const Value * {
            V = peel(V);
            if (auto it = rootOf.find(V); it != rootOf.end())
              return it->second;
            if (auto *L = dyn_cast<LoadInst>(V)) {
              if (auto *A = dyn_cast<AllocaInst>(peel(L->getPointerOperand())))
                if (auto it = rootOf.find(A); it != rootOf.end())
                  return it->second;
            }
            if (auto *CB = dyn_cast<CallBase>(V))
              if (CB->getType()->isPointerTy())
                return CB;
            return nullptr;
          };
          auto fieldSteps = [&](Value *Ptr, const Value *&root, Suffix &steps) {
            steps.clear();
            std::vector<Step> rev;
            std::unordered_set<const Value *> seen;
            while (Ptr && seen.insert(Ptr).second) {
              Ptr = peel(Ptr);
              if (auto *G = dyn_cast<GEPOperator>(Ptr)) {
                if (!G->hasAllConstantIndices())
                  return false;
                Step st;
                if (!constStep(dl, G, st))
                  return false;
                if (movesAddress(st))
                  rev.push_back(st);
                Ptr = G->getPointerOperand();
                continue;
              }
              root = asRoot(Ptr);
              if (!root)
                return false;
              for (size_t i = rev.size(); i-- > 0;)
                steps.push_back(rev[i]);
              return !steps.empty();
            }
            return false;
          };
          auto graftLoc = [&](const Loc &base, const Suffix &steps, Loc &out) {
            out = base;
            bool first = true;
            for (Step st : steps) {
              if (first) {
                st.deref = true;
                first = false;
              }
              out.suf.push_back(st);
            }
          };
          auto emitKilling = [&](Instruction *At, const Loc &cell, const std::set<std::string> &vals) {
            Loc as = cell;
            if (!wantStore(cell, vals, as))
              return;
            cells.insert({as.arg, as.suf});
            Ev ev;
            ev.at = At;
            ev.fn = F;
            ev.anchor = anchor;
            // The use demands this value, so the witness is a path through
            // the store. Domination of every return is a different question.
            ev.callMust = true;
            ev.mustExit = dominatesReturns(At);
            ev.kind = 's';
            ev.cell = {as.arg, as.suf};
            ev.vals = vals;
            for (const std::string &v : vals)
              stepStore[curStep][{as.arg, as.suf}].insert(v);
            stepEv[curStep].push_back(std::move(ev));
          };
          auto emitGrafts = [&](Instruction *At, const Value *root, const Loc &base) {
            auto it = fields.find(root);
            if (it == fields.end())
              return;
            for (const Graft &g : it->second) {
              Loc cell;
              graftLoc(base, g.steps, cell);
              emitKilling(At, cell, g.vals);
            }
          };
          for (Instruction &I : instructions(*F)) {
            if (!reach.count(I.getParent()))
              continue;
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              grow(S->getPointerOperand(), dl.getTypeStoreSize(S->getValueOperand()->getType()).getFixedValue());
              Loc cell;
              if (located(S->getPointerOperand(), cell)) {
                cells.insert({cell.arg, cell.suf});
                Ev ev;
                ev.at = S;
                ev.fn = F;
                ev.anchor = F == seq[curStep] ? nullptr : anchor;
                ev.callMust = callMust;
                ev.mustExit = F == seq[curStep] || dominatesReturns(S);
                ev.cell = {cell.arg, cell.suf};
                ev.kind = 's';
                if (auto *CI = dyn_cast<ConstantInt>(S->getValueOperand())) {
                  seqStore[{cell.arg, cell.suf}].insert(dec(CI));
                  stepStore[curStep][{cell.arg, cell.suf}].insert(dec(CI));
                  ev.vals.insert(dec(CI));
                  Loc as;
                  if (wantStore(cell, ev.vals, as)) {
                    ev.cell = {as.arg, as.suf};
                    ev.callMust = true;
                    stepEv[curStep].push_back(std::move(ev));
                  }
                } else if (auto *Sel = dyn_cast<SelectInst>(S->getValueOperand())) {
                  // store (select cmp, c1, c2) kills the cell with the arm a
                  // later use demands, and conjoins that comparison. The other
                  // arm is a different path.
                  auto *T = dyn_cast<ConstantInt>(Sel->getTrueValue());
                  auto *Fv = dyn_cast<ConstantInt>(Sel->getFalseValue());
                  auto *Cmp = dyn_cast<ICmpInst>(Sel->getCondition());
                  if (T && Fv && Cmp) {
                    std::string tv = dec(T), fv = dec(Fv);
                    bool wantT = demanded(cell, tv), wantF = demanded(cell, fv);
                    if (wantT != wantF) {
                      Value *lhs = Cmp->getOperand(0);
                      Value *rhs = Cmp->getOperand(1);
                      while (auto *C = dyn_cast<CastInst>(lhs))
                        lhs = C->getOperand(0);
                      while (auto *C = dyn_cast<CastInst>(rhs))
                        rhs = C->getOperand(0);
                      Loc cond;
                      ConstantInt *ck = nullptr;
                      bool left = false;
                      auto side = [&](Value *loadSide, Value *constSide, bool ldLeft) {
                        auto *Ld = dyn_cast<LoadInst>(loadSide);
                        if (!Ld || !isa<ConstantInt>(constSide) || !located(Ld->getPointerOperand(), cond))
                          return false;
                        ck = cast<ConstantInt>(constSide);
                        left = ldLeft;
                        return true;
                      };
                      if (side(lhs, rhs, true) || side(rhs, lhs, false)) {
                        auto pred = Cmp->getPredicate();
                        if (!wantT)
                          pred = Cmp->getInversePredicate();
                        if (!left)
                          pred = ICmpInst::getSwappedPredicate(pred);
                        Ev br;
                        br.at = Cmp;
                        br.fn = F;
                        br.anchor = anchor;
                        br.callMust = callMust;
                        br.mustExit = dominatesReturns(Cmp);
                        br.cell = {cond.arg, cond.suf};
                        br.vals.insert(dec(ck));
                        br.pred = (int)pred;
                        if (auto *IT = dyn_cast<IntegerType>(Cmp->getOperand(0)->getType()))
                          br.bits = IT->getBitWidth();
                        br.kind = pred == ICmpInst::ICMP_EQ ? 'e' : pred == ICmpInst::ICMP_NE ? 'n' : 'r';
                        cells.insert(br.cell);
                        stepEv[curStep].push_back(std::move(br));
                        ev.vals.insert(wantT ? tv : fv);
                        ev.callMust = true;
                        br.callMust = true;
                        stepStore[curStep][{cell.arg, cell.suf}].insert(*ev.vals.begin());
                        stepEv[curStep].push_back(std::move(ev));
                      }
                    }
                  }
                } else if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
                  if (Function *D = define(Fn->getName()))
                    Fn = D;
                  if (!Fn->isDeclaration()) {
                    stepStore[curStep][{cell.arg, cell.suf}].insert(Fn->getName().str());
                    ev.vals.insert(Fn->getName().str());
                    Loc as;
                    if (wantStore(cell, ev.vals, as)) {
                      ev.cell = {as.arg, as.suf};
                      ev.callMust = true;
                      stepEv[curStep].push_back(std::move(ev));
                    }
                  }
                } else if (auto *Ld = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts())) {
                  Loc src;
                  if (located(Ld->getPointerOperand(), src)) {
                    cells.insert({src.arg, src.suf});
                    ev.kind = 'c';
                    ev.src = {src.arg, src.suf};
                    if (F != seq[curStep])
                      stepEv[curStep].push_back(std::move(ev));
                  }
                }
              }
              if (const Value *root = asRoot(S->getValueOperand())) {
                Value *dst = peel(S->getPointerOperand());
                if (auto *A = dyn_cast<AllocaInst>(dst))
                  rootOf[A] = root;
                else {
                  Loc base;
                  if (located(S->getPointerOperand(), base)) {
                    published[root] = base;
                    emitGrafts(S, root, base);
                  }
                }
              } else {
                const Value *fieldRoot = nullptr;
                Suffix steps;
                std::set<std::string> vals;
                if (auto *CI = dyn_cast<ConstantInt>(S->getValueOperand()))
                  vals.insert(dec(CI));
                else if (auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
                  if (Function *D = define(Fn->getName()))
                    Fn = D;
                  if (!Fn->isDeclaration())
                    vals.insert(Fn->getName().str());
                }
                if (!vals.empty() && fieldSteps(S->getPointerOperand(), fieldRoot, steps)) {
                  fields[fieldRoot].push_back(Graft{steps, vals});
                  if (auto it = published.find(fieldRoot); it != published.end()) {
                    Loc gcell;
                    graftLoc(it->second, steps, gcell);
                    emitKilling(S, gcell, vals);
                  }
                }
              }
            }
            if (auto *L = dyn_cast<LoadInst>(&I))
              grow(L->getPointerOperand(), dl.getTypeStoreSize(L->getType()).getFixedValue());
            if (auto *CB = dyn_cast<CallBase>(&I)) {
              Copy copied = fixedCopy(*CB);
              // An integer result is computed from the arguments. It is not
              // a copy of copied.len bytes, so it does not size the object.
              if (copied.ok && !CB->getType()->isIntegerTy()) {
                grow(CB->getArgOperand(copied.src), copied.len);
                grow(CB->getArgOperand(copied.dst), copied.len);
                if (copied.len > dl.getPointerSize(0) * 2) {
                  Loc dst, src;
                  if (located(CB->getArgOperand(copied.dst), dst) && located(CB->getArgOperand(copied.src), src)) {
                    cells.insert({dst.arg, dst.suf});
                    cells.insert({src.arg, src.suf});
                    Ev ev;
                    ev.at = CB;
                    ev.fn = F;
                    ev.anchor = F == seq[curStep] ? nullptr : anchor;
                    ev.callMust = callMust;
                    ev.mustExit = F == seq[curStep] || dominatesReturns(CB);
                    ev.kind = 'c';
                    ev.cell = {dst.arg, dst.suf};
                    ev.src = {src.arg, src.suf};
                    if (F != seq[curStep])
                      stepEv[curStep].push_back(std::move(ev));
                  }
                }
              }
              Function *C = CB->getCalledFunction();
              if (C)
                if (Function *D = define(C->getName()))
                  C = D;
              if (C && !C->isDeclaration()) {
                std::vector<std::optional<Loc>> downArgs;
                bool touch = false;
                for (Value *Op : CB->args()) {
                  Loc L;
                  if (cellLoc(m, Op, L)) {
                    downArgs.push_back(L);
                    touch = true;
                  } else
                    downArgs.push_back(std::nullopt);
                }
                  if (touch) {
                  std::string sg = C->getName().str();
                  for (const auto &a : downArgs) {
                    sg.push_back('|');
                    if (!a) {
                      sg.push_back('-');
                      continue;
                    }
                    sg += std::to_string(a->arg);
                    for (const Step &st : a->suf)
                      sg += ":" + st.type + "+" + std::to_string(st.off);
                  }
                  if (walked.insert(sg).second) {
                    Instruction *childAnchor = F == seq[curStep] ? CB : anchor;
                    bool childMust = F == seq[curStep] || (callMust && dominatesReturns(CB));
                    noteCallee(C, downArgs, childAnchor, childMust);
                  }
                }
              }
              if (!C) {
                // An indirect call reaches the target whose body stores a
                // function the later use demands. The same test applies in a
                // callee: the store is not required to sit in the sequence
                // function itself. Other targets of the type do not define it.
                for (Function *T : targetsOf(CB)) {
                  if (!mayStoreDemanded(T))
                    continue;
                  if (Function *D = define(T->getName()))
                    T = D;
                  if (!T || T->isDeclaration())
                    continue;
                  std::vector<std::optional<Loc>> downArgs;
                  bool touch = false;
                  for (Value *Op : CB->args()) {
                    Loc L;
                    if (cellLoc(m, Op, L)) {
                      downArgs.push_back(L);
                      touch = true;
                    } else
                      downArgs.push_back(std::nullopt);
                  }
                  if (!touch)
                    continue;
                  std::string sg = T->getName().str();
                  for (const auto &a : downArgs) {
                    sg.push_back('|');
                    if (!a) {
                      sg.push_back('-');
                      continue;
                    }
                    sg += std::to_string(a->arg);
                    for (const Step &st : a->suf)
                      sg += ":" + st.type + "+" + std::to_string(st.off);
                  }
                  if (!walked.insert(sg).second)
                    continue;
                  Instruction *useAnchor = F == seq[curStep] ? CB : anchor;
                  if (useAnchor)
                    noteCallee(T, downArgs, useAnchor, true);
                }
                Read rd = asRead(*CB);
                Loc cell;
                if (rd.ok && noBody(CB) && located(CB->getCalledOperand(), cell) && cells.count({cell.arg, cell.suf})) {
                  fileCell[{cell.arg, cell.suf}] = CB->getFunctionType();
                  if (rd.len)
                    fileLen[{cell.arg, cell.suf}] = *rd.len;
                }
              }
            }
          }
        };
    for (size_t i = 0; i < mapped && i < seq.size(); ++i) {
      curStep = i;
      noteCallee(seq[i], frames[i], nullptr, true);
    }
    // open produced the read's handle. The pointer it passes is the file
    // path when those bytes are a cell, including through a fixed copy and
    // the object a call returns.
    {
      struct Site {
        Function *caller = nullptr;
        CallBase *cb = nullptr;
      };
      std::map<Function *, std::vector<Site>> sites;
      std::map<Function *, const std::vector<std::optional<Loc>> *> frameOf;
      for (size_t i = 0; i < mapped && i < seq.size(); ++i)
        frameOf[seq[i]] = &frames[i];
      std::vector<std::pair<Function *, int>> q;
      std::unordered_set<Function *> seenFn;
      for (size_t i = 0; i < mapped && i < seq.size(); ++i)
        q.push_back({seq[i], 0});
      for (size_t qi = 0; qi < q.size(); ++qi) {
        Function *F = q[qi].first;
        if (!F || !seenFn.insert(F).second)
          continue;
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          std::vector<Function *> ts = targetsOf(CB);
          if (ts.empty())
            ts = vtableReads(CB);
          for (Function *T : ts) {
            if (T->isDeclaration())
              continue;
            sites[T].push_back(Site{F, CB});
            q.push_back({T, 0});
          }
        }
      }
      auto baseOff = [&](Value *V, Value *&base, int64_t &off) {
        base = V;
        off = 0;
        std::unordered_set<const Value *> seen;
        while (base && seen.insert(base).second) {
          if (auto *C = dyn_cast<CastInst>(base)) {
            base = C->getOperand(0);
            continue;
          }
          auto *G = dyn_cast<GEPOperator>(base);
          if (!G)
            break;
          APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta))
            break;
          off += delta.getSExtValue();
          base = G->getPointerOperand();
        }
        if (base)
          base = base->stripPointerCasts();
      };
      std::set<std::pair<Function *, const Value *>> stack;
      std::map<std::pair<const Function *, const Value *>, std::optional<Loc>> known;
      std::function<std::optional<Loc>(Function *, Value *, int)> find;
      std::function<std::optional<Loc>(Function *, int64_t, CallBase *, int)> fieldIn;
      find = [&](Function *F, Value *V, int depth) -> std::optional<Loc> {
        if (!F || !V)
          return std::nullopt;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (auto it = known.find({F, V}); it != known.end())
          return it->second;
        if (!stack.insert({F, V}).second)
          return std::nullopt;
        struct Pop {
          std::set<std::pair<Function *, const Value *>> &s;
          Function *F;
          const Value *V;
          ~Pop() { s.erase({F, V}); }
        } pop{stack, F, V};
        Value *base = nullptr;
        int64_t off = 0;
        baseOff(V, base, off);
        if (off == 0)
          if (auto *Ld = dyn_cast<LoadInst>(base)) {
            if (Ld->getType()->isPointerTy()) {
              if (auto L = find(F, Ld->getPointerOperand(), depth + 1)) {
                pathPtr.insert({L->arg, L->suf});
                return L;
              }
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              auto fr0 = frameOf.find(F);
              if (Al && fr0 != frameOf.end()) {
                for (Instruction &SI : instructions(*F)) {
                  auto *S = dyn_cast<StoreInst>(&SI);
                  if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                    continue;
                  auto *Arg = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
                  if (!Arg || Arg->getArgNo() >= fr0->second->size() || !(*fr0->second)[Arg->getArgNo()])
                    continue;
                  Loc L = *(*fr0->second)[Arg->getArgNo()];
                  if (L.suf.empty())
                    continue;
                  return L;
                }
              }
            }
          }
        auto fr = frameOf.find(F);
        if (fr != frameOf.end()) {
          Mem m;
          bindFormals(m, F, *fr->second);
          Loc L;
          if (locOf(m, V, L) && !L.suf.empty())
            return L;
        }
        if (auto *A = dyn_cast<Argument>(base)) {
          Suffix field = suffix(V);
          if (field.empty() && off != 0)
            field.push_back(Step{"", off});
          if (fr != frameOf.end() && A->getArgNo() < fr->second->size() && (*fr->second)[A->getArgNo()]) {
            Loc L = *(*fr->second)[A->getArgNo()];
            L.suf.insert(L.suf.end(), field.begin(), field.end());
            if (!L.suf.empty())
              return L;
          }
          auto sit = sites.find(F);
          if (sit != sites.end()) {
            for (const Site &s : sit->second) {
              if (A->getArgNo() >= s.cb->arg_size())
                continue;
              Value *act = s.cb->getArgOperand(A->getArgNo())->stripPointerCasts();
              if (field.empty()) {
                if (auto L = find(s.caller, act, depth + 1))
                  return L;
                continue;
              }
              if (auto *CB = dyn_cast<CallBase>(act)) {
                if (Function *D = CB->getCalledFunction())
                  if (Function *B = define(D->getName()))
                    if (auto L = fieldIn(B, off, CB, depth + 1))
                      return L;
              }
              if (auto *Arg = dyn_cast<Argument>(act)) {
                auto cfr = frameOf.find(s.caller);
                if (cfr != frameOf.end() && Arg->getArgNo() < cfr->second->size() && (*cfr->second)[Arg->getArgNo()]) {
                  Loc L = *(*cfr->second)[Arg->getArgNo()];
                  L.suf.insert(L.suf.end(), field.begin(), field.end());
                  if (!L.suf.empty())
                    return L;
                }
              }
            }
          }
        }
        if (auto *Al = dyn_cast<AllocaInst>(base)) {
          for (Instruction &I : instructions(*F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Copy copied = fixedCopy(*CB);
            if (!copied.ok)
              continue;
            Value *db = nullptr;
            int64_t doff = 0;
            baseOff(CB->getArgOperand(copied.dst), db, doff);
            if (db != Al || doff != off)
              continue;
            if (auto L = find(F, CB->getArgOperand(copied.src), depth + 1))
              return L;
          }
        }
        if (auto *CB = dyn_cast<CallBase>(base)) {
          if (Function *D = CB->getCalledFunction())
            if (Function *B = define(D->getName()))
              if (auto L = fieldIn(B, off, CB, depth + 1))
                return L;
          // A call with no body that returns a pointer yields the bytes of
          // the object it was given. That pointer is the cell.
          if (noBody(CB) && CB->getType()->isPointerTy()) {
            for (Value *Op : CB->args()) {
              if (!Op->getType()->isPointerTy())
                continue;
              if (auto L = find(F, Op, depth + 1)) {
                // Offset 0 of the object is its data pointer. A field that
                // already names the bytes stays the bytes.
                if (L->suf.size() == 1 && L->suf[0].type.empty() && L->suf[0].off == 0)
                  pathPtr.insert({L->arg, L->suf});
                return L;
              }
              auto *Arg = dyn_cast<Argument>(Op->stripPointerCasts());
              auto fr2 = frameOf.find(F);
              if (!Arg || fr2 == frameOf.end() || Arg->getArgNo() >= fr2->second->size() || !(*fr2->second)[Arg->getArgNo()])
                continue;
              Loc L = *(*fr2->second)[Arg->getArgNo()];
              if (L.suf.empty())
                continue;
              pathPtr.insert({L.arg, L.suf});
              return L;
            }
          }
        }
        if (auto *Ld = dyn_cast<LoadInst>(base)) {
          auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
          if (Al) {
            for (Instruction &I : instructions(*F)) {
              auto *S = dyn_cast<StoreInst>(&I);
              if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
                continue;
              if (auto L = find(F, S->getValueOperand(), depth + 1)) {
                known[{F, V}] = L;
                return L;
              }
            }
          }
        }
        known[{F, V}] = std::nullopt;
        return std::nullopt;
      };
      fieldIn = [&](Function *D, int64_t want, CallBase *CB, int depth) -> std::optional<Loc> {
        if (!D)
          return std::nullopt;
        std::vector<Value *> roots;
        for (BasicBlock &BB : *D) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue())
            continue;
          Value *base = nullptr;
          int64_t o = 0;
          baseOff(R->getReturnValue(), base, o);
          if (base && o == 0)
            roots.push_back(base);
        }
        for (Instruction &I : instructions(*D)) {
          auto *Call = dyn_cast<CallBase>(&I);
          if (!Call)
            continue;
          Copy copied = fixedCopy(*Call);
          if (!copied.ok)
            continue;
          Value *db = nullptr;
          int64_t doff = 0;
          baseOff(Call->getArgOperand(copied.dst), db, doff);
          if (!db || doff != want)
            continue;
          bool retObj = false;
          for (Value *r : roots)
            if (r == db)
              retObj = true;
          if (!retObj)
            continue;
          Value *src = Call->getArgOperand(copied.src);
          if (auto L = find(D, src, depth + 1))
            return L;
          Value *sb = nullptr;
          int64_t soff = 0;
          baseOff(src, sb, soff);
          auto *Arg = dyn_cast<Argument>(sb);
          if (!Arg || Arg->getArgNo() >= CB->arg_size())
            continue;
          Value *act = CB->getArgOperand(Arg->getArgNo())->stripPointerCasts();
          Suffix field = suffix(src);
          if (field.empty() && soff != 0)
            field.push_back(Step{"", soff});
          if (auto *ActArg = dyn_cast<Argument>(act)) {
            auto cfr = frameOf.find(CB->getFunction());
            if (cfr != frameOf.end() && ActArg->getArgNo() < cfr->second->size() && (*cfr->second)[ActArg->getArgNo()]) {
              Loc L = *(*cfr->second)[ActArg->getArgNo()];
              L.suf.insert(L.suf.end(), field.begin(), field.end());
              if (!L.suf.empty())
                return L;
            }
          }
          if (auto *Inner = dyn_cast<CallBase>(act)) {
            if (Function *ID = Inner->getCalledFunction())
              if (Function *IB = define(ID->getName()))
                if (auto L = fieldIn(IB, soff, Inner, depth + 1))
                  return L;
          }
        }
        return std::nullopt;
      };
      std::vector<std::pair<CallBase *, CallBase *>> opens;
      for (Function *F : seenFn) {
        for (Instruction &I : instructions(*F)) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || !noBody(CB))
            continue;
          Read rd = asRead(*CB);
          if (!rd.ok)
            continue;
          int slot = -1;
          if (rd.file >= 0)
            slot = (int)rd.file;
          else if (rd.handle >= 0)
            slot = (int)rd.handle;
          if (slot < 0 || (unsigned)slot >= CB->arg_size())
            continue;
          Value *H = CB->getArgOperand((unsigned)slot);
          while (auto *C = dyn_cast<CastInst>(H))
            H = C->getOperand(0);
          if (auto *Ld = dyn_cast<LoadInst>(H)) {
            auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
            if (Al) {
              for (Instruction &S : instructions(*F)) {
                auto *St = dyn_cast<StoreInst>(&S);
                if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                  H = St->getValueOperand();
              }
              while (auto *C = dyn_cast<CastInst>(H))
                H = C->getOperand(0);
            }
          }
          if (auto *P = dyn_cast<CallBase>(H->stripPointerCasts())) {
            if (noBody(P))
              opens.push_back({P, CB});
            continue;
          }
          Suffix hs = suffix(H);
          if (hs.empty())
            continue;
          for (Function *G : seenFn) {
            for (Instruction &S : instructions(*G)) {
              auto *St = dyn_cast<StoreInst>(&S);
              if (!St || suffix(St->getPointerOperand()) != hs)
                continue;
              auto *P = dyn_cast<CallBase>(St->getValueOperand()->stripPointerCasts());
              if (P && noBody(P))
                opens.push_back({P, CB});
            }
          }
        }
      }
      std::set<std::pair<Function *, const Value *>> pret;
      std::function<bool(Function *, Value *, int)> ptrRet;
      ptrRet = [&](Function *F, Value *V, int depth) -> bool {
        if (!F || !V)
          return false;
        while (auto *C = dyn_cast<CastInst>(V))
          V = C->getOperand(0);
        if (!pret.insert({F, V}).second)
          return false;
        if (auto *CB = dyn_cast<CallBase>(V)) {
          if (!noBody(CB) || !CB->getType()->isPointerTy())
            return false;
          // The call returns a pointer into an object. A pointer into a
          // byte array is the bytes themselves.
          auto intoObject = [&](Function *Fn, Value *A) {
            while (auto *C = dyn_cast<CastInst>(A))
              A = C->getOperand(0);
            if (auto *Ld = dyn_cast<LoadInst>(A)) {
              auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
              if (Al)
                for (Instruction &I : instructions(*Fn)) {
                  auto *S = dyn_cast<StoreInst>(&I);
                  if (S && S->getPointerOperand()->stripPointerCasts() == Al)
                    A = S->getValueOperand()->stripPointerCasts();
                }
            }
            if (auto *G = dyn_cast<GEPOperator>(A))
              return G->getResultElementType()->isStructTy();
            auto *Arg = dyn_cast<Argument>(A);
            if (!Arg)
              return false;
            auto sit = sites.find(Fn);
            if (sit == sites.end())
              return false;
            for (const Site &s : sit->second) {
              if (Arg->getArgNo() >= s.cb->arg_size())
                continue;
              Value *act = s.cb->getArgOperand(Arg->getArgNo())->stripPointerCasts();
              if (auto *G = dyn_cast<GEPOperator>(act))
                if (G->getResultElementType()->isStructTy())
                  return true;
            }
            return false;
          };
          for (Value *Op : CB->args()) {
            if (!Op->getType()->isPointerTy())
              continue;
            return intoObject(CB->getFunction(), Op);
          }
          return false;
        }
        if (auto *Ld = dyn_cast<LoadInst>(V)) {
          auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
          if (!Al)
            return false;
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (S && S->getPointerOperand()->stripPointerCasts() == Al && ptrRet(F, S->getValueOperand(), depth + 1))
              return true;
          }
          return false;
        }
        auto *A = dyn_cast<Argument>(V);
        if (!A)
          return false;
        auto sit = sites.find(F);
        if (sit == sites.end())
          return false;
        for (const Site &s : sit->second) {
          if (A->getArgNo() >= s.cb->arg_size())
            continue;
          if (ptrRet(s.caller, s.cb->getArgOperand(A->getArgNo()), depth + 1))
            return true;
        }
        return false;
      };
      auto remember = [&](const FileIO &io) {
        for (const FileIO &e : fileIO)
          if (e.name == io.name && e.opener == io.opener)
            return;
        fileIO.push_back(io);
      };
      for (auto [P, R] : opens) {
        bool got = false;
        int pathArg = 0;
        for (unsigned i = 0; i < P->arg_size(); ++i) {
          Value *Op = P->getArgOperand(i);
          if (!Op->getType()->isPointerTy())
            continue;
          if (auto L = find(P->getFunction(), Op, 0)) {
            pathAt.insert({L->arg, L->suf});
            if (ptrRet(P->getFunction(), Op, 0))
              pathPtr.insert({L->arg, L->suf});
            got = true;
            pathArg = (int)i;
          }
        }
        if (!got)
          continue;
        if (Function *C = P->getCalledFunction()) {
          FileIO io;
          io.name = C->getName().str();
          io.opener = true;
          io.retPtr = P->getType()->isPointerTy();
          io.pathArg = pathArg;
          remember(io);
        }
        Read rd = asRead(*R);
        if (rd.ok)
          if (Function *C = R->getCalledFunction()) {
            FileIO io;
            io.name = C->getName().str();
            io.bufArg = (int)rd.buf;
            io.countArg = (int)rd.count;
            if (rd.file >= 0)
              for (int i = (int)rd.count + 1; i < rd.file; ++i)
                if ((unsigned)i < R->arg_size() &&
                    R->getArgOperand((unsigned)i)->getType()->isIntegerTy())
                  io.count2 = i;
            remember(io);
          }
      }
      for (const auto &c : pathAt)
        cells.insert(c);
    }
    auto tail = [](const Suffix &cell, const Suffix &store) {
      if (cell.size() != store.size())
        return false;
      for (size_t i = 0; i < cell.size(); ++i)
        if (cell[i].type != store[i].type || cell[i].off != store[i].off)
          return false;
      return true;
    };
    // A pointer loaded from a cell is an object. The function stored in a
    // slot of that object, and the pointer stored beside it, are cells.
    // A function that returns one field of the object and writes another
    // through an argument names the bytes and their length.
    {
      auto sameSuf = [](const Suffix &a, const Suffix &b) {
        if (a.size() != b.size())
          return false;
        for (size_t i = 0; i < a.size(); ++i)
          if (a[i].type != b[i].type || a[i].off != b[i].off)
            return false;
        return true;
      };
      struct Bytes {
        Suffix data;
        Suffix len;
        bool hasLen = false;
        bool ok = false;
      };
      std::unordered_map<const Function *, Bytes> byteOf;
      auto fieldsOf = [&](Function *F) -> Bytes {
        auto it = byteOf.find(F);
        if (it != byteOf.end())
          return it->second;
        Bytes b;
        if (!F || F->isDeclaration() || F->arg_empty()) {
          byteOf[F] = b;
          return b;
        }
        std::unordered_set<const Value *> th{F->getArg(0)};
        std::unordered_set<const AllocaInst *> boxes;
        for (int pass = 0; pass < 3; ++pass)
          for (Instruction &I : instructions(*F)) {
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
        auto fieldOf = [&](Value *V) -> Suffix {
          auto *L = dyn_cast<LoadInst>(V->stripPointerCasts());
          if (!L)
            return {};
          Value *P = L->getPointerOperand()->stripPointerCasts();
          Value *base = P;
          if (auto *G = dyn_cast<GEPOperator>(base))
            base = G->getPointerOperand()->stripPointerCasts();
          if (!th.count(base))
            return {};
          return suffix(P);
        };
        for (const BasicBlock &BB : *F) {
          auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
          if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
            continue;
          Suffix d = fieldOf(R->getReturnValue());
          if (!d.empty())
            b.data = d;
        }
        if (!b.data.empty()) {
          for (Instruction &I : instructions(*F)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || !S->getValueOperand()->getType()->isIntegerTy())
              continue;
            Suffix n = fieldOf(S->getValueOperand());
            if (!n.empty()) {
              b.len = n;
              b.hasLen = true;
            }
          }
          b.ok = true;
        }
        byteOf[F] = b;
        return b;
      };
      ensureSlots();
      auto addFns = [&](int arg, Suffix full, const std::vector<Function *> &fns) {
        if (fns.empty() || full.empty())
          return;
        cells.insert({arg, full});
        auto &names = calleeAt[{arg, full}];
        for (Function *Fn : fns)
          names.insert(Fn->getName().str());
      };
      for (const auto &hold : ptrHold) {
        if (pathAt.count(hold) || pathPtr.count(hold))
          continue;
        std::vector<Suffix> blobs;
        for (size_t si = 0; si < seq.size(); ++si) {
          Mem &m = memAt(si);
          for (Instruction &I : instructions(*seq[si])) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            for (unsigned i = 0; i < CB->arg_size(); ++i) {
              if (!CB->getArgOperand(i)->getType()->isPointerTy())
                continue;
              Loc L;
              if (!cellLoc(m, CB->getArgOperand(i), L) || L.arg != hold.first || !sameSuf(L.suf, hold.second))
                continue;
              Function *Cal = CB->getCalledFunction();
              if (!Cal)
                continue;
              Function *D = define(Cal->getName());
              if (!D)
                continue;
              std::vector<std::pair<Function *, unsigned>> work{{D, i}};
              std::unordered_set<Function *> seenD;
              for (size_t wi = 0; wi < work.size(); ++wi) {
                Function *Dw = work[wi].first;
                unsigned argNo = work[wi].second;
                if (!Dw || !seenD.insert(Dw).second)
                  continue;
              for (Instruction &J : instructions(*Dw)) {
                auto *IC = dyn_cast<CallBase>(&J);
                if (!IC)
                  continue;
                if (Function *N0 = IC->getCalledFunction()) {
                  Function *ND = define(N0->getName());
                  if (!ND)
                    continue;
                  for (unsigned k = 0; k < IC->arg_size() && k < ND->arg_size(); ++k) {
                    Value *Op = IC->getArgOperand(k);
                    while (auto *C = dyn_cast<CastInst>(Op))
                      Op = C->getOperand(0);
                    if (auto *Ld = dyn_cast<LoadInst>(Op)) {
                      auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                      if (Al)
                        for (Instruction &SI : instructions(*Dw)) {
                          auto *St = dyn_cast<StoreInst>(&SI);
                          if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                            Op = St->getValueOperand()->stripPointerCasts();
                        }
                    }
                    if (auto *A2 = dyn_cast<Argument>(Op))
                      if (A2->getArgNo() == argNo)
                        work.push_back({ND, k});
                  }
                  continue;
                }
                Value *base = IC->getCalledOperand();
                std::unordered_set<const Value *> seen;
                bool mine = false;
                while (base && seen.insert(base).second) {
                  if (auto *C = dyn_cast<CastInst>(base)) {
                    base = C->getOperand(0);
                    continue;
                  }
                  if (auto *G = dyn_cast<GEPOperator>(base)) {
                    base = G->getPointerOperand();
                    continue;
                  }
                  if (auto *Ld = dyn_cast<LoadInst>(base)) {
                    base = Ld->getPointerOperand();
                    continue;
                  }
                  if (auto *Al = dyn_cast<AllocaInst>(base)) {
                    Value *stored = nullptr;
                    for (Instruction &SI : instructions(*Dw)) {
                      auto *St = dyn_cast<StoreInst>(&SI);
                      if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                        stored = St->getValueOperand();
                    }
                    base = stored;
                    continue;
                  }
                  break;
                }
                if (auto *A = dyn_cast<Argument>(base ? base->stripPointerCasts() : nullptr))
                  mine = A->getArgNo() == argNo;
                if (!mine) {
                  Function *N = IC->getCalledFunction();
                  if (N) {
                    if (Function *ND = define(N->getName()))
                      N = ND;
                    for (unsigned k = 0; k < IC->arg_size() && k < N->arg_size(); ++k) {
                      Value *Op = IC->getArgOperand(k);
                      while (auto *C = dyn_cast<CastInst>(Op))
                        Op = C->getOperand(0);
                      if (auto *Ld = dyn_cast<LoadInst>(Op)) {
                        auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                        if (Al)
                          for (Instruction &SI : instructions(*Dw)) {
                            auto *St = dyn_cast<StoreInst>(&SI);
                            if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                              Op = St->getValueOperand()->stripPointerCasts();
                          }
                      }
                      if (auto *A2 = dyn_cast<Argument>(Op))
                        if (A2->getArgNo() == argNo)
                          work.push_back({N, k});
                    }
                  }
                  continue;
                }
                Suffix slot = suffix(IC->getCalledOperand());
                std::vector<Function *> fns;
                auto sit = slotAt.find(slot);
                if (sit != slotAt.end())
                  fns = sit->second;
                if (fns.empty()) {
                  auto fit = fnAt.find(slot);
                  if (fit != fnAt.end())
                    fns = fit->second;
                }
                Suffix full = hold.second;
                full.insert(full.end(), slot.begin(), slot.end());
                addFns(hold.first, full, fns);
                for (const Suffix &side : besidePtr[slot]) {
                  Suffix comp = hold.second;
                  comp.insert(comp.end(), side.begin(), side.end());
                  cells.insert({hold.first, comp});
                  for (Function *H : builderOf[side]) {
                    for (const auto &st : argStored[H]) {
                      if (st.first >= H->arg_size() || !H->getArg(st.first)->getType()->isPointerTy())
                        continue;
                      Suffix inner = comp;
                      inner.insert(inner.end(), st.second.begin(), st.second.end());
                      cells.insert({hold.first, inner});
                      blobs.push_back(inner);
                    }
                  }
                }
              }
              }
              Bytes fb = fieldsOf(D);
              if (fb.ok) {
                Suffix data = hold.second;
                data.insert(data.end(), fb.data.begin(), fb.data.end());
                data.push_back(Step{"", 0});
                cells.insert({hold.first, data});
                if (fb.hasLen) {
                  Suffix ln = hold.second;
                  ln.insert(ln.end(), fb.len.begin(), fb.len.end());
                  cells.insert({hold.first, ln});
                }
              }
            }
          }
        }
        for (const Suffix &blob : blobs) {
          for (size_t si = 0; si < seq.size(); ++si)
            for (Instruction &I : instructions(*seq[si])) {
              auto *CB = dyn_cast<CallBase>(&I);
              if (!CB)
                continue;
              Function *Cal = CB->getCalledFunction();
              if (!Cal)
                continue;
              Function *D = define(Cal->getName());
              Bytes fb = fieldsOf(D);
              if (!fb.ok)
                continue;
              bool touch = false;
              for (Value *Op : CB->args()) {
                if (!Op->getType()->isPointerTy())
                  continue;
                Value *Act = Op->stripPointerCasts();
                if (auto *Ld = dyn_cast<LoadInst>(Act)) {
                  auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                  if (Al)
                    for (Instruction &SI : instructions(*seq[si])) {
                      auto *St = dyn_cast<StoreInst>(&SI);
                      if (St && St->getPointerOperand()->stripPointerCasts() == Al)
                        Act = St->getValueOperand()->stripPointerCasts();
                    }
                }
                auto *Inner = dyn_cast<CallBase>(Act);
                if (!Inner)
                  continue;
                for (Value *In : Inner->args()) {
                  Loc L;
                  if (cellLoc(memAt(si), In, L) && L.arg == hold.first && sameSuf(L.suf, hold.second))
                    touch = true;
                }
              }
              if (!touch)
                continue;
              Suffix data = blob;
              data.insert(data.end(), fb.data.begin(), fb.data.end());
              data.push_back(Step{"", 0});
              cells.insert({hold.first, data});
              if (fb.hasLen) {
                Suffix ln = blob;
                ln.insert(ln.end(), fb.len.begin(), fb.len.end());
                cells.insert({hold.first, ln});
              }
            }
        }
      }
    }
