
    solvedCells.clear();
    framePins.clear();
    rels.clear();
    readBytes.clear();
    countCap.clear();
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
    // §3.5 경계 근: D→U 교차 간선의 포인터 실인자가 가리키는 셀. 교차 실인자가
    // export에서 도달하지 않으면(loc=⊥) 셀이 아니라 미해결 근으로 센다.
    std::set<std::pair<int, Suffix>> boundaryRoots;
    unsigned boundaryUnresolved = 0;
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
      std::vector<std::string> words;
      int pred = 0;
      unsigned bits = 0;
      // A later call that is not a lookup reads this object, so the result
      // is not a substitute for those bytes.
      bool live = false;
    };
    std::map<size_t, std::vector<Ev>> stepEv;
    // The witness path of a step whose shortest path contradicts itself.
    std::map<size_t, std::unordered_set<const BasicBlock *>> stepPath;
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
          if (locOf(m, CB->getCalledOperand(), calleeLoc) && calleeLoc.pointee && !calleeLoc.suf.empty()) {
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
          } else if ((lastPins.clear(), locOf(m, Op, L))) {
            a.loc = L;
            a.address = !L.pointee;
            a.missing = false;
            any = true;
            framePins.insert(lastPins.begin(), lastPins.end());
            for (const Value *V = Op;;) {
              if (auto it = m.pins.find(V); it != m.pins.end())
                framePins.insert(it->second.begin(), it->second.end());
              auto *C = dyn_cast<CastInst>(V);
              if (!C)
                break;
              V = C->getOperand(0);
            }
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
      // §3.5 경계 간선: 다운스트림 함수가 업스트림 함수를 부르는 시퀀스 간선.
      // 그 포인터 실인자의 셀이 경계 근이다. loc이 풀리지 않은 포인터 실인자는
      // export에서 도달하지 않는 D-로컬 객체이므로 미해결 근으로 센다.
      if (F->getParent() == &down && Next->getParent() == &up) {
        for (unsigned i = 0; i < edge->arg_size(); ++i) {
          if (!edge->getArgOperand(i)->getType()->isPointerTy())
            continue;
          if (i < nextArgs.size() && nextArgs[i])
            boundaryRoots.insert({nextArgs[i]->arg, nextArgs[i]->suf});
          else
            ++boundaryUnresolved;
        }
      }
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
    // A file callback is a pointer field that is called. A struct field at
    // the same offset is the object itself, such as a path string.
    auto pointerSlot = [&](const Loc &cell) {
      if (cell.suf.empty())
        return false;
      const Step &st = cell.suf.back();
      if (st.type.empty())
        return true;
      return fieldIsPointer(st.type, st.off);
    };
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
          if (locOf(m, S->getPointerOperand(), cell) && cellAt(cell, cell)) {
            cells.insert({cell.arg, cell.suf});
            size_t before = stepEv[curStep].size();
            // A store of a value the events cannot name still defines the
            // cell on the path, so a later read is not of the entry value.
            struct Kill {
              std::map<size_t, std::vector<Ev>> &evs;
              size_t step, before;
              StoreInst *S;
              Function *F;
              std::pair<int, Suffix> cell;
              ~Kill() {
                if (evs[step].size() != before)
                  return;
                Ev k;
                k.at = S;
                k.fn = F;
                k.kind = 'd';
                k.cell = cell;
                evs[step].push_back(std::move(k));
              }
            } kill{stepEv, curStep, before, S, F, {cell.arg, cell.suf}};
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
              if (locOf(m, Ld->getPointerOperand(), src) && cellAt(src, src)) {
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
          if (locOf(m, L->getPointerOperand(), cell) && cellAt(cell, cell) && cells.count({cell.arg, cell.suf}))
            wide[{cell.arg, cell.suf}] = (unsigned)dl.getTypeStoreSize(L->getType()).getFixedValue();
        }
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          Copy copied = fixedCopy(*CB);
          if (copied.ok && !CB->getType()->isIntegerTy() && copied.len > dl.getPointerSize(0) * 2) {
            Loc dst, src;
            if (locOf(m, CB->getArgOperand(copied.dst), dst) && locOf(m, CB->getArgOperand(copied.src), src) &&
                cellAt(dst, dst) && cellAt(src, src)) {
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
            if (locOf(m, CB->getCalledOperand(), cell) && cell.pointee && !cell.suf.empty() && cells.count({cell.arg, cell.suf}) && pointerSlot(cell)) {
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
        // A scalar local holds what was stored into it: the sink's index or
        // length is computed into a local before the sink reads it.
        if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
            Al && !L->getType()->isPointerTy()) {
          for (User *U : Al->users())
            if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Al)
              trace(si, S->getValueOperand());
          return;
        }
        trace(si, L->getPointerOperand());
        return;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        for (Value *in : P->incoming_values())
          trace(si, in);
        return;
      }
      // An offset or a length computed from cells reads those cells.
      if (isa<BinaryOperator>(V) || isa<UnaryOperator>(V) || isa<CmpInst>(V) || isa<SelectInst>(V)) {
        for (Value *Op : cast<Instruction>(V)->operands())
          if (!isa<Constant>(Op))
            trace(si, Op);
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
            if (cellLoc(memAt(si), L->getPointerOperand(), cell) && cellAt(cell, cell)) {
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
          if (!cellLoc(memAt(si), CB->getCalledOperand(), cell) || !cell.pointee || cell.suf.empty() || !pointerSlot(cell))
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
      // A bool object holds 0 or 1, so a test of its value is the equation
      // of its cell with 1, or with 0 on the false side.
      auto boolLoad = [&](Value *V) -> LoadInst * {
        auto *L = dyn_cast<LoadInst>(V);
        if (!L)
          return nullptr;
        const DIType *T = source::pointee(L->getPointerOperand());
        while (auto *D = dyn_cast_or_null<DIDerivedType>(T))
          if (D->getTag() == dwarf::DW_TAG_typedef || D->getTag() == dwarf::DW_TAG_const_type ||
              D->getTag() == dwarf::DW_TAG_volatile_type)
            T = D->getBaseType();
          else
            break;
        auto *B = dyn_cast_or_null<DIBasicType>(T);
        return B && B->getEncoding() == dwarf::DW_ATE_boolean ? L : nullptr;
      };
      // The witness of a step is a path from its entry to its goal. Its
      // branch conditions are equations and disequations of cells, and its
      // stores give cells values. The shortest path is the witness when
      // these agree along it. Otherwise the witness is the shortest path on
      // which they agree, a search over pairs of a block and the cell state
      // reaching it (ESP, Das et al. PLDI'02). A call that may write an
      // object makes its cells unknown, so the search admits every path on
      // which the conditions can agree. When none can, no execution of the
      // step reaches the goal, and the shortest path stands for the
      // contradiction.
      // MOD(D), the cells a call of D may write, relative to D's formals
      // (Cooper and Kennedy, PLDI'88): the targets of its stores, and,
      // marked under, every object it passes to a callee with no body that
      // may write memory, which may write anything under that object. A call
      // site instantiates the summary by composing each relative location
      // with the location of the actual. A function met again while its
      // summary is being built is a recursive edge; it is widened to
      // "anything under each pointer formal", which contains every fixpoint.
      struct ModAt {
        Loc at;
        bool under = false;
      };
      // compose(B, R) is the location the operations that took a formal to R
      // reach from B. Only the first operation that sets pointee sees the
      // base: a moving step enters B's pointee, a load of a held pointer
      // records the dereference it crosses.
      auto composeLoc = [](const Loc &B, const Loc &R) {
        Loc res = B;
        if (R.suf.empty()) {
          if (R.pointee) {
            if (B.pointee)
              res.suf.push_back(Step{"", 0, true});
            res.pointee = true;
          }
          return res;
        }
        if (!R.suf[0].deref) {
          Step first = R.suf[0];
          first.deref = B.pointee;
          res.suf.push_back(first);
          res.suf.insert(res.suf.end(), R.suf.begin() + 1, R.suf.end());
        } else {
          if (B.pointee)
            res.suf.push_back(Step{"", 0, true});
          res.suf.insert(res.suf.end(), R.suf.begin(), R.suf.end());
        }
        res.pointee = R.pointee;
        return res;
      };
      std::unordered_map<const Function *, std::vector<ModAt>> modSum, modWide;
      std::unordered_set<const Function *> modBusy;
      std::function<void(CallBase *, Mem &, std::vector<ModAt> &)> callModsRel;
      std::function<const std::vector<ModAt> &(Function *)> summaryOf = [&](Function *D) -> const std::vector<ModAt> & {
        if (auto it = modSum.find(D); it != modSum.end())
          return it->second;
        if (!modBusy.insert(D).second) {
          auto &w = modWide[D];
          if (w.empty())
            for (Argument &A : D->args())
              if (A.getType()->isPointerTy())
                w.push_back({Loc{(int)A.getArgNo(), {}, false}, true});
          return w;
        }
        std::vector<std::optional<Loc>> self;
        for (Argument &A : D->args())
          self.push_back(A.getType()->isPointerTy() ? std::optional<Loc>(Loc{(int)A.getArgNo(), {}, false}) : std::nullopt);
        Mem dm;
        bindFormals(dm, D, self);
        propagateObject(dm, D);
        std::vector<ModAt> got;
        for (Instruction &I : instructions(*D)) {
          Loc c;
          if (auto *S = dyn_cast<StoreInst>(&I)) {
            if (objectLoc(dm, S->getPointerOperand(), c))
              got.push_back({c, false});
          } else if (auto *CB = dyn_cast<CallBase>(&I))
            callModsRel(CB, dm, got);
        }
        // A use reads every entry as "anything under it", so MOD is closed
        // upward in the prefix order of cell keys and is its antichain of
        // minimal keys; an entry below another adds nothing. Keys are taken
        // as the call site spells them: a store's cell, an object's path.
        auto keyRel = [](const ModAt &x) {
          Loc c = x.at;
          if (!x.under && c.pointee)
            c.suf.push_back(Step{"", 0, true});
          std::string k = std::to_string(c.arg);
          for (const Step &st : c.suf)
            k += "|" + st.type + "@" + std::to_string(st.off) + (st.deref ? "*" : "");
          return k;
        };
        std::map<std::string, const ModAt *> byKey;
        for (const ModAt &x : got)
          byKey.emplace(keyRel(x), &x);
        std::vector<ModAt> uniq;
        for (const auto &[k, x] : byKey) {
          bool below = false;
          for (size_t cut = k.find('|'); cut != std::string::npos && !below; cut = k.find('|', cut + 1))
            below = byKey.count(k.substr(0, cut)) > 0;
          if (!below)
            uniq.push_back(*x);
        }
        modBusy.erase(D);
        return modSum[D] = std::move(uniq);
      };
      callModsRel = [&](CallBase *CB, Mem &cm, std::vector<ModAt> &out) {
        if (ignorable(CB->getCalledFunction()) && !isa<MemIntrinsic>(CB))
          return;
        if (CB->onlyReadsMemory())
          return;
        std::vector<std::optional<Loc>> in;
        bool touch = false;
        for (unsigned a = 0; a < CB->arg_size(); ++a) {
          Loc L;
          if (CB->getArgOperand(a)->getType()->isPointerTy() && objectLoc(cm, CB->getArgOperand(a), L)) {
            in.push_back(L);
            touch = true;
          } else
            in.push_back(std::nullopt);
        }
        if (!touch)
          return;
        bool body = false;
        for (Function *T : targetsOf(CB))
          if (T && !T->isDeclaration()) {
            body = true;
            const std::vector<ModAt> &sum = summaryOf(T);
            for (const ModAt &x : sum)
              if (x.at.arg >= 0 && (size_t)x.at.arg < in.size() && in[x.at.arg])
                out.push_back({composeLoc(*in[x.at.arg], x.at), x.under});
          }
        if (body)
          return;
        for (unsigned a = 0; a < in.size(); ++a)
          if (in[a] && !CB->onlyReadsMemory(a))
            out.push_back({*in[a], true});
      };
      auto feasiblePath = [&](Function *F, const std::unordered_set<Instruction *> &goals, Mem &m,
                              const std::unordered_set<const BasicBlock *> &shortest)
          -> std::unordered_set<const BasicBlock *> {
        auto spellLoc = [](const Loc &c) {
          std::string k = std::to_string(c.arg);
          for (const Step &s : c.suf)
            k += "|" + s.type + "@" + std::to_string(s.off) + (s.deref ? "*" : "");
          return k;
        };
        auto keyOf = [&](Value *P, std::string &k) {
          Loc c;
          if (!objectLoc(m, P, c) || !cellAt(c, c))
            return false;
          k = spellLoc(c);
          return true;
        };
        struct Atom {
          std::string key;
          bool eq;
          std::string v;
        };
        auto loadKey = [&](Value *V, std::string &k) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(V);
          return L && keyOf(L->getPointerOperand(), k) && k.find('|') != std::string::npos;
        };
        std::function<void(Value *, bool, std::vector<Atom> &)> atoms = [&](Value *V, bool need, std::vector<Atom> &out) {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          std::string k;
          if (boolLoad(V)) {
            if (loadKey(V, k))
              out.push_back({k, true, need ? "1" : "0"});
            return;
          }
          if (auto *BO = dyn_cast<BinaryOperator>(V)) {
            auto *One = dyn_cast<ConstantInt>(BO->getOperand(1));
            if (BO->getOpcode() == Instruction::Xor && One && One->isOne())
              atoms(BO->getOperand(0), !need, out);
            else if ((need && BO->getOpcode() == Instruction::And) || (!need && BO->getOpcode() == Instruction::Or)) {
              atoms(BO->getOperand(0), need, out);
              atoms(BO->getOperand(1), need, out);
            }
            return;
          }
          auto *Cmp = dyn_cast<ICmpInst>(V);
          if (!Cmp)
            return;
          auto pred = need ? Cmp->getPredicate() : Cmp->getInversePredicate();
          if (pred != ICmpInst::ICMP_EQ && pred != ICmpInst::ICMP_NE)
            return;
          for (int side = 0; side < 2; ++side) {
            Value *C = Cmp->getOperand(1 - side);
            while (auto *X = dyn_cast<CastInst>(C))
              C = X->getOperand(0);
            std::string v;
            if (isa<ConstantPointerNull>(C))
              v = "0";
            else if (auto *CI = dyn_cast<ConstantInt>(C))
              v = dec(CI);
            else
              continue;
            if (loadKey(Cmp->getOperand(side), k)) {
              out.push_back({k, pred == ICmpInst::ICMP_EQ, v});
              return;
            }
          }
        };
        // The atoms that hold when the terminator of B passes to S.
        auto edge = [&](const BasicBlock *B, const BasicBlock *S, std::vector<Atom> &out) {
          const Instruction *T = B->getTerminator();
          if (auto *BR = dyn_cast<BranchInst>(T)) {
            if (BR->isConditional() && BR->getSuccessor(0) != BR->getSuccessor(1))
              atoms(BR->getCondition(), S == BR->getSuccessor(0), out);
            return;
          }
          auto *SW = dyn_cast<SwitchInst>(T);
          std::string k;
          if (!SW || !loadKey(SW->getCondition(), k))
            return;
          std::vector<std::string> to;
          for (auto &C : SW->cases())
            if (C.getCaseSuccessor() == S)
              to.push_back(dec(C.getCaseValue()));
          if (S == SW->getDefaultDest()) {
            if (!to.empty())
              return;
            for (auto &C : SW->cases())
              out.push_back({k, false, dec(C.getCaseValue())});
          } else if (to.size() == 1)
            out.push_back({k, true, to[0]});
        };
        std::unordered_set<const BasicBlock *> goalB, back;
        std::vector<const BasicBlock *> work;
        for (Instruction *g : goals)
          if (g && g->getFunction() == F) {
            goalB.insert(g->getParent());
            work.push_back(g->getParent());
          }
        while (!work.empty()) {
          const BasicBlock *B = work.back();
          work.pop_back();
          if (!back.insert(B).second)
            continue;
          for (const BasicBlock *P : predecessors(B))
            work.push_back(P);
        }
        // The cells some branch tests; only their state decides a path.
        std::set<std::string> tested;
        for (const BasicBlock *B : back)
          for (const BasicBlock *S : successors(B)) {
            std::vector<Atom> as;
            edge(B, S, as);
            for (const Atom &a : as)
              tested.insert(a.key);
          }
        if (tested.empty())
          return shortest;
        // A cell is the entry value under equations and disequations, a
        // known value, or unknown.
        struct Val {
          char kind = 'e';
          std::string v;
          std::set<std::string> ne;
        };
        using State = std::map<std::string, Val>;
        auto under = [](const std::string &k, const std::string &p) {
          return k == p || (k.size() > p.size() && k.compare(0, p.size(), p) == 0 && k[p.size()] == '|');
        };
        auto effects = [&](const BasicBlock *B, State &st) {
          for (Instruction &I : *const_cast<BasicBlock *>(B)) {
            if (auto *S = dyn_cast<StoreInst>(&I)) {
              std::string k;
              if (!keyOf(S->getPointerOperand(), k))
                continue;
              for (const std::string &t : tested)
                if (under(t, k) && t != k)
                  st[t] = Val{'a', "", {}};
              if (tested.count(k)) {
                auto *CI = dyn_cast<ConstantInt>(S->getValueOperand());
                auto *CN = dyn_cast<ConstantPointerNull>(S->getValueOperand());
                st[k] = CI ? Val{'k', dec(CI), {}} : CN ? Val{'k', "0", {}} : Val{'a', "", {}};
              }
              continue;
            }
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            std::set<std::string> ks;
            std::vector<ModAt> ms;
            callModsRel(CB, m, ms);
            for (const ModAt &x : ms) {
              Loc c;
              if (x.under)
                ks.insert(spellLoc(x.at));
              else if (cellAt(x.at, c))
                ks.insert(spellLoc(c));
            }
            for (const std::string &k : ks)
              for (const std::string &t : tested)
                if (under(t, k))
                  st[t] = Val{'a', "", {}};
          }
        };
        auto apply = [](State &st, const Atom &a) {
          Val &x = st[a.key];
          if (x.kind == 'k')
            return (x.v == a.v) == a.eq;
          if (x.kind == 'a') {
            if (a.eq)
              x = Val{'k', a.v, {}};
            return true;
          }
          if (a.eq) {
            if ((!x.v.empty() && x.v != a.v) || x.ne.count(a.v))
              return false;
            x.v = a.v;
            return true;
          }
          if (x.v == a.v)
            return false;
          x.ne.insert(a.v);
          return true;
        };
        auto spell = [](const State &st) {
          std::string s;
          for (const auto &kv : st) {
            s += kv.first + "=" + kv.second.kind + kv.second.v;
            for (const std::string &n : kv.second.ne)
              s += "!" + n;
            s += ";";
          }
          return s;
        };
        auto search = [&](const std::unordered_set<const BasicBlock *> &allowed) {
          std::unordered_set<const BasicBlock *> path;
          const BasicBlock *entry = &F->getEntryBlock();
          if (!allowed.count(entry))
            return path;
          struct Node {
            const BasicBlock *bb;
            State st;
            int prev;
          };
          std::vector<Node> nodes{{entry, State{}, -1}};
          std::set<std::pair<const BasicBlock *, std::string>> seen{{entry, ""}};
          std::deque<int> q{0};
          while (!q.empty()) {
            int n = q.front();
            q.pop_front();
            if (goalB.count(nodes[n].bb)) {
              for (int i = n; i >= 0; i = nodes[i].prev)
                path.insert(nodes[i].bb);
              return path;
            }
            State st = nodes[n].st;
            effects(nodes[n].bb, st);
            std::vector<const BasicBlock *> succs;
            for (const BasicBlock *S : successors(nodes[n].bb))
              if (allowed.count(S))
                succs.push_back(S);
            std::sort(succs.begin(), succs.end(),
                      [](const BasicBlock *A, const BasicBlock *B) { return A->getName() < B->getName(); });
            for (const BasicBlock *S : succs) {
              std::vector<Atom> as;
              edge(nodes[n].bb, S, as);
              State next = st;
              bool ok = true;
              for (const Atom &a : as)
                ok = ok && apply(next, a);
              if (!ok || !seen.insert({S, spell(next)}).second)
                continue;
              nodes.push_back(Node{S, std::move(next), n});
              q.push_back((int)nodes.size() - 1);
            }
          }
          return path;
        };
        if (!search(shortest).empty())
          return shortest;
        auto found = search(back);
        return found.empty() ? shortest : found;
      };
      std::function<void(Function *, const std::vector<std::optional<Loc>> &, const std::unordered_set<Instruction *> &, bool, Function *)>
          pathFacts;
      pathFacts = [&](Function *F, const std::vector<std::optional<Loc>> &args, const std::unordered_set<Instruction *> &goals,
                      bool enterCallee, Function *reachTo) {
        if (!F || F->isDeclaration() || goals.empty())
          return;
        // The branch condition of one path, not the intersection of every
        // path that can still reach the goal.
        auto reach = chosenPath(F, goals);
        // Inside a callee the goal is any return. A branch there constrains
        // the entry only when one successor alone can still return; where
        // both can, the shortest path's choice is not a condition of the
        // sequence, and taking it would exclude the other outcome.
        std::unordered_set<const BasicBlock *> canReturn;
        if (F != seq[curStep]) {
          std::vector<const BasicBlock *> work;
          for (Instruction *G : goals)
            if (G && G->getFunction() == F)
              work.push_back(G->getParent());
          while (!work.empty()) {
            const BasicBlock *B = work.back();
            work.pop_back();
            if (!canReturn.insert(B).second)
              continue;
            for (const BasicBlock *P : predecessors(B))
              work.push_back(P);
          }
        }
        const auto &decides = F == seq[curStep] ? reach : canReturn;
        Mem m;
        bindFormals(m, F, args);
        propagateObject(m, F);
        if (F == seq[curStep]) {
          auto witness = feasiblePath(F, goals, m, reach);
          if (witness != reach) {
            reach = std::move(witness);
            stepPath[curStep] = reach;
          }
        }
        // The first call site met enters a callee, so the walk goes in
        // program order.
        std::vector<const BasicBlock *> reachOrd;
        for (const BasicBlock &RB : *F)
          if (reach.count(&RB))
            reachOrd.push_back(&RB);
        auto locate = [&](Value *V, Loc &cell) -> bool {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          auto *L = dyn_cast<LoadInst>(V);
          if (!L)
            return false;
          return objectLoc(m, L->getPointerOperand(), cell) && cellAt(cell, cell);
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
        // The value a required comparison actually tests. A cell load stays
        // that load. A local is the store that dominates the branch. A call
        // that returns one argument is that argument. Any other call stays
        // the call, so the comparison is a constraint on its result.
        auto mustVal = [&](Value *V) -> Value * {
          std::unordered_set<Value *> seen;
          std::function<Value *(Value *)> go = [&](Value *V) -> Value * {
            if (!V || !seen.insert(V).second)
              return V;
            while (auto *C = dyn_cast<CastInst>(V))
              V = C->getOperand(0);
            if (auto *L = dyn_cast<LoadInst>(V)) {
              Loc cell;
              if (locate(L, cell))
                return L;
              auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (!A || !factAt)
                return L;
              // The definition is the last writer that dominates the branch.
              // A call that receives the slot overwrites an earlier store, so
              // that store is not the value.
              Instruction *best = nullptr;
              bool wrote = false;
              auto take = [&](Instruction *I, bool asCall) {
                if (!dominatesBefore(I, factAt))
                  return;
                if (best && !dominatesBefore(best, I))
                  return;
                best = I;
                wrote = asCall;
              };
              for (User *U : A->users()) {
                auto *S = dyn_cast<StoreInst>(U);
                if (S && S->getPointerOperand()->stripPointerCasts() == A)
                  take(S, false);
                auto *CB = dyn_cast<CallBase>(U);
                if (!CB)
                  continue;
                for (Value *Op : CB->args())
                  if (Op->stripPointerCasts() == A)
                    take(CB, true);
              }
              if (!best || wrote)
                return L;
              return go(cast<StoreInst>(best)->getValueOperand());
            }
            if (auto *CB = dyn_cast<CallBase>(V)) {
              Function *C = CB->getCalledFunction();
              Function *D = C ? define(C->getName()) : nullptr;
              if (D && !D->isDeclaration()) {
                auto arg = carryArg(D);
                if (arg && *arg >= 0 && *arg < (int)CB->arg_size())
                  return go(CB->getArgOperand((unsigned)*arg));
              }
              return CB;
            }
            return V;
          };
          return go(V);
        };
        // 반환 제약(§3.4 정제): 경로가 호출 CB의 결과를 상수와 비교해 한쪽만 이어질 때,
        // 그 비교는 피호출자의 반환값에 대한 must 조건이다. 'q' 이벤트(may측 실현)와
        // 별도로 호출지별로 모아 두어, 아래 피호출자 하강이 목표 ret를 이 제약을
        // 만족할 수 있는 ret로 한정하게 한다.
        std::map<const CallBase *, std::vector<std::pair<unsigned, int64_t>>> retCons;
        auto noteReturn = [&](CallBase *CB, ICmpInst::Predicate pred, Constant *C) {
          if (!factAt || !CB)
            return;
          Function *Cal = CB->getCalledFunction();
          if (!Cal)
            return;
          std::string k;
          int64_t kv = 0;
          if (isa<ConstantPointerNull>(C))
            k = "0";
          else if (auto *CI = dyn_cast<ConstantInt>(C)) {
            k = dec(CI);
            kv = CI->getSExtValue();
          } else
            return;
          retCons[CB].push_back({(unsigned)pred, kv});
          Ev ev;
          ev.at = CB;
          ev.fn = F;
          ev.anchor = F == seq[curStep] ? nullptr : myAnchor;
          ev.callMust = myMust;
          ev.mustExit = F == seq[curStep] || dominatesReturns(CB);
          ev.kind = 'q';
          ev.pred = (int)pred;
          ev.vals.insert(std::move(k));
          ev.words.push_back(Cal->getName().str());
          auto cstr = [](Value *V) -> std::string {
            auto *G = dyn_cast<GlobalVariable>(V->stripPointerCasts());
            if (!G || !G->hasInitializer())
              return {};
            auto *A = dyn_cast<ConstantDataArray>(G->getInitializer());
            if (!A || !A->isCString())
              return {};
            return A->getAsCString().str();
          };
          // An argument built by an earlier call is the constant string that
          // call passes in, when that call is the last one dominating this one.
          for (Value *Op : CB->args()) {
            if (std::string s = cstr(Op); !s.empty()) {
              ev.words.push_back(std::move(s));
              continue;
            }
            auto *Slot = dyn_cast<AllocaInst>(Op->stripPointerCasts());
            if (!Slot)
              continue;
            Instruction *best = nullptr;
            std::string text;
            for (User *U : Slot->users()) {
              auto *W = dyn_cast<CallBase>(U);
              if (!W || W == CB || !dominatesBefore(W, CB))
                continue;
              std::string got;
              for (Value *Arg : W->args())
                if (std::string s = cstr(Arg); !s.empty())
                  got = std::move(s);
              if (got.empty())
                continue;
              if (best && !dominatesBefore(best, W))
                continue;
              best = W;
              text = std::move(got);
            }
            if (!text.empty())
              ev.words.push_back(std::move(text));
          }
          stepEv[curStep].push_back(std::move(ev));
        };
        auto onCmp = [&](ICmpInst *Cmp, ICmpInst::Predicate pred) {
          Value *lhs = mustVal(Cmp->getOperand(0));
          Value *rhs = mustVal(Cmp->getOperand(1));
          if (auto *CB = dyn_cast<CallBase>(lhs)) {
            if (auto *C = dyn_cast<Constant>(rhs))
              if (isa<ConstantInt>(C) || isa<ConstantPointerNull>(C)) {
                noteReturn(CB, pred, C);
                return;
              }
          }
          if (auto *CB = dyn_cast<CallBase>(rhs)) {
            if (auto *C = dyn_cast<Constant>(lhs))
              if (isa<ConstantInt>(C) || isa<ConstantPointerNull>(C)) {
                noteReturn(CB, ICmpInst::getSwappedPredicate(pred), C);
                return;
              }
          }
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
        for (const BasicBlock *CBB : reachOrd) {
          BasicBlock *BB = const_cast<BasicBlock *>(CBB);
          Instruction *Term = BB->getTerminator();
          auto *BR = dyn_cast<BranchInst>(Term);
          if (BR && BR->isConditional()) {
            BasicBlock *only = nullptr;
            int n = 0;
            for (BasicBlock *S : successors(BR))
              if (decides.count(S)) {
                ++n;
                only = S;
              }
            if (n == 1 && reach.count(only)) {
              factAt = BR;
              bool takenTrue = only == BR->getSuccessor(0);
              std::function<void(Value *, bool)> req = [&](Value *V, bool need) {
                while (auto *C = dyn_cast<CastInst>(V))
                  V = C->getOperand(0);
                if (LoadInst *L = boolLoad(V)) {
                  Loc cell;
                  if (locate(L, cell))
                    equation(cell, need ? "1" : "0");
                  return;
                }
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
            bool def = decides.count(SW->getDefaultDest());
            if (def)
              ++n;
            for (auto &Case : SW->cases())
              if (decides.count(Case.getCaseSuccessor())) {
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
        for (const BasicBlock *CBB : reachOrd)
          for (Instruction &I : *const_cast<BasicBlock *>(CBB)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB || CB->getCalledFunction() || !vtableTargets(CB).empty())
              continue;
            Loc cell;
            if (!cellLoc(m, CB->getCalledOperand(), cell) || !cell.pointee || cell.suf.empty())
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
        for (const BasicBlock *CBB : reachOrd)
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
            if (!cellLoc(m, L, cell) || !cell.pointee || cell.suf.empty())
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
        for (const BasicBlock *CBB : reachOrd)
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
            // 피호출자 안의 목표는 반환이다. 이 호출의 결과에 경로가 반환 제약을
            // 걸었으면(위 retCons), 목표는 그 제약을 만족할 수 있는 반환값의
            // 정의 지점으로 한정한다. 반환값이 phi면 incoming 변, 반환 슬롯의
            // load면 그 슬롯에의 store, 그 밖이면 ret 자체가 정의 지점이다. 상수
            // 정의는 상수가 제약을 어기면 제외되고, 상수가 아닌 정의는 남는다.
            // 그러면 "한쪽 후계자만 목표에 닿는" 분기 규칙이 제외된 정의로만 가는
            // 분기를 조건으로 잡아, 피호출자가 결과를 정하는 데 읽는 셀이 경로의
            // 셀이 된다. 어떤 정의도 제약을 만족할 수 없으면 제약을 무시한다.
            std::unordered_set<Instruction *> rets, allRets;
            auto rc = retCons.find(CB);
            auto admits = [&](Value *V) {
              while (V && isa<CastInst>(V))
                V = cast<CastInst>(V)->getOperand(0);
              std::optional<int64_t> cv;
              if (V && isa<ConstantPointerNull>(V))
                cv = 0;
              else if (auto *CI = dyn_cast_or_null<ConstantInt>(V))
                cv = CI->getSExtValue();
              if (!cv)
                return true;
              for (const auto &c : rc->second)
                if (!cmpHolds(c.first, *cv, c.second))
                  return false;
              return true;
            };
            for (BasicBlock &RBB : *D) {
              auto *R = dyn_cast<ReturnInst>(RBB.getTerminator());
              if (!R)
                continue;
              allRets.insert(R);
              if (rc == retCons.end()) {
                rets.insert(R);
                continue;
              }
              Value *RV = R->getReturnValue();
              while (RV && isa<CastInst>(RV))
                RV = cast<CastInst>(RV)->getOperand(0);
              if (auto *Phi = dyn_cast_or_null<PHINode>(RV)) {
                for (unsigned pi = 0; pi < Phi->getNumIncomingValues(); ++pi)
                  if (admits(Phi->getIncomingValue(pi)))
                    rets.insert(Phi->getIncomingBlock(pi)->getTerminator());
                continue;
              }
              if (auto *Ld = dyn_cast_or_null<LoadInst>(RV)) {
                auto *Slot = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                bool anyStore = false;
                if (Slot)
                  for (User *U : Slot->users()) {
                    auto *St = dyn_cast<StoreInst>(U);
                    if (!St || St->getPointerOperand()->stripPointerCasts() != Slot)
                      continue;
                    anyStore = true;
                    if (admits(St->getValueOperand()))
                      rets.insert(St);
                  }
                if (anyStore)
                  continue;
              }
              if (admits(RV))
                rets.insert(R);
            }
            if (rets.empty())
              rets = allRets;
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
          auto located = [&](Value *Ptr, Loc &cell) {
            return cellLoc(m, Ptr, cell) && cellAt(cell, cell);
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
                size_t before = stepEv[curStep].size();
                // Inside a callee only a store on every way to a return is a
                // definition the caller sees; that one replaces the cell even
                // when its value has no name in the events.
                struct Kill {
                  std::map<size_t, std::vector<Ev>> &evs;
                  size_t step, before;
                  bool must;
                  StoreInst *S;
                  Function *F;
                  Instruction *anchor;
                  std::pair<int, Suffix> cell;
                  ~Kill() {
                    if (!must || evs[step].size() != before)
                      return;
                    Ev k;
                    k.at = S;
                    k.fn = F;
                    k.anchor = anchor;
                    k.callMust = true;
                    k.mustExit = true;
                    k.kind = 'd';
                    k.cell = cell;
                    evs[step].push_back(std::move(k));
                  }
                } kill{stepEv, curStep, before, F != seq[curStep] && callMust && dominatesReturns(S), S, F, anchor, {cell.arg, cell.suf}};
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
                  // A callee's events belong to the step whose call runs it,
                  // so one visited under another step is not yet visited.
                  std::string sg = std::to_string(curStep) + "#" + C->getName().str();
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
                  std::string sg = std::to_string(curStep) + "#" + T->getName().str();
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
                if (rd.ok && noBody(CB) && cellLoc(m, CB->getCalledOperand(), cell) && cell.pointee && !cell.suf.empty() && cells.count({cell.arg, cell.suf}) && pointerSlot(cell)) {
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
      std::vector<Function *> fnOrder;
      for (size_t i = 0; i < mapped && i < seq.size(); ++i)
        q.push_back({seq[i], 0});
      for (size_t qi = 0; qi < q.size(); ++qi) {
        Function *F = q[qi].first;
        if (!F || !seenFn.insert(F).second)
          continue;
        fnOrder.push_back(F);
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
          Function *D = CB->getCalledFunction();
          Function *B = D ? define(D->getName()) : nullptr;
          if (B)
            if (auto L = fieldIn(B, off, CB, depth + 1))
              return L;
          // A call that returns the pointer held at the start of an argument
          // yields that argument. The opener then reads the path it holds.
          if (B && off == 0 && CB->getType()->isPointerTy()) {
            for (BasicBlock &BB : *B) {
              auto *R = dyn_cast<ReturnInst>(BB.getTerminator());
              if (!R || !R->getReturnValue() || !R->getReturnValue()->getType()->isPointerTy())
                continue;
              Value *rb = nullptr;
              int64_t ro = 0;
              baseOff(R->getReturnValue(), rb, ro);
              if (auto *Ld = dyn_cast<LoadInst>(rb))
                baseOff(Ld->getPointerOperand(), rb, ro);
              auto *Arg = dyn_cast<Argument>(rb);
              if (!Arg || Arg->getParent() != B || ro != 0 || Arg->getArgNo() >= CB->arg_size())
                continue;
              if (auto L = find(F, CB->getArgOperand(Arg->getArgNo()), depth + 1)) {
                pathPtr.insert({L->arg, L->suf});
                return L;
              }
            }
          }
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
      for (Function *F : fnOrder) {
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
          for (Function *G : fnOrder) {
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
        for (size_t before = SIZE_MAX; before != th.size() + boxes.size();) {
          before = th.size() + boxes.size();
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
    // A pointer and the integer that follows it are a buffer when the callee
    // reads that many bytes through the pointer. The bytes are the cell the
    // pointer locates to. A lookup stays a witness only when no later call
    // that is not a lookup reads that cell or a cell inside it.
    {
      // The one materialization bound. An object no access bounds and whose
      // count is a free input is this large; nothing above it is built.
      const uint64_t kExtentCap = 1ull << 20;
      auto rootOf = [&](size_t si, Value *V, Loc &cell) -> bool {
        return cellLoc(memAt(si), V, cell) && !cell.suf.empty();
      };
      // The entry cells a value may be, across calls. A term is the address
      // of a cell, the value a cell holds, or the address of a local of some
      // frame. A formal is what its caller bound. A load of a local is every
      // store into it, including the stores a callee makes through the
      // address it was passed. A call is every return of every target,
      // evaluated with its actuals bound to its formals. Constants, fresh
      // objects and arithmetic are no entry cell and contribute nothing.
      //
      // The evaluation is a function of the value, its environment, and the
      // functions on the call string: a call to a function already on the
      // call string contributes nothing, so call strings are acyclic. The
      // equations a loop makes cyclic are solved as their least fixpoint, by
      // rounds in which a value under evaluation reads the previous round's
      // approximation, until a round changes nothing. A path that repeats a
      // field step is a position inside a recursive structure, not a fixed
      // cell, and contributes nothing. Paths without a repeated step over the
      // finite set of field steps are finite, so the fixpoint exists and the
      // rounds end, and its value does not depend on the order of evaluation.
      struct Term {
        int arg = -1;
        Suffix suf;
        bool val = false;
        const AllocaInst *local = nullptr;
        std::string lname;
        bool operator<(const Term &o) const {
          return std::tie(arg, suf, val, lname) < std::tie(o.arg, o.suf, o.val, o.lname);
        }
        bool operator==(const Term &o) const {
          return std::tie(arg, suf, val, lname) == std::tie(o.arg, o.suf, o.val, o.lname);
        }
      };
      using Terms = std::set<Term>;
      std::map<std::string, Terms> evDone, evRound, evPrev;
      std::set<std::string> evBusy;
      std::unordered_set<const Function *> active;
      std::set<std::string> activeNames;
      std::map<const AllocaInst *, std::string> localName;
      auto nameOf = [&](const AllocaInst *A) -> const std::string & {
        auto it = localName.find(A);
        if (it != localName.end())
          return it->second;
        unsigned pos = 0;
        for (const Instruction &I : instructions(*A->getFunction())) {
          if (&I == A)
            break;
          ++pos;
        }
        return localName[A] = A->getFunction()->getName().str() + "#" + std::to_string(pos);
      };
      auto repeats = [](const Suffix &suf, const Step &s) {
        for (const Step &x : suf)
          if (x.type == s.type && x.off == s.off && x.deref == s.deref)
            return true;
        return false;
      };
      auto envKey = [&](const Function *F, const Value *V, const std::vector<Terms> &env) {
        std::string k = std::to_string(reinterpret_cast<uintptr_t>(F)) + "/" + std::to_string(reinterpret_cast<uintptr_t>(V));
        for (const Terms &ts : env) {
          k += "|";
          for (const Term &t : ts) {
            k += "{" + std::to_string(t.arg) + (t.val ? "v" : "a") + t.lname;
            for (const Step &s : t.suf)
              k += ";" + s.type + "@" + std::to_string(s.off) + (s.deref ? "*" : "");
            k += "}";
          }
        }
        k += "#";
        for (const std::string &a : activeNames)
          k += a + ",";
        return k;
      };
      auto enter = [&](Function *T) {
        active.insert(T);
        activeNames.insert(T->getName().str());
      };
      auto leave = [&](Function *T) {
        active.erase(T);
        activeNames.erase(T->getName().str());
      };
      std::function<Terms(Function *, Value *, const std::vector<Terms> &)> ev;
      std::function<Terms(Function *, const std::vector<Terms> &, const AllocaInst *)> storesTo;
      auto bind = [&](Function *F, CallBase *CB, const std::vector<Terms> &env, Function *T) {
        std::vector<Terms> g(T->arg_size());
        for (unsigned a = 0; a < T->arg_size() && a < CB->arg_size(); ++a)
          g[a] = ev(F, CB->getArgOperand(a), env);
        return g;
      };
      auto bodies = [&](CallBase *CB) {
        std::vector<Function *> out;
        if (Function *C = CB->getCalledFunction())
          if (C->isIntrinsic())
            return out;
        for (Function *T : targetsOf(CB))
          if (T && !T->isDeclaration() && !active.count(T))
            out.push_back(T);
        return out;
      };
      auto holdsLocal = [](const Terms &ts, const AllocaInst *A) {
        for (const Term &t : ts)
          if (t.local == A && t.suf.empty())
            return true;
        return false;
      };
      storesTo = [&](Function *T, const std::vector<Terms> &env, const AllocaInst *A) -> Terms {
        Terms r;
        for (Instruction &I : instructions(*T)) {
          if (auto *S = dyn_cast<StoreInst>(&I)) {
            if (holdsLocal(ev(T, S->getPointerOperand(), env), A)) {
              Terms v = ev(T, S->getValueOperand(), env);
              r.insert(v.begin(), v.end());
            }
            continue;
          }
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          bool passes = false;
          for (Value *Op : CB->args())
            if (Op->getType()->isPointerTy() && holdsLocal(ev(T, Op, env), A))
              passes = true;
          if (!passes)
            continue;
          for (Function *T2 : bodies(CB)) {
            std::vector<Terms> g = bind(T, CB, env, T2);
            enter(T2);
            Terms v = storesTo(T2, g, A);
            leave(T2);
            r.insert(v.begin(), v.end());
          }
        }
        return r;
      };
      ev = [&](Function *F, Value *V, const std::vector<Terms> &env) -> Terms {
        if (!V)
          return {};
        std::string k = envKey(F, V, env);
        if (auto it = evDone.find(k); it != evDone.end())
          return it->second;
        if (auto it = evRound.find(k); it != evRound.end())
          return it->second;
        if (!evBusy.insert(k).second) {
          auto it = evPrev.find(k);
          return it == evPrev.end() ? Terms{} : it->second;
        }
        Terms r;
        auto add = [&](const Terms &ts) { r.insert(ts.begin(), ts.end()); };
        if (auto *A = dyn_cast<Argument>(V)) {
          if (A->getParent() == F && A->getArgNo() < env.size())
            add(env[A->getArgNo()]);
        } else if (auto *C = dyn_cast<CastInst>(V)) {
          add(ev(F, C->getOperand(0), env));
        } else if (auto *Fr = dyn_cast<FreezeInst>(V)) {
          add(ev(F, Fr->getOperand(0), env));
        } else if (auto *G = dyn_cast<GEPOperator>(V)) {
          Step st;
          bool constant = constStep(dl, G, st);
          bool structVar = !G->hasAllConstantIndices() && isa<StructType>(G->getSourceElementType());
          for (Term t : ev(F, G->getPointerOperand(), env)) {
            if (t.local) {
              if (constant && st.off == 0)
                r.insert(t);
              continue;
            }
            if (structVar)
              continue;
            if (!G->hasAllConstantIndices()) {
              r.insert(t);
              continue;
            }
            if (!constant)
              continue;
            Step s = st;
            s.deref = t.val;
            if (movesAddress(s)) {
              if (repeats(t.suf, s))
                continue;
              t.suf.push_back(s);
              t.val = false;
            }
            r.insert(t);
          }
        } else if (auto *CE = dyn_cast<ConstantExpr>(V)) {
          if (CE->isCast())
            add(ev(F, CE->getOperand(0), env));
        } else if (auto *L = dyn_cast<LoadInst>(V)) {
          Value *Ptr = L->getPointerOperand()->stripPointerCasts();
          auto *Al = dyn_cast<AllocaInst>(Ptr);
          if (Al && Al->getFunction() == F) {
            for (User *U : Al->users()) {
              if (auto *S = dyn_cast<StoreInst>(U)) {
                if (S->getPointerOperand()->stripPointerCasts() == Al)
                  add(ev(F, S->getValueOperand(), env));
                continue;
              }
              auto *CB = dyn_cast<CallBase>(U);
              if (!CB)
                continue;
              for (Function *T : bodies(CB)) {
                std::vector<Terms> g = bind(F, CB, env, T);
                enter(T);
                add(storesTo(T, g, Al));
                leave(T);
              }
            }
          } else {
            for (Term t : ev(F, Ptr, env)) {
              if (t.local)
                continue;
              if (t.val) {
                Step s{"", 0, true};
                if (repeats(t.suf, s))
                  continue;
                t.suf.push_back(s);
              }
              t.val = true;
              r.insert(t);
            }
          }
        } else if (auto *CB = dyn_cast<CallBase>(V)) {
          for (Function *T : bodies(CB)) {
            std::vector<Terms> g = bind(F, CB, env, T);
            enter(T);
            for (BasicBlock &BB : *T)
              if (auto *R = dyn_cast<ReturnInst>(BB.getTerminator()))
                if (R->getReturnValue())
                  add(ev(T, R->getReturnValue(), g));
            leave(T);
          }
        } else if (auto *Phi = dyn_cast<PHINode>(V)) {
          for (Value *In : Phi->incoming_values())
            if (!isa<UndefValue>(In) && !isa<ConstantPointerNull>(In))
              add(ev(F, In, env));
        } else if (auto *Sel = dyn_cast<SelectInst>(V)) {
          add(ev(F, Sel->getTrueValue(), env));
          add(ev(F, Sel->getFalseValue(), env));
        } else if (auto *Al = dyn_cast<AllocaInst>(V)) {
          Term t;
          t.local = Al;
          t.lname = nameOf(Al);
          r.insert(t);
        }
        evBusy.erase(k);
        evRound[k] = r;
        return r;
      };
      // The least fixpoint of the equations V reaches.
      auto solveAt = [&](Function *F, Value *V, const std::vector<Terms> &env) {
        evPrev.clear();
        for (;;) {
          evRound.clear();
          Terms r = ev(F, V, env);
          if (evRound == evPrev) {
            evDone.insert(evRound.begin(), evRound.end());
            evRound.clear();
            return r;
          }
          evPrev = std::move(evRound);
        }
      };
      std::vector<std::optional<std::vector<Terms>>> envAt(seq.size());
      // The entry cells whose value V may be, at a step of the sequence.
      auto valuesOf = [&](size_t si, Value *V) {
        std::vector<Loc> out;
        Loc L;
        if (cellLoc(memAt(si), V, L) && L.pointee && !L.suf.empty()) {
          out.push_back(L);
          return out;
        }
        if (!envAt[si]) {
          std::vector<Terms> env(seq[si]->arg_size());
          Mem &m = memAt(si);
          for (Argument &A : seq[si]->args())
            if (auto it = m.loc.find(&A); it != m.loc.end()) {
              Term t;
              t.arg = it->second.arg;
              t.suf = it->second.suf;
              t.val = it->second.pointee;
              env[A.getArgNo()].insert(t);
            }
          envAt[si] = std::move(env);
        }
        for (const Term &t : solveAt(seq[si], V, *envAt[si]))
          if (t.arg >= 0 && !t.local && t.val && !t.suf.empty())
            out.push_back(Loc{t.arg, t.suf, true});
        return out;
      };
      auto writeSuf = [&](int arg, const Suffix &suf) {
        out << " arg" << arg;
        for (const Step &st : suf)
          out << " " << st.type << "+" << st.off << (st.deref ? "*" : "");
      };
      auto growCell = [&](const Loc &cell, uint64_t n) {
        cells.insert({cell.arg, cell.suf});
        Suffix child = cell.suf;
        child.push_back(Step{"", 0, true});
        cells.insert({cell.arg, child});
        auto key = std::make_pair(cell.arg, child);
        auto it = readBytes.find(key);
        if (it == readBytes.end() || it->second < n)
          readBytes[key] = n;
      };
      // Returns whether some entry cell now holds the n bytes.
      auto grow = [&](size_t si, Value *Buf, uint64_t n) -> bool {
        if (!n || n > kExtentCap)
          return false;
        // A buffer at a cell's own address is inside the entry object; one
        // whose address a cell holds is that cell's pointee.
        Loc cell;
        if (rootOf(si, Buf, cell)) {
          if (cell.pointee)
            growCell(cell, n);
          else {
            cells.insert({cell.arg, cell.suf});
            auto key = std::make_pair(cell.arg, cell.suf);
            auto it = readBytes.find(key);
            if (it == readBytes.end() || it->second < n)
              readBytes[key] = n;
          }
          return true;
        }
        std::vector<Loc> held = valuesOf(si, Buf);
        for (const Loc &c : held) {
          growCell(c, n);
          out << "bytes";
          writeSuf(c.arg, c.suf);
          out << " " << n << "\n";
        }
        return !held.empty();
      };
      std::map<std::tuple<const Function *, unsigned, unsigned>, bool> lenMemo;
      std::function<bool(Function *, unsigned, unsigned)> usedAsLen =
          [&](Function *F, unsigned p, unsigned n) -> bool {
        if (!F || F->isDeclaration() || p >= F->arg_size() || n >= F->arg_size())
          return false;
        auto key = std::make_tuple(F, p, n);
        if (auto it = lenMemo.find(key); it != lenMemo.end())
          return it->second;
        lenMemo[key] = false;
        auto derivesArg = [&](Value *V, unsigned arg) {
          std::unordered_set<const Value *> seen;
          while (V && seen.insert(V).second) {
            if (auto *A = dyn_cast<Argument>(V->stripPointerCasts()))
              return A->getArgNo() == arg;
            if (auto *C = dyn_cast<CastInst>(V)) {
              V = C->getOperand(0);
              continue;
            }
            if (auto *G = dyn_cast<GEPOperator>(V)) {
              V = G->getPointerOperand();
              continue;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (!Al)
                return false;
              Value *st = nullptr;
              for (User *U : Al->users())
                if (auto *S = dyn_cast<StoreInst>(U))
                  if (S->getPointerOperand()->stripPointerCasts() == Al)
                    st = S->getValueOperand();
              V = st;
              continue;
            }
            return false;
          }
          return false;
        };
        // An index names the same storage across -O0 reloads: the local it is
        // loaded from, else the value itself.
        auto indexRoot = [](Value *V) -> const Value * {
          while (auto *C = dyn_cast<CastInst>(V))
            V = C->getOperand(0);
          if (auto *L = dyn_cast<LoadInst>(V))
            if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
              return A;
          return V;
        };
        bool yes = false;
        std::unordered_set<const Value *> indices;
        for (Instruction &I : instructions(*F))
          if (auto *G = dyn_cast<GetElementPtrInst>(&I))
            if (!G->hasAllConstantIndices() && derivesArg(G->getPointerOperand(), p))
              for (Value *Ix : G->indices())
                if (!isa<Constant>(Ix))
                  indices.insert(indexRoot(Ix));
        for (Instruction &I : instructions(*F)) {
          // The pointer is indexed by a value compared with the count.
          if (auto *C = dyn_cast<ICmpInst>(&I))
            for (unsigned s = 0; s < 2; ++s)
              if (derivesArg(C->getOperand(s), n) && indices.count(indexRoot(C->getOperand(1 - s))))
                yes = true;
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          Function *Cal = CB->getCalledFunction();
          if (Cal && (Cal->getName().starts_with("llvm.memcpy") || Cal->getName().starts_with("llvm.memmove"))) {
            if (CB->arg_size() >= 3 &&
                (derivesArg(CB->getArgOperand(0), p) || derivesArg(CB->getArgOperand(1), p)) &&
                derivesArg(CB->getArgOperand(2), n))
              yes = true;
          }
          if (!Cal)
            continue;
          Function *D = define(Cal->getName());
          if (!D)
            D = Cal;
          for (unsigned i = 0; i + 1 < CB->arg_size() && i < D->arg_size(); ++i) {
            if (!derivesArg(CB->getArgOperand(i), p) || !CB->getArgOperand(i)->getType()->isPointerTy())
              continue;
            if (!derivesArg(CB->getArgOperand(i + 1), n) || !CB->getArgOperand(i + 1)->getType()->isIntegerTy())
              continue;
            if (D->isDeclaration()) {
              if (CB->onlyReadsMemory(i) || D->onlyReadsMemory())
                yes = true;
            } else if (i + 1 < D->arg_size() && usedAsLen(D, i, i + 1))
              yes = true;
          }
        }
        lenMemo[key] = yes;
        return yes;
      };
      // A pointer stored into a field of a local is the value a callee loads
      // back from that field. The bytes read are the uses of the reloaded
      // pointer.
      std::function<uint64_t(Function *, unsigned)> carried =
          [&](Function *F, unsigned arg) -> uint64_t {
        if (!F || F->isDeclaration() || arg >= F->arg_size())
          return 0;
        std::unordered_set<const Function *> seen;
        uint64_t n = pointedExtent(F, F->getArg(arg), seen, 0);
        auto derivesArg = [&](Value *V) {
          std::unordered_set<const Value *> seenV;
          while (V && seenV.insert(V).second) {
            if (auto *A = dyn_cast<Argument>(V->stripPointerCasts()))
              return A->getArgNo() == arg;
            if (auto *C = dyn_cast<CastInst>(V)) {
              V = C->getOperand(0);
              continue;
            }
            if (auto *G = dyn_cast<GEPOperator>(V)) {
              V = G->getPointerOperand();
              continue;
            }
            if (auto *L = dyn_cast<LoadInst>(V)) {
              auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
              if (!Al)
                return false;
              Value *st = nullptr;
              for (User *U : Al->users())
                if (auto *S = dyn_cast<StoreInst>(U))
                  if (S->getPointerOperand()->stripPointerCasts() == Al)
                    st = S->getValueOperand();
              V = st;
              continue;
            }
            return false;
          }
          return false;
        };
        struct Put {
          const AllocaInst *A;
          int64_t off;
        };
        std::vector<Put> puts;
        for (Instruction &I : instructions(*F)) {
          auto *S = dyn_cast<StoreInst>(&I);
          if (!S || !S->getValueOperand()->getType()->isPointerTy() || !derivesArg(S->getValueOperand()))
            continue;
          auto *G = dyn_cast<GEPOperator>(S->getPointerOperand()->stripPointerCasts());
          auto *A = dyn_cast<AllocaInst>(G ? G->getPointerOperand()->stripPointerCasts() : S->getPointerOperand()->stripPointerCasts());
          if (!A)
            continue;
          int64_t off = 0;
          if (G) {
            APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
            if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta))
              continue;
            off = delta.getSExtValue();
          }
          puts.push_back({A, off});
        }
        for (const Put &put : puts) {
          for (Instruction &I : instructions(*F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (!CB)
              continue;
            Function *Cal = CB->getCalledFunction();
            Function *D = Cal ? define(Cal->getName()) : nullptr;
            if (!D || D->isDeclaration())
              continue;
            for (unsigned k = 0; k < CB->arg_size() && k < D->arg_size(); ++k) {
              if (CB->getArgOperand(k)->stripPointerCasts() != put.A)
                continue;
              for (Instruction &J : instructions(*D)) {
                auto *L = dyn_cast<LoadInst>(&J);
                if (!L || !L->getType()->isPointerTy())
                  continue;
                auto *G = dyn_cast<GEPOperator>(L->getPointerOperand()->stripPointerCasts());
                if (!G)
                  continue;
                Value *base = G->getPointerOperand()->stripPointerCasts();
                bool from = false;
                if (auto *A = dyn_cast<Argument>(base))
                  from = A->getArgNo() == k;
                else if (auto *Ld = dyn_cast<LoadInst>(base)) {
                  auto *Al = dyn_cast<AllocaInst>(Ld->getPointerOperand()->stripPointerCasts());
                  if (Al)
                    for (User *U : Al->users())
                      if (auto *St = dyn_cast<StoreInst>(U))
                        if (St->getPointerOperand()->stripPointerCasts() == Al)
                          if (auto *Ag = dyn_cast<Argument>(St->getValueOperand()->stripPointerCasts()))
                            from = Ag->getArgNo() == k;
                }
                if (!from)
                  continue;
                APInt delta(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
                if (!G->hasAllConstantIndices() || !G->accumulateConstantOffset(dl, delta))
                  continue;
                if (delta.getSExtValue() != put.off)
                  continue;
                std::unordered_set<const Function *> seenL;
                n = std::max(n, pointedExtent(D, L, seenL, 0));
              }
            }
          }
        }
        return n;
      };
      struct Site {
        size_t si = 0;
        Instruction *at = nullptr;
        const Function *callee = nullptr;
        std::vector<std::pair<int, Suffix>> roots;
      };
      std::vector<Site> sites;
      for (size_t si = 0; si < seq.size(); ++si) {
        if (!seq[si] || seq[si]->isDeclaration())
          continue;
        for (Instruction &I : instructions(*seq[si])) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->isDebugOrPseudoInst())
            continue;
          Function *Cal = CB->getCalledFunction();
          if (Cal && ignorable(Cal))
            continue;
          Copy copied = fixedCopy(*CB);
          if (copied.ok)
            grow(si, CB->getArgOperand(copied.src), copied.len);
          Function *D = Cal ? define(Cal->getName()) : nullptr;
          if (!D)
            D = Cal;
          for (unsigned i = 0; i + 1 < CB->arg_size(); ++i) {
            Value *Buf = CB->getArgOperand(i);
            Value *Cnt = CB->getArgOperand(i + 1);
            if (!Buf->getType()->isPointerTy() || !Cnt->getType()->isIntegerTy())
              continue;
            bool input = false;
            if (!D || D->isDeclaration())
              input = CB->onlyReadsMemory(i) || (D && D->onlyReadsMemory());
            else if (i + 1 < D->arg_size())
              input = usedAsLen(D, i, i + 1) || pairRead(D, i, i + 1);
            if (!input)
              continue;
            uint64_t n = 0;
            if (auto *C = dyn_cast<ConstantInt>(Cnt)) {
              if (!C->isNegative() && C->getBitWidth() <= 64)
                n = C->getZExtValue();
            }
            if (!n) {
              std::unordered_set<const Function *> seenF;
              n = pointedExtent(seq[si], Buf, seenF, 0);
            }
            if (!n && D && !D->isDeclaration() && i < D->arg_size())
              n = carried(D, i);
            // The count is itself an entry cell, a free input, and no access
            // bounds it. The bytes number that free count, so the only limit
            // is the materialization cap.
            std::vector<Loc> counts;
            if (!isa<ConstantInt>(Cnt)) {
              Loc lenCell;
              if (rootOf(si, Cnt, lenCell))
                counts.push_back(lenCell);
              else
                counts = valuesOf(si, Cnt);
            }
            if (!n && !counts.empty())
              n = kExtentCap;
            if (!grow(si, Buf, n))
              continue;
            // The callee reads Cnt bytes through Buf, and the harness holds n
            // bytes there, so every entry cell the count may be is at most n.
            // A sign extension reads the cell as signed.
            Value *raw = Cnt;
            bool sext = false;
            while (auto *C = dyn_cast<CastInst>(raw)) {
              sext = sext || isa<SExtInst>(C);
              raw = C->getOperand(0);
            }
            unsigned bits = raw->getType()->isIntegerTy() ? raw->getType()->getIntegerBitWidth() : 64;
            uint64_t most = n;
            if (bits < 64)
              most = std::min<uint64_t>(most, sext ? (1ull << (bits - 1)) - 1 : (1ull << bits) - 1);
            for (const Loc &c : counts) {
              cells.insert({c.arg, c.suf});
              CountCap &cap = countCap[{c.arg, c.suf}];
              if (!cap.most || most < cap.most)
                cap.most = most;
              cap.bytes = std::max(1u, bits / 8);
              out << "count";
              writeSuf(c.arg, c.suf);
              out << " ule " << cap.most << "\n";
            }
          }
          Site s;
          s.si = si;
          s.at = CB;
          s.callee = D;
          for (Value *Op : CB->args()) {
            if (!Op->getType()->isPointerTy())
              continue;
            Loc L;
            if (rootOf(si, Op, L))
              s.roots.push_back({L.arg, L.suf});
          }
          if (!s.roots.empty())
            sites.push_back(std::move(s));
        }
      }
      auto under = [](const Suffix &inner, const Suffix &outer) {
        if (outer.size() > inner.size())
          return false;
        for (size_t i = 0; i < outer.size(); ++i)
          if (inner[i].type != outer[i].type || inner[i].off != outer[i].off || inner[i].deref != outer[i].deref)
            return false;
        return true;
      };
      for (auto &kv : stepEv) {
        for (Ev &e : kv.second) {
          if (e.kind != 'q' || !e.at)
            continue;
          const Site *here = nullptr;
          for (const Site &s : sites)
            if (s.at == e.at) {
              here = &s;
              break;
            }
          if (!here)
            continue;
          for (const Site &s : sites) {
            if (s.at == here->at)
              continue;
            bool after = s.si > here->si || (s.si == here->si && dominatesBefore(here->at, s.at));
            if (!after)
              continue;
            if (s.callee && lookupOnly(s.callee))
              continue;
            bool hit = false;
            for (const auto &a : here->roots)
              for (const auto &b : s.roots)
                if (a.first == b.first && under(b.second, a.second))
                  hit = true;
            if (!hit)
              continue;
            e.live = true;
            for (const auto &a : here->roots) {
              cells.insert(a);
              std::unordered_set<const Function *> seenF;
              uint64_t n = 0;
              bool held = false;
              for (Value *Op : cast<CallBase>(here->at)->args()) {
                Loc L;
                if (rootOf(here->si, Op, L) && L.arg == a.first && L.suf == a.second) {
                  n = std::max(n, pointedExtent(seq[here->si], Op, seenF, 0));
                  held = held || L.pointee;
                }
              }
              if (n && n <= kExtentCap) {
                Suffix child = a.second;
                if (held)
                  child.push_back(Step{"", 0, true});
                cells.insert({a.first, child});
                auto it = readBytes.find({a.first, child});
                if (it == readBytes.end() || it->second < n)
                  readBytes[{a.first, child}] = n;
              }
            }
            break;
          }
        }
      }
    }
