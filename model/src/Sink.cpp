// §3.12 싱크 가드와 싱크 의존 (DESIGN-D.md).
//
// 두 사실을 may 층의 증인에 더한다.
//
// 1. 싱크 가드 G(s). 싱크 함수 f_n의 CFG 위에서 싱크 블록에 이르는 조건을 제어
//    의존으로 계산한 DNF다. G(b)는 블록 b에서 싱크에 이르는 조건이고,
//    G(싱크 블록) = ⊤, 싱크에 닿지 않는 블록은 ⊥, 조건 분기 b: c ? T : F 는
//    (c ∧ G(T)) ∨ (¬c ∧ G(F))다. 두 후계자의 G가 같으면 c는 사라지므로(흡수) 싱크와
//    무관한 분기는 공식에 남지 않는다. 단락 평가(||, &&)는 두 분기로 내려오므로 이
//    재귀가 그대로 논리합·논리곱을 만든다. 역방향 간선은 ⊥이고(한 번의 통과),
//    싱크를 담지 않는 루프 안의 분기는 리터럴 없이 두 후계자의 합이다(반복마다 값이
//    달라 한 값에 대한 사실이 아니다). 모든 절에 드는 리터럴이 must 가드(sinkmust),
//    절마다 남는 것이 대안(sinkalt)이다.
//
//    리터럴의 피연산자는 셀이 f_0의 인자에서 도달하지 않아도(loc=⊥) 적는다. 자리는
//    그 명령이 속한 함수의 형식인자·지역·전역에서 시작하는 접근 경로로 쓴다
//    (`arg0 class.LibRaw+1234 struct.libraw_image_sizes_t+8`). 셀·상수가 아닌
//    피연산자(곱, 호출 결과)는 식 그대로 적는다(정의 A가 사영으로 버리던 것).
//
// 2. 싱크 의존. 가드 리터럴의 피연산자와 싱크 명령의 피연산자에서 시작해 값 흐름을
//    거슬러 간다. SSA 연산은 피연산자로, 필드의 적재는 f_0의 호출 닫힘 안에서 같은 필드
//    (소스 구조체 이름, 오프셋)에 쓰는 store의 값으로(§3.10의 필드 기반 칸과 같은 추상),
//    형식인자는 호출 문맥이 있으면 그 호출 지점의 실인자로, 없으면 닫힘 안 모든 호출
//    지점의 실인자로(간접 호출은 Tgt), 정의된 피호출자의 결과는 그 반환값으로, φ는
//    들어온 값과 그 간선을 고른 분기 조건으로, 할당의 포인터는 그 정수 인자로 잇는다.
//    멈추는 출처는 다섯이다: 이름 조회(§3.8.6의 G(o, κ, d); 결과가
//    κ의 설정값이므로 `named "κ"`), 몸체 없는 읽기(`file`), f_0의 인자(`arg`), 전역
//    (`global`), 그 밖의 몸체 없는 호출(`ext`). 이것이 §3.8.6 측정(1729)의
//    "half_size는 φ에 없다"를 메운다: 싱크의 복사 크기가 IO.shrink를 거쳐
//    get_int_attribute("raw:half_size")에 의존한다는 사실이 증인에 남고, 하네스는 그
//    설정을 시드 경로에 올린다.
#include "Model.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/DebugInfo.h"

namespace {

struct Lit {
  Value *v;
  bool pos;
};
using Clause = std::vector<Lit>;
// DNF: 절의 집합. 빈 집합은 ⊥, 빈 절 하나는 ⊤.
using DNF = std::vector<Clause>;
const size_t kMaxClauses = 64, kMaxLits = 32, kMaxDepth = 12;
// Set when disj/conj exceeded kMaxClauses and returned ⊤; the DNF then holds
// no alternatives, and the must set comes from the dominator rule below.
bool gCapped = false;

DNF top() { return DNF{Clause{}}; }
DNF bottom() { return DNF{}; }
bool isTop(const DNF &d) {
  for (const Clause &c : d)
    if (c.empty())
      return true;
  return false;
}

bool addLit(Clause &c, const Lit &l) {
  for (const Lit &x : c)
    if (x.v == l.v)
      return x.pos == l.pos;
  c.push_back(l);
  return true;
}

bool sameClause(const Clause &a, const Clause &b) {
  if (a.size() != b.size())
    return false;
  for (const Lit &l : a) {
    bool f = false;
    for (const Lit &m : b)
      f = f || (m.v == l.v && m.pos == l.pos);
    if (!f)
      return false;
  }
  return true;
}

DNF disj(DNF a, const DNF &b) {
  if (isTop(a) || isTop(b))
    return top();
  for (const Clause &y : b) {
    bool dup = false;
    for (const Clause &x : a)
      dup = dup || sameClause(x, y);
    if (!dup)
      a.push_back(y);
    if (a.size() > kMaxClauses) {
      gCapped = true;
      return top(); // 상한을 넘으면 대안을 버린다(과근사); must는 지배자 규칙이 지킨다
    }
  }
  return a;
}

DNF conj(const DNF &a, const DNF &b) {
  DNF r;
  for (const Clause &x : a)
    for (const Clause &y : b) {
      Clause c = x;
      bool ok = true;
      for (const Lit &l : y)
        if (!addLit(c, l)) {
          ok = false;
          break;
        }
      if (!ok || c.size() > kMaxLits)
        continue;
      bool dup = false;
      for (const Clause &z : r)
        dup = dup || sameClause(z, c);
      if (!dup)
        r.push_back(c);
      if (r.size() > kMaxClauses)
        return top();
    }
  return r;
}

Value *stripCasts(Value *V) {
  while (auto *C = dyn_cast<CastInst>(V))
    V = C->getOperand(0);
  return V;
}

// i1 값 V가 need일 조건의 DNF.
DNF cond(Value *V, bool need, unsigned depth = 0) {
  V = stripCasts(V);
  if (depth > kMaxDepth)
    return DNF{Clause{Lit{V, need}}};
  if (auto *CI = dyn_cast<ConstantInt>(V))
    return (CI->isZero() != need) ? top() : bottom();
  if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    auto *One = dyn_cast<ConstantInt>(BO->getOperand(1));
    if (BO->getOpcode() == Instruction::Xor && One && One->isOne())
      return cond(BO->getOperand(0), !need, depth + 1);
    if (BO->getOpcode() == Instruction::And || BO->getOpcode() == Instruction::Or) {
      bool andLike = (BO->getOpcode() == Instruction::And) == need;
      DNF a = cond(BO->getOperand(0), need, depth + 1), b = cond(BO->getOperand(1), need, depth + 1);
      return andLike ? conj(a, b) : disj(a, b);
    }
  }
  if (auto *S = dyn_cast<SelectInst>(V)) {
    if (S->getType()->isIntegerTy(1)) {
      DNF c1 = cond(S->getCondition(), true, depth + 1), c0 = cond(S->getCondition(), false, depth + 1);
      return disj(conj(c1, cond(S->getTrueValue(), need, depth + 1)), conj(c0, cond(S->getFalseValue(), need, depth + 1)));
    }
  }
  return DNF{Clause{Lit{V, need}}};
}

// 접근 경로 철자: 기저(argN | local:name | @global | ret:fn | phi | ?)와 바깥부터
// 안쪽 순서의 구조체 층 "<struct>+<off>", 적재는 "*".
std::string spellPath(Value *P, const DataLayout &dl, unsigned depth = 0) {
  std::vector<std::string> layers;
  std::string base;
  Value *V = P;
  while (true) {
    V = stripCasts(V);
    if (auto *G = dyn_cast<GEPOperator>(V)) {
      APInt off(dl.getIndexTypeSizeInBits(G->getType()), 0);
      std::string name;
      if (isa<StructType>(G->getSourceElementType())) {
        name = source::container(G, dl);
        if (name.empty())
          name = "struct";
      }
      if (G->accumulateConstantOffset(dl, off))
        layers.push_back(name + "+" + std::to_string(off.getSExtValue()));
      else
        layers.push_back(name + "+?");
      V = G->getPointerOperand();
      continue;
    }
    if (auto *L = dyn_cast<LoadInst>(V)) {
      layers.push_back("*");
      V = L->getPointerOperand();
      continue;
    }
    if (auto *A = dyn_cast<Argument>(V)) {
      base = "arg" + std::to_string(A->getArgNo());
    } else if (auto *Al = dyn_cast<AllocaInst>(V)) {
      // -O0 비트코드: 형식인자는 자기 슬롯에 한 번 저장된다. 그 슬롯의 적재는 인자
      // 자체다(argN). 그 밖의 지역은 디버그 이름, 없으면 ?.
      Argument *held = nullptr;
      unsigned stores = 0;
      for (User *U : Al->users())
        if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Al) {
          ++stores;
          held = dyn_cast<Argument>(S->getValueOperand());
        }
      if (stores == 1 && held) {
        base = "arg" + std::to_string(held->getArgNo());
        if (!layers.empty() && layers.back() == "*")
          layers.pop_back(); // 슬롯의 적재는 인자 값 자체다.
      } else {
        std::string nm = Al->hasName() ? Al->getName().str() : "";
        if (nm.empty())
          for (DbgDeclareInst *D : findDbgDeclares(Al))
            if (D->getVariable()) {
              nm = D->getVariable()->getName().str();
              break;
            }
        base = "local:" + (nm.empty() ? std::string("?") : nm);
      }
    } else if (auto *GV = dyn_cast<GlobalVariable>(V)) {
      base = "@" + GV->getName().str();
    } else if (auto *CB = dyn_cast<CallBase>(V)) {
      Function *F = CB->getCalledFunction();
      base = "ret:" + (F ? F->getName().str() : std::string("indirect"));
    } else if (isa<PHINode>(V)) {
      base = "phi";
    } else if (isa<ConstantPointerNull>(V)) {
      base = "null";
    } else {
      base = "?";
    }
    break;
  }
  std::string s = base;
  for (auto it = layers.rbegin(); it != layers.rend(); ++it)
    s += " " + *it;
  return s;
}

std::string spellValue(Value *V, const DataLayout &dl, unsigned depth = 0) {
  V = stripCasts(V);
  if (auto *CI = dyn_cast<ConstantInt>(V))
    return "k:" + std::to_string(CI->getSExtValue());
  if (isa<ConstantPointerNull>(V))
    return "k:0";
  if (auto *L = dyn_cast<LoadInst>(V))
    return "[" + spellPath(L->getPointerOperand(), dl) + "]";
  if (auto *A = dyn_cast<Argument>(V))
    return "arg" + std::to_string(A->getArgNo());
  if (auto *CB = dyn_cast<CallBase>(V)) {
    Function *F = CB->getCalledFunction();
    std::string s = "call:" + (F ? F->getName().str() : std::string("indirect"));
    if (const DebugLoc &DL = CB->getDebugLoc())
      s += "@" + std::to_string(DL.getLine());
    return s;
  }
  if (depth >= 3)
    return "...";
  if (auto *BO = dyn_cast<BinaryOperator>(V))
    return std::string(BO->getOpcodeName()) + "(" + spellValue(BO->getOperand(0), dl, depth + 1) + "," +
           spellValue(BO->getOperand(1), dl, depth + 1) + ")";
  if (auto *S = dyn_cast<SelectInst>(V))
    return "select(" + spellValue(S->getCondition(), dl, depth + 1) + "," + spellValue(S->getTrueValue(), dl, depth + 1) +
           "," + spellValue(S->getFalseValue(), dl, depth + 1) + ")";
  if (auto *P = dyn_cast<PHINode>(V)) {
    std::string s = "phi(";
    for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
      s += (i ? "," : "") + spellValue(P->getIncomingValue(i), dl, depth + 1);
    return s + ")";
  }
  if (auto *G = dyn_cast<GEPOperator>(V))
    return "&" + spellPath(G, dl);
  return "?";
}

std::string spellLit(const Lit &l, const DataLayout &dl) {
  if (auto *C = dyn_cast<ICmpInst>(l.v)) {
    ICmpInst::Predicate p = l.pos ? C->getPredicate() : C->getInversePredicate();
    return spellValue(C->getOperand(0), dl) + " " + std::string(ICmpInst::getPredicateName(p)) + " " +
           spellValue(C->getOperand(1), dl);
  }
  return spellValue(l.v, dl) + (l.pos ? " ne k:0" : " eq k:0");
}

// 주소의 필드 열쇠: 가장 안쪽 구조체 층 (구조체 이름, 오프셋). 층이 없으면 비어 있다.
std::pair<std::string, int64_t> fieldKey(Value *P, const DataLayout &dl) {
  Value *V = P;
  while (true) {
    V = stripCasts(V);
    auto *G = dyn_cast<GEPOperator>(V);
    if (!G)
      return {};
    // 가장 안쪽 구조체 층이 열쇠다. `p->b.c`와 `q->c`는 둘 다 안쪽 층 (B, o_c)를 가진다
    // (§3.10 층 규칙의 접미 관계와 같은 추상). 이름은 source::container: 링크가 붙인
    // 숫자 접미사 없이, 소스 타입으로 정규화한 이름(Source.h). 컴파일 단위마다 다른
    // 접미사가 붙은 같은 구조체(OIIO 쪽 libraw_output_params_t.N)가 한 열쇠가 된다.
    APInt off(dl.getIndexTypeSizeInBits(G->getType()), 0);
    if (isa<StructType>(G->getSourceElementType()) && G->accumulateConstantOffset(dl, off)) {
      std::string name = source::container(G, dl);
      if (!name.empty())
        return {name, off.getSExtValue()};
    }
    V = G->getPointerOperand();
  }
}

std::string cstr(Value *V) {
  auto *G = dyn_cast<GlobalVariable>(V->stripPointerCasts());
  auto *A = G && G->hasInitializer() ? dyn_cast<ConstantDataArray>(G->getInitializer()) : nullptr;
  return A && A->isCString() ? A->getAsCString().str() : "";
}

// 호출 CB의 j번째 실인자가 담는 상수 텍스트. 인자가 상수 문자열이면 그것이고, 지역
// 슬롯이면(string_view 같은 값 전달) 그 슬롯을 채우는, CB를 지배하는 마지막 호출이
// 넘긴 상수 문자열이다(Client::named와 같은 규칙).
std::string keyText(CallBase *CB, unsigned j, std::map<Function *, std::unique_ptr<DominatorTree>> &dts) {
  Value *Op = CB->getArgOperand(j);
  if (std::string k = cstr(Op); !k.empty())
    return k;
  auto *Slot = dyn_cast<AllocaInst>(Op->stripPointerCasts());
  if (!Slot)
    return "";
  Function *F = CB->getFunction();
  auto &dt = dts[F];
  if (!dt)
    dt = std::make_unique<DominatorTree>(*F);
  CallBase *best = nullptr;
  std::string got;
  for (User *U : Slot->users()) {
    auto *W = dyn_cast<CallBase>(U);
    if (!W || W == CB || !W->getCalledFunction() || !dt->dominates(W, CB) || (best && !dt->dominates(best, W)))
      continue;
    bool slot = false;
    std::string text;
    for (unsigned a = 0; a < W->arg_size(); ++a) {
      Value *Arg = W->getArgOperand(a);
      if (Arg->stripPointerCasts() == Slot)
        slot = true;
      else if (std::string k = cstr(Arg); !k.empty() && text.empty())
        text = k;
    }
    if (slot && !text.empty()) {
      best = W;
      got = text;
    }
  }
  return got;
}

struct Index {
  // 프로그램 전체: 필드 (구조체, 오프셋) → 그 필드에 쓰는 store들.
  std::map<std::pair<std::string, int64_t>, std::vector<StoreInst *>> fieldStores;
  // 함수 → 그 함수를 부르는 호출 지점(직접·간접 Tgt).
  std::unordered_map<const Function *, std::vector<CallBase *>> callers;
  bool built = false;
};

} // namespace

void Model::sinkFacts(const std::vector<Function *> &seq, raw_ostream &out) {
  if (seq.empty())
    return;
  Function *Sink = seq.back();
  std::vector<Instruction *> sinks;
  for (Instruction &I : instructions(*Sink))
    if (sinkHere(I, sinkFile, sinkLine))
      sinks.push_back(&I);
  if (sinks.empty())
    return;
  size_t sn = seq.size() - 1;

  // ---- 1. 싱크 가드 ----
  std::unordered_set<const BasicBlock *> sinkBlocks, back;
  for (Instruction *I : sinks)
    sinkBlocks.insert(I->getParent());
  {
    std::vector<const BasicBlock *> work(sinkBlocks.begin(), sinkBlocks.end());
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!back.insert(B).second)
        continue;
      for (const BasicBlock *P : predecessors(B))
        work.push_back(P);
    }
  }
  // 역방향 간선: 진입에서의 DFS.
  std::set<std::pair<const BasicBlock *, const BasicBlock *>> backEdges;
  {
    enum { W, G, B };
    std::unordered_map<const BasicBlock *, int> color;
    std::unordered_map<const BasicBlock *, std::vector<const BasicBlock *>> succs;
    for (const BasicBlock &BB : *Sink)
      succs[&BB].assign(succ_begin(&BB), succ_end(&BB));
    std::vector<std::pair<const BasicBlock *, size_t>> st;
    const BasicBlock *E = &Sink->getEntryBlock();
    color[E] = G;
    st.push_back({E, 0});
    while (!st.empty()) {
      const BasicBlock *Bk = st.back().first;
      size_t &i = st.back().second;
      const std::vector<const BasicBlock *> &ss = succs[Bk];
      if (i >= ss.size()) {
        color[Bk] = B;
        st.pop_back();
        continue;
      }
      const BasicBlock *S = ss[i++];
      int c = color.count(S) ? color[S] : W;
      if (c == G)
        backEdges.insert({Bk, S});
      else if (c == W) {
        color[S] = G;
        st.push_back({S, 0});
      }
    }
  }
  DominatorTree DT(*Sink);
  LoopInfo LI(DT);
  std::unordered_map<const BasicBlock *, DNF> memo;
  std::function<DNF(const BasicBlock *)> Gf = [&](const BasicBlock *Bk) -> DNF {
    if (sinkBlocks.count(Bk))
      return top();
    if (!back.count(Bk))
      return bottom();
    auto it = memo.find(Bk);
    if (it != memo.end())
      return it->second;
    memo[Bk] = bottom(); // 순환 보호
    auto succG = [&](const BasicBlock *S) { return backEdges.count({Bk, S}) ? bottom() : Gf(S); };
    const Instruction *T = Bk->getTerminator();
    DNF r = bottom();
    if (auto *BR = dyn_cast<BranchInst>(T)) {
      if (!BR->isConditional() || BR->getSuccessor(0) == BR->getSuccessor(1)) {
        r = succG(BR->getSuccessor(0));
      } else {
        DNF gT = succG(BR->getSuccessor(0)), gF = succG(BR->getSuccessor(1));
        Loop *L = LI.getLoopFor(Bk);
        bool loopOut = L && std::none_of(sinkBlocks.begin(), sinkBlocks.end(),
                                         [&](const BasicBlock *S) { return L->contains(S); });
        if (loopOut || (gT.size() == gF.size() && std::equal(gT.begin(), gT.end(), gF.begin(), sameClause)))
          r = disj(gT, gF);
        else
          r = disj(conj(cond(BR->getCondition(), true), gT), conj(cond(BR->getCondition(), false), gF));
      }
    } else if (auto *SW = dyn_cast<SwitchInst>(T)) {
      // 케이스 값은 리터럴로 싣지 않는다(정의 P: 목표에 닿는 케이스가 하나일 때만 원자).
      std::set<const BasicBlock *> seen;
      for (const BasicBlock *S : successors(SW))
        if (seen.insert(S).second)
          r = disj(r, succG(S));
    } else if (auto *IV = dyn_cast<InvokeInst>(T)) {
      r = succG(IV->getNormalDest());
    } else {
      for (const BasicBlock *S : successors(Bk))
        r = disj(r, succG(S));
    }
    memo[Bk] = r;
    return r;
  };
  gCapped = false;
  DNF G = Gf(&Sink->getEntryBlock());
  bool capped = gCapped;
  std::vector<Lit> must;
  auto addMust = [&](const Lit &l) {
    for (const Lit &m : must)
      if (m.v == l.v && m.pos == l.pos)
        return;
    must.push_back(l);
  };
  if (!G.empty() && !capped) {
    for (const Lit &l : G.front()) {
      bool all = true;
      for (const Clause &c : G) {
        bool f = false;
        for (const Lit &m : c)
          f = f || (m.v == l.v && m.pos == l.pos);
        all = all && f;
      }
      if (all)
        addMust(l);
    }
  }
  // 지배자 규칙: 모든 싱크 블록을 지배하는 조건 분기에서 후계자 하나만 싱크에 닿으면
  // 그 쪽의 조건은 모든 경로의 조건이다. DNF 상한과 무관하게 성립하고, 상한을 넘어
  // 대안을 버린 경우에도 must는 여기서 나온다. 싱크를 담지 않는 루프 안의 분기는
  // 공식과 같은 이유로 뺀다.
  for (const BasicBlock *Bk : back) {
    auto *BR = dyn_cast<BranchInst>(Bk->getTerminator());
    if (!BR || !BR->isConditional() || BR->getSuccessor(0) == BR->getSuccessor(1))
      continue;
    bool domAll = true;
    for (const BasicBlock *S : sinkBlocks)
      domAll = domAll && DT.dominates(Bk, S);
    if (!domAll)
      continue;
    Loop *L = LI.getLoopFor(Bk);
    if (L && std::none_of(sinkBlocks.begin(), sinkBlocks.end(), [&](const BasicBlock *S) { return L->contains(S); }))
      continue;
    bool t = back.count(BR->getSuccessor(0)) && !backEdges.count({Bk, BR->getSuccessor(0)});
    bool f = back.count(BR->getSuccessor(1)) && !backEdges.count({Bk, BR->getSuccessor(1)});
    if (t == f)
      continue;
    DNF c = cond(BR->getCondition(), t);
    // 한 절뿐일 때만 리터럴의 논리곱이다(두 절이면 논리합이라 must가 아니다).
    if (c.size() == 1)
      for (const Lit &l : c.front())
        addMust(l);
  }
  out << "sinkguard " << sn << " " << Sink->getName() << " clauses " << G.size() << " must " << must.size()
      << (capped ? " capped" : "") << "\n";
  for (const Lit &l : must) {
    out << "sinkmust " << sn << " " << spellLit(l, dl);
    if (auto *I = dyn_cast<Instruction>(l.v))
      if (const DebugLoc &DL = I->getDebugLoc())
        out << " line " << DL.getLine();
    out << "\n";
  }
  for (const Clause &c : G) {
    std::vector<std::string> rest;
    for (const Lit &l : c) {
      bool isMust = false;
      for (const Lit &m : must)
        isMust = isMust || (m.v == l.v && m.pos == l.pos);
      if (!isMust)
        rest.push_back(spellLit(l, dl));
    }
    if (rest.empty())
      continue;
    out << "sinkalt " << sn;
    for (size_t i = 0; i < rest.size(); ++i)
      out << (i ? " ; " : " ") << rest[i];
    out << "\n";
  }

  // ---- 2. 싱크 의존 ----
  if (!sinkIdx) {
    auto idx = std::make_shared<Index>();
    for (Module *M : {&down, &up})
      for (Function &F : *M) {
        if (F.isDeclaration())
          continue;
        for (Instruction &I : instructions(F)) {
          if (auto *S = dyn_cast<StoreInst>(&I)) {
            auto k = fieldKey(S->getPointerOperand(), dl);
            if (!k.first.empty())
              idx->fieldStores[k].push_back(S);
          } else if (auto *CB = dyn_cast<CallBase>(&I)) {
            if (Function *C = CB->getCalledFunction()) {
              if (Function *D = define(C->getName()))
                idx->callers[D].push_back(CB);
              else
                idx->callers[C].push_back(CB);
            } else {
              for (Function *T : targetsOf(CB))
                idx->callers[T].push_back(CB);
            }
          }
        }
      }
    idx->built = true;
    sinkIdx = idx;
  }
  Index &idx = *static_cast<Index *>(sinkIdx.get());

  // 시드는 출처 종류(guard, alt, sink)마다 한 집합이다. 출처는 종류별로만 적으므로 한
  // 종류의 시드들은 한 번의 걸음(공유 방문 집합)으로 간다.
  struct Seed {
    std::string from;
    std::vector<Value *> vs;
  };
  std::vector<Seed> seeds{{"guard", {}}, {"alt", {}}, {"sink", {}}};
  auto addLitSeeds = [](std::vector<Value *> &into, const Lit &l) {
    if (auto *C = dyn_cast<ICmpInst>(l.v)) {
      into.push_back(C->getOperand(0));
      into.push_back(C->getOperand(1));
    } else
      into.push_back(l.v);
  };
  for (const Lit &l : must)
    addLitSeeds(seeds[0].vs, l);
  for (const Clause &c : G)
    for (const Lit &l : c)
      addLitSeeds(seeds[1].vs, l);
  for (Instruction *I : sinks)
    for (Value *Op : I->operands())
      if (!isa<BasicBlock>(Op) && !isa<Function>(Op))
        seeds[2].vs.push_back(Op);

  std::set<std::string> lines;
  std::map<Function *, std::unique_ptr<DominatorTree>> dts;
  const size_t kMaxNodes = 4000000;
  // 호출 문맥(호출 문자열). 피호출자의 반환값으로 내려간 걸음은 (호출 지점, 피호출자)를
  // 쌓고, 그 피호출자의 형식인자는 그 호출 지점의 실인자로만 돌아간다(실현 가능한
  // 경로만; std::min<int> 같은 공용 함수가 프로그램 전체의 호출자로 번지지 않는다).
  // 문맥이 비면(출발 함수의 형식인자, 필드 store로 건너뛴 뒤) 모든 호출자다. 깊이
  // kCtx를 넘으면 가장 오래된 것을 버린다(그 아래는 모든 호출자로 근사).
  const size_t kCtx = 8;
  using Ctx = std::vector<std::pair<CallBase *, Function *>>;
  struct Node {
    Value *v;
    Ctx ctx;
  };
  struct NodeHash {
    size_t operator()(const std::pair<Value *, Ctx> &k) const {
      size_t h = std::hash<Value *>()(k.first);
      for (const auto &c : k.second)
        h = h * 1000003u ^ std::hash<CallBase *>()(c.first) ^ (std::hash<Function *>()(c.second) << 1);
      return h;
    }
  };
  std::map<std::string, std::pair<size_t, bool>> stats; // from → (nodes, capped)
  // 진단(SP_SINK_TRACE=1): 방문한 함수와 노드 수를 stderr에 적는다.
  const bool trace = getenv("SP_SINK_TRACE") != nullptr;
  std::map<const Function *, size_t> visited;
  std::set<std::pair<std::string, int64_t>> tracedKeys;
  // 하네스가 실행하는 코드는 f_0의 호출 닫힘이다(§4: f_0 호출 하나). 그 밖의 함수에
  // 있는 store·호출 지점은 이 실행에서 일어나지 않으므로 정의가 아니다(필드 기반
  // def-use를 프로그램 전체에서 실행 가능한 부분으로 좁히는 것; 닫힘 밖의 쓰기 —
  // 생성자·설정자 — 는 φ(§3.5)와 §3.8.6이 다룬다). 문맥이 있는 형식인자의 복귀는
  // 그 호출 지점이 이미 닫힘 안이므로 검사하지 않는다.
  auto runs = [&](Function *F) { return F == seq.front() || reachesFn(seq.front(), F); };
  for (const Seed &sd : seeds) {
    std::unordered_set<std::pair<Value *, Ctx>, NodeHash> seen;
    std::vector<Node> work;
    for (Value *v : sd.vs)
      work.push_back({v, {}});
    auto push = [&](Value *v, const Ctx &c) { work.push_back({v, c}); };
    auto origin = [&](const std::string &what) { lines.insert("sinkdep " + sd.from + " " + what); };
    auto done = [&]() {
      auto &st = stats[sd.from];
      st.first += seen.size();
      st.second = st.second || !work.empty();
    };
    while (!work.empty() && seen.size() < kMaxNodes) {
      Node nd = std::move(work.back());
      work.pop_back();
      Value *V = stripCasts(nd.v);
      const Ctx &ctx = nd.ctx;
      if (!V || !seen.insert({V, ctx}).second)
        continue;
      if (trace)
        if (auto *I = dyn_cast<Instruction>(V))
          visited[I->getFunction()]++;
      if (isa<ConstantInt>(V) || isa<ConstantPointerNull>(V) || isa<UndefValue>(V) || isa<ConstantFP>(V))
        continue;
      if (auto *GV = dyn_cast<GlobalVariable>(V)) {
        origin("global @" + GV->getName().str());
        continue;
      }
      if (isa<Constant>(V))
        continue;
      if (auto *A = dyn_cast<Argument>(V)) {
        Function *F = A->getParent();
        if (F == seq.front()) {
          origin("arg" + std::to_string(A->getArgNo()));
          continue;
        }
        if (!ctx.empty() && ctx.back().second == F) {
          CallBase *CB = ctx.back().first;
          if (A->getArgNo() < CB->arg_size())
            push(CB->getArgOperand(A->getArgNo()), Ctx(ctx.begin(), ctx.end() - 1));
          continue;
        }
        auto it = idx.callers.find(F);
        if (it == idx.callers.end())
          continue;
        for (CallBase *CB : it->second)
          if (A->getArgNo() < CB->arg_size() && runs(CB->getFunction()))
            push(CB->getArgOperand(A->getArgNo()), {});
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(V)) {
        Value *P = L->getPointerOperand()->stripPointerCasts();
        auto k = fieldKey(P, dl);
        if (!k.first.empty()) {
          auto it = idx.fieldStores.find(k);
          if (trace && tracedKeys.insert(k).second)
            errs() << "sinktrace-field " << k.first << "+" << k.second << " stores "
                   << (it == idx.fieldStores.end() ? 0 : it->second.size()) << " in " << L->getFunction()->getName() << "\n";
          if (it != idx.fieldStores.end())
            for (StoreInst *S : it->second)
              if (runs(S->getFunction()))
                push(S->getValueOperand(), {});
          continue;
        }
        if (auto *Al = dyn_cast<AllocaInst>(P)) {
          for (User *U : Al->users())
            if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Al)
              push(S->getValueOperand(), ctx);
          continue;
        }
        if (auto *GV = dyn_cast<GlobalVariable>(P)) {
          origin("global @" + GV->getName().str());
          for (User *U : GV->users())
            if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == GV)
              push(S->getValueOperand(), {});
          continue;
        }
        // 층 없는 주소(배열 원소 등): 그 기저 포인터의 출처가 곧 이 값의 출처다.
        push(P, ctx);
        continue;
      }
      if (auto *CB = dyn_cast<CallBase>(V)) {
        Function *C = CB->getCalledFunction();
        std::vector<Function *> targets;
        if (C) {
          if (Function *D = define(C->getName()))
            targets.push_back(D);
          else
            targets.push_back(C);
        } else
          targets = targetsOf(CB);
        bool stopped = false;
        for (Function *T : targets) {
          if (T->isDeclaration()) {
            Read rd = asRead(*CB);
            if (rd.ok)
              origin("file via " + T->getName().str());
            else
              origin("ext " + T->getName().str());
            // 새 객체(Origin.cpp isAlloc)의 값은 그 크기를 지닌다: 정수 인자가 객체의
            // 범위를 정하므로 포인터의 의존에 든다.
            if (isAlloc(*CB))
              for (Value *A : CB->args())
                if (A->getType()->isIntegerTy())
                  push(A, ctx);
            stopped = true;
            continue;
          }
          // §3.8.6 조회: 결과는 이름 κ의 설정값이다.
          if (T->getReturnType()->isIntegerTy() && lookupOnly(T)) {
            if (auto fb = fallbackArg(T)) {
              std::string key;
              for (unsigned j = 0; j < CB->arg_size(); ++j)
                if (j != *fb && key.empty())
                  key = keyText(CB, j, dts);
              if (!key.empty()) {
                std::string at = CB->getFunction()->getName().str();
                if (const DebugLoc &DL = CB->getDebugLoc())
                  at += " line " + std::to_string(DL.getLine());
                origin("named \"" + key + "\" lookup " + T->getName().str() + " at " + at);
                stopped = true;
                continue;
              }
            }
          }
          Ctx inner = ctx;
          inner.emplace_back(CB, T);
          if (inner.size() > kCtx)
            inner.erase(inner.begin());
          for (BasicBlock &BB : *T)
            if (auto *R = dyn_cast<ReturnInst>(BB.getTerminator()))
              if (R->getReturnValue())
                push(R->getReturnValue(), inner);
        }
        (void)stopped;
        continue;
      }
      if (auto *P = dyn_cast<PHINode>(V)) {
        // φ의 값은 들어온 값과, 그 들어온 간선을 고른 분기의 조건에 의존한다(-O0의
        // &&, ||, ?: 는 상수 true/false를 나르는 φ로 내려오므로 조건이 곧 값이다).
        // 간선을 고른 분기: 들어온 블록의 조건 분기, 아니면 유일한 선행자 사슬을
        // 거슬러 처음 만나는 조건 분기.
        for (unsigned i = 0; i < P->getNumIncomingValues(); ++i) {
          push(P->getIncomingValue(i), ctx);
          const BasicBlock *B = P->getIncomingBlock(i);
          std::unordered_set<const BasicBlock *> walked;
          while (B && walked.insert(B).second) {
            const Instruction *T = B->getTerminator();
            if (auto *BR = dyn_cast<BranchInst>(T); BR && BR->isConditional()) {
              push(BR->getCondition(), ctx);
              break;
            }
            if (auto *SW = dyn_cast<SwitchInst>(T)) {
              push(SW->getCondition(), ctx);
              break;
            }
            B = B->getUniquePredecessor();
          }
        }
        continue;
      }
      if (auto *U = dyn_cast<User>(V)) {
        if (isa<AllocaInst>(V)) {
          for (User *UU : V->users())
            if (auto *S = dyn_cast<StoreInst>(UU); S && S->getPointerOperand()->stripPointerCasts() == V)
              push(S->getValueOperand(), ctx);
          continue;
        }
        for (Value *Op : U->operands())
          if (!isa<BasicBlock>(Op) && !isa<Function>(Op))
            push(Op, ctx);
      }
    }
    done();
  }
  for (const auto &st : stats)
    out << "sinkdep " << st.first << " nodes " << st.second.first << (st.second.second ? " capped" : "") << "\n";
  if (trace)
    for (const auto &v : visited)
      errs() << "sinktrace " << sn << " " << v.first->getName() << " " << v.second << "\n";
  for (const std::string &s : lines)
    out << s << "\n";
}
