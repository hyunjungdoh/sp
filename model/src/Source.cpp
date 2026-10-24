#include "Source.h"

#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>

using namespace llvm;

namespace source {
namespace {

struct State {
  std::map<std::string, const DICompositeType *> defs;
  std::unordered_map<const Value *, const DIType *> memo;
  std::unordered_set<const Value *> open;
  std::map<std::string, StructType *> ir;
  Stats stats;
};

State &state() {
  static State s;
  return s;
}

bool qualifier(unsigned tag) {
  return tag == dwarf::DW_TAG_typedef || tag == dwarf::DW_TAG_const_type || tag == dwarf::DW_TAG_volatile_type ||
         tag == dwarf::DW_TAG_restrict_type || tag == dwarf::DW_TAG_atomic_type;
}

// T without typedefs and qualifiers; the innermost typedef name in alias.
const DIType *strip(const DIType *T, StringRef *alias = nullptr) {
  while (auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
    if (!qualifier(D->getTag()))
      break;
    if (alias && D->getTag() == dwarf::DW_TAG_typedef)
      *alias = D->getName();
    T = D->getBaseType();
  }
  return T;
}

bool pointerLike(const DIType *T) {
  auto *D = dyn_cast_or_null<DIDerivedType>(T);
  return D && (D->getTag() == dwarf::DW_TAG_pointer_type || D->getTag() == dwarf::DW_TAG_reference_type ||
               D->getTag() == dwarf::DW_TAG_rvalue_reference_type);
}

bool record(const DICompositeType *C) {
  auto t = C->getTag();
  return t == dwarf::DW_TAG_structure_type || t == dwarf::DW_TAG_class_type || t == dwarf::DW_TAG_union_type;
}

// The IR spelling of a source composite: struct.N, class.ns::N, union.N.
std::string qualified(const DICompositeType *C, StringRef alias) {
  std::string n = C->getName().str();
  if (n.empty())
    n = alias.str();
  if (n.empty())
    return "";
  for (const DIScope *S = C->getScope(); S; S = S->getScope()) {
    StringRef sn;
    if (isa<DINamespace>(S))
      sn = S->getName().empty() ? StringRef("(anonymous namespace)") : S->getName();
    else if (isa<DICompositeType>(S))
      sn = S->getName();
    else
      break;
    if (sn.empty())
      break;
    n = sn.str() + "::" + n;
  }
  const char *pre = C->getTag() == dwarf::DW_TAG_class_type   ? "class."
                    : C->getTag() == dwarf::DW_TAG_union_type ? "union."
                                                              : "struct.";
  return pre + n;
}

// The composite T denotes, with its definition when T only declares it.
const DICompositeType *composite(const DIType *T, StringRef *alias = nullptr) {
  StringRef a;
  auto *C = dyn_cast_or_null<DICompositeType>(strip(T, &a));
  if (alias)
    *alias = a;
  if (!C || !record(C))
    return nullptr;
  if (!C->isForwardDecl())
    return C;
  auto it = state().defs.find(qualified(C, a));
  return it == state().defs.end() ? C : it->second;
}

uint64_t bits(const DIType *T) {
  T = strip(T);
  if (auto *C = dyn_cast_or_null<DICompositeType>(T))
    if (record(C))
      if (const DICompositeType *D = composite(C))
        return D->getSizeInBits();
  return T ? T->getSizeInBits() : 0;
}

const DIType *deref(const DIType *T) {
  T = strip(T);
  return pointerLike(T) ? cast<DIDerivedType>(T)->getBaseType() : nullptr;
}

bool same(const DIType *A, const DIType *B) {
  if (A == B)
    return true;
  StringRef aa, ba;
  const DICompositeType *CA = composite(A, &aa), *CB = composite(B, &ba);
  return CA && CB && qualified(CA, aa) == qualified(CB, ba);
}

// The type of the object a GEP addresses, following its IR indices through
// the source members at the same offsets.
const DIType *through(const GEPOperator *G, const DataLayout &dl) {
  const DIType *D = pointee(G->getPointerOperand());
  if (!D)
    return nullptr;
  Type *T = G->getSourceElementType();
  auto idx = G->idx_begin();
  if (idx == G->idx_end())
    return D;
  if (!T->isAggregateType() && G->getNumIndices() == 1) {
    auto *K = dyn_cast<ConstantInt>(*idx);
    return K && K->isZero() ? D : (T->isSized() && bits(D) == 8 * dl.getTypeAllocSize(T) ? D : nullptr);
  }
  for (++idx; idx != G->idx_end() && D; ++idx) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      unsigned i = (unsigned)cast<ConstantInt>(*idx)->getZExtValue();
      Type *E = ST->getElementType(i);
      D = member(D, dl.getStructLayout(ST)->getElementOffset(i), E->isSized() ? dl.getTypeAllocSize(E) : 0);
      T = E;
    } else if (auto *AT = dyn_cast<ArrayType>(T)) {
      D = element(D);
      T = AT->getElementType();
    } else if (auto *VT = dyn_cast<VectorType>(T)) {
      D = element(D);
      T = VT->getElementType();
    } else
      return nullptr;
  }
  return D;
}

std::string base(const std::string &n) {
  auto dot = n.find_last_of('.');
  if (dot != std::string::npos && dot + 1 < n.size() &&
      n.find_first_not_of("0123456789", dot + 1) == std::string::npos && n.compare(0, dot, "struct") &&
      n.compare(0, dot, "class") && n.compare(0, dot, "union"))
    return n.substr(0, dot);
  return n;
}

// Every field of S sits at the offset of a member of C: the source layout
// is the IR layout, the condition under which the linker merges the two.
bool fits(const DICompositeType *C, StructType *S, const DataLayout &dl) {
  if (!S->isSized() || C->getSizeInBits() != 8 * dl.getTypeAllocSize(S))
    return false;
  std::set<uint64_t> at;
  for (const DINode *N : C->getElements())
    if (auto *M = dyn_cast<DIDerivedType>(N))
      if ((M->getTag() == dwarf::DW_TAG_member || M->getTag() == dwarf::DW_TAG_inheritance) && !M->isStaticMember())
        at.insert(M->getOffsetInBits() / 8);
  if (C->getTag() == dwarf::DW_TAG_union_type)
    return true;
  const StructLayout *L = dl.getStructLayout(S);
  for (unsigned i = 0; i < S->getNumElements(); ++i) {
    Type *E = S->getElementType(i);
    if (E->isArrayTy() && cast<ArrayType>(E)->getElementType()->isIntegerTy(8))
      continue;
    if (!at.count(L->getElementOffset(i)))
      return false;
  }
  return true;
}

} // namespace

void index(Module &M) {
  DebugInfoFinder F;
  F.processModule(M);
  for (DIType *T : F.types())
    if (auto *C = dyn_cast<DICompositeType>(T))
      if (record(C) && !C->isForwardDecl() && !C->getName().empty())
        state().defs.emplace(qualified(C, ""), C);
}

void reset() {
  State &s = state();
  s.defs.clear();
  s.memo.clear();
  s.open.clear();
  s.ir.clear();
  s.stats = Stats{};
}

const DIType *ofGlobal(const GlobalVariable &G) {
  SmallVector<DIGlobalVariableExpression *, 1> es;
  G.getDebugInfo(es);
  for (auto *E : es)
    if (E->getExpression()->getNumElements() == 0)
      return E->getVariable()->getType();
  return nullptr;
}

const DIType *member(const DIType *D, uint64_t off, uint64_t size) {
  const DICompositeType *C = composite(D);
  if (!C)
    return nullptr;
  const DIType *any = nullptr;
  unsigned count = 0;
  for (const DINode *N : C->getElements()) {
    auto *M = dyn_cast<DIDerivedType>(N);
    if (!M || (M->getTag() != dwarf::DW_TAG_member && M->getTag() != dwarf::DW_TAG_inheritance) ||
        M->isStaticMember() || M->isBitField() || M->getOffsetInBits() != 8 * off)
      continue;
    const DIType *T = M->getBaseType();
    if (size && bits(T) == 8 * size)
      return T;
    any = T;
    ++count;
  }
  return count == 1 ? any : nullptr;
}

const DIType *element(const DIType *D) {
  auto *C = dyn_cast_or_null<DICompositeType>(strip(D));
  if (C && (C->getTag() == dwarf::DW_TAG_array_type))
    return C->getBaseType();
  return nullptr;
}

const DIType *pointee(const Value *V) {
  if (!V)
    return nullptr;
  State &s = state();
  auto hit = s.memo.find(V);
  if (hit != s.memo.end())
    return hit->second;
  if (!s.open.insert(V).second)
    return nullptr;
  const DIType *r = nullptr;
  if (auto *C = dyn_cast<Operator>(V); C && (C->getOpcode() == Instruction::BitCast ||
                                             C->getOpcode() == Instruction::AddrSpaceCast))
    r = pointee(C->getOperand(0));
  else if (auto *A = dyn_cast<Argument>(V)) {
    const Function *F = A->getParent();
    DISubprogram *SP = F->getSubprogram();
    auto *ST = SP ? SP->getType() : nullptr;
    if (ST) {
      auto ts = ST->getTypeArray();
      unsigned shift = 0;
      for (unsigned k = 0; k < F->arg_size(); ++k)
        if (F->hasParamAttribute(k, Attribute::StructRet))
          ++shift;
      unsigned n = ts.size() > 0 && !ts[ts.size() - 1] ? ts.size() - 2 : ts.size() - 1;
      unsigned k = A->getArgNo();
      if (ts.size() > 0 && F->arg_size() == n + shift) {
        if (F->hasParamAttribute(k, Attribute::StructRet))
          r = deref(ts[0]);
        else {
          unsigned before = 0;
          for (unsigned j = 0; j < k; ++j)
            if (F->hasParamAttribute(j, Attribute::StructRet))
              ++before;
          const DIType *T = ts[k + 1 - before];
          r = A->hasByValAttr() || !pointerLike(strip(T)) ? (composite(T) ? T : nullptr) : deref(T);
        }
      }
    }
  } else if (auto *AI = dyn_cast<AllocaInst>(V)) {
    for (DbgDeclareInst *D : findDbgDeclares(const_cast<AllocaInst *>(AI)))
      if (D->getExpression()->getNumElements() == 0) {
        r = D->getVariable()->getType();
        break;
      }
  } else if (auto *G = dyn_cast<GlobalVariable>(V))
    r = ofGlobal(*G);
  else if (auto *G = dyn_cast<GEPOperator>(V)) {
    const DataLayout *dl = nullptr;
    if (auto *I = dyn_cast<Instruction>(V))
      dl = &I->getModule()->getDataLayout();
    else if (auto *GV = dyn_cast<GlobalValue>(G->getPointerOperand()->stripPointerCasts()))
      dl = &GV->getParent()->getDataLayout();
    if (dl)
      r = through(G, *dl);
  } else if (auto *L = dyn_cast<LoadInst>(V))
    r = deref(pointee(L->getPointerOperand()));
  else if (auto *CB = dyn_cast<CallBase>(V)) {
    if (auto *F = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts()))
      if (DISubprogram *SP = F->getSubprogram())
        if (auto *ST = SP->getType())
          if (ST->getTypeArray().size() > 0)
            r = deref(ST->getTypeArray()[0]);
  } else if (isa<PHINode>(V) || isa<SelectInst>(V)) {
    std::vector<const Value *> ins;
    if (auto *P = dyn_cast<PHINode>(V))
      for (const Value *I : P->incoming_values())
        ins.push_back(I);
    else
      ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
    bool agree = true;
    for (const Value *I : ins) {
      if (isa<ConstantPointerNull>(I) || isa<UndefValue>(I) || s.open.count(I))
        continue;
      const DIType *T = pointee(I);
      if (!T || (r && !same(r, T))) {
        agree = false;
        break;
      }
      r = T;
    }
    if (!agree)
      r = nullptr;
  }
  s.open.erase(V);
  s.memo[V] = r;
  return r;
}

std::string name(const DIType *D) {
  StringRef alias;
  const DICompositeType *C = composite(D, &alias);
  return C ? qualified(C, alias) : "";
}

std::string key(const DIType *D, StructType *S, const DataLayout &dl) {
  if (!S || !S->hasName())
    return "";
  State &s = state();
  std::string ir = base(S->getName().str());
  StringRef alias;
  const DICompositeType *C = composite(D, &alias);
  std::string src = C ? qualified(C, alias) : "";
  std::string out = ir;
  if (src.empty() || C->isForwardDecl() || !fits(C, S, dl))
    ++s.stats.ir;
  else {
    ++s.stats.source;
    if (ir != src) {
      // A source type whose own IR struct has another layout than S is
      // accessed through a cast to S; the access is S's.
      StructType *own = StructType::getTypeByName(S->getContext(), src);
      if (!own || own->isOpaque() || own->isLayoutIdentical(S)) {
        ++s.stats.renamed;
        out = src;
      }
    }
  }
  s.ir.emplace(out, S);
  return out;
}

std::string container(const GEPOperator *G, const DataLayout &dl) {
  auto *S = dyn_cast<StructType>(G->getSourceElementType());
  if (!S || !S->hasName())
    return "";
  return key(pointee(G->getPointerOperand()), S, dl);
}

std::vector<std::pair<std::string, int64_t>> levels(const GEPOperator *G, const DataLayout &dl) {
  std::vector<std::pair<std::string, int64_t>> out;
  if (!G->hasAllConstantIndices())
    return out;
  APInt total(dl.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
  if (!G->accumulateConstantOffset(dl, total))
    return out;
  Type *T = G->getSourceElementType();
  const DIType *D = pointee(G->getPointerOperand());
  int64_t rest = total.getSExtValue();
  auto idx = G->idx_begin();
  if (idx != G->idx_end()) {
    if (!T->isSized())
      return out;
    rest -= cast<ConstantInt>(*idx)->getSExtValue() * (int64_t)dl.getTypeAllocSize(T);
    ++idx;
    if (rest < 0)
      return out;
  }
  for (;;) {
    auto *STy = dyn_cast<StructType>(T);
    if (STy && STy->hasName())
      out.push_back({key(D, STy, dl), rest});
    if (idx == G->idx_end())
      break;
    int64_t i = cast<ConstantInt>(*idx)->getSExtValue();
    ++idx;
    if (STy) {
      uint64_t o = dl.getStructLayout(STy)->getElementOffset((unsigned)i);
      rest -= (int64_t)o;
      T = STy->getElementType((unsigned)i);
      D = D ? member(D, o, T->isSized() ? dl.getTypeAllocSize(T) : 0) : nullptr;
    } else if (auto *AT = dyn_cast<ArrayType>(T)) {
      rest -= i * (int64_t)dl.getTypeAllocSize(AT->getElementType());
      T = AT->getElementType();
      D = D ? element(D) : nullptr;
    } else
      break;
  }
  return out;
}

StructType *irType(const std::string &name) {
  auto it = state().ir.find(name);
  return it == state().ir.end() ? nullptr : it->second;
}

const Stats &stats() { return state().stats; }

} // namespace source
