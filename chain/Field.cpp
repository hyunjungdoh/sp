#include "Field.hpp"

#include "llvm/Demangle/Demangle.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"

#include <cstdint>
#include <functional>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {
namespace {

constexpr int64_t Any = INT64_MIN;

struct Step {
  int parent = 0;
  int formal = -1;
  int type = 0;
  int64_t off = 0;
  uint64_t seen = 0;
};

struct InternKey {
  int parent, formal, type;
  int64_t off;
  bool operator==(const InternKey &o) const {
    return parent == o.parent && formal == o.formal && type == o.type && off == o.off;
  }
};

struct InternHash {
  size_t operator()(const InternKey &k) const {
    size_t h = (size_t)k.parent * 1315423911u;
    h ^= (size_t)k.formal + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= (size_t)k.type + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= (size_t)k.off + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};

struct VKey {
  const llvm::Value *v;
  int formal;
  int path;
  bool operator==(const VKey &o) const { return v == o.v && formal == o.formal && path == o.path; }
};

struct VHash {
  size_t operator()(const VKey &k) const {
    return ((size_t)k.v >> 4) ^ ((size_t)k.formal * 1315423911u) ^ ((size_t)k.path * 2654435761u);
  }
};

struct PairHash {
  size_t operator()(const std::pair<int, int64_t> &p) const {
    return (size_t)p.first * 1315423911u ^ (size_t)p.second;
  }
};

struct VecHash {
  size_t operator()(const std::vector<int> &v) const {
    size_t h = v.size();
    for (int x : v)
      h = h * 1315423911u + (size_t)x;
    return h;
  }
};

struct Slot {
  int formal = -1;
  int key = 0;
};

struct Ret {
  int formal = -1;
  int path = 0;
  int dep = 0;
  int fdep = 0;
  int sdep = 0;
};

struct Wr {
  int formal = -1;
  int path = 0;
  int64_t len = 0;
  int dep = 0;
  int fdep = 0;
  int sdep = 0;
  int key = 0;
  std::string fn;
};

struct CopySite {
  int df = -1, dp = 0, sf = -1, sp = 0;
  int64_t n = 0;
  bool anyN = true;
};

// kind 0 formal, 1 alloca or noalias return, 2 global, 3 open.
struct LiftFrom {
  int kind = 3;
  int formal = -1;
  int path = 0;
  std::string name;
  bool operator==(const LiftFrom &o) const {
    return kind == o.kind && formal == o.formal && path == o.path && name == o.name;
  }
};

struct ArgAt {
  std::vector<int> keys;
  std::vector<int> formals;
  std::vector<int> vformals;
  std::vector<LiftFrom> lift;
  int chain = 0;
};

struct Pub {
  int formal = -1;
  int slot = 0;
  int box = -1;
};

struct Site {
  llvm::Function *callee = nullptr;
  llvm::FunctionType *fty = nullptr;
  int calleeBox = -1;
  std::vector<int> calleeKeys;
  std::vector<ArgAt> args;
};

struct Edge {
  llvm::Function *fn = nullptr;
  int arg = -1;
};

struct FAHash {
  size_t operator()(const std::pair<llvm::Function *, int> &p) const {
    return ((size_t)p.first >> 4) ^ ((size_t)p.second * 1315423911u);
  }
};

struct FnSum {
  std::vector<Ret> rets;
  std::vector<Wr> writes;
  std::vector<CopySite> copies;
  std::vector<Site> sites;
  std::vector<Pub> pubs;
  std::vector<int> lineKeys;
  std::vector<int> nameKeys;
  std::vector<int> lineFormals;
  std::vector<int> nameFormals;
  std::vector<Edge> lineEdges;
  std::vector<Edge> nameEdges;
  std::vector<int> indirectKeys;
  bool hitLine = false;
  bool hitName = false;
  uint64_t retSig = 0;
  uint64_t fnSig = 0;
};

struct WRef {
  llvm::Function *fn = nullptr;
  Wr w;
};

class Engine {
 public:
  Engine(llvm::Module &down, llvm::Module &up, std::string file, unsigned line, std::vector<std::string> sinks)
      : down(down), up(up), file(std::move(file)), line(line), sinkFns(std::move(sinks)) {
    steps.push_back(Step{});
    deps.push_back({});
    fdeps.push_back({});
    slots.push_back(Slot{});
    sdeps.push_back({});
  }

  FieldReport run(const std::vector<std::string> &chops,
                        const std::unordered_map<std::string, std::vector<Input>> &inputs) {
    for (const std::string &c : chops)
      chopName.insert(c);
    for (const auto &kv : inputs)
      for (const Input &in : kv.second)
        if (in.arg >= 0)
          passIn.insert({in.func, in.arg});
    inMap = &inputs;
    index();
    callGraph();
    orderFns();
    solve();
    forwardCopies();
    return answer();
  }

 private:
  llvm::Module &down;
  llvm::Module &up;
  std::string file;
  unsigned line = 0;
  std::vector<std::string> sinkFns;
  bool anyLine = false;

  std::vector<Step> steps;
  std::unordered_map<InternKey, int, InternHash> interned;
  std::unordered_map<InternKey, int, InternHash> appendMemo;

  std::vector<std::string> typeName;
  std::unordered_map<std::string, int> typeByName;
  std::unordered_map<int, unsigned> typeElems;
  std::unordered_set<std::string> structNames;
  std::unordered_map<const llvm::StructType *, int> typeId;
  std::unordered_map<std::pair<int, int64_t>, int, PairHash> keys;
  std::unordered_map<InternKey, int, InternHash> chainMemo;
  int chainN = 1;
  std::vector<int> chainParent{0};
  std::vector<int> chainTy{0};
  std::vector<int64_t> chainOff{0};
  std::vector<std::vector<int>> deps;
  std::unordered_map<std::vector<int>, int, VecHash> depMemo;
  std::unordered_map<std::uint64_t, int> uniteMemo;
  std::vector<std::vector<int>> fdeps;
  std::unordered_map<std::vector<int>, int, VecHash> fdepMemo;
  std::unordered_map<std::uint64_t, int> funiteMemo;
  std::vector<Slot> slots;
  std::unordered_map<std::uint64_t, int> slotMemo;
  std::vector<std::vector<int>> sdeps;
  std::unordered_map<std::vector<int>, int, VecHash> sdepMemo;
  std::unordered_map<std::uint64_t, int> suniteMemo;

  std::unordered_map<std::string, llvm::Function *> byName;
  std::unordered_map<llvm::Function *, std::vector<llvm::Function *>> callers, callees;
  std::unordered_map<llvm::Function *, std::unordered_set<llvm::Function *>> indirectCallers;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> watchers;
  std::vector<llvm::Function *> order;
  std::unordered_map<llvm::Function *, int> ord;
  std::unordered_map<llvm::Function *, FnSum> sum;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> fnAt;
  // Functions stored through a call, keyed by the object's field chain and the inner slot.
  std::unordered_map<std::uint64_t, std::unordered_set<llvm::Function *>> held;
  std::vector<WRef> extra;
  std::set<std::string> chopName;
  std::set<std::pair<std::string, int>> passIn;
  const std::unordered_map<std::string, std::vector<Input>> *inMap = nullptr;
  std::unordered_set<int> pointerOnly;

  static bool allPointers(const llvm::StructType *T) {
    if (!T || T->isOpaque() || T->getNumElements() == 0)
      return false;
    for (llvm::Type *E : T->elements()) {
      if (E->isPointerTy())
        continue;
      if (const auto *A = llvm::dyn_cast<llvm::ArrayType>(E))
        if (A->getElementType()->isPointerTy())
          continue;
      return false;
    }
    return true;
  }

  llvm::Function *bodyOf(llvm::Function *F) {
    if (!F || F->isIntrinsic())
      return nullptr;
    if (!F->isDeclaration())
      return F;
    if (!F->hasName())
      return nullptr;
    auto it = byName.find(F->getName().str());
    return it == byName.end() ? nullptr : it->second;
  }

  std::string canonicalName(llvm::StringRef n) const {
    auto dot = n.rfind('.');
    if (dot == llvm::StringRef::npos || dot + 1 >= n.size())
      return n.str();
    for (size_t i = dot + 1; i < n.size(); ++i)
      if (n[i] < '0' || n[i] > '9')
        return n.str();
    std::string prefix = n.substr(0, dot).str();
    if (!structNames.count(prefix))
      return n.str();
    return prefix;
  }

  int internType(const llvm::StructType *T) {
    auto cached = typeId.find(T);
    if (cached != typeId.end())
      return cached->second;
    if (T->hasName()) {
      std::string n = canonicalName(T->getName());
      unsigned nEl = T->getNumElements();
      auto nit = typeByName.find(n);
      if (nit != typeByName.end() && typeElems[nit->second] == nEl) {
        typeId.emplace(T, nit->second);
        return nit->second;
      }
      if (nit != typeByName.end())
        n = T->getName().str();
      int id = (int)typeName.size() + 1;
      typeByName.emplace(n, id);
      typeElems.emplace(id, nEl);
      typeName.push_back(std::move(n));
      typeId.emplace(T, id);
      if (allPointers(T))
        pointerOnly.insert(id);
      return id;
    }
    int id = (int)typeName.size() + 1;
    typeName.push_back("anon" + std::to_string(id));
    typeId.emplace(T, id);
    if (allPointers(T))
      pointerOnly.insert(id);
    return id;
  }

  // A string is basic_string or string_view by declared name. A struct of
  // pointers, such as heif_track, is an object.
  bool stringTypeName(llvm::StringRef n) {
    return n.contains("basic_string") || n.contains("string_view");
  }

  bool diCharContainer(const llvm::DIType *T, int depth) {
    if (!T || depth > 8)
      return false;
    if (const auto *D = llvm::dyn_cast<llvm::DIDerivedType>(T)) {
      unsigned tag = D->getTag();
      if (tag == llvm::dwarf::DW_TAG_typedef || tag == llvm::dwarf::DW_TAG_const_type ||
          tag == llvm::dwarf::DW_TAG_restrict_type || tag == llvm::dwarf::DW_TAG_volatile_type ||
          tag == llvm::dwarf::DW_TAG_reference_type || tag == llvm::dwarf::DW_TAG_rvalue_reference_type ||
          tag == llvm::dwarf::DW_TAG_pointer_type || tag == llvm::dwarf::DW_TAG_member ||
          tag == llvm::dwarf::DW_TAG_inheritance)
        return diCharContainer(D->getBaseType(), depth + 1);
      return false;
    }
    if (llvm::isa<llvm::DIBasicType>(T))
      return false;
    const auto *C = llvm::dyn_cast<llvm::DICompositeType>(T);
    return C && stringTypeName(C->getName());
  }

  bool argDiChar(llvm::Function *Fn, int formal) {
    if (!Fn || Fn->isDeclaration() || formal < 0 || formal >= (int)Fn->arg_size())
      return false;
    const llvm::DIType *Ty = nullptr;
    for (llvm::Instruction &I : llvm::instructions(*Fn)) {
      const auto *D = llvm::dyn_cast<llvm::DbgDeclareInst>(&I);
      if (!D || !D->getVariable() || D->getVariable()->getArg() != (unsigned)formal + 1)
        continue;
      Ty = D->getVariable()->getType();
    }
    if (!Ty) {
      const llvm::Argument *A = Fn->getArg((unsigned)formal);
      for (llvm::DbgDeclareInst *D : llvm::findDbgDeclares(const_cast<llvm::Argument *>(A))) {
        if (!D || !D->getVariable() || D->getVariable()->getArg() != (unsigned)formal + 1)
          continue;
        Ty = D->getVariable()->getType();
      }
    }
    return Ty && diCharContainer(Ty, 0);
  }

  int internStep(int parent, int formal, int type, int64_t off) {
    if (parent > 0)
      formal = steps[parent].formal;
    InternKey k{parent, formal, type, off};
    auto it = interned.find(k);
    if (it != interned.end())
      return it->second;
    int id = (int)steps.size();
    uint64_t seen = parent > 0 ? steps[parent].seen : 0;
    seen |= 1ull << ((unsigned)type & 63);
    steps.push_back(Step{parent, formal, type, off, seen});
    interned.emplace(k, id);
    return id;
  }

  int append(int formal, int path, int type, int64_t off) {
    if (type > 0 && pointerOnly.count(type))
      return path;
    if (type <= 0 && off != Any)
      return path;
    InternKey memoKey{path, formal, type, off};
    auto mit = appendMemo.find(memoKey);
    if (mit != appendMemo.end())
      return mit->second;
    uint64_t bit = 1ull << ((unsigned)type & 63);
    int result;
    if (path <= 0 || (steps[path].seen & bit) == 0) {
      result = internStep(path, formal, type, off);
    } else {
      int repeat = 0;
      for (int p = path; p > 0; p = steps[p].parent)
        if (steps[p].type == type)
          repeat = p;
      if (repeat == 0 || steps[repeat].off == Any) {
        result = repeat == 0 ? internStep(path, formal, type, off) : repeat;
      } else {
        std::vector<int> prefix;
        for (int p = steps[repeat].parent; p > 0; p = steps[p].parent)
          prefix.push_back(p);
        int cur = 0;
        int f = formal;
        for (int j = (int)prefix.size() - 1; j >= 0; --j) {
          cur = internStep(cur, f, steps[prefix[j]].type, steps[prefix[j]].off);
          f = steps[cur].formal;
        }
        result = internStep(cur, f, type, Any);
      }
    }
    appendMemo.emplace(memoKey, result);
    return result;
  }

  int concat(int formal, int base, int ext) {
    std::vector<std::pair<int, int64_t>> suf;
    for (int p = ext; p > 0; p = steps[p].parent)
      suf.push_back({steps[p].type, steps[p].off});
    int cur = base;
    for (int i = (int)suf.size() - 1; i >= 0; --i)
      cur = append(formal, cur, suf[i].first, suf[i].second);
    return cur;
  }

  int keyAt(int type, int64_t off) {
    if (type <= 0)
      return 0;
    if (pointerOnly.count(type)) {
      auto e = typeElems.find(type);
      if (e == typeElems.end() || e->second < 2)
        return 0;
    }
    auto it = keys.find({type, off});
    if (it != keys.end())
      return it->second;
    int id = (int)keys.size() + 1;
    keys.emplace(std::pair<int, int64_t>{type, off}, id);
    return id;
  }

  int lastKey(int path) {
    if (path <= 0)
      return 0;
    return keyAt(steps[path].type, steps[path].off);
  }

  // Slot identity is the sequence of struct fields, outer field first.
  // Two puns of one LLVM struct match only when that sequence is the same.
  int slotStep(int parent, int type, int64_t off) {
    if (type <= 0)
      return parent;
    InternKey k{parent, 0, type, off};
    auto it = chainMemo.find(k);
    if (it != chainMemo.end())
      return it->second;
    int id = chainN++;
    chainMemo.emplace(k, id);
    if ((int)chainParent.size() <= id) {
      chainParent.resize((size_t)id + 1);
      chainTy.resize((size_t)id + 1);
      chainOff.resize((size_t)id + 1);
    }
    chainParent[(size_t)id] = parent;
    chainTy[(size_t)id] = type;
    chainOff[(size_t)id] = off;
    return id;
  }

  int pathToSlot(int path) {
    std::vector<std::pair<int, int64_t>> rev;
    for (int p = path; p > 0; p = steps[p].parent)
      rev.push_back({steps[p].type, steps[p].off});
    int cur = 0;
    for (int i = (int)rev.size() - 1; i >= 0; --i)
      cur = slotStep(cur, rev[i].first, rev[i].second);
    return cur;
  }

  static bool callTypeMatches(const llvm::Function *F, const llvm::FunctionType *Ty) {
    if (!Ty)
      return true;
    return F && F->getFunctionType() == Ty;
  }

  int internDep(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = depMemo.find(v);
    if (it != depMemo.end())
      return it->second;
    int id = (int)deps.size();
    depMemo.emplace(v, id);
    deps.push_back(std::move(v));
    return id;
  }

  int unite(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = uniteMemo.find(k);
    if (it != uniteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(deps[a].size() + deps[b].size());
    m.insert(m.end(), deps[a].begin(), deps[a].end());
    m.insert(m.end(), deps[b].begin(), deps[b].end());
    int id = internDep(std::move(m));
    uniteMemo.emplace(k, id);
    return id;
  }

  int oneKey(int key) {
    if (key <= 0)
      return 0;
    return internDep({key});
  }

  int internF(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = fdepMemo.find(v);
    if (it != fdepMemo.end())
      return it->second;
    int id = (int)fdeps.size();
    fdepMemo.emplace(v, id);
    fdeps.push_back(std::move(v));
    return id;
  }

  int uniteF(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = funiteMemo.find(k);
    if (it != funiteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(fdeps[a].size() + fdeps[b].size());
    m.insert(m.end(), fdeps[a].begin(), fdeps[a].end());
    m.insert(m.end(), fdeps[b].begin(), fdeps[b].end());
    int id = internF(std::move(m));
    funiteMemo.emplace(k, id);
    return id;
  }

  int oneF(int formal) {
    if (formal < 0)
      return 0;
    return internF({formal});
  }

  int internSlot(int formal, int key) {
    if (formal < 0 || key <= 0)
      return 0;
    uint64_t k = ((uint64_t)(unsigned)formal << 32) | (unsigned)key;
    auto it = slotMemo.find(k);
    if (it != slotMemo.end())
      return it->second;
    int id = (int)slots.size();
    slots.push_back(Slot{formal, key});
    slotMemo.emplace(k, id);
    return id;
  }

  int internS(std::vector<int> v) {
    if (v.empty())
      return 0;
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    auto it = sdepMemo.find(v);
    if (it != sdepMemo.end())
      return it->second;
    int id = (int)sdeps.size();
    sdepMemo.emplace(v, id);
    sdeps.push_back(std::move(v));
    return id;
  }

  int uniteS(int a, int b) {
    if (a == 0 || a == b)
      return a == 0 ? b : a;
    if (b == 0)
      return a;
    uint64_t k = ((uint64_t)(unsigned)std::min(a, b) << 32) | (unsigned)std::max(a, b);
    auto it = suniteMemo.find(k);
    if (it != suniteMemo.end())
      return it->second;
    std::vector<int> m;
    m.reserve(sdeps[a].size() + sdeps[b].size());
    m.insert(m.end(), sdeps[a].begin(), sdeps[a].end());
    m.insert(m.end(), sdeps[b].begin(), sdeps[b].end());
    int id = internS(std::move(m));
    suniteMemo.emplace(k, id);
    return id;
  }

  int oneS(int slot) {
    if (slot <= 0)
      return 0;
    return internS({slot});
  }

  static std::string baseName(llvm::StringRef p) {
    auto s = p.find_last_of("/\\");
    return (s == llvm::StringRef::npos ? p : p.drop_front(s + 1)).str();
  }

  bool onLine(const llvm::Instruction &I) const {
    const llvm::DebugLoc &DL = I.getDebugLoc();
    if (!DL || file.empty() || line == 0)
      return false;
    const llvm::DILocation *S = DL.get();
    while (S) {
      if (S->getLine() == line && S->getFile() && baseName(S->getFile()->getFilename()) == baseName(file))
        return true;
      S = S->getInlinedAt();
    }
    return false;
  }

  bool nameMatch(llvm::Function &F) const {
    if (!F.hasName() || sinkFns.empty())
      return false;
    std::string raw = F.getName().str();
    std::string dem = llvm::demangle(raw);
    for (const std::string &s : sinkFns)
      if (!s.empty() && (s == raw || s == dem))
        return true;
    return false;
  }

  void index() {
    auto add = [&](llvm::Module &M) {
      for (llvm::StructType *T : M.getIdentifiedStructTypes())
        if (T->hasName())
          structNames.insert(T->getName().str());
      for (llvm::Function &F : M) {
        if (F.isDeclaration() || F.isIntrinsic() || !F.hasName())
          continue;
        byName.emplace(F.getName().str(), &F);
      }
    };
    add(down);
    add(up);
    std::vector<llvm::StructType *> namedTy;
    auto collectNamed = [&](llvm::Module &M) {
      for (llvm::StructType *T : M.getIdentifiedStructTypes())
        if (T->hasName() && !T->isOpaque() && T->getNumElements() > 0)
          namedTy.push_back(T);
    };
    collectNamed(down);
    collectNamed(up);
    auto sameType = [&](llvm::Type *a, llvm::Type *b, const llvm::DataLayout &DL, auto &self) -> bool {
      if (a == b)
        return true;
      if (a->isPointerTy() && b->isPointerTy())
        return true;
      if (const auto *aa = llvm::dyn_cast<llvm::ArrayType>(a)) {
        const auto *bb = llvm::dyn_cast<llvm::ArrayType>(b);
        return bb && aa->getNumElements() == bb->getNumElements() &&
               self(aa->getElementType(), bb->getElementType(), DL, self);
      }
      auto *as = llvm::dyn_cast<llvm::StructType>(a);
      auto *bs = llvm::dyn_cast<llvm::StructType>(b);
      if (!as || !bs || as->isOpaque() || bs->isOpaque() || as->getNumElements() != bs->getNumElements())
        return false;
      const llvm::StructLayout *A = DL.getStructLayout(as);
      const llvm::StructLayout *B = DL.getStructLayout(bs);
      if (A->getSizeInBytes() != B->getSizeInBytes())
        return false;
      for (unsigned i = 0; i < as->getNumElements(); ++i) {
        if (A->getElementOffset(i) != B->getElementOffset(i))
          return false;
        if (!self(as->getElementType(i), bs->getElementType(i), DL, self))
          return false;
      }
      return true;
    };
    auto scanInit = [&](llvm::Constant *C, const llvm::DataLayout &DL, int parent, auto &self) -> void {
      if (!C)
        return;
      if (const auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
        auto *ST = const_cast<llvm::StructType *>(CS->getType());
        int ty = internType(ST);
        const llvm::StructLayout *SL = DL.getStructLayout(ST);
        std::vector<int> twins;
        if (!ST->hasName()) {
          for (llvm::StructType *NT : namedTy) {
            if (NT->getNumElements() != ST->getNumElements())
              continue;
            const llvm::StructLayout *NL = DL.getStructLayout(NT);
            if (!sameType(ST, NT, DL, sameType))
              continue;
            twins.push_back(internType(NT));
          }
        }
        for (unsigned i = 0; i < CS->getNumOperands(); ++i) {
          llvm::Constant *Op = CS->getOperand(i);
          int64_t off = (int64_t)SL->getElementOffset(i);
          int slot = slotStep(parent, ty, off);
          const auto *Fn = llvm::dyn_cast<llvm::Function>(Op->stripPointerCasts());
          if (Fn && Fn->hasName() && !Fn->isIntrinsic()) {
            if (slot > 0)
              fnAt[slot].insert(const_cast<llvm::Function *>(Fn));
            for (int nt : twins) {
              int alt = slotStep(parent, nt, off);
              if (alt > 0)
                fnAt[alt].insert(const_cast<llvm::Function *>(Fn));
            }
          }
          self(Op, DL, slot, self);
        }
        return;
      }
      if (const auto *CA = llvm::dyn_cast<llvm::ConstantArray>(C)) {
        for (llvm::Value *Op : CA->operands())
          self(llvm::cast<llvm::Constant>(Op), DL, parent, self);
      }
    };
    auto scanGlobals = [&](llvm::Module &M) {
      const llvm::DataLayout &DL = M.getDataLayout();
      for (llvm::GlobalVariable &G : M.globals())
        if (G.hasInitializer())
          scanInit(G.getInitializer(), DL, 0, scanInit);
    };
    scanGlobals(down);
    scanGlobals(up);
  }

  void callGraph() {
    auto scan = [&](llvm::Module &M) {
      for (llvm::Function &F : M) {
        if (F.isDeclaration())
          continue;
        for (llvm::Instruction &I : llvm::instructions(F)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          llvm::Function *D = nullptr;
          if (llvm::Function *CF = CB->getCalledFunction())
            D = bodyOf(CF);
          else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            D = bodyOf(FN);
          if (!D || D == &F)
            continue;
          callees[&F].push_back(D);
          callers[D].push_back(&F);
        }
      }
    };
    scan(down);
    scan(up);
  }

  void orderFns() {
    std::unordered_set<llvm::Function *> seen;
    std::function<void(llvm::Function *)> dfs = [&](llvm::Function *F) {
      if (!seen.insert(F).second)
        return;
      auto it = callees.find(F);
      if (it != callees.end())
        for (llvm::Function *C : it->second)
          dfs(C);
      ord[F] = (int)order.size();
      order.push_back(F);
    };
    for (llvm::Function &F : down)
      if (!F.isDeclaration())
        dfs(&F);
    for (llvm::Function &F : up)
      if (!F.isDeclaration())
        dfs(&F);
  }

  static uint64_t retSigOf(const FnSum &s) {
    uint64_t h = s.rets.size();
    for (const Ret &r : s.rets) {
      h ^= (uint64_t)r.formal * 0x9e3779b97f4a7c15ULL;
      h ^= (uint64_t)r.path << 1;
      h ^= (uint64_t)r.fdep * 0xbf58476d1ce4e5b9ULL;
      h ^= (uint64_t)r.sdep * 0x94d049bb133111ebULL;
    }
    for (const Pub &p : s.pubs) {
      h ^= (uint64_t)(unsigned)p.formal * 0x85ebca6bULL;
      h ^= (uint64_t)(unsigned)p.slot * 0xc2b2ae35ULL;
      h ^= (uint64_t)(unsigned)p.box * 0x27d4eb2fULL;
    }
    return h;
  }

  static uint64_t fnSigOf(const FnSum &s) {
    uint64_t h = 0;
    for (const Wr &w : s.writes) {
      if (w.fn.empty())
        continue;
      h ^= (uint64_t)w.key * 0x9e3779b97f4a7c15ULL;
      for (char c : w.fn)
        h = h * 131 + (unsigned char)c;
    }
    return h;
  }

  void solve() {
    std::set<std::pair<int, llvm::Function *>> dirty;
    for (llvm::Function *F : order)
      dirty.insert({ord[F], F});
    int spins = 0;
    while (!dirty.empty() && spins < 2000000) {
      ++spins;
      llvm::Function *F = dirty.begin()->second;
      dirty.erase(dirty.begin());
      uint64_t oldRet = sum[F].retSig;
      uint64_t oldFn = sum[F].fnSig;
      std::unordered_set<int> oldKeys;
      for (const Wr &w : sum[F].writes)
        if (!w.fn.empty())
          oldKeys.insert(w.key);
      analyze(*F);
      if (sum[F].retSig != oldRet) {
        auto cit = callers.find(F);
        if (cit != callers.end())
          for (llvm::Function *C : cit->second)
            dirty.insert({ord[C], C});
        auto iit = indirectCallers.find(F);
        if (iit != indirectCallers.end())
          for (llvm::Function *C : iit->second)
            dirty.insert({ord[C], C});
      }
      if (sum[F].fnSig != oldFn) {
        for (const Wr &w : sum[F].writes) {
          if (w.fn.empty() || oldKeys.count(w.key))
            continue;
          auto wit = watchers.find(w.key);
          if (wit == watchers.end())
            continue;
          for (llvm::Function *C : wit->second)
            dirty.insert({ord[C], C});
        }
      }
    }
  }

  void analyze(llvm::Function &F) {
    if (F.isDeclaration())
      return;
    const llvm::DataLayout &DL = F.getParent()->getDataLayout();
    std::unordered_map<VKey, int, VHash> state;
    std::unordered_map<const llvm::Value *, std::vector<VKey>> byVal;
    struct Q {
      const llvm::Value *v;
      int formal;
      int path;
      int gen;
    };
    std::vector<Q> work;
    std::unordered_map<VKey, int, VHash> gen;
    auto grow = [&](const llvm::Value *v, int formal, int path, int dep) {
      if (!v)
        return;
      VKey k{v, formal, path};
      auto it = state.find(k);
      if (it == state.end()) {
        state.emplace(k, dep);
        byVal[v].push_back(k);
        int g = ++gen[k];
        work.push_back(Q{v, formal, path, g});
        return;
      }
      int u = unite(it->second, dep);
      if (u == it->second)
        return;
      it->second = u;
      int g = ++gen[k];
      work.push_back(Q{v, formal, path, g});
    };
    auto depOf = [&](const llvm::Value *v) {
      int d = 0;
      auto it = byVal.find(v);
      if (it == byVal.end())
        return d;
      for (const VKey &k : it->second) {
        auto st = state.find(k);
        if (st != state.end())
          d = unite(d, st->second);
      }
      return d;
    };

    std::function<void(const llvm::CallBase *)> applyCall;
    applyCall = [&](const llvm::CallBase *CB) {
      if (CB->isInlineAsm())
        return;
      auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(CB);
      if (II && (II->getIntrinsicID() == llvm::Intrinsic::memcpy || II->getIntrinsicID() == llvm::Intrinsic::memmove ||
                 II->getIntrinsicID() == llvm::Intrinsic::memset))
        return;
      llvm::Function *target = nullptr;
      if (llvm::Function *CF = CB->getCalledFunction())
        target = bodyOf(CF);
      else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
        target = bodyOf(FN);
      auto takeRet = [&](llvm::Function *G) {
        if (!G)
          return;
        indirectCallers[G].insert(&F);
        for (const Ret &r : sum[G].rets) {
          if (r.formal >= 0 && r.formal < (int)CB->arg_size()) {
            const llvm::Value *arg = CB->getArgOperand(r.formal);
            auto it = byVal.find(arg);
            if (it == byVal.end()) {
              if (!CB->getType()->isVoidTy() && !CB->getType()->isPointerTy())
                grow(CB, -1, 0, r.dep);
              continue;
            }
            for (const VKey &s : it->second) {
              auto st = state.find(s);
              int sd = st == state.end() ? 0 : st->second;
              int path = concat(s.formal, s.path, r.path);
              int d = unite(sd, r.dep);
              if (CB->getType()->isPointerTy())
                grow(CB, s.formal, path, d);
              else if (!CB->getType()->isVoidTy())
                grow(CB, -1, 0, d);
            }
          } else if (!CB->getType()->isVoidTy()) {
            grow(CB, -1, 0, r.dep);
          }
        }
      };
      auto ensurePointer = [&]() {
        if (!CB->getType()->isPointerTy() || byVal.count(CB))
          return;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          if (!arg->getType()->isPointerTy())
            continue;
          auto it = byVal.find(arg);
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int path = append(s.formal, s.path, 0, Any);
            auto st = state.find(s);
            int sd = st == state.end() ? 0 : st->second;
            grow(CB, s.formal, path, sd);
          }
        }
      };
      if (target) {
        auto pit = sum.find(target);
        if (pit != sum.end()) {
          for (const Pub &p : pit->second.pubs) {
            if (p.slot <= 0 || p.formal < 0 || p.formal >= (int)CB->arg_size())
              continue;
            const llvm::Value *arg = CB->getArgOperand((unsigned)p.formal);
            const auto *Fn = llvm::dyn_cast<llvm::Function>(arg->stripPointerCasts());
            if (!Fn || !Fn->hasName())
              continue;
            auto nit = byName.find(Fn->getName().str());
            if (nit == byName.end())
              continue;
            if (p.box >= 0 && p.box < (int)CB->arg_size()) {
              int container = fnSlotOf(CB->getArgOperand((unsigned)p.box), DL);
              if (container > 0) {
                held[(uint64_t)(unsigned)container << 32 | (unsigned)p.slot].insert(nit->second);
                continue;
              }
            }
            fnAt[p.slot].insert(nit->second);
          }
        }
        takeRet(target);
        ensurePointer();
        return;
      }
      std::unordered_set<llvm::Function *> targets;
      int slot = fnSlotOf(CB->getCalledOperand(), DL);
      if (slot > 0) {
        watchers[slot].insert(&F);
        auto fit = fnAt.find(slot);
        if (fit != fnAt.end())
          for (llvm::Function *T : fit->second)
            if (callTypeMatches(T, CB->getFunctionType()))
              targets.insert(T);
      }
      if (targets.empty()) {
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          if (!arg->getType()->isPointerTy())
            continue;
          auto it = byVal.find(arg);
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int path = append(s.formal, s.path, 0, Any);
            auto st = state.find(s);
            int sd = st == state.end() ? 0 : st->second;
            if (CB->getType()->isPointerTy())
              grow(CB, s.formal, path, sd);
            else if (!CB->getType()->isVoidTy())
              grow(CB, -1, 0, sd);
          }
        }
        return;
      }
      for (llvm::Function *G : targets)
        takeRet(G);
      ensurePointer();
    };

    for (llvm::Argument &A : F.args())
      if (A.getType()->isPointerTy())
        grow(&A, A.getArgNo(), 0, 0);

    while (!work.empty()) {
      Q q = work.back();
      work.pop_back();
      VKey k{q.v, q.formal, q.path};
      auto git = gen.find(k);
      if (git == gen.end() || git->second != q.gen)
        continue;
      int dep = state[k];
      for (const llvm::User *U : q.v->users()) {
        if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
          if (!CB->isInlineAsm())
            applyCall(CB);
          continue;
        }
        if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (St->getValueOperand() == q.v && St->getPointerOperand() != q.v) {
            if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(St->getPointerOperand())) {
              for (const llvm::User *LU : AI->users()) {
                const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(LU);
                if (Ld && Ld->getPointerOperand() == AI)
                  grow(Ld, q.formal, q.path, dep);
              }
            }
          }
          continue;
        }
        if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U)) {
          if (Ld->getPointerOperand() != q.v)
            continue;
          int d = dep;
          int key = lastKey(q.path);
          if (key > 0)
            d = unite(d, oneKey(key));
          if (Ld->getType()->isPointerTy())
            grow(Ld, q.formal, q.path, d);
          else
            grow(Ld, -1, 0, d);
          continue;
        }
        if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U)) {
          if (C->getType()->isPointerTy())
            grow(C, q.formal, q.path, dep);
          else
            grow(C, -1, 0, dep);
          continue;
        }
        if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U)) {
          if (Fz->getType()->isPointerTy())
            grow(Fz, q.formal, q.path, dep);
          else
            grow(Fz, -1, 0, dep);
          continue;
        }
        if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
          if (PN->getType()->isPointerTy())
            grow(PN, q.formal, q.path, dep);
          else
            grow(PN, -1, 0, dep);
          continue;
        }
        if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
          if (Sel->getType()->isPointerTy())
            grow(Sel, q.formal, q.path, dep);
          else
            grow(Sel, -1, 0, dep);
          continue;
        }
        if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
          if (llvm::isa<llvm::ConstantExpr>(U) || G->getPointerOperand() != q.v)
            continue;
          int ty = 0;
          int64_t off = Any;
          const llvm::Type *src = G->getSourceElementType();
          const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
          if (!ST)
            if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
              ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
          if (ST)
            ty = internType(ST);
          llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
          if (ty > 0 && G->accumulateConstantOffset(DL, ap)) {
            if (ap.getSignificantBits() > 63 && !ap.isNegative())
              off = Any;
            else
              off = ap.getSExtValue();
          }
          int path2 = ty > 0 ? append(q.formal, q.path, ty, off) : q.path;
          if (G->getType()->isPointerTy())
            grow(G, q.formal, path2, dep);
          continue;
        }
        if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(U)) {
          if (BI->isConditional() && BI->getCondition() == q.v)
            for (unsigned s = 0; s < BI->getNumSuccessors(); ++s)
              for (llvm::PHINode &PN : BI->getSuccessor(s)->phis())
                grow(&PN, -1, 0, dep);
          continue;
        }
        if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(U)) {
          if (SW->getCondition() == q.v)
            for (unsigned s = 0; s < SW->getNumSuccessors(); ++s)
              for (llvm::PHINode &PN : SW->getSuccessor(s)->phis())
                grow(&PN, -1, 0, dep);
          continue;
        }
        if (const auto *I = llvm::dyn_cast<llvm::Instruction>(U)) {
          if (I->getType()->isVoidTy() || llvm::isa<llvm::ReturnInst>(I))
            continue;
          if (I->getType()->isPointerTy())
            grow(I, q.formal, q.path, dep);
          else
            grow(I, -1, 0, dep);
        }
      }
    }

    std::unordered_map<const llvm::BasicBlock *, std::vector<const llvm::Value *>> ctrl;
    {
      llvm::PostDominatorTree PDT;
      PDT.recalculate(F);
      auto addEdge = [&](const llvm::BasicBlock *X, const llvm::BasicBlock *S, const llvm::Value *cond) {
        auto *nx = PDT.getNode(X);
        auto *node = PDT.getNode(S);
        if (!nx || !node || !cond)
          return;
        auto *stop = nx->getIDom();
        while (node && node != stop) {
          if (const llvm::BasicBlock *B = node->getBlock()) {
            auto &v = ctrl[B];
            bool seen = false;
            for (const llvm::Value *c : v)
              if (c == cond)
                seen = true;
            if (!seen)
              v.push_back(cond);
          }
          node = node->getIDom();
        }
      };
      for (llvm::BasicBlock &X : F) {
        auto *T = X.getTerminator();
        if (const auto *BI = llvm::dyn_cast<llvm::BranchInst>(T)) {
          if (BI->isConditional())
            for (unsigned s = 0; s < BI->getNumSuccessors(); ++s)
              addEdge(&X, BI->getSuccessor(s), BI->getCondition());
        } else if (const auto *SW = llvm::dyn_cast<llvm::SwitchInst>(T)) {
          for (unsigned s = 0; s < SW->getNumSuccessors(); ++s)
            addEdge(&X, SW->getSuccessor(s), SW->getCondition());
        }
      }
    }

    std::unordered_map<const llvm::Value *, int> fOf;
    std::unordered_map<const llvm::Value *, int> sOf;
    auto addFset = [&](const llvm::Value *v, int id) {
      if (!v || id <= 0)
        return false;
      int cur = 0;
      auto it = fOf.find(v);
      if (it != fOf.end())
        cur = it->second;
      int nxt = uniteF(cur, id);
      if (nxt == cur)
        return false;
      fOf[v] = nxt;
      return true;
    };
    auto addSset = [&](const llvm::Value *v, int id) {
      if (!v || id <= 0)
        return false;
      int cur = 0;
      auto it = sOf.find(v);
      if (it != sOf.end())
        cur = it->second;
      int nxt = uniteS(cur, id);
      if (nxt == cur)
        return false;
      sOf[v] = nxt;
      return true;
    };
    for (llvm::Argument &A : F.args())
      addFset(&A, oneF((int)A.getArgNo()));
    for (auto &kv : byVal)
      for (const VKey &s : kv.second)
        if (s.formal >= 0)
          addFset(kv.first, oneF(s.formal));
    struct FH {
      size_t operator()(const std::pair<int, int> &p) const {
        return (size_t)p.first * 1315423911u ^ (size_t)p.second;
      }
    };
    std::unordered_map<std::pair<int, int>, std::vector<const llvm::LoadInst *>, FH> loadsAt;
    std::unordered_map<const llvm::Value *, std::vector<std::pair<int, int>>> slotsOf;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        auto it = byVal.find(Ld->getPointerOperand());
        if (it == byVal.end())
          continue;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (s.formal >= 0 && key > 0)
            loadsAt[{s.formal, key}].push_back(Ld);
        }
      } else if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto it = byVal.find(St->getPointerOperand());
        if (it == byVal.end())
          continue;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (s.formal >= 0 && key > 0)
            slotsOf[St->getValueOperand()].push_back({s.formal, key});
        }
      }
    }
    std::vector<const llvm::Value *> fq;
    std::unordered_set<const llvm::Value *> inq;
    auto enq = [&](const llvm::Value *v) {
      if (v && inq.insert(v).second)
        fq.push_back(v);
    };
    for (auto &kv : loadsAt) {
      int slot = oneS(internSlot(kv.first.first, kv.first.second));
      for (const llvm::LoadInst *Ld : kv.second)
        if (addSset(Ld, slot))
          enq(Ld);
    }
    for (auto &kv : fOf)
      enq(kv.first);
    auto slotUsed = [&](int sdep, int idx) {
      if (sdep <= 0 || sdep >= (int)sdeps.size())
        return false;
      for (int sid : sdeps[sdep]) {
        if (sid <= 0 || sid >= (int)slots.size())
          continue;
        if (slots[sid].formal == idx)
          return true;
      }
      return false;
    };
    auto mapRetSlots = [&](const llvm::CallBase *CB, llvm::Function *target) {
      if (!target || CB->getType()->isVoidTy())
        return;
      auto sit = sum.find(target);
      if (sit == sum.end())
        return;
      for (const Ret &r : sit->second.rets) {
        if (r.sdep <= 0 || r.sdep >= (int)sdeps.size())
          continue;
        for (int sid : sdeps[r.sdep]) {
          if (sid <= 0 || sid >= (int)slots.size())
            continue;
          const Slot &sl = slots[sid];
          if (sl.formal < 0 || sl.key <= 0 || sl.formal >= (int)CB->arg_size())
            continue;
          auto it = byVal.find(CB->getArgOperand((unsigned)sl.formal));
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int got = oneS(internSlot(s.formal, sl.key));
            if (addSset(CB, got))
              enq(CB);
          }
        }
      }
    };
    for (size_t qi = 0; qi < fq.size(); ++qi) {
      const llvm::Value *v = fq[qi];
      inq.erase(v);
      int id = 0;
      int sid = 0;
      auto fit = fOf.find(v);
      if (fit != fOf.end())
        id = fit->second;
      auto sit0 = sOf.find(v);
      if (sit0 != sOf.end())
        sid = sit0->second;
      if (id <= 0 && sid <= 0)
        continue;
      for (const llvm::User *U : v->users()) {
        if (llvm::isa<llvm::StoreInst>(U) || llvm::isa<llvm::BranchInst>(U) || llvm::isa<llvm::SwitchInst>(U) ||
            llvm::isa<llvm::ReturnInst>(U))
          continue;
        if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
          if (CB->isInlineAsm() || CB->getType()->isVoidTy())
            continue;
          int idx = -1;
          for (unsigned i = 0; i < CB->arg_size(); ++i)
            if (CB->getArgOperand(i) == v)
              idx = (int)i;
          if (idx < 0)
            continue;
          llvm::Function *target = nullptr;
          if (llvm::Function *CF = CB->getCalledFunction())
            target = bodyOf(CF);
          else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
            target = bodyOf(FN);
          bool known = false;
          bool use = false;
          if (target) {
            auto sit = sum.find(target);
            if (sit != sum.end() && !sit->second.rets.empty()) {
              known = true;
              for (const Ret &r : sit->second.rets) {
                if (r.formal == idx)
                  use = true;
                if (r.fdep > 0 && r.fdep < (int)fdeps.size())
                  for (int f : fdeps[r.fdep])
                    if (f == idx)
                      use = true;
                if (slotUsed(r.sdep, idx))
                  use = true;
              }
            }
          }
          if (!known && v->getType()->isPointerTy())
            use = true;
          if (!use)
            continue;
          bool grew = addFset(CB, id) || addSset(CB, sid);
          mapRetSlots(CB, target);
          if (grew)
            enq(CB);
          continue;
        }
        if (const auto *UI = llvm::dyn_cast<llvm::Instruction>(U))
          if (addFset(UI, id) || addSset(UI, sid))
            enq(UI);
      }
      auto sit = slotsOf.find(v);
      if (sit == slotsOf.end())
        continue;
      for (auto slot : sit->second) {
        auto lit = loadsAt.find(slot);
        if (lit == loadsAt.end())
          continue;
        int slotId = oneS(internSlot(slot.first, slot.second));
        for (const llvm::LoadInst *Ld : lit->second)
          if (addFset(Ld, id) || addSset(Ld, sid) || addSset(Ld, slotId))
            enq(Ld);
      }
    }

    FnSum next;
    if (F.hasName()) {
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *St = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!St)
          continue;
        if (const auto *Fn = llvm::dyn_cast<llvm::Function>(St->getValueOperand()->stripPointerCasts())) {
          if (Fn->hasName()) {
            auto nit = byName.find(Fn->getName().str());
            if (nit != byName.end()) {
              int slot = fnSlotOf(St->getPointerOperand(), DL);
              if (slot > 0)
                fnAt[slot].insert(nit->second);
            }
          }
        }
        int pubSlot = fnSlotOf(St->getPointerOperand(), DL);
        if (pubSlot > 0) {
          int box = -1;
          auto bit = byVal.find(St->getPointerOperand());
          if (bit != byVal.end())
            for (const VKey &s : bit->second)
              if (s.formal >= 0) {
                box = s.formal;
                break;
              }
          auto vit = byVal.find(St->getValueOperand());
          if (vit != byVal.end())
            for (const VKey &s : vit->second)
              if (s.formal >= 0)
                next.pubs.push_back(Pub{s.formal, pubSlot, box});
        }
        auto ait = byVal.find(St->getPointerOperand());
        if (ait == byVal.end())
          continue;
        const std::vector<VKey> &addr = ait->second;
        int vd = depOf(St->getValueOperand());
        std::string fn;
        if (const auto *Fn = llvm::dyn_cast<llvm::Function>(St->getValueOperand()->stripPointerCasts()))
          if (Fn->hasName())
            fn = Fn->getName().str();
        int64_t len = (int64_t)DL.getTypeStoreSize(St->getValueOperand()->getType());
        for (const VKey &s : addr) {
          int key = lastKey(s.path);
          if (key <= 0)
            continue;
          auto st = state.find(s);
          int pd = st == state.end() ? 0 : st->second;
          Wr w;
          w.formal = s.formal;
          w.path = s.path;
          w.len = len;
          int cd = 0;
          auto cit = ctrl.find(St->getParent());
          if (cit != ctrl.end())
            for (const llvm::Value *c : cit->second)
              cd = unite(cd, depOf(c));
          w.dep = unite(unite(vd, pd), cd);
          w.key = key;
          w.fn = fn;
          auto fit = fOf.find(St->getValueOperand());
          if (fit != fOf.end())
            w.fdep = fit->second;
          auto sit = sOf.find(St->getValueOperand());
          if (sit != sOf.end())
            w.sdep = sit->second;
          next.writes.push_back(std::move(w));
          if (!fn.empty()) {
            auto nit = byName.find(fn);
            if (nit != byName.end()) {
              int slot = fnSlotOf(St->getPointerOperand(), DL);
              if (slot > 0)
                fnAt[slot].insert(nit->second);
            }
          }
        }
      }
    }
    for (llvm::BasicBlock &BB : F) {
      auto *R = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
      if (!R || !R->getReturnValue())
        continue;
      auto it = byVal.find(R->getReturnValue());
      if (it == byVal.end()) {
        Ret r;
        r.dep = depOf(R->getReturnValue());
        auto fit = fOf.find(R->getReturnValue());
        if (fit != fOf.end())
          r.fdep = fit->second;
        auto sit = sOf.find(R->getReturnValue());
        if (sit != sOf.end())
          r.sdep = sit->second;
        if (r.dep != 0 || r.fdep != 0 || r.sdep != 0)
          next.rets.push_back(r);
        continue;
      }
      for (const VKey &s : it->second) {
        auto st = state.find(s);
        Ret r;
        r.formal = s.formal;
        r.path = s.path;
        r.dep = st == state.end() ? 0 : st->second;
        auto fit = fOf.find(R->getReturnValue());
        if (fit != fOf.end())
          r.fdep = fit->second;
        auto sit = sOf.find(R->getReturnValue());
        if (sit != sOf.end())
          r.sdep = sit->second;
        if (r.formal >= 0)
          r.fdep = uniteF(r.fdep, oneF(r.formal));
        next.rets.push_back(r);
      }
    }
    for (llvm::Instruction &I : llvm::instructions(F)) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      bool isCopy = false;
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(CB))
        isCopy = II->getIntrinsicID() == llvm::Intrinsic::memcpy || II->getIntrinsicID() == llvm::Intrinsic::memmove;
      else if (llvm::Function *CF = CB->getCalledFunction())
        isCopy = CF->getName() == "memcpy" || CF->getName() == "memmove";
      if (!isCopy) {
        llvm::Function *callee = nullptr;
        if (llvm::Function *CF = CB->getCalledFunction())
          callee = bodyOf(CF);
        else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
          callee = bodyOf(FN);
        Site site;
        site.callee = callee;
        if (!callee) {
          site.fty = CB->getFunctionType();
          int slot = fnSlotOf(CB->getCalledOperand(), DL);
          if (slot > 0) {
            site.calleeKeys.push_back(slot);
            next.indirectKeys.push_back(slot);
          }
          auto bit = byVal.find(CB->getCalledOperand());
          if (bit != byVal.end())
            for (const VKey &s : bit->second)
              if (s.formal >= 0) {
                site.calleeBox = s.formal;
                break;
              }
        }
        site.args.resize(CB->arg_size());
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          ArgAt &a = site.args[i];
          int d = depOf(arg);
          if (d > 0)
            a.keys.insert(a.keys.end(), deps[d].begin(), deps[d].end());
          auto fit = fOf.find(arg);
          if (fit != fOf.end() && fit->second > 0)
            a.vformals = fdeps[fit->second];
          a.chain = fnSlotOf(arg, DL);
          auto it = byVal.find(arg);
          if (it != byVal.end()) {
            for (const VKey &s : it->second) {
              int key = lastKey(s.path);
              if (key > 0)
                a.keys.push_back(key);
              if (s.formal >= 0) {
                a.formals.push_back(s.formal);
                a.lift.push_back(LiftFrom{0, s.formal, s.path, {}});
              }
            }
          } else if (arg->getType()->isPointerTy()) {
            std::set<std::pair<const llvm::Value *, int>> seenV;
            collectActual(arg, 0, DL, seenV, a.lift);
          }
          std::sort(a.keys.begin(), a.keys.end());
          a.keys.erase(std::unique(a.keys.begin(), a.keys.end()), a.keys.end());
          std::sort(a.formals.begin(), a.formals.end());
          a.formals.erase(std::unique(a.formals.begin(), a.formals.end()), a.formals.end());
          std::sort(a.lift.begin(), a.lift.end(), [](const LiftFrom &x, const LiftFrom &y) {
            if (x.kind != y.kind)
              return x.kind < y.kind;
            if (x.formal != y.formal)
              return x.formal < y.formal;
            if (x.path != y.path)
              return x.path < y.path;
            return x.name < y.name;
          });
          a.lift.erase(std::unique(a.lift.begin(), a.lift.end()), a.lift.end());
        }
        std::sort(site.calleeKeys.begin(), site.calleeKeys.end());
        site.calleeKeys.erase(std::unique(site.calleeKeys.begin(), site.calleeKeys.end()), site.calleeKeys.end());
        next.sites.push_back(std::move(site));
        continue;
      }
      if (CB->arg_size() < 3)
        continue;
      int64_t n = 0;
      bool anyN = true;
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(2))) {
        anyN = false;
        n = CI->getSExtValue();
      }
      auto dit = byVal.find(CB->getArgOperand(0));
      auto sit = byVal.find(CB->getArgOperand(1));
      if (dit == byVal.end() || sit == byVal.end())
        continue;
      for (const VKey &d : dit->second)
        for (const VKey &s : sit->second)
          next.copies.push_back(CopySite{d.formal, d.path, s.formal, s.path, n, anyN});
    }
    auto addUse = [&](const llvm::Instruction &I, std::vector<int> &out, std::vector<int> &forms, std::vector<Edge> &edges) {
      auto takeVal = [&](const llvm::Value *op) {
        if (!op || llvm::isa<llvm::BasicBlock>(op))
          return;
        int d = depOf(op);
        if (d > 0)
          out.insert(out.end(), deps[d].begin(), deps[d].end());
        auto it = byVal.find(op);
        if (it == byVal.end())
          return;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (key > 0)
            out.push_back(key);
          if (s.formal >= 0)
            forms.push_back(s.formal);
        }
      };
      takeVal(&I);
      for (const llvm::Value *op : I.operands())
        takeVal(op);
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (CB->isInlineAsm())
          return;
        llvm::Function *callee = nullptr;
        if (llvm::Function *CF = CB->getCalledFunction())
          callee = bodyOf(CF);
        else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
          callee = bodyOf(FN);
        if (!callee)
          return;
        auto sit = sum.find(callee);
        if (sit == sum.end())
          return;
        for (const Ret &r : sit->second.rets)
          if (r.formal >= 0)
            edges.push_back(Edge{callee, r.formal});
      }
    };
    for (llvm::Instruction &I : llvm::instructions(F)) {
      if (onLine(I)) {
        anyLine = true;
        next.hitLine = true;
        addUse(I, next.lineKeys, next.lineFormals, next.lineEdges);
      }
    }
    if (nameMatch(F)) {
      next.hitName = true;
      for (llvm::Instruction &I : llvm::instructions(F))
        if (llvm::isa<llvm::LoadInst>(I) || llvm::isa<llvm::StoreInst>(I) || llvm::isa<llvm::CallBase>(I))
          addUse(I, next.nameKeys, next.nameFormals, next.nameEdges);
    }
    auto uniqInts = [](std::vector<int> &v) {
      std::sort(v.begin(), v.end());
      v.erase(std::unique(v.begin(), v.end()), v.end());
    };
    uniqInts(next.lineKeys);
    uniqInts(next.nameKeys);
    uniqInts(next.lineFormals);
    uniqInts(next.nameFormals);
    auto uniqEdges = [](std::vector<Edge> &v) {
      std::sort(v.begin(), v.end(), [](const Edge &a, const Edge &b) {
        if (a.fn != b.fn)
          return a.fn < b.fn;
        return a.arg < b.arg;
      });
      v.erase(std::unique(v.begin(), v.end(), [](const Edge &a, const Edge &b) { return a.fn == b.fn && a.arg == b.arg; }),
              v.end());
    };
    uniqEdges(next.lineEdges);
    uniqEdges(next.nameEdges);
    std::sort(next.pubs.begin(), next.pubs.end(), [](const Pub &a, const Pub &b) {
      if (a.formal != b.formal)
        return a.formal < b.formal;
      return a.slot < b.slot;
    });
    next.pubs.erase(std::unique(next.pubs.begin(), next.pubs.end(),
                                [](const Pub &a, const Pub &b) { return a.formal == b.formal && a.slot == b.slot; }),
                    next.pubs.end());
    std::sort(next.indirectKeys.begin(), next.indirectKeys.end());
    next.indirectKeys.erase(std::unique(next.indirectKeys.begin(), next.indirectKeys.end()), next.indirectKeys.end());
    next.retSig = retSigOf(next);
    next.fnSig = fnSigOf(next);
    sum[&F] = std::move(next);
  }

  bool isPrefix(int whole, int pre, std::vector<std::pair<int, int64_t>> &suf) const {
    suf.clear();
    if (pre == 0)
      return false;
    int p = whole;
    while (p > 0 && p != pre) {
      suf.push_back({steps[p].type, steps[p].off});
      p = steps[p].parent;
    }
    if (p != pre)
      return false;
    std::reverse(suf.begin(), suf.end());
    return true;
  }

  void forwardCopies() {
    std::unordered_map<int, std::vector<WRef>> byAnc;
    auto indexWrite = [&](llvm::Function *F, const Wr &w) {
      WRef ref{F, w};
      for (int p = w.path; p > 0; p = steps[p].parent)
        byAnc[p].push_back(ref);
    };
    for (auto &kv : sum)
      for (const Wr &w : kv.second.writes)
        indexWrite(kv.first, w);
    std::vector<WRef> added;
    for (auto &kv : sum) {
      for (const CopySite &c : kv.second.copies) {
        auto it = byAnc.find(c.sp);
        if (it == byAnc.end())
          continue;
        for (const WRef &src : it->second) {
          std::vector<std::pair<int, int64_t>> suf;
          if (!isPrefix(src.w.path, c.sp, suf))
            continue;
          int64_t bytes = 0;
          bool any = false;
          for (auto [t, o] : suf) {
            (void)t;
            if (o == Any)
              any = true;
            else
              bytes += o < 0 ? -o : o;
          }
          if (!c.anyN && (any || bytes >= c.n))
            continue;
          int path = c.dp;
          for (auto [t, o] : suf)
            path = append(c.df, path, t, o);
          Wr w = src.w;
          w.formal = c.df;
          w.fdep = c.sf >= 0 ? oneF(c.sf) : 0;
          int sk = lastKey(c.sp);
          w.sdep = c.sf >= 0 ? oneS(internSlot(c.sf, sk)) : 0;
          w.path = path;
          w.key = lastKey(path);
          if (w.key <= 0)
            continue;
          added.push_back(WRef{kv.first, std::move(w)});
        }
      }
    }
    extra = std::move(added);
  }

  std::string showFn(const llvm::Function *F) const {
    if (!F || !F->hasName())
      return "?";
    std::string n = F->getName().str();
    std::string d = llvm::demangle(n);
    if (d.empty() || d == n)
      return n;
    return d;
  }

  int gepStep(const llvm::GEPOperator *G, const llvm::DataLayout &DL) {
    int ty = 0;
    int64_t off = Any;
    const llvm::Type *src = G->getSourceElementType();
    const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
    if (!ST)
      if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
        ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
    if (ST)
      ty = internType(ST);
    if (ty <= 0)
      return 0;
    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
    if (G->accumulateConstantOffset(DL, ap)) {
      if (ap.getSignificantBits() > 63 && !ap.isNegative())
        off = Any;
      else
        off = ap.getSExtValue();
    }
    return append(-1, 0, ty, off);
  }

  int gepKey(const llvm::GEPOperator *G, const llvm::DataLayout &DL) {
    const llvm::Type *src = G->getSourceElementType();
    const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
    if (!ST)
      if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
        ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
    if (!ST)
      return 0;
    int ty = internType(ST);
    int64_t off = Any;
    llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
    if (G->accumulateConstantOffset(DL, ap)) {
      if (ap.getSignificantBits() > 63 && !ap.isNegative())
        off = Any;
      else
        off = ap.getSExtValue();
    }
    return keyAt(ty, off);
  }

  int fnSlotOf(const llvm::Value *V, const llvm::DataLayout &DL) {
    std::set<const llvm::Value *> seen;
    std::function<int(const llvm::Value *)> walk = [&](const llvm::Value *U) -> int {
      if (!U || !seen.insert(U).second)
        return 0;
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(U)) {
        if (CE->isCast())
          return walk(CE->getOperand(0));
        if (CE->getOpcode() != llvm::Instruction::GetElementPtr)
          return 0;
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(U)) {
        int base = walk(G->getPointerOperand());
        const llvm::Type *src = G->getSourceElementType();
        const auto *ST = llvm::dyn_cast<llvm::StructType>(src);
        if (!ST)
          if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(src))
            ST = llvm::dyn_cast<llvm::StructType>(AT->getElementType());
        if (!ST)
          return base;
        int ty = internType(ST);
        int64_t off = Any;
        llvm::APInt ap(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
        if (G->accumulateConstantOffset(DL, ap)) {
          if (ap.getSignificantBits() <= 63 || ap.isNegative())
            off = ap.getSExtValue();
        }
        return slotStep(base, ty, off);
      }
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(U))
        return walk(Ld->getPointerOperand());
      if (const auto *AI = llvm::dyn_cast<llvm::AllocaInst>(U)) {
        for (const llvm::User *SU : AI->users()) {
          const auto *St = llvm::dyn_cast<llvm::StoreInst>(SU);
          if (!St || St->getPointerOperand() != AI)
            continue;
          int k = walk(St->getValueOperand());
          if (k > 0)
            return k;
        }
        return 0;
      }
      if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
        if (CB->isInlineAsm())
          return 0;
        llvm::Function *target = nullptr;
        if (llvm::Function *CF = CB->getCalledFunction())
          target = bodyOf(CF);
        else if (auto *FN = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts()))
          target = bodyOf(FN);
        if (!target)
          return 0;
        auto sit = sum.find(target);
        if (sit == sum.end())
          return 0;
        for (const Ret &r : sit->second.rets) {
          int k = pathToSlot(r.path);
          if (k > 0)
            return k;
        }
        return 0;
      }
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
        return walk(C->getOperand(0));
      if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(U))
        return walk(Fz->getOperand(0));
      if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(U)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
          int k = walk(PN->getIncomingValue(i));
          if (k > 0)
            return k;
        }
        return 0;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U)) {
        int k = walk(Sel->getTrueValue());
        return k > 0 ? k : walk(Sel->getFalseValue());
      }
      return 0;
    };
    return walk(V);
  }

  // Field key of a function pointer loaded from a global or an argument,
  // when that address is not itself a tracked value.
  int calleeKeyOf(const llvm::Value *V, const llvm::DataLayout &DL) {
    std::set<const llvm::Value *> seen;
    std::function<int(const llvm::Value *, int)> walk = [&](const llvm::Value *V, int suffix) -> int {
      if (!V || !seen.insert(V).second)
        return 0;
      if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
        if (CE->isCast())
          return walk(CE->getOperand(0), suffix);
        if (CE->getOpcode() != llvm::Instruction::GetElementPtr)
          return 0;
      }
      if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
        int slot = gepKey(G, DL);
        if (slot > 0)
          return slot;
        int step = gepStep(G, DL);
        int next = step > 0 ? concat(-1, step, suffix) : suffix;
        return walk(G->getPointerOperand(), next);
      }
      if (const auto *Ld = llvm::dyn_cast<llvm::LoadInst>(V))
        return walk(Ld->getPointerOperand(), suffix);
      if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V))
        return walk(C->getOperand(0), suffix);
      if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(V))
        return walk(Fz->getOperand(0), suffix);
      if (llvm::isa<llvm::GlobalValue>(V) || llvm::isa<llvm::Argument>(V))
        return suffix > 0 ? lastKey(suffix) : 0;
      if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
          int k = walk(PN->getIncomingValue(i), suffix);
          if (k > 0)
            return k;
        }
        return 0;
      }
      if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
        int k = walk(Sel->getTrueValue(), suffix);
        return k > 0 ? k : walk(Sel->getFalseValue(), suffix);
      }
      return 0;
    };
    return walk(V, 0);
  }

  // suffix is the field path from V out to the callsite actual.
  void collectActual(const llvm::Value *V, int suffix, const llvm::DataLayout &DL,
                     std::set<std::pair<const llvm::Value *, int>> &seen, std::vector<LiftFrom> &out) {
    if (!V || !seen.insert({V, suffix}).second)
      return;
    if (const auto *A = llvm::dyn_cast<llvm::Argument>(V)) {
      if (A->getType()->isPointerTy())
        out.push_back(LiftFrom{0, (int)A->getArgNo(), suffix, {}});
      else
        out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    if (llvm::isa<llvm::AllocaInst>(V)) {
      out.push_back(LiftFrom{1, -1, suffix, {}});
      return;
    }
    if (const auto *GV = llvm::dyn_cast<llvm::GlobalValue>(V)) {
      out.push_back(LiftFrom{2, -1, suffix, GV->hasName() ? GV->getName().str() : std::string()});
      return;
    }
    if (llvm::isa<llvm::ConstantPointerNull>(V) || llvm::isa<llvm::UndefValue>(V) || llvm::isa<llvm::PoisonValue>(V)) {
      out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      if (CE->isCast()) {
        collectActual(CE->getOperand(0), suffix, DL, seen, out);
        return;
      }
      if (CE->getOpcode() != llvm::Instruction::GetElementPtr) {
        out.push_back(LiftFrom{3, -1, suffix, {}});
        return;
      }
    }
    if (const auto *G = llvm::dyn_cast<llvm::GEPOperator>(V)) {
      int step = gepStep(G, DL);
      int next = step > 0 ? concat(-1, step, suffix) : suffix;
      collectActual(G->getPointerOperand(), next, DL, seen, out);
      return;
    }
    if (const auto *C = llvm::dyn_cast<llvm::CastInst>(V)) {
      collectActual(C->getOperand(0), suffix, DL, seen, out);
      return;
    }
    if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      collectActual(Fz->getOperand(0), suffix, DL, seen, out);
      return;
    }
    if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
      for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
        collectActual(PN->getIncomingValue(i), suffix, DL, seen, out);
      return;
    }
    if (const auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
      collectActual(Sel->getTrueValue(), suffix, DL, seen, out);
      collectActual(Sel->getFalseValue(), suffix, DL, seen, out);
      return;
    }
    if (const auto *CB = llvm::dyn_cast<llvm::CallBase>(V)) {
      if (CB->hasRetAttr(llvm::Attribute::NoAlias))
        out.push_back(LiftFrom{1, -1, suffix, {}});
      else
        out.push_back(LiftFrom{3, -1, suffix, {}});
      return;
    }
    out.push_back(LiftFrom{3, -1, suffix, {}});
  }

  std::string pathString(int formal, int path) const {
    std::vector<std::pair<int, int64_t>> keys;
    for (int p = path; p > 0; p = steps[p].parent)
      keys.push_back({steps[p].type, steps[p].off});
    std::string s = formal >= 0 ? "arg" + std::to_string(formal) : "ext";
    for (int i = (int)keys.size() - 1; i >= 0; --i) {
      s += ".";
      int ty = keys[i].first;
      if (ty > 0 && ty <= (int)typeName.size())
        s += typeName[ty - 1];
      else
        s += "ext";
      s += "+";
      s += keys[i].second == Any ? "any" : std::to_string(keys[i].second);
    }
    return s;
  }

  FieldReport answer() {
    std::unordered_set<int> K;
    const bool useLine = anyLine;
    struct SiteRef {
      llvm::Function *caller;
      const Site *site;
    };
    std::unordered_map<llvm::Function *, std::vector<SiteRef>> directAt;
    std::unordered_map<int, std::vector<SiteRef>> indirectAt;
    std::unordered_map<int, std::vector<std::pair<llvm::Function *, const Wr *>>> writesAt;
    for (auto &kv : sum) {
      for (const Site &site : kv.second.sites) {
        if (site.callee)
          directAt[site.callee].push_back(SiteRef{kv.first, &site});
        for (int k : site.calleeKeys)
          indirectAt[k].push_back(SiteRef{kv.first, &site});
      }
      for (const Wr &w : kv.second.writes)
        if (w.key > 0)
          writesAt[w.key].push_back({kv.first, &w});
    }
    for (const WRef &e : extra)
      if (e.w.key > 0)
        writesAt[e.w.key].push_back({e.fn, &e.w});
    auto typeOk = [](const llvm::Function *T, const llvm::FunctionType *Ty) {
      if (!Ty)
        return true;
      return T && T->getFunctionType() == Ty;
    };
    std::unordered_map<llvm::Function *, std::vector<SiteRef>> viaFn;
    for (auto &kv : fnAt) {
      auto sit = indirectAt.find(kv.first);
      if (sit == indirectAt.end())
        continue;
      for (llvm::Function *T : kv.second)
        for (const SiteRef &r : sit->second)
          if (typeOk(T, r.site->fty))
            viaFn[T].push_back(r);
    }

    std::unordered_set<std::pair<llvm::Function *, int>, FAHash> seenFormal;
    std::vector<std::pair<llvm::Function *, int>> fq;
    std::vector<int> kq;
    auto addKey = [&](int k) {
      if (k <= 0 || !K.insert(k).second)
        return;
      kq.push_back(k);
    };
    auto addFormal = [&](llvm::Function *fn, int arg) {
      if (!fn || arg < 0)
        return;
      if (!seenFormal.emplace(fn, arg).second)
        return;
      fq.emplace_back(fn, arg);
    };
    auto bindActual = [&](llvm::Function *F, int arg, const SiteRef &r) {
      if (arg >= (int)r.site->args.size())
        return;
      const ArgAt &a = r.site->args[(size_t)arg];
      for (int k : a.keys)
        addKey(k);
      for (int j : a.formals)
        addFormal(r.caller, j);
      for (int k : r.site->calleeKeys)
        addKey(k);
      (void)F;
    };

    for (auto &kv : sum) {
      bool take = useLine ? kv.second.hitLine : kv.second.hitName;
      if (!take)
        continue;
      const std::vector<int> &seed = useLine ? kv.second.lineKeys : kv.second.nameKeys;
      for (int k : seed)
        addKey(k);
      const std::vector<int> &forms = useLine ? kv.second.lineFormals : kv.second.nameFormals;
      for (int arg : forms)
        addFormal(kv.first, arg);
      const std::vector<Edge> &edges = useLine ? kv.second.lineEdges : kv.second.nameEdges;
      for (const Edge &e : edges)
        addFormal(e.fn, e.arg);
    }

    std::size_t fi = 0, ki = 0;
    while (fi < fq.size() || ki < kq.size()) {
      if (fi < fq.size()) {
        llvm::Function *F = fq[fi].first;
        int arg = fq[fi].second;
        ++fi;
        auto dit = directAt.find(F);
        if (dit != directAt.end())
          for (const SiteRef &r : dit->second)
            bindActual(F, arg, r);
        auto vit = viaFn.find(F);
        if (vit != viaFn.end())
          for (const SiteRef &r : vit->second)
            bindActual(F, arg, r);
        continue;
      }
      int k = kq[ki++];
      auto wit = writesAt.find(k);
      if (wit != writesAt.end())
        for (auto &wr : wit->second) {
          const Wr *w = wr.second;
          if (w->dep > 0)
            for (int d : deps[w->dep])
              addKey(d);
        }
      auto fit = fnAt.find(k);
      auto iit = indirectAt.find(k);
      if (fit == fnAt.end() || iit == indirectAt.end())
        continue;
      for (llvm::Function *T : fit->second)
        for (const SiteRef &r : iit->second) {
          if (!typeOk(T, r.site->fty))
            continue;
          for (unsigned i = 0; i < r.site->args.size(); ++i)
            addFormal(T, (int)i);
        }
    }
    struct OKey {
      llvm::Function *fn = nullptr;
      int formal = -1;
      bool operator==(const OKey &o) const { return fn == o.fn && formal == o.formal; }
    };
    struct OKeyHash {
      size_t operator()(const OKey &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u);
      }
    };
    struct Hit {
      llvm::Function *who = nullptr;
      int arg = -1;
      int viaHead = -1;
    };
    std::vector<std::pair<llvm::Function *, int>> viaNodes;
    auto pushVia = [&](int prev, llvm::Function *fn) {
      viaNodes.push_back({fn, prev});
      return (int)viaNodes.size() - 1;
    };
    auto isInput = [&](llvm::Function *F, int formal) {
      if (!F || formal < 0 || !F->hasName())
        return false;
      if (passIn.count({F->getName().str(), formal}))
        return true;
      return passIn.count({showFn(F), formal}) > 0;
    };
    std::unordered_map<OKey, std::vector<Hit>, OKeyHash> hitCache;
    std::unordered_set<OKey, OKeyHash> hitDone;
    auto hitsOf = [&](llvm::Function *start, int formal) -> const std::vector<Hit> & {
      static const std::vector<Hit> none;
      OKey key{start, formal};
      if (!hitDone.insert(key).second)
        return hitCache[key];
      std::vector<Hit> hits;
      struct Item {
        llvm::Function *fn;
        int formal;
        int via;
      };
      std::vector<Item> q;
      std::unordered_set<OKey, OKeyHash> seen;
      if (!start || formal < 0) {
        hitCache[key] = std::move(hits);
        return hitCache[key];
      }
      seen.insert(key);
      q.push_back(Item{start, formal, pushVia(-1, start)});
      for (size_t qi = 0; qi < q.size(); ++qi) {
        llvm::Function *F = q[qi].fn;
        int fml = q[qi].formal;
        int via = q[qi].via;
        if (isInput(F, fml)) {
          bool have = false;
          for (const Hit &h : hits)
            if (h.who == F && h.arg == fml)
              have = true;
          if (!have)
            hits.push_back(Hit{F, fml, via});
          continue;
        }
        auto step = [&](llvm::Function *caller, const Site &site) {
          if (!caller || fml >= (int)site.args.size())
            return;
          const ArgAt &a = site.args[(size_t)fml];
          std::vector<int> next = a.vformals;
          next.insert(next.end(), a.formals.begin(), a.formals.end());
          std::sort(next.begin(), next.end());
          next.erase(std::unique(next.begin(), next.end()), next.end());
          for (int j : next) {
            if (j < 0)
              continue;
            if (!seen.insert(OKey{caller, j}).second)
              continue;
            q.push_back(Item{caller, j, pushVia(via, caller)});
          }
        };
        auto dit = directAt.find(F);
        if (dit != directAt.end())
          for (const SiteRef &r : dit->second)
            step(r.caller, *r.site);
        auto vit = viaFn.find(F);
        if (vit != viaFn.end())
          for (const SiteRef &r : vit->second)
            step(r.caller, *r.site);
      }
      hitCache[key] = std::move(hits);
      return hitCache[key];
    };
    auto rootLine = [&](const Hit &h, const std::string &path) {
      std::string s = "pass ";
      s += std::to_string(h.arg);
      s += " ";
      s += path;
      s += " :: ";
      s += showFn(h.who);
      s += " :: ";
      std::vector<llvm::Function *> seq;
      for (int n = h.viaHead; n >= 0; n = viaNodes[(size_t)n].second)
        seq.push_back(viaNodes[(size_t)n].first);
      for (size_t i = 0; i < seq.size(); ++i) {
        if (i != 0)
          s += " => ";
        s += showFn(seq[i]);
      }
      return s;
    };
    std::unordered_map<std::string, llvm::Function *> byShow;
    for (auto &kv : byName) {
      byShow.emplace(kv.first, kv.second);
      byShow.emplace(showFn(kv.second), kv.second);
    }
    auto lookupFn = [&](const std::string &n) -> llvm::Function * {
      auto it = byShow.find(n);
      return it == byShow.end() ? nullptr : it->second;
    };
    auto targetsOf = [&](const Site &site, const std::vector<int> &boxes) {
      std::vector<llvm::Function *> tg;
      auto take = [&](llvm::Function *T) {
        if (typeOk(T, site.fty))
          tg.push_back(T);
      };
      if (site.callee) {
        tg.push_back(site.callee);
        return tg;
      }
      for (int key : site.calleeKeys) {
        std::vector<std::pair<int, int64_t>> steps;
        for (int c = key; c > 0 && c < (int)chainParent.size(); c = chainParent[(size_t)c])
          steps.push_back({chainTy[(size_t)c], chainOff[(size_t)c]});
        std::reverse(steps.begin(), steps.end());
        if (steps.empty() && key > 0)
          steps.push_back({0, 0});
        std::vector<int> suffixes;
        for (size_t s = 0; s < steps.size(); ++s) {
          int id = 0;
          bool ok = true;
          for (size_t k = s; k < steps.size(); ++k) {
            if (steps[k].first <= 0) {
              ok = false;
              break;
            }
            id = slotStep(id, steps[k].first, steps[k].second);
          }
          if (!ok || id <= 0)
            continue;
          suffixes.push_back(id);
          auto fit = fnAt.find(id);
          if (fit != fnAt.end())
            for (llvm::Function *T : fit->second)
              take(T);
        }
        if (suffixes.empty() && key > 0)
          suffixes.push_back(key);
        if (site.calleeBox >= 0 && site.calleeBox < (int)boxes.size() && boxes[(size_t)site.calleeBox] > 0) {
          int container = boxes[(size_t)site.calleeBox];
          for (int id : suffixes) {
            uint64_t hk = (uint64_t)(unsigned)container << 32 | (unsigned)id;
            auto hit = held.find(hk);
            if (hit != held.end())
              for (llvm::Function *T : hit->second)
                take(T);
          }
        }
      }
      return tg;
    };
    struct AHit {
      llvm::Function *who = nullptr;
      int arg = -1;
      std::vector<llvm::Function *> seq;
    };
    struct AK {
      llvm::Function *fn = nullptr;
      int formal = -1;
      llvm::Function *who = nullptr;
      int arg = -1;
      bool operator==(const AK &o) const {
        return fn == o.fn && formal == o.formal && who == o.who && arg == o.arg;
      }
    };
    struct AKHash {
      size_t operator()(const AK &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u) ^ ((size_t)k.who >> 4) ^
               ((size_t)k.arg * 1315423911u);
      }
    };
    struct Reach {
      llvm::Function *who = nullptr;
      int arg = -1;
      std::vector<llvm::Function *> seq;
    };
    struct RK {
      llvm::Function *F = nullptr;
      llvm::Function *who = nullptr;
      int arg = -1;
      uint64_t box = 0;
      bool operator==(const RK &o) const { return F == o.F && who == o.who && arg == o.arg && box == o.box; }
    };
    struct RKHash {
      size_t operator()(const RK &k) const {
        return ((size_t)k.F >> 4) ^ ((size_t)k.who >> 4) ^ ((size_t)k.arg * 1315423911u) ^ (size_t)k.box;
      }
    };
    std::unordered_map<llvm::Function *, std::vector<Reach>> reachFromChop;
    {
      struct Item {
        llvm::Function *F = nullptr;
        Reach r;
        std::vector<int> boxes;
        uint64_t box = 0;
      };
      std::vector<Item> rq;
      std::unordered_set<RK, RKHash> seenR;
      for (const auto &kvIn : *inMap) {
        llvm::Function *chop = lookupFn(kvIn.first);
        if (!chop)
          continue;
        for (const Input &in : kvIn.second) {
          if (in.arg < 0)
            continue;
          llvm::Function *who = lookupFn(in.func);
          if (!who)
            continue;
          Item it;
          it.F = chop;
          it.r.who = who;
          it.r.arg = in.arg;
          it.r.seq = {who, chop};
          rq.push_back(std::move(it));
        }
      }
      for (size_t qi = 0; qi < rq.size(); ++qi) {
        Item cur = rq[qi];
        if (!cur.F || !seenR.insert(RK{cur.F, cur.r.who, cur.r.arg, cur.box}).second)
          continue;
        reachFromChop[cur.F].push_back(cur.r);
        auto sit = sum.find(cur.F);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites)
          for (llvm::Function *T : targetsOf(site, cur.boxes)) {
            if (!T || T == cur.F)
              continue;
            Item nxt;
            nxt.F = T;
            nxt.r = cur.r;
            nxt.r.seq = cur.r.seq;
            nxt.r.seq.push_back(T);
            if (site.callee) {
              nxt.boxes.assign(site.args.size(), 0);
              for (unsigned i = 0; i < site.args.size(); ++i) {
                int c = site.args[i].chain;
                if (c == 0)
                  for (int f : site.args[i].formals)
                    if (f >= 0 && f < (int)cur.boxes.size() && cur.boxes[(size_t)f] > 0)
                      c = cur.boxes[(size_t)f];
                nxt.boxes[i] = c;
              }
              uint64_t bh = 1469598103934665603ull;
              for (int c : nxt.boxes)
                bh = (bh ^ (uint64_t)(unsigned)c) * 1099511628211ull;
              nxt.box = bh;
            }
            rq.push_back(std::move(nxt));
          }
      }
    }
    std::unordered_map<std::uint64_t, std::unordered_set<std::uint64_t>> pointedAt;
    std::unordered_map<std::uint64_t, std::unordered_set<int>> pointedTy;
    auto packPtr = [](llvm::Function *F, int formal) {
      return ((uint64_t)(uintptr_t)F) ^ ((uint64_t)(unsigned)formal * 0x9e3779b97f4a7c15ull);
    };
    auto fillPointed = [&](llvm::Function *from, int arg) {
      uint64_t pk = packPtr(from, arg);
      if (pointedAt.count(pk))
        return;
      struct P {
        llvm::Function *fn;
        int formal;
        bool operator==(const P &o) const { return fn == o.fn && formal == o.formal; }
      };
      struct PH {
        size_t operator()(const P &p) const { return ((size_t)p.fn >> 4) ^ (size_t)p.formal * 1315423911u; }
      };
      std::unordered_set<P, PH> got;
      std::vector<P> q;
      q.push_back({from, arg});
      for (size_t qi = 0; qi < q.size() && qi < 400000; ++qi) {
        P cur = q[qi];
        if (!cur.fn || !got.insert(cur).second)
          continue;
        auto sit = sum.find(cur.fn);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites)
          for (unsigned i = 0; i < site.args.size(); ++i) {
            bool pass = false;
            for (int f : site.args[i].formals)
              pass = pass || f == cur.formal;
            if (!pass)
              continue;
            for (llvm::Function *T : targetsOf(site, {}))
              if (T)
                q.push_back({T, (int)i});
          }
      }
      std::unordered_set<std::uint64_t> pack;
      for (const P &p : got)
        pack.insert(packPtr(p.fn, p.formal));
      pointedAt.emplace(pk, std::move(pack));
      std::unordered_set<int> tys;
      struct FK {
        llvm::Function *fn;
        int formal;
        bool operator==(const FK &o) const { return fn == o.fn && formal == o.formal; }
      };
      struct FKH {
        size_t operator()(const FK &k) const { return ((size_t)k.fn >> 4) ^ (size_t)k.formal * 17u; }
      };
      std::unordered_set<FK, FKH> walked;
      auto strict = [&](llvm::Function *Fn, int formal, int depth, auto &self) -> void {
        if (!Fn || Fn->isDeclaration() || formal < 0 || formal >= (int)Fn->arg_size() || depth > 6)
          return;
        if (!walked.insert(FK{Fn, formal}).second)
          return;
        const llvm::Argument *Arg = Fn->getArg((unsigned)formal);
        std::unordered_set<const llvm::Value *> derived;
        std::unordered_set<const llvm::Value *> slots;
        derived.insert(Arg);
        bool grew = true;
        for (int guard = 0; grew && guard < 12; ++guard) {
          grew = false;
          for (llvm::Instruction &I : llvm::instructions(*Fn)) {
            bool ok = false;
            if (const auto *B = llvm::dyn_cast<llvm::BitCastInst>(&I))
              ok = derived.count(B->getOperand(0)) > 0;
            else if (const auto *Fz = llvm::dyn_cast<llvm::FreezeInst>(&I))
              ok = derived.count(Fz->getOperand(0)) > 0;
            else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I))
              ok = derived.count(G->getPointerOperand()) > 0;
            else if (const auto *P = llvm::dyn_cast<llvm::PHINode>(&I)) {
              ok = P->getNumIncomingValues() > 0;
              for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
                ok = ok && derived.count(P->getIncomingValue(i)) > 0;
            } else if (const auto *S = llvm::dyn_cast<llvm::SelectInst>(&I))
              ok = derived.count(S->getTrueValue()) > 0 && derived.count(S->getFalseValue()) > 0;
            else if (const auto *L = llvm::dyn_cast<llvm::LoadInst>(&I))
              ok = slots.count(L->getPointerOperand()->stripPointerCasts()) > 0;
            if (ok && derived.insert(&I).second)
              grew = true;
            if (const auto *St = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              const llvm::Value *Dst = St->getPointerOperand()->stripPointerCasts();
              if (derived.count(St->getValueOperand()) > 0 && llvm::isa<llvm::AllocaInst>(Dst) && slots.insert(Dst).second)
                grew = true;
            }
          }
        }
        for (const llvm::Value *V : derived) {
          const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(V);
          if (!G)
            continue;
          llvm::Type *Src = G->getSourceElementType();
          if (const auto *AT = llvm::dyn_cast<llvm::ArrayType>(Src))
            Src = AT->getElementType();
          if (const auto *ST = llvm::dyn_cast<llvm::StructType>(Src)) {
            int id = internType(ST);
            if (id > 0)
              tys.insert(id);
          }
        }
        for (llvm::Instruction &I : llvm::instructions(*Fn)) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm())
            continue;
          auto *Cal = llvm::dyn_cast<llvm::Function>(CB->getCalledOperand()->stripPointerCasts());
          if (!Cal)
            continue;
          if (Cal->isDeclaration()) {
            auto nit = byName.find(Cal->getName().str());
            if (nit != byName.end())
              Cal = nit->second;
          }
          for (unsigned i = 0; i < CB->arg_size(); ++i)
            if (derived.count(CB->getArgOperand(i)) > 0)
              self(Cal, (int)i, depth + 1, self);
        }
      };
      strict(from, arg, 0, strict);
      pointedTy.emplace(pk, std::move(tys));
    };
    auto charArg = [&](llvm::Function *from, int arg) {
      auto it = pointedTy.find(packPtr(from, arg));
      if (it == pointedTy.end() || it->second.empty())
        return argDiChar(from, arg);
      for (int id : it->second) {
        if (id <= 0 || id > (int)typeName.size() || !stringTypeName(typeName[(size_t)id - 1]))
          return false;
      }
      return true;
    };
    for (const auto &kvIn : *inMap)
      for (const Input &in : kvIn.second) {
        llvm::Function *who = lookupFn(in.func);
        if (who && in.arg >= 0)
          fillPointed(who, in.arg);
      }
    auto pointerHits = [&](llvm::Function *from, int arg, llvm::Function *to, int formal) {
      auto it = pointedAt.find(packPtr(from, arg));
      return it != pointedAt.end() && it->second.count(packPtr(to, formal)) > 0;
    };
    std::unordered_map<OKey, std::vector<AHit>, OKeyHash> anchorAt;
    {
      struct Item {
        llvm::Function *fn;
        int formal;
        llvm::Function *who;
        int arg;
        std::vector<llvm::Function *> seq;
      };
      std::vector<Item> q;
      std::unordered_set<AK, AKHash> seen;
      for (const auto &kvIn : *inMap) {
        llvm::Function *chop = lookupFn(kvIn.first);
        if (!chop)
          continue;
        for (const Input &in : kvIn.second) {
          if (in.arg < 0 || in.chopArg < 0 || in.chopArg >= (int)chop->arg_size())
            continue;
          llvm::Function *who = lookupFn(in.func);
          if (!who || charArg(who, in.arg))
            continue;
          if (!pointerHits(who, in.arg, chop, in.chopArg))
            continue;
          Item it;
          it.fn = chop;
          it.formal = in.chopArg;
          it.who = who;
          it.arg = in.arg;
          it.seq = {who, chop};
          q.push_back(std::move(it));
        }
      }
      for (size_t qi = 0; qi < q.size(); ++qi) {
        Item cur = q[qi];
        if (!seen.insert(AK{cur.fn, cur.formal, cur.who, cur.arg}).second)
          continue;
        anchorAt[OKey{cur.fn, cur.formal}].push_back(AHit{cur.who, cur.arg, cur.seq});
        auto sit = sum.find(cur.fn);
        if (sit == sum.end())
          continue;
        for (const Site &site : sit->second.sites)
          for (llvm::Function *T : targetsOf(site, {}))
            for (unsigned i = 0; i < site.args.size(); ++i) {
              const ArgAt &a = site.args[i];
              bool pass = false;
              for (int f : a.formals)
                if (f == cur.formal)
                  pass = true;
              for (int f : a.vformals)
                if (f == cur.formal)
                  pass = true;
              if (!pass)
                continue;
              Item nxt;
              nxt.fn = T;
              nxt.formal = (int)i;
              nxt.who = cur.who;
              nxt.arg = cur.arg;
              nxt.seq = cur.seq;
              nxt.seq.push_back(T);
              q.push_back(std::move(nxt));
            }
      }
    }
    auto anchorLine = [&](const AHit &h, const std::string &path) {
      std::string s = "pass ";
      s += std::to_string(h.arg);
      s += " ";
      s += path;
      s += " :: ";
      s += showFn(h.who);
      s += " :: ";
      for (size_t i = 0; i < h.seq.size(); ++i) {
        if (i != 0)
          s += " => ";
        s += showFn(h.seq[i]);
      }
      return s;
    };

    struct NKey {
      llvm::Function *fn = nullptr;
      int formal = -1;
      int key = 0;
      bool operator==(const NKey &o) const { return fn == o.fn && formal == o.formal && key == o.key; }
    };
    struct NKeyHash {
      size_t operator()(const NKey &k) const {
        return ((size_t)k.fn >> 4) ^ ((size_t)k.formal * 1315423911u) ^ ((size_t)k.key * 0x9e3779b9u);
      }
    };
    struct Origin {
      llvm::Function *fn = nullptr;
      int formal = -1;
      bool operator==(const Origin &o) const { return fn == o.fn && formal == o.formal; }
    };
    struct OHash {
      size_t operator()(const Origin &o) const {
        return ((size_t)o.fn >> 4) ^ ((size_t)o.formal * 1315423911u);
      }
    };
    struct Local {
      int fdep = 0;
      int sdep = 0;
    };
    std::unordered_map<NKey, std::vector<Local>, NKeyHash> locals;
    auto addLocal = [&](llvm::Function *Fn, const Wr &w) {
      if (!Fn || w.formal < 0 || w.key <= 0)
        return;
      locals[NKey{Fn, w.formal, w.key}].push_back(Local{w.fdep, w.sdep});
    };
    for (auto &kv : sum)
      for (const Wr &w : kv.second.writes)
        addLocal(kv.first, w);
    for (const WRef &e : extra)
      addLocal(e.fn, e.w);
    std::unordered_map<NKey, std::vector<NKey>, NKeyHash> preds;
    std::unordered_map<NKey, std::vector<Origin>, NKeyHash> originOf;
    std::unordered_map<NKey, std::unordered_set<Origin, OHash>, NKeyHash> have;
    std::unordered_map<NKey, char, NKeyHash> built;
    auto addOrigin = [&](const NKey &n, llvm::Function *Fn, int formal) {
      if (!Fn || formal < 0)
        return false;
      if (!have[n].insert(Origin{Fn, formal}).second)
        return false;
      originOf[n].push_back(Origin{Fn, formal});
      return true;
    };
    auto buildSlot = [&](NKey start) {
      std::vector<NKey> stack;
      stack.push_back(start);
      while (!stack.empty()) {
        NKey n = stack.back();
        stack.pop_back();
        if (built[n])
          continue;
        built[n] = 1;
        auto lit = locals.find(n);
        if (lit != locals.end()) {
          for (const Local &L : lit->second) {
            if (L.fdep > 0 && L.fdep < (int)fdeps.size())
              for (int f : fdeps[L.fdep])
                addOrigin(n, n.fn, f);
            if (L.sdep > 0 && L.sdep < (int)sdeps.size())
              for (int sid : sdeps[L.sdep]) {
                if (sid <= 0 || sid >= (int)slots.size())
                  continue;
                const Slot &sl = slots[sid];
                if (sl.formal < 0 || sl.key <= 0)
                  continue;
                if (sl.formal == n.formal && sl.key == n.key)
                  continue;
                NKey p{n.fn, sl.formal, sl.key};
                preds[n].push_back(p);
                if (!built[p])
                  stack.push_back(p);
              }
          }
        }
        auto linkCaller = [&](llvm::Function *caller, const Site &site) {
          if (!caller || n.formal < 0 || n.formal >= (int)site.args.size())
            return;
          for (int p : site.args[(size_t)n.formal].formals) {
            if (p < 0)
              continue;
            NKey c{caller, p, n.key};
            preds[n].push_back(c);
            if (!built[c])
              stack.push_back(c);
          }
        };
        auto dit = directAt.find(n.fn);
        if (dit != directAt.end())
          for (const SiteRef &r : dit->second)
            linkCaller(r.caller, *r.site);
        auto vit = viaFn.find(n.fn);
        if (vit != viaFn.end())
          for (const SiteRef &r : vit->second)
            linkCaller(r.caller, *r.site);
      }
    };
    auto seedSlots = [&](llvm::Function *Fn, const Wr &w) {
      if (!Fn || !K.count(w.key) || w.sdep <= 0 || w.sdep >= (int)sdeps.size())
        return;
      for (int sid : sdeps[w.sdep]) {
        if (sid <= 0 || sid >= (int)slots.size())
          continue;
        const Slot &sl = slots[sid];
        if (sl.formal < 0 || sl.key <= 0)
          continue;
        buildSlot(NKey{Fn, sl.formal, sl.key});
      }
    };
    for (auto &kv : sum)
      for (const Wr &w : kv.second.writes)
        seedSlots(kv.first, w);
    for (const WRef &e : extra)
      seedSlots(e.fn, e.w);
    std::unordered_map<NKey, std::vector<NKey>, NKeyHash> fwd;
    for (auto &kv : preds) {
      std::vector<NKey> ps = kv.second;
      std::sort(ps.begin(), ps.end(), [](const NKey &a, const NKey &b) {
        if (a.fn != b.fn)
          return a.fn < b.fn;
        if (a.formal != b.formal)
          return a.formal < b.formal;
        return a.key < b.key;
      });
      ps.erase(std::unique(ps.begin(), ps.end()), ps.end());
      for (const NKey &p : ps)
        fwd[p].push_back(kv.first);
    }
    std::vector<NKey> oq;
    std::unordered_set<NKey, NKeyHash> oinq;
    for (auto &kv : originOf)
      if (!kv.second.empty() && oinq.insert(kv.first).second)
        oq.push_back(kv.first);
    for (size_t qi = 0; qi < oq.size() && qi < 20000000; ++qi) {
      NKey n = oq[qi];
      oinq.erase(n);
      auto fit = fwd.find(n);
      if (fit == fwd.end())
        continue;
      std::vector<Origin> src = originOf[n];
      for (const NKey &d : fit->second) {
        bool grew = false;
        for (const Origin &o : src)
          if (addOrigin(d, o.fn, o.formal))
            grew = true;
        if (grew && oinq.insert(d).second)
          oq.push_back(d);
      }
    }

    std::vector<Cell> out;
    std::unordered_set<std::string> seen;
    auto emit = [&](llvm::Function *F, const Wr &w) {
      if (!F || !F->hasName() || w.path <= 0)
        return;
      int ty = steps[w.path].type;
      std::string type = ty > 0 && ty <= (int)typeName.size() ? typeName[ty - 1] : "";
      if (!K.count(w.key))
        return;
      std::string path = pathString(w.formal, w.path);
      std::string key = std::to_string(w.key) + " " + F->getName().str() + " " + std::to_string(w.len) + " " + w.fn +
                        " " + path;
      if (!seen.insert(key).second)
        return;
      Cell c;
      c.chopArg = -1;
      c.off = steps[w.path].off;
      c.len = w.len;
      c.func = F->getName().str();
      c.fn = w.fn;
      c.type = std::move(type);
      c.path = std::move(path);
      std::vector<Hit> hits;
      auto takeAt = [&](llvm::Function *G, int formal) {
        if (!G || formal < 0)
          return;
        for (const Hit &h : hitsOf(G, formal))
          hits.push_back(h);
        auto ait = anchorAt.find(OKey{G, formal});
        if (ait == anchorAt.end())
          return;
        for (const AHit &h : ait->second)
          c.roots.push_back(anchorLine(h, c.path));
      };
      takeAt(F, w.formal);
      if (w.fdep > 0 && w.fdep < (int)fdeps.size())
        for (int f : fdeps[w.fdep])
          takeAt(F, f);
      if (w.sdep > 0 && w.sdep < (int)sdeps.size())
        for (int sid : sdeps[w.sdep]) {
          if (sid <= 0 || sid >= (int)slots.size())
            continue;
          const Slot &sl = slots[sid];
          if (sl.formal < 0 || sl.key <= 0)
            continue;
          auto oit = originOf.find(NKey{F, sl.formal, sl.key});
          if (oit == originOf.end())
            continue;
          for (const Origin &o : oit->second)
            takeAt(o.fn, o.formal);
        }
      auto rit = reachFromChop.find(F);
      if (rit != reachFromChop.end())
        for (const Reach &r : rit->second) {
          if (r.who && charArg(r.who, r.arg)) {
            bool chars = true;
            for (int p = w.path; p > 0; p = steps[p].parent) {
              int ty = steps[p].type;
              if (ty <= 0 || ty > (int)typeName.size())
                continue;
              if (!stringTypeName(typeName[(size_t)ty - 1]))
                chars = false;
            }
            if (!chars)
              continue;
          }
          AHit h;
          h.who = r.who;
          h.arg = r.arg;
          h.seq = r.seq;
          c.roots.push_back(anchorLine(h, c.path));
        }
      if (c.roots.empty() && hits.empty())
        return;
      for (const Hit &h : hits) {
        if (h.who && charArg(h.who, h.arg)) {
          bool chars = true;
          for (int p = w.path; p > 0; p = steps[p].parent) {
            int ty = steps[p].type;
            if (ty <= 0 || ty > (int)typeName.size())
              continue;
            if (!stringTypeName(typeName[(size_t)ty - 1]))
              chars = false;
          }
          if (!chars)
            continue;
        }
        c.roots.push_back(rootLine(h, c.path));
      }
      if (c.roots.empty())
        return;
      std::sort(c.roots.begin(), c.roots.end());
      c.roots.erase(std::unique(c.roots.begin(), c.roots.end()), c.roots.end());
      out.push_back(std::move(c));
    };
    for (auto &kv : sum)
      for (const Wr &w : kv.second.writes)
        emit(kv.first, w);
    for (const WRef &e : extra)
      emit(e.fn, e.w);
    std::sort(out.begin(), out.end(), [](const Cell &a, const Cell &b) {
      if (a.type != b.type)
        return a.type < b.type;
      if (a.off != b.off)
        return a.off < b.off;
      if (a.func != b.func)
        return a.func < b.func;
      return a.fn < b.fn;
    });
    std::vector<std::string> seqs;
    std::unordered_set<std::string> seenSeq;
    for (const auto &kv : reachFromChop)
      for (const Reach &r : kv.second) {
        if (!r.who || r.seq.empty())
          continue;
        std::string s = "pass ";
        s += std::to_string(r.arg);
        s += " :: ";
        s += showFn(r.who);
        s += " :: ";
        for (size_t i = 0; i < r.seq.size(); ++i) {
          if (i != 0)
            s += " => ";
          s += showFn(r.seq[i]);
        }
        if (seenSeq.insert(s).second)
          seqs.push_back(std::move(s));
      }
    std::sort(seqs.begin(), seqs.end());
    return FieldReport{std::move(out), std::move(seqs)};
  }
};

} // namespace

FieldReport fieldCells(llvm::Module &downstream, llvm::Module &upstream, const std::string &sinkFile,
                       unsigned sinkLine, const std::vector<std::string> &sinkFns,
                       const std::vector<std::string> &chops,
                       const std::unordered_map<std::string, std::vector<Input>> &inputs) {
  Engine E(downstream, upstream, sinkFile, sinkLine, sinkFns);
  return E.run(chops, inputs);
}

} // namespace chain
