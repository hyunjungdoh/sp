#include "Field.hpp"

#include "llvm/Demangle/Demangle.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
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

struct Ret {
  int formal = -1;
  int path = 0;
  int dep = 0;
};

struct Wr {
  int formal = -1;
  int path = 0;
  int64_t len = 0;
  int dep = 0;
  int key = 0;
  std::string fn;
};

struct CopySite {
  int df = -1, dp = 0, sf = -1, sp = 0;
  int64_t n = 0;
  bool anyN = true;
};

struct ArgAt {
  std::vector<int> keys;
  std::vector<int> formals;
};

struct Site {
  llvm::Function *callee = nullptr;
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
  }

  std::vector<Cell> run() {
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
  std::vector<std::vector<int>> deps;
  std::unordered_map<std::vector<int>, int, VecHash> depMemo;
  std::unordered_map<std::uint64_t, int> uniteMemo;

  std::unordered_map<std::string, llvm::Function *> byName;
  std::unordered_map<llvm::Function *, std::vector<llvm::Function *>> callers, callees;
  std::unordered_map<llvm::Function *, std::unordered_set<llvm::Function *>> indirectCallers;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> watchers;
  std::vector<llvm::Function *> order;
  std::unordered_map<llvm::Function *, int> ord;
  std::unordered_map<llvm::Function *, FnSum> sum;
  std::unordered_map<int, std::unordered_set<llvm::Function *>> fnAt;
  std::vector<WRef> extra;

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
      return id;
    }
    int id = (int)typeName.size() + 1;
    typeName.push_back("anon" + std::to_string(id));
    typeId.emplace(T, id);
    return id;
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

  int lastKey(int path) {
    if (path <= 0)
      return 0;
    int type = steps[path].type;
    int64_t off = steps[path].off;
    if (type <= 0)
      return 0;
    auto it = keys.find({type, off});
    if (it != keys.end())
      return it->second;
    int id = (int)keys.size() + 1;
    keys.emplace(std::pair<int, int64_t>{type, off}, id);
    return id;
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
        takeRet(target);
        ensurePointer();
        return;
      }
      std::unordered_set<llvm::Function *> targets;
      auto consider = [&](const llvm::Value *op) {
        auto it = byVal.find(op);
        if (it == byVal.end())
          return;
        for (const VKey &s : it->second) {
          int key = lastKey(s.path);
          if (key <= 0)
            continue;
          watchers[key].insert(&F);
          auto fit = fnAt.find(key);
          if (fit != fnAt.end())
            targets.insert(fit->second.begin(), fit->second.end());
          for (const WRef &e : extra) {
            if (e.w.key == key && !e.w.fn.empty()) {
              auto nit = byName.find(e.w.fn);
              if (nit != byName.end())
                targets.insert(nit->second);
            }
          }
        }
      };
      consider(CB->getCalledOperand());
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

    FnSum next;
    if (F.hasName()) {
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *St = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!St)
          continue;
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
          next.writes.push_back(std::move(w));
          if (!fn.empty()) {
            auto nit = byName.find(fn);
            if (nit != byName.end())
              fnAt[key].insert(nit->second);
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
        if (r.dep != 0)
          next.rets.push_back(r);
        continue;
      }
      for (const VKey &s : it->second) {
        auto st = state.find(s);
        Ret r;
        r.formal = s.formal;
        r.path = s.path;
        r.dep = st == state.end() ? 0 : st->second;
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
          auto it = byVal.find(CB->getCalledOperand());
          if (it != byVal.end())
            for (const VKey &s : it->second) {
              int key = lastKey(s.path);
              if (key > 0) {
                site.calleeKeys.push_back(key);
                next.indirectKeys.push_back(key);
              }
            }
        }
        site.args.resize(CB->arg_size());
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          ArgAt &a = site.args[i];
          int d = depOf(arg);
          if (d > 0)
            a.keys.insert(a.keys.end(), deps[d].begin(), deps[d].end());
          auto it = byVal.find(arg);
          if (it == byVal.end())
            continue;
          for (const VKey &s : it->second) {
            int key = lastKey(s.path);
            if (key > 0)
              a.keys.push_back(key);
            if (s.formal >= 0)
              a.formals.push_back(s.formal);
          }
          std::sort(a.keys.begin(), a.keys.end());
          a.keys.erase(std::unique(a.keys.begin(), a.keys.end()), a.keys.end());
          std::sort(a.formals.begin(), a.formals.end());
          a.formals.erase(std::unique(a.formals.begin(), a.formals.end()), a.formals.end());
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

  std::vector<Cell> answer() {
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
    std::unordered_map<llvm::Function *, std::vector<SiteRef>> viaFn;
    for (auto &kv : fnAt) {
      auto sit = indirectAt.find(kv.first);
      if (sit == indirectAt.end())
        continue;
      for (llvm::Function *T : kv.second)
        viaFn[T].insert(viaFn[T].end(), sit->second.begin(), sit->second.end());
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
        for (const SiteRef &r : iit->second)
          for (unsigned i = 0; i < r.site->args.size(); ++i)
            addFormal(T, (int)i);
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
    return out;
  }
};

} // namespace

std::vector<Cell> fieldCells(llvm::Module &downstream, llvm::Module &upstream, const std::string &sinkFile,
                             unsigned sinkLine, const std::vector<std::string> &sinkFns) {
  Engine E(downstream, upstream, sinkFile, sinkLine, sinkFns);
  return E.run();
}

} // namespace chain
