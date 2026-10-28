#include "Calls.h"
#include "../../engine/klee/include/klee/Support/CallTargets.h"

#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <sstream>

using namespace llvm;

namespace calls {

// One line per function with indirect sites, one per site, tab-separated:
//   fn <side> <name>
//   site <side> <name> <side> <name> ...
void write(const Table &t, const std::filesystem::path &p) {
  std::ofstream out(p);
  for (const auto &[f, sites] : t) {
    out << "fn\t" << f.first << "\t" << f.second << "\n";
    for (const auto &ts : sites) {
      out << "site";
      for (const Fn &g : ts)
        out << "\t" << g.first << "\t" << g.second;
      out << "\n";
    }
  }
}

bool read(Table &t, const std::filesystem::path &p) {
  std::ifstream in(p);
  if (!in)
    return false;
  std::vector<std::vector<Fn>> *cur = nullptr;
  for (std::string line; std::getline(in, line);) {
    std::vector<std::string> f;
    std::istringstream s(line);
    for (std::string x; std::getline(s, x, '\t');)
      f.push_back(x);
    if (f.size() == 3 && f[0] == "fn" && f[1].size() == 1) {
      cur = &t[{f[1][0], f[2]}];
    } else if (!f.empty() && f[0] == "site" && cur && f.size() % 2 == 1) {
      std::vector<Fn> ts;
      for (size_t i = 1; i + 1 < f.size(); i += 2)
        ts.push_back({f[i][0], f[i + 1]});
      cur->push_back(ts);
    } else {
      return false;
    }
  }
  return true;
}

bool annotate(Module &D, Module &U, const Table &t) {
  LLVMContext &C = D.getContext();
  Type *i64 = Type::getInt64Ty(C);
  // A function linking may merge (one name defined in both) has one id, so
  // the definition that survives carries it.
  std::map<Fn, uint64_t> ids;
  auto key = [](char side, const Function &F) { return F.hasLocalLinkage() ? Fn{side, F.getName().str()} : Fn{'*', F.getName().str()}; };
  auto idOf = [&](char side, const Function &F) { return ids.emplace(key(side, F), ids.size()).first->second; };
  for (auto [side, M] : {std::pair<char, Module *>{'D', &D}, {'U', &U}})
    for (Function &F : *M)
      if (!F.isDeclaration())
        F.setMetadata("sp.fn", MDNode::get(C, {ConstantAsMetadata::get(ConstantInt::get(i64, idOf(side, F)))}));
  unsigned bad = 0;
  for (auto [side, M] : {std::pair<char, Module *>{'D', &D}, {'U', &U}})
    for (Function &F : *M) {
      if (F.isDeclaration())
        continue;
      auto it = t.find({side, F.getName().str()});
      size_t k = 0, n = it == t.end() ? 0 : it->second.size();
      for (Instruction &I : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || !klee::calls::indirect(*CB))
          continue;
        if (k >= n) {
          ++k;
          continue;
        }
        std::vector<Metadata *> ops;
        for (const Fn &g : it->second[k]) {
          Function *T = (g.first == 'D' ? D : U).getFunction(g.second);
          if (T && !T->isDeclaration())
            ops.push_back(ConstantAsMetadata::get(ConstantInt::get(i64, idOf(g.first, *T))));
        }
        CB->setMetadata("sp.tgt", MDNode::get(C, ops));
        ++k;
      }
      if (k != n) {
        errs() << "calls: " << side << " " << F.getName() << " has " << k << " indirect sites, table " << n << "\n";
        ++bad;
      }
    }
  return bad == 0;
}

} // namespace calls
