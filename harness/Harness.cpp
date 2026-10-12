#include "Harness.hpp"

#include <cctype>
#include <sstream>
#include <unordered_set>

namespace harness {

namespace {

void splitDefs(const std::vector<realdef::UseDef> &uses, std::vector<std::string> &useNames,
               std::vector<realdef::Def> &symbolic, std::vector<realdef::Def> &writes) {
  for (const realdef::UseDef &u : uses) {
    useNames.push_back(u.use);
    for (const realdef::Def &d : u.defs) {
      if (d.kind == "external")
        symbolic.push_back(d);
      else
        writes.push_back(d);
    }
  }
}

} // namespace

std::vector<Spec> specs(const std::vector<chain::EntryGroup> &groups,
                        const std::vector<realdef::UseDef> &uses) {
  std::vector<std::string> useNames;
  std::vector<realdef::Def> symbolic;
  std::vector<realdef::Def> writes;
  splitDefs(uses, useNames, symbolic, writes);

  std::vector<Spec> out;
  for (const chain::EntryGroup &g : groups) {
    if (g.entries.empty())
      continue;
    if (!g.flow) {
      Spec s;
      s.chop = g.chop;
      s.calls = g.entries;
      for (const realdef::Def &d : symbolic)
        if (d.func.empty() || d.func == g.chop)
          s.symbolic.push_back(d);
      s.writes = writes;
      s.uses = useNames;
      out.push_back(std::move(s));
      continue;
    }
    std::vector<int> want;
    for (const realdef::Def &d : symbolic)
      if (d.func == g.chop && d.arg >= 0)
        want.push_back(d.arg);
    auto wanted = [&](int chopArg) {
      if (want.empty())
        return true;
      for (int a : want)
        if (a == chopArg)
          return true;
      return false;
    };
    const std::vector<std::string> &roots = g.initial.empty() ? g.entries : g.initial;
    std::unordered_set<int> covered;
    auto finish = [&](Spec &s) {
      s.writes = writes;
      s.uses = useNames;
      out.push_back(std::move(s));
    };
    for (const std::string &root : roots) {
      Spec s;
      s.chop = g.chop;
      s.calls = {root};
      for (const chain::Input &in : g.inputs) {
        if (in.func != root || in.arg < 0 || !wanted(in.chopArg))
          continue;
        covered.insert(in.chopArg);
        realdef::Def d;
        d.kind = "input";
        d.func = in.func;
        d.arg = in.arg;
        d.chopArg = in.chopArg;
        s.symbolic.push_back(std::move(d));
      }
      for (const chain::Input &in : g.unreduced) {
        if (in.func != root || !wanted(in.chopArg))
          continue;
        realdef::Def d;
        d.kind = "open";
        d.func = in.func;
        d.chopArg = in.chopArg;
        s.symbolic.push_back(std::move(d));
      }
      if (s.symbolic.empty())
        continue;
      finish(s);
    }
    Spec open;
    open.chop = g.chop;
    open.calls = roots;
    for (const chain::Input &in : g.inputs) {
      if (in.arg >= 0 || !wanted(in.chopArg) || covered.count(in.chopArg))
        continue;
      realdef::Def d;
      d.kind = "input";
      d.func = in.func;
      d.arg = in.arg;
      d.chopArg = in.chopArg;
      open.symbolic.push_back(std::move(d));
    }
    for (int a : g.openArgs) {
      if (!wanted(a) || covered.count(a))
        continue;
      realdef::Def d;
      d.kind = "open";
      d.chopArg = a;
      open.symbolic.push_back(std::move(d));
    }
    if (!open.symbolic.empty())
      finish(open);
  }
  return out;
}

namespace {

std::string trim(const std::string &s) {
  size_t b = 0;
  while (b < s.size() && std::isspace(static_cast<unsigned char>(s[b])))
    ++b;
  size_t e = s.size();
  while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1])))
    --e;
  return s.substr(b, e - b);
}

} // namespace

std::vector<chain::EntryGroup> loadEntries(const std::string &text) {
  std::vector<chain::EntryGroup> groups;
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) {
    if (line.rfind("chop ", 0) == 0) {
      chain::EntryGroup g;
      g.chop = line.substr(5);
      groups.push_back(std::move(g));
      continue;
    }
    if (groups.empty())
      continue;
    if (line == "flow") {
      groups.back().flow = true;
      continue;
    }
    if (line.rfind("input ", 0) == 0) {
      std::istringstream ls(line.substr(6));
      chain::Input in;
      ls >> in.chopArg >> in.arg;
      std::string name;
      std::getline(ls, name);
      in.func = trim(name);
      groups.back().inputs.push_back(std::move(in));
      groups.back().flow = true;
      continue;
    }
    if (line.rfind("open ", 0) == 0) {
      std::istringstream ls(line.substr(5));
      int a = 0;
      ls >> a;
      std::string name;
      std::getline(ls, name);
      name = trim(name);
      if (name.empty())
        groups.back().openArgs.push_back(a);
      else {
        chain::Input in;
        in.chopArg = a;
        in.arg = -1;
        in.func = name;
        groups.back().unreduced.push_back(std::move(in));
      }
      groups.back().flow = true;
      continue;
    }
    if (line.rfind("initial ", 0) == 0) {
      std::string name = line.substr(8);
      if (name != "(none)")
        groups.back().initial.push_back(name);
      continue;
    }
    if (line.rfind("entry ", 0) != 0)
      continue;
    std::string name = line.substr(6);
    if (name != "(none)")
      groups.back().entries.push_back(name);
  }
  return groups;
}

std::vector<realdef::UseDef> loadDefs(const std::string &text) {
  std::vector<realdef::UseDef> uses;
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) {
    std::string t = trim(line);
    if (t.rfind("use ", 0) == 0) {
      realdef::UseDef u;
      u.use = t.substr(4);
      uses.push_back(std::move(u));
      continue;
    }
    if (t.rfind("def ", 0) != 0 || uses.empty())
      continue;
    std::istringstream ls(t.substr(4));
    std::string kind;
    ls >> kind;
    if (kind != "external" && kind != "store" && kind != "init")
      continue;
    realdef::Def d;
    d.kind = kind;
    std::string func;
    if (!(ls >> func)) {
      uses.back().defs.push_back(std::move(d));
      continue;
    }
    std::string tok;
    if (!(ls >> tok)) {
      d.func = func;
      uses.back().defs.push_back(std::move(d));
      continue;
    }
    if (tok == "arg") {
      d.func = func;
      ls >> d.arg;
      uses.back().defs.push_back(std::move(d));
      continue;
    }
    d.func = func;
    auto colon = tok.rfind(':');
    if (colon != std::string::npos && colon + 1 < tok.size()) {
      d.file = tok.substr(0, colon);
      d.line = static_cast<unsigned>(std::stoul(tok.substr(colon + 1)));
    }
    if (ls >> tok && tok == "arg")
      ls >> d.arg;
    uses.back().defs.push_back(std::move(d));
  }
  return uses;
}

std::string format(const std::vector<Spec> &out) {
  std::ostringstream o;
  for (const Spec &s : out) {
    o << "chop " << s.chop << "\n";
    for (const std::string &c : s.calls)
      o << "call " << c << "\n";
    for (const std::string &u : s.uses)
      o << "use " << u << "\n";
    for (const realdef::Def &d : s.symbolic) {
      o << "symbolic ";
      if (d.kind == "open")
        o << "open ";
      o << d.func;
      if (!d.file.empty())
        o << " " << d.file << ":" << d.line;
      if (d.arg >= 0)
        o << " arg " << d.arg;
      if (d.chopArg >= 0)
        o << " chop-arg " << d.chopArg;
      o << "\n";
    }
    for (const realdef::Def &d : s.writes)
      o << "write " << d.kind << " " << d.func << " " << d.file << ":" << d.line << "\n";
  }
  return o.str();
}

} // namespace harness
