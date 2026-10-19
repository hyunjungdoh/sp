#include "gen/Driver.hpp"

#include <cctype>
#include <map>
#include <optional>

namespace gen {

namespace {

std::optional<std::vector<Step>> parsePath(const std::string &path) {
  size_t i = 0;
  if (path.compare(0, 3, "ext") == 0) {
    i = 3;
  } else if (path.compare(0, 3, "arg") == 0) {
    i = 3;
    if (i >= path.size() || !std::isdigit(static_cast<unsigned char>(path[i])))
      return std::nullopt;
    while (i < path.size() && std::isdigit(static_cast<unsigned char>(path[i])))
      ++i;
  } else {
    return std::nullopt;
  }
  if (i != path.size() && path[i] != '.')
    return std::nullopt;
  std::vector<Step> steps;
  while (i < path.size()) {
    if (path[i] != '.')
      return std::nullopt;
    ++i;
    auto plus = path.find_first_of("+^*", i);
    if (plus == std::string::npos)
      return std::nullopt;
    Step s;
    s.type = path.substr(i, plus - i);
    s.neu = path[plus] == '^';
    s.both = path[plus] == '*';
    i = plus + 1;
    if (path.compare(i, 3, "any") == 0) {
      s.any = true;
      s.off = 0;
      i += 3;
      if (s.type.empty())
        return std::nullopt;
      steps.push_back(std::move(s));
      continue;
    }
    size_t j = i;
    if (j < path.size() && (path[j] == '+' || path[j] == '-'))
      ++j;
    size_t d = j;
    while (j < path.size() && std::isdigit(static_cast<unsigned char>(path[j])))
      ++j;
    if (j == d)
      return std::nullopt;
    s.off = std::stoll(path.substr(i, j - i));
    if (s.off < 0 || s.type.empty())
      return std::nullopt;
    steps.push_back(std::move(s));
    i = j;
  }
  if (steps.empty()) {
    if (i == path.size() && path.compare(0, 3, "arg") == 0)
      return std::vector<Step>{};
    return std::nullopt;
  }
  return steps;
}

} // namespace

std::vector<Driver> driversOf(const Report &report) {
  std::map<std::string, std::map<int, std::vector<Field>>> byFunc;
  std::map<std::string, std::vector<Rel>> pending;
  for (const Input &in : report.inputs) {
    if (in.arg < 0 || in.func.empty())
      continue;
    byFunc[in.func][in.arg];
  }
  for (const Cell &c : report.cells) {
    if (c.len <= 0)
      continue;
    for (const Root &r : c.roots) {
      auto fit = byFunc.find(r.func);
      if (fit == byFunc.end())
        continue;
      fit->second[r.arg];
      auto ait = fit->second.find(r.arg);
      auto steps = parsePath(!r.path.empty() ? r.path : c.path);
      if (!steps)
        continue;
      Field f;
      f.steps = std::move(*steps);
      f.len = c.len;
      ait->second.push_back(std::move(f));
    }
  }
  for (const GuardFix &g : report.guards) {
    if (g.len <= 0 || g.func.empty() || g.arg < 0)
      continue;
    auto place = [&](int arg, const std::string &path, bool pin, unsigned assumePred,
                     const std::vector<std::string> &vals) {
      auto steps = parsePath(path);
      if (!steps)
        return;
      byFunc[g.func][arg];
      Field f;
      f.steps = std::move(*steps);
      f.len = g.len;
      f.pin = pin;
      if (pin && !vals.empty())
        f.pinVal = vals[0];
      f.assumePred = assumePred;
      f.assumeVals = vals;
      f.mask = g.mask;
      byFunc[g.func][arg].push_back(std::move(f));
    };
    if (g.otherArg >= 0) {
      auto left = parsePath(g.path);
      auto right = parsePath(g.otherPath);
      if (left && right) {
        Rel rel;
        rel.arg = g.arg;
        rel.otherArg = g.otherArg;
        rel.pred = g.pred;
        rel.len = g.len;
        rel.left = std::move(*left);
        rel.right = std::move(*right);
        byFunc[g.func];
        pending[g.func].push_back(std::move(rel));
      }
      place(g.arg, g.path, false, 0, {});
      place(g.otherArg, g.otherPath, false, 0, {});
      continue;
    }
    bool pin = g.mask.empty() && g.pred == 32 && g.vals.size() == 1;
    place(g.arg, g.path, pin, pin ? 0 : g.pred, g.vals);
  }
  for (const FnBind &fn : report.fns) {
    if (fn.func.empty() || fn.arg < 0 || (fn.name.empty() && !fn.self))
      continue;
    auto steps = parsePath(fn.path);
    if (!steps || steps->empty())
      continue;
    byFunc[fn.func][fn.arg];
    Field f;
    f.steps = std::move(*steps);
    f.fn = fn.name;
    f.self = fn.self;
    byFunc[fn.func][fn.arg].push_back(std::move(f));
  }
  std::vector<Driver> drivers;
  for (const FileBytes &f : report.files) {
    if (f.func.empty() || f.len < 0)
      continue;
    byFunc[f.func];
    if (f.arg >= 0)
      byFunc[f.func][f.arg];
  }
  for (auto &fv : byFunc) {
    Driver d;
    d.func = fv.first;
    for (auto &av : fv.second) {
      Argument a;
      a.index = av.first;
      a.fields = std::move(av.second);
      d.args.push_back(std::move(a));
    }
    d.file = false;
    d.fileArg = -1;
    for (const FileBytes &f : report.files) {
      if (f.func != d.func || f.len < 0)
        continue;
      d.file = true;
      if (f.arg >= 0)
        d.fileArg = f.arg;
      if (f.len > d.fileBytes)
        d.fileBytes = f.len;
    }
    auto pit = pending.find(d.func);
    if (pit != pending.end())
      d.rels = std::move(pit->second);
    drivers.push_back(std::move(d));
  }
  return drivers;
}

} // namespace gen
