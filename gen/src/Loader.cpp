#include "gen/Loader.hpp"

#include <cctype>
#include <cstdint>
#include <fstream>
#include <optional>
#include <string>

namespace gen {

namespace {

std::string trim(std::string s) {
  size_t a = 0;
  while (a < s.size() && std::isspace(static_cast<unsigned char>(s[a])))
    ++a;
  size_t b = s.size();
  while (b > a && std::isspace(static_cast<unsigned char>(s[b - 1])))
    --b;
  return s.substr(a, b - a);
}

bool starts(const std::string &s, const char *p) {
  return s.compare(0, std::char_traits<char>::length(p), p) == 0;
}

unsigned predOf(const std::string &op) {
  if (op == "eq" || op == "in") return 32;
  if (op == "ne") return 33;
  if (op == "ugt") return 34;
  if (op == "uge") return 35;
  if (op == "ult") return 36;
  if (op == "ule") return 37;
  if (op == "sgt") return 38;
  if (op == "sge") return 39;
  if (op == "slt") return 40;
  if (op == "sle") return 41;
  return 0;
}

std::string takeWord(const std::string &s, size_t &i) {
  while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i])))
    ++i;
  size_t j = i;
  while (j < s.size() && !std::isspace(static_cast<unsigned char>(s[j])))
    ++j;
  std::string w = s.substr(i, j - i);
  i = j;
  return w;
}

// A path token ends at a space that is outside template argument lists.
// `unsigned char` inside `<>` is part of the type, not the next field.
std::string takePath(const std::string &s, size_t &i) {
  while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i])))
    ++i;
  int depth = 0;
  size_t j = i;
  while (j < s.size()) {
    char c = s[j];
    if (c == '<')
      ++depth;
    else if (c == '>' && depth > 0)
      --depth;
    else if (depth == 0 && std::isspace(static_cast<unsigned char>(c)))
      break;
    ++j;
  }
  std::string w = s.substr(i, j - i);
  i = j;
  return w;
}

std::vector<std::string> takeVals(const std::string &tok) {
  std::vector<std::string> out;
  size_t i = 0;
  while (i < tok.size()) {
    size_t j = tok.find(',', i);
    if (j == std::string::npos)
      j = tok.size();
    if (j > i)
      out.push_back(tok.substr(i, j - i));
    i = j + 1;
  }
  return out;
}

std::optional<int64_t> takeInt(const std::string &s, size_t &i) {
  while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i])))
    ++i;
  size_t j = i;
  if (j < s.size() && (s[j] == '+' || s[j] == '-'))
    ++j;
  size_t d = j;
  while (j < s.size() && std::isdigit(static_cast<unsigned char>(s[j])))
    ++j;
  if (j == d)
    return std::nullopt;
  int64_t v = std::stoll(s.substr(i, j - i));
  i = j;
  return v;
}

std::optional<Input> parseInput(const std::string &line) {
  size_t i = 6;
  auto chop = takeInt(line, i);
  auto arg = takeInt(line, i);
  if (!chop || !arg)
    return std::nullopt;
  while (i < line.size() && std::isspace(static_cast<unsigned char>(line[i])))
    ++i;
  if (i >= line.size())
    return std::nullopt;
  Input in;
  in.chopArg = static_cast<int>(*chop);
  in.arg = static_cast<int>(*arg);
  in.func = line.substr(i);
  return in;
}

// cell CHOP OFF FUNC LEN [TYPE] [path PATH]
// FUNC is the demangled name of the writer, so it contains spaces. LEN is
// the integer before TYPE, and TYPE is the last token before " path ".
std::optional<Cell> parseCell(const std::string &line) {
  size_t i = 5;
  auto chop = takeInt(line, i);
  if (!chop)
    return std::nullopt;
  while (i < line.size() && std::isspace(static_cast<unsigned char>(line[i])))
    ++i;
  Cell c;
  if (line.compare(i, 3, "any") == 0) {
    c.off = INT64_MIN;
    i += 3;
  } else {
    auto off = takeInt(line, i);
    if (!off)
      return std::nullopt;
    c.off = *off;
  }
  std::string rest = trim(line.substr(i));
  auto mark = rest.rfind(" path ");
  if (mark != std::string::npos) {
    c.path = rest.substr(mark + 6);
    rest = trim(rest.substr(0, mark));
  }
  auto sp = rest.rfind(' ');
  if (sp == std::string::npos) {
    size_t p = 0;
    auto len = takeInt(rest, p);
    if (!len || p != rest.size())
      return std::nullopt;
    c.len = *len;
    return c;
  }
  std::string last = rest.substr(sp + 1);
  std::string head = rest.substr(0, sp);
  size_t p = 0;
  if (!takeInt(last, p) || p != last.size()) {
    auto sp2 = head.rfind(' ');
    if (sp2 == std::string::npos)
      return std::nullopt;
    last = head.substr(sp2 + 1);
    p = 0;
    auto len = takeInt(last, p);
    if (!len || p != last.size())
      return std::nullopt;
    c.len = *len;
  } else {
    c.len = std::stoll(last);
  }
  return c;
}

std::optional<Root> parseRoot(const std::string &line) {
  if (!starts(line, "root pass "))
    return std::nullopt;
  size_t i = 10;
  auto arg = takeInt(line, i);
  if (!arg)
    return std::nullopt;
  while (i < line.size() && std::isspace(static_cast<unsigned char>(line[i])))
    ++i;
  auto a = line.find(" :: ", i);
  if (a == std::string::npos)
    return std::nullopt;
  auto b = line.find(" :: ", a + 4);
  if (b == std::string::npos)
    return std::nullopt;
  Root r;
  r.arg = static_cast<int>(*arg);
  r.path = line.substr(i, a - i);
  r.func = line.substr(a + 4, b - (a + 4));
  return r;
}

} // namespace

Report loadReport(const std::string &path) {
  std::ifstream in(path);
  Report report;
  std::string line;
  Cell *open = nullptr;
  while (std::getline(in, line)) {
    if (!line.empty() && line.back() == '\r')
      line.pop_back();
    if (starts(line, "ptr ")) {
      size_t i = 4;
      auto arg = takeInt(line, i);
      std::string path = trim(line.substr(i));
      if (arg && !path.empty() && report.kept.size()) {
        FnBind f;
        f.arg = static_cast<int>(*arg);
        f.path = std::move(path);
        f.self = true;
        size_t a = report.kept.find(" :: ");
        size_t b = a == std::string::npos ? std::string::npos : report.kept.find(" :: ", a + 4);
        if (a != std::string::npos && b != std::string::npos)
          f.func = report.kept.substr(a + 4, b - (a + 4));
        if (!f.func.empty())
          report.fns.push_back(std::move(f));
      }
      open = nullptr;
    } else if (starts(line, "fn ")) {
      size_t i = 3;
      auto arg = takeInt(line, i);
      std::string path = takePath(line, i);
      std::string name = trim(line.substr(i));
      if (arg && !path.empty() && !name.empty() && report.kept.size()) {
        FnBind f;
        f.arg = static_cast<int>(*arg);
        f.path = std::move(path);
        f.name = std::move(name);
        size_t a = report.kept.find(" :: ");
        size_t b = a == std::string::npos ? std::string::npos : report.kept.find(" :: ", a + 4);
        if (a != std::string::npos && b != std::string::npos)
          f.func = report.kept.substr(a + 4, b - (a + 4));
        if (!f.func.empty())
          report.fns.push_back(std::move(f));
      }
      open = nullptr;
    } else if (starts(line, "file ")) {
      size_t i = 5;
      auto arg = takeInt(line, i);
      auto len = takeInt(line, i);
      if (arg && len && *len >= 0) {
        FileBytes f;
        f.arg = static_cast<int>(*arg);
        f.len = *len;
        f.func = trim(line.substr(i));
        if (!f.func.empty())
          report.files.push_back(std::move(f));
      }
      open = nullptr;
    } else if (starts(line, "kept ")) {
      report.kept = trim(line.substr(5));
      open = nullptr;
    } else if (starts(line, "guard ")) {
      size_t i = 6;
      auto arg = takeInt(line, i);
      std::string op = takeWord(line, i);
      auto len = takeInt(line, i);
      std::string mask;
      if (op == "mask") {
        mask = takeWord(line, i);
        op = takeWord(line, i);
      }
      std::string vals = takeWord(line, i);
      auto sep = line.find(" :: ", i);
      unsigned pred = predOf(op);
      if (arg && len && *len > 0 && pred != 0 && sep != std::string::npos) {
        GuardFix g;
        g.arg = static_cast<int>(*arg);
        g.pred = pred;
        g.len = *len;
        g.mask = mask;
        g.vals = takeVals(vals);
        g.path = trim(line.substr(i, sep - i));
        g.func = trim(line.substr(sep + 4));
        if (!g.path.empty() && !g.func.empty() && !g.vals.empty())
          report.guards.push_back(std::move(g));
      }
      open = nullptr;
    } else if (starts(line, "rel ")) {
      size_t i = 4;
      auto arg = takeInt(line, i);
      auto other = takeInt(line, i);
      std::string op = takeWord(line, i);
      auto len = takeInt(line, i);
      auto sep = line.find(" :: ", i);
      auto sep2 = sep == std::string::npos ? sep : line.find(" :: ", sep + 4);
      unsigned pred = predOf(op);
      if (arg && other && len && *len > 0 && pred != 0 && sep2 != std::string::npos) {
        GuardFix g;
        g.arg = static_cast<int>(*arg);
        g.otherArg = static_cast<int>(*other);
        g.pred = pred;
        g.len = *len;
        g.path = trim(line.substr(i, sep - i));
        g.otherPath = trim(line.substr(sep + 4, sep2 - (sep + 4)));
        g.func = trim(line.substr(sep2 + 4));
        if (!g.path.empty() && !g.otherPath.empty() && !g.func.empty())
          report.guards.push_back(std::move(g));
      }
      open = nullptr;
    } else if (starts(line, "input ")) {
      if (auto v = parseInput(line))
        report.inputs.push_back(std::move(*v));
      open = nullptr;
    } else if (starts(line, "cell ")) {
      if (auto v = parseCell(line)) {
        report.cells.push_back(std::move(*v));
        open = &report.cells.back();
      } else {
        open = nullptr;
      }
    } else if (starts(line, "root ")) {
      if (open) {
        if (auto v = parseRoot(line))
          open->roots.push_back(std::move(*v));
      }
    } else {
      open = nullptr;
    }
  }
  return report;
}

} // namespace gen
