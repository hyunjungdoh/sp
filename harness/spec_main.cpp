#include "Harness.hpp"

#include <fstream>
#include <iostream>
#include <sstream>

namespace {

std::string readAll(const std::string &path) {
  std::ifstream in(path);
  std::ostringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

} // namespace

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cerr << "usage: harness_spec <entry.txt> <def.log>\n";
    return 1;
  }
  auto groups = harness::loadEntries(readAll(argv[1]));
  auto uses = harness::loadDefs(readAll(argv[2]));
  auto out = harness::specs(groups, uses);
  unsigned calls = 0;
  unsigned symbolic = 0;
  unsigned symbolicNamed = 0;
  unsigned writes = 0;
  for (const harness::Spec &s : out) {
    calls += s.calls.size();
    symbolic += s.symbolic.size();
    writes += s.writes.size();
    for (const realdef::Def &d : s.symbolic)
      if (!d.func.empty())
        ++symbolicNamed;
  }
  std::cout << "queries " << out.size() << " calls " << calls << " symbolic " << symbolic
            << " symbolic-named " << symbolicNamed << " writes " << writes << " uses "
            << (out.empty() ? 0 : out[0].uses.size()) << "\n";
  std::cout << harness::format(out);
  return 0;
}
