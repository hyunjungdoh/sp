#include "Model.h"

bool Model::solve(const std::vector<Function *> &seq, raw_ostream &out) {
  entryKnown.clear();
  // Each pass seeds the path choice with the previous pass's entry constants.
  // A fixed point is reached when they agree; the bound stops a cycle.
  for (unsigned pass = 0;; ++pass) {
    stepTested.clear();
    entryKnownNext.clear();
    std::string text;
    raw_string_ostream os(text);
    bool ok = solveOnce(seq, os);
    os.flush();
    if (entryKnownNext == entryKnown || pass == 3) {
      // §3.12: the sink guard and sink dependencies of a satisfiable sequence
      // go inside its block, before the "sat" delimiter the reader splits on.
      const std::string tail = "sat\n";
      bool endsSat = text.size() >= tail.size() && text.compare(text.size() - tail.size(), tail.size(), tail) == 0 &&
                     (text.size() == tail.size() || text[text.size() - tail.size() - 1] == '\n');
      if (ok && endsSat) {
        text.resize(text.size() - tail.size());
        raw_string_ostream so(text);
        sinkFacts(seq, so);
        so.flush();
        text += tail;
      }
      out << text;
      return ok;
    }
    entryKnown = std::move(entryKnownNext);
  }
}

bool Model::solveOnce(const std::vector<Function *> &seq, raw_ostream &out) {
#include "SolveEvents.inc"
#include "SolveClose.inc"
}
