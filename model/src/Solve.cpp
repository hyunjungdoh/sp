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
