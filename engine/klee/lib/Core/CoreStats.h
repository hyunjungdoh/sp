//===-- CoreStats.h ---------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CORESTATS_H
#define KLEE_CORESTATS_H

#include "klee/Core/BranchTypes.h"
#include "klee/Core/TerminationTypes.h"
#include "klee/Statistics/Statistic.h"

namespace klee {
namespace stats {

  extern Statistic allocations;
  extern Statistic resolveTime;
  extern Statistic instructions;
  extern Statistic instructionTime;
  extern Statistic instructionRealTime;
  extern Statistic coveredInstructions;
  extern Statistic uncoveredInstructions;  
  extern Statistic trueBranches;
  extern Statistic falseBranches;
  extern Statistic forkTime;
  extern Statistic solverTime;

  /// The number of external calls.
  extern Statistic externalCalls;

  /// The number of process forks.
  extern Statistic forks;

  /// Number of inhibited forks.
  extern Statistic inhibitedForks;

  /// Number of states, this is a "fake" statistic used by istats, it
  /// isn't normally up-to-date.
  extern Statistic states;

  /// Instruction level statistic tracking the minimum intraprocedural
  /// distance to an uncovered instruction; this is only periodically
  /// updated.
  extern Statistic minDistToUncovered;

  /// Instruction level statistic tracking the minimum intraprocedural
  /// distance to a function return.
  extern Statistic minDistToReturn;

  /// Instruction level statistic for `nurs:sink`. Stored value is the
  /// design distance plus one, so the sink instruction itself is 1 and
  /// 0 means the sink is unreachable from here. The search weight
  /// 1/stored^2 is the design weight 1/(d+1)^2.
  extern Statistic minDistToSink;

  /// minDistToReturn and minDistToSink over the call graph of slot targets.
  extern Statistic minDistToReturnSlot;
  extern Statistic minDistToSinkSlot;
  /// minDistToSink when a call descends toward the sink only along a
  /// witness edge (T_W). Return distances are those of the slot graph.
  extern Statistic minDistToSinkWit;
  /// Distance to an input-dispatch installer (sp.st, §3.7 D item 2).
  extern Statistic minDistToSt;

  /// Count branch types in execution tree. Inhibited branches are ignored.
  #undef BTYPE
  #define BTYPE(Name,I) extern Statistic branches ## Name;
  BRANCH_TYPES

  /// Count termination types.
  #undef TCLASS
  #define TCLASS(Name,I) extern Statistic termination ## Name;
  TERMINATION_CLASSES

  /// Increase a branch statistic for the given reason by value.
  void incBranchStat(BranchType reason, std::uint32_t value);
}
}

#endif /* KLEE_CORESTATS_H */
