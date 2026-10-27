//===-- StatsTracker.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_STATSTRACKER_H
#define KLEE_STATSTRACKER_H

#include "CallPathManager.h"
#include "klee/System/Time.h"

#include <memory>
#include <set>
#include <sqlite3.h>

namespace llvm {
  class BranchInst;
  class Function;
  class Instruction;
  class raw_fd_ostream;
}

namespace klee {
  class ExecutionState;
  class Executor;
  class InstructionInfoTable;
  class InterpreterHandler;
  struct KInstruction;
  struct StackFrame;

  class StatsTracker {
    friend class WriteStatsTimer;
    friend class WriteIStatsTimer;

    Executor &executor;
    std::string objectFilename;

    std::unique_ptr<llvm::raw_fd_ostream> istatsFile;
    ::sqlite3 *statsFile = nullptr;
    ::sqlite3_stmt *transactionBeginStmt = nullptr;
    ::sqlite3_stmt *transactionEndStmt = nullptr;
    ::sqlite3_stmt *insertStmt = nullptr;
    std::uint32_t statsCommitEvery;
    std::uint32_t statsWriteCount = 0;
    time::Point startWallTime;

    unsigned numBranches;
    unsigned fullBranches, partialBranches;

    CallPathManager callPathManager;

    bool updateMinDistToUncovered;

  public:
    static bool useStatistics();
    static bool useIStats();

  private:
    void updateStateStatistics(uint64_t addend);
    void writeStatsHeader();
    void writeStatsLine();
    void writeIStats();

  public:
    StatsTracker(Executor &_executor, std::string _objectFilename,
                 bool _updateMinDistToUncovered);
    ~StatsTracker();

    StatsTracker(const StatsTracker &other) = delete;
    StatsTracker(StatsTracker &&other) noexcept = delete;
    StatsTracker &operator=(const StatsTracker &other) = delete;
    StatsTracker &operator=(StatsTracker &&other) noexcept = delete;

    // called after a new StackFrame has been pushed (for callpath tracing)
    void framePushed(ExecutionState &es, StackFrame *parentFrame);

    // called after a StackFrame has been popped
    void framePopped(ExecutionState &es);

    // called when some side of a branch has been visited. it is
    // imperative that this be called when the statistics index is at
    // the index for the branch itself.
    void markBranchVisited(ExecutionState *visitedTrue,
                           ExecutionState *visitedFalse);

    // called when execution is done and stats files should be flushed
    void done();

    // process stats for a single instruction step, es is the state
    // about to be stepped
    void stepInstruction(ExecutionState &es);

    /// Return duration since execution start.
    time::Span elapsed();

    void computeReachableUncovered();
    void computeSinkDistance();
  };

  uint64_t computeMinDistToUncovered(const KInstruction *ki,
                                     uint64_t minDistAtRA);

  /// Stack distance to the sink. `minDistAtRA` is the distance from this
  /// frame's return, already folded over the frames above it. The stored
  /// instruction distance is d+1, and 0 means unreachable.
  uint64_t computeMinDistToSink(const KInstruction *ki, uint64_t minDistAtRA);

  /// The same over the call graph of slot targets (T_slot).
  uint64_t computeMinDistToSinkSlot(const KInstruction *ki,
                                    uint64_t minDistAtRA);

  /// The search order of a state: T_slot when finite, else past every
  /// finite T_slot by T. 0 exactly when T is infinite.
  extern uint64_t sinkGuideOffset;
  uint64_t sinkGuide(uint64_t slot, uint64_t sig);

}

#endif /* KLEE_STATSTRACKER_H */
