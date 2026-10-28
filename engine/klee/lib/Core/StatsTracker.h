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

#include <cstdint>
#include <memory>
#include <set>
#include <sqlite3.h>
#include <vector>

namespace llvm {
  class BranchInst;
  class CallBase;
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

  /// The same with calls descending toward the sink only along witness
  /// edges (T_W).
  uint64_t computeMinDistToSinkWit(const KInstruction *ki,
                                   uint64_t minDistAtRA);

  /// Distance to an input-dispatch installer (sp.st / T_st).
  uint64_t computeMinDistToSt(const KInstruction *ki, uint64_t minDistAtRA);

  /// The search order of a state: T_W when finite, else past every finite
  /// T_W by T_slot, else past both by T. 0 exactly when T is infinite.
  extern uint64_t sinkGuideWitOffset, sinkGuideOffset, sinkGuideStOffset;
  uint64_t sinkGuide(uint64_t wit, uint64_t slot, uint64_t sig);
  /// Order with the Π_I installer gate: T_st until an sp.st function has
  /// run, then sinkGuide past every finite T_st.
  uint64_t sinkOrder(bool stInstalled, uint64_t st, uint64_t wit, uint64_t slot,
                     uint64_t sig);
  // Whether f is in the refined target set Tgt(cb) of the indirect call cb.
  bool slotAdmits(const llvm::CallBase &cb, const llvm::Function *f);

  // Π_I gate keys for a comparison instruction (DESIGN-D §6): the key
  // constants a dispatch table pairs with an installer-reaching function,
  // extended to the compared width. Null when the comparison is not a gate.
  // A state may assert one of these keys directly as a solver query instead
  // of marching through the table one entry at a time.
  const std::vector<std::uint64_t> *gateKeys(const llvm::Instruction *cmp);

}

#endif /* KLEE_STATSTRACKER_H */
