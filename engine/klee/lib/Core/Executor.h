//===-- Executor.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Class to perform actual execution, hides implementation details from external
// interpreter.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTOR_H
#define KLEE_EXECUTOR_H

#include "ExecutionState.h"
#include "UserSearcher.h"

#include "klee/ADT/RNG.h"
#include "klee/Core/BranchTypes.h"
#include "klee/Core/Interpreter.h"
#include "klee/Core/TerminationTypes.h"
#include "klee/Expr/ArrayCache.h"
#include "klee/Expr/ArrayExprOptimizer.h"
#include "klee/Module/Cell.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/System/Time.h"

#include "llvm/ADT/Twine.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

struct KTest;

namespace llvm {
  class BasicBlock;
  class BranchInst;
  class CallInst;
  class LandingPadInst;
  class Constant;
  class ConstantExpr;
  class Function;
  class GlobalValue;
  class Instruction;
  class LLVMContext;
  class MDNode;
  class DataLayout;
  class Twine;
  class Value;
}

namespace klee {
class Array;
struct Cell;
class ExecutionState;
class ExternalDispatcher;
class Expr;
class InstructionInfoTable;
class KCallable;
struct KFunction;
struct KInstruction;
class KInstIterator;
class KModule;
class MemoryManager;
class MemoryObject;
class ObjectState;
class ExecutionTree;
class Searcher;
class SeedInfo;
class SpecialFunctionHandler;
struct StackFrame;
class StatsTracker;
class TimingSolver;
class TreeStreamWriter;
class MergeHandler;
class MergingSearcher;
template <class T> class ref;

/// \todo Add a context object to keep track of data only live
/// during an instruction step. Should contain addedStates,
/// removedStates, and haltExecution, among others.

class Executor : public Interpreter {
  friend class OwningSearcher;
  friend class WeightedRandomSearcher;
  friend class SpecialFunctionHandler;
  friend class StatsTracker;
  friend class MergeHandler;
  friend class ObjectState;
  friend klee::Searcher *klee::constructUserSearcher(Executor &executor);

public:
  typedef std::pair<ExecutionState*,ExecutionState*> StatePair;

  /// The random number generator.
  RNG theRNG;

private:
  std::unique_ptr<KModule> kmodule;
  InterpreterHandler *interpreterHandler;
  Searcher *searcher;

  ExternalDispatcher *externalDispatcher;
  std::unique_ptr<TimingSolver> solver;
  std::unique_ptr<MemoryManager> memory;
  std::set<ExecutionState*, ExecutionStateIDCompare> states;
  StatsTracker *statsTracker;
  TreeStreamWriter *pathWriter, *symPathWriter;
  SpecialFunctionHandler *specialFunctionHandler;
  TimerGroup timers;
  std::unique_ptr<ExecutionTree> executionTree;

  /// Used to track states that have been added during the current
  /// instructions step. 
  /// \invariant \ref addedStates is a subset of \ref states. 
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> addedStates;
  /// Used to track states that have been removed during the current
  /// instructions step. 
  /// \invariant \ref removedStates is a subset of \ref states. 
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> removedStates;

  /// When non-empty the Executor is running in "seed" mode. The
  /// states in this map will be executed in an arbitrary order
  /// (outside the normal search interface) until they terminate. When
  /// the states reach a symbolic branch then either direction that
  /// satisfies one or more seeds will be added to this map. What
  /// happens with other states (that don't satisfy the seeds) depends
  /// on as-yet-to-be-determined flags.
  std::map<ExecutionState*, std::vector<SeedInfo> > seedMap;

  /// Map of globals to their representative memory object.
  std::map<const llvm::GlobalValue*, MemoryObject*> globalObjects;

  /// Map of globals to their bound address. This also includes
  /// globals that have no representative object (e.g. aliases).
  std::map<const llvm::GlobalValue*, ref<ConstantExpr>> globalAddresses;

  /// Map of legal function addresses to the corresponding Function.
  /// Used to validate and dereference function pointers.
  std::unordered_map<std::uint64_t, llvm::Function*> legalFunctions;

  /// When non-null the bindings that will be used for calls to
  /// klee_make_symbolic in order replay.
  const struct KTest *replayKTest;

  /// When non-null a list of branch decisions to be used for replay.
  const std::vector<bool> *replayPath;

  /// The index into the current \ref replayKTest or \ref replayPath
  /// object.
  unsigned replayPosition;

  /// When non-null a list of "seed" inputs which will be used to
  /// drive execution.
  const std::vector<struct KTest *> *usingSeeds;  

  /// Disables forking, instead a random path is chosen. Enabled as
  /// needed to control memory usage. \see fork()
  bool atMemoryLimit;

  /// Disables forking, set by client. \see setInhibitForking()
  bool inhibitForking;

  /// Signals the executor to halt execution at the next instruction
  /// step.
  bool haltExecution;  

  /// Whether implied-value concretization is enabled. Currently
  /// false, it is buggy (it needs to validate its writes).
  bool ivcEnabled;

  /// The maximum time to allow for a single core solver query.
  /// (e.g. for a single STP query)
  time::Span coreSolverTimeout;

  /// Maximum time to allow for a single instruction.
  time::Span maxInstructionTime;

  /// Assumes ownership of the created array objects
  ArrayCache arrayCache;

  /// File to print executed instructions to
  std::unique_ptr<llvm::raw_ostream> debugInstFile;

  // @brief Buffer used by logBuffer
  std::string debugBufferString;

  // @brief buffer to store logs before flushing to file
  llvm::raw_string_ostream debugLogBuffer;

  /// Optimizes expressions
  ExprOptimizer optimizer;

  /// Points to the merging searcher of the searcher chain,
  /// `nullptr` if merging is disabled
  MergingSearcher *mergingSearcher = nullptr;

  /// Typeids used during exception handling
  std::vector<ref<Expr>> eh_typeids;

  /// Return the typeid corresponding to a certain `type_info`
  ref<ConstantExpr> getEhTypeidFor(ref<Expr> type_info);

  llvm::Function* getTargetFunction(llvm::Value *calledVal);
  
  void executeInstruction(ExecutionState &state, KInstruction *ki);

  void run(ExecutionState &initialState);

  // Given a concrete object in our [klee's] address space, add it to 
  // objects checked code can reference.
  MemoryObject *addExternalObject(ExecutionState &state, void *addr, 
                                  unsigned size, bool isReadOnly);

  void initializeGlobalAlias(const llvm::Constant *c);
  void initializeGlobalObject(ExecutionState &state, ObjectState *os, 
			      const llvm::Constant *c,
			      unsigned offset);
  void initializeGlobals(ExecutionState &state);
  void allocateGlobalObjects(ExecutionState &state);

  MemoryObject *allocateFunctionMemoryObject(ExecutionState &state,
                                             llvm::Function &function,
                                             std::uint64_t prefixBytes);

  /// Allocate KLEE's synthetic object for a function and return the concrete
  /// address that should be used as the function pointer value.
  std::uint64_t allocateFunctionObject(ExecutionState &state,
                                       llvm::Function &function);

#if LLVM_VERSION_CODE >= LLVM_VERSION(17, 0)
  /// Allocate a synthetic function object containing LLVM's UBSan function
  /// sanitizer prefix and return the address after that prefix.
  std::uint64_t allocateFunctionObjectWithUBSan(ExecutionState &state,
                                                llvm::Function &function,
                                                llvm::MDNode &metadata);
#endif
  void initializeGlobalAliases();
  void initializeGlobalObjects(ExecutionState &state);

  void stepInstruction(ExecutionState &state);
  void updateStates(ExecutionState *current);
  void transferToBasicBlock(llvm::BasicBlock *dst, 
			    llvm::BasicBlock *src,
			    ExecutionState &state);

  void callExternalFunction(ExecutionState &state,
                            KInstruction *target,
                            KCallable *callable,
                            std::vector< ref<Expr> > &arguments);

  ObjectState *bindObjectInState(ExecutionState &state, const MemoryObject *mo,
                                 bool isLocal, const Array *array = 0);

  /// Resolve a pointer to the memory objects it could point to the
  /// start of, forking execution when necessary and generating errors
  /// for pointers to invalid locations (either out of bounds or
  /// address inside the middle of objects).
  ///
  /// \param results[out] A list of ((MemoryObject,ObjectState),
  /// state) pairs for each object the given address can point to the
  /// beginning of.
  typedef std::vector< std::pair<std::pair<const MemoryObject*, const ObjectState*>, 
                                 ExecutionState*> > ExactResolutionList;
  void resolveExact(ExecutionState &state,
                    ref<Expr> p,
                    ExactResolutionList &results,
                    const std::string &name);

  /// Allocate and bind a new object in a particular state. NOTE: This
  /// function may fork.
  ///
  /// \param isLocal Flag to indicate if the object should be
  /// automatically deallocated on function return (this also makes it
  /// illegal to free directly).
  ///
  /// \param target Value at which to bind the base address of the new
  /// object.
  ///
  /// \param reallocFrom If non-zero and the allocation succeeds,
  /// initialize the new object from the given one and unbind it when
  /// done (realloc semantics). The initialized bytes will be the
  /// minimum of the size of the old and new objects, with remaining
  /// bytes initialized as specified by zeroMemory.
  ///
  /// \param allocationAlignment If non-zero, the given alignment is
  /// used. Otherwise, the alignment is deduced via
  /// Executor::getAllocationAlignment
  void executeAlloc(ExecutionState &state,
                    ref<Expr> size,
                    bool isLocal,
                    KInstruction *target,
                    bool zeroMemory=false,
                    const ObjectState *reallocFrom=0,
                    size_t allocationAlignment=0);

  /// Free the given address with checking for errors. If target is
  /// given it will be bound to 0 in the resulting states (this is a
  /// convenience for realloc). Note that this function can cause the
  /// state to fork and that \ref state cannot be safely accessed
  /// afterwards.
  void executeFree(ExecutionState &state,
                   ref<Expr> address,
                   KInstruction *target = 0);

  /// Serialize a landingpad instruction so it can be handled by the
  /// libcxxabi-runtime
  MemoryObject *serializeLandingpad(ExecutionState &state,
                                    const llvm::LandingPadInst &lpi,
                                    bool &stateTerminated);

  /// Unwind the given state until it hits a landingpad. This is used
  /// for exception handling.
  void unwindToNextLandingpad(ExecutionState &state);

  void executeCall(ExecutionState &state, 
                   KInstruction *ki,
                   llvm::Function *f,
                   std::vector< ref<Expr> > &arguments);
                   
  // do address resolution / object binding / out of bounds checking
  // and perform the operation
  void executeMemoryOperation(ExecutionState &state,
                              bool isWrite,
                              ref<Expr> address,
                              ref<Expr> value /* undef if read */,
                              KInstruction *target /* undef if write */);

  void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo,
                           const std::string &name);

  /// Create a new state where each input condition has been added as
  /// a constraint and return the results. The input state is included
  /// as one of the results. Note that the output vector may include
  /// NULL pointers for states which were unable to be created.
  void branch(ExecutionState &state, const std::vector<ref<Expr>> &conditions,
              std::vector<ExecutionState *> &result, BranchType reason);

  /// Fork current and return states in which condition holds / does
  /// not hold, respectively. One of the states is necessarily the
  /// current state, and one of the states may be null.
  StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal,
                 BranchType reason);

  // If the MaxStatic*Pct limits have been reached, concretize the condition and
  // return it. Otherwise, return the unmodified condition.
  ref<Expr> maxStaticPctChecks(ExecutionState &current, ref<Expr> condition);

  /// Add the given (boolean) condition as a constraint on state. This
  /// function is a wrapper around the state's addConstraint function
  /// which also manages propagation of implied values,
  /// validity checks, and seed patching.
  void addConstraint(ExecutionState &state, ref<Expr> condition);

  // Called on [for now] concrete reads, replaces constant with a symbolic
  // Used for testing.
  ref<Expr> replaceReadWithSymbolic(ExecutionState &state, ref<Expr> e);

  const Cell& eval(KInstruction *ki, unsigned index, 
                   ExecutionState &state) const;

  Cell& getArgumentCell(ExecutionState &state,
                        KFunction *kf,
                        unsigned index) {
    return state.stack.back().locals[kf->getArgRegister(index)];
  }

  Cell& getDestCell(ExecutionState &state,
                    KInstruction *target) {
    return state.stack.back().locals[target->dest];
  }

  void bindLocal(KInstruction *target, 
                 ExecutionState &state, 
                 ref<Expr> value);
  void bindArgument(KFunction *kf, 
                    unsigned index,
                    ExecutionState &state,
                    ref<Expr> value);

  /// Evaluates an LLVM constant expression.  The optional argument ki
  /// is the instruction where this constant was encountered, or NULL
  /// if not applicable/unavailable.
  ref<klee::ConstantExpr> evalConstantExpr(const llvm::ConstantExpr *c,
					   const KInstruction *ki = NULL);

  /// Evaluates an LLVM constant.  The optional argument ki is the
  /// instruction where this constant was encountered, or NULL if
  /// not applicable/unavailable.
  ref<klee::ConstantExpr> evalConstant(const llvm::Constant *c,
				       const KInstruction *ki = NULL);

  /// Return a unique constant value for the given expression in the
  /// given state, if it has one (i.e. it provably only has a single
  /// value). Otherwise return the original expression.
  ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &e);

  /// Return a constant value for the given expression.  If \param concretize is
  /// true, the expression is forced to be a constant by adding a constraint if
  /// necessary. Note that this function breaks completeness and
  /// should generally be avoided.
  ///
  /// \param reason A documentation string stating the reason for concretization
  ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e,
                                     const std::string &reason,
                                     bool concretize = true);

  /// Evaluate the given expression under each seed, and return the
  /// first one that results in a constant, if such a seed exist.  Otherwise,
  /// return the non-constant evaluation of the expression under one of the
  /// seeds.
  ref<klee::ConstantExpr> getValueFromSeeds(ExecutionState &state, ref<Expr> e);

  /// Concolic mode (--concolic). True if the state carries seeds, i.e. it
  /// follows a concrete input and may decide branches without the solver.
  bool concolicSeeded(ExecutionState &state);

  /// Concolic mode. Decide a condition under the seeds of a state without the
  /// solver: 1 if every seed satisfies it, 0 if none does, 2 if they differ,
  /// -1 if some seed does not evaluate it to a constant.
  int seedsDecide(ExecutionState &state, ref<Expr> condition);

  /// Concolic mode. A pending state (split off without a seed) is solved once;
  /// the model becomes its seed. Returns false if it gets no seed, in which
  /// case the caller discards the state; its fate then says whether the path
  /// was proven infeasible or the solver gave up.
  bool ensureSeed(ExecutionState &state);

  /// Concolic mode. Solve the path condition of a state for a full input.
  /// 1: values are a model; 0: no model exists (proven only if the path was
  /// never concretized); -1: the solver gave up.
  int solveInput(ExecutionState &state, std::vector<const Array *> &objects,
                 std::vector<std::vector<unsigned char>> &values);
  /// The same for a path condition with these objects; bytes the path does
  /// not read keep the parent input's values, if there is one.
  int solveInput(const ConstraintSet &path,
                 const std::vector<const Array *> &objects,
                 const Assignment *parent, SolverQueryMetaData &meta,
                 std::vector<std::vector<unsigned char>> &values);

  /// Concolic mode. The fate of every state the search ends, and the
  /// candidates (pending flips) it creates. The run is exhaustive within its
  /// bounds iff it ends with no state, no deferred input and no open count.
  struct Ledger {
    uint64_t flips = 0, bounded = 0, respawned = 0;
    uint64_t checkpoints = 0, checkpointAt = 0; // pristine moves, last count
    uint64_t slotMisses = 0; // executed indirect targets the slot rule omits
    uint64_t gates = 0; // Π_I gate flips spawned
    std::map<std::string, uint64_t> fates, open;
  } ledger;
  void concolicAccount(ExecutionState &state, StateTerminationType reason);
  void writeLedger(bool exhausted);

  /// Concolic mode. A state the search cannot keep in memory is replaced by
  /// its inputs, or by its path condition if it is pending (solved when it
  /// runs again), and run again later from the checkpoint
  /// (advanceCheckpoint); decisions before floor are not flipped again.
  /// Nothing is discarded for lack of memory.
  struct Deferred {
    std::pair<unsigned, uint64_t> key; // orderKey of the deferred state
    unsigned floor;
    std::vector<KTest *> inputs; // the state's seeds, re-run together
    std::set<std::string> fixed;
    std::vector<std::string> names; // of the symbolic objects, in order
    std::optional<ConstraintSet> path; // a pending flip's path condition
    std::shared_ptr<const Assignment> parent;
    std::vector<const Array *> objects;
    bool concretized = false;
  };
  std::vector<Deferred> deferred; // min-heap on key
  std::vector<std::unique_ptr<KTest, void (*)(KTest *)>> deferredInputs;
  KTest *storeInput(const std::vector<std::string> &names,
                    const std::vector<std::vector<unsigned char>> &values);
  ExecutionState *pristine = nullptr;
  std::set<std::string> programFunctions; // defined in the input module
  uint64_t memoryBase = 0; // MB in use when the run starts
  void defer(ExecutionState &state);
  void respawn();
  /// Concolic mode. Move pristine forward along the input-independent
  /// prefix (no constraint, one state), at instruction counts 2^k.
  bool checkpointOpen = true;
  void advanceCheckpoint();
  /// Bind seed si's value for a new symbolic object (by name or position).
  bool bindSeedObject(ExecutionState &state, SeedInfo &si,
                      const MemoryObject *mo, const Array *array);

  /// Concolic mode. The seed files (--seed-dir) as values of a data object.
  /// A path's constraints read only some bytes of its input; every other
  /// value of the rest gives an input of the same path. When a seeded state
  /// first depends on a data object (--concolic-data) that its path does not
  /// yet constrain, the object takes the corpus files as its values instead
  /// of zeros: seed j gets file j, and the state carries max(seeds, files)
  /// seeds.
  std::vector<std::vector<unsigned char>> corpus;
  std::map<const Array *, bool> dataObjects;
  bool isDataObject(const Array *array);
  void bindCorpus(ExecutionState &state, ref<Expr> e);
  void bindLength(ExecutionState &state, const Array *data);

  /// Concolic mode. klee_assume(e) in a seeded state: seeds satisfying e stay;
  /// if none does, the state drops its seeds and becomes pending. Returns
  /// false if the state is not concolic (caller uses the solver).
  bool concolicAssume(ExecutionState &state, ref<Expr> e);

  /// Concolic mode. A fork the seeds decide without creating a flip: used for
  /// environment decisions (bounds checks, allocation success). Seeds that
  /// disagree split the state; a state without seeds forks normally.
  StatePair seedFork(ExecutionState &state, ref<Expr> condition,
                     BranchType reason);

  /// Concolic mode. Sink distance of a state (d+1; 0 = sink unreachable).
  uint64_t sinkDistance(ExecutionState &state);

  /// Concolic mode. Order of a state toward the sink (sinkGuide): T_slot,
  /// falling back to T. Zero exactly when sinkDistance is.
  uint64_t sinkOrder(ExecutionState &state);

  /// Concolic mode (DESIGN-D §6, order). The order key k = (gen, g) of a
  /// state: its generation, then its sink order g (sinkOrder, or 1 without a
  /// sink guide; an unreachable state sorts last). Selection takes the least
  /// key, deferral the greatest.
  std::pair<unsigned, uint64_t> orderKey(ExecutionState &state);

  /// Concolic mode. The input-carrying state now running: it runs for a
  /// quantum of --batch-instructions, or until it ends, is deferred, or loses
  /// its input; then the state of least key runs. selectConcolic returns
  /// null when that is a deferred input, which respawn then brings back.
  ExecutionState *running = nullptr;
  uint64_t runningSince = 0;
  ExecutionState *selectConcolic();

  /// Concolic mode. Turn a seeded state into a pending flip of the next
  /// generation; parent is the input it followed (kept if null).
  void makePending(ExecutionState &state,
                   std::shared_ptr<const Assignment> parent);

  /// Concolic mode. Keep at most --concolic-pending flips in memory; the
  /// greatest keys are deferred first.
  void prunePending();

  /// Concolic mode. End a state (seeded or pending) whose sink distance is
  /// infinite: no continuation of it, hence no flip of it, reaches the sink.
  bool dropUnreachable(ExecutionState *state);

  /// Concolic mode, Π_I gate (DESIGN-D §6). At a comparison that reads a
  /// dispatch table's key field, spawn a pending flip that asserts the key
  /// selecting an uninstalled input-dispatch installer, so the installer is
  /// reached by one solver query rather than by marching the table entry by
  /// entry. `state` is the path the seed follows; `cond` is the branch
  /// condition; `ki` the branch. Bounded per path and skipped under the
  /// memory cap.
  void spawnGateFlips(ExecutionState &state, const ref<Expr> &cond,
                      KInstruction *ki);

  /// Bind a constant value for e to the given target. NOTE: This
  /// function may fork state if the state has multiple seeds.
  void executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target);

  /// Get textual information regarding a memory address.
  std::string getAddressInfo(ExecutionState &state, ref<Expr> address) const;

  // Determines the \param lastInstruction of the \param state which is not KLEE
  // internal and returns its InstructionInfo
  const InstructionInfo & getLastNonKleeInternalInstruction(const ExecutionState &state,
      llvm::Instruction** lastInstruction);

  /// Remove state from queue and delete state. This function should only be
  /// used in the termination functions below.
  void terminateState(ExecutionState &state, StateTerminationType reason);

  /// Call exit handler and terminate state normally
  /// (end of execution path)
  void terminateStateOnExit(ExecutionState &state);

  /// Call exit handler and terminate state early
  /// (e.g. due to state merging or memory pressure)
  void terminateStateEarly(ExecutionState &state, const llvm::Twine &message,
                           StateTerminationType reason);

  /// Call exit handler and terminate state early
  /// (e.g. caused by the applied algorithm as in state merging or replaying)
  void terminateStateEarlyAlgorithm(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason);

  /// Call exit handler and terminate state early
  /// (e.g. due to klee_silent_exit issued by user)
  void terminateStateEarlyUser(ExecutionState &state,
                               const llvm::Twine &message);

  /// Call error handler and terminate state in case of errors.
  /// The underlying function of all error-handling termination functions
  /// below. This function should only be used in the termination functions
  /// below.
  void terminateStateOnError(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason,
                                    const llvm::Twine &longMessage = "",
                                    const char *suffix = nullptr);

  /// Call error handler and terminate state in case of program errors
  /// (e.g. free()ing globals, out-of-bound accesses)
  void terminateStateOnProgramError(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason,
                                    const llvm::Twine &longMessage = "",
                                    const char *suffix = nullptr);

  /// Call error handler and terminate state in case of execution errors
  /// (things that should not be possible, like illegal instruction or
  /// unlowered intrinsic, or unsupported intrinsics, like inline assembly)
  void terminateStateOnExecError(
      ExecutionState &state, const llvm::Twine &message,
      StateTerminationType = StateTerminationType::Execution);

  /// Call error handler and terminate state in case of solver errors
  /// (solver error or timeout)
  void terminateStateOnSolverError(ExecutionState &state,
                                   const llvm::Twine &message);

  /// Call error handler and terminate state for user errors
  /// (e.g. wrong usage of klee.h API)
  void terminateStateOnUserError(ExecutionState &state,
                                 const llvm::Twine &message,
                                 bool writeErr = true);

  /// bindModuleConstants - Initialize the module constant table.
  void bindModuleConstants();

  template <typename TypeIt>
  void computeOffsetsSeqTy(KGEPInstruction *kgepi,
                           ref<ConstantExpr> &constantOffset, uint64_t index,
                           const TypeIt it);

  template <typename TypeIt>
  void computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie);

  /// bindInstructionConstants - Initialize any necessary per instruction
  /// constant values.
  void bindInstructionConstants(KInstruction *KI);

  void doImpliedValueConcretization(ExecutionState &state,
                                    ref<Expr> e,
                                    ref<ConstantExpr> value);

  /// check memory usage and terminate states when over threshold of -max-memory + 100MB
  /// \return true if below threshold, false otherwise (states were terminated)
  bool checkMemoryUsage();

  /// check if branching/forking is allowed
  bool branchingPermitted(const ExecutionState &state) const;

  void printDebugInstructions(ExecutionState &state);
  void doDumpStates();

  /// Only for debug purposes; enable via debugger or klee-control
  void dumpStates();
  void dumpExecutionTree();

public:
  Executor(llvm::LLVMContext &ctx, const InterpreterOptions &opts,
      InterpreterHandler *ie);
  virtual ~Executor();

  const InterpreterHandler& getHandler() {
    return *interpreterHandler;
  }

  void setPathWriter(TreeStreamWriter *tsw) override { pathWriter = tsw; }

  void setSymbolicPathWriter(TreeStreamWriter *tsw) override {
    symPathWriter = tsw;
  }

  void setReplayKTest(const struct KTest *out) override {
    assert(!replayPath && "cannot replay both buffer and path");
    replayKTest = out;
    replayPosition = 0;
  }

  void setReplayPath(const std::vector<bool> *path) override {
    assert(!replayKTest && "cannot replay both buffer and path");
    replayPath = path;
    replayPosition = 0;
  }

  llvm::Module *setModule(std::vector<std::unique_ptr<llvm::Module>> &modules,
                          const ModuleOptions &opts) override;

  void useSeeds(const std::vector<struct KTest *> *seeds) override {
    usingSeeds = seeds;
  }

  void runFunctionAsMain(llvm::Function *f, int argc, char **argv,
                         char **envp) override;

  /*** Runtime options ***/

  void setHaltExecution(bool value) override { haltExecution = value; }

  void setInhibitForking(bool value) override { inhibitForking = value; }

  void prepareForEarlyExit() override;

  /*** State accessor methods ***/

  unsigned getPathStreamID(const ExecutionState &state) override;

  unsigned getSymbolicPathStreamID(const ExecutionState &state) override;

  void getConstraintLog(const ExecutionState &state, std::string &res,
                        Interpreter::LogType logFormat =
                            Interpreter::STP) override;

  bool getSymbolicSolution(
      const ExecutionState &state,
      std::vector<std::pair<std::string, std::vector<unsigned char>>> &res)
      override;

  void getCoveredLines(const ExecutionState &state,
                       std::map<const std::string *, std::set<unsigned>> &res)
      override;

  Expr::Width getWidthForLLVMType(llvm::Type *type) const;
  size_t getAllocationAlignment(const llvm::Value *allocSite) const;

  /// Returns the errno location in memory of the state
  int *getErrnoLocation(const ExecutionState &state) const;

  MergingSearcher *getMergingSearcher() const { return mergingSearcher; };
  void setMergingSearcher(MergingSearcher *ms) { mergingSearcher = ms; };
};

} // namespace klee

#endif /* KLEE_EXECUTOR_H */
