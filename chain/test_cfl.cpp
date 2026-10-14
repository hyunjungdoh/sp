// Unit tests for the CFL graph and automaton (Day 1-2).
//
// These tests build small graphs by hand and verify that the automaton
// transitions match the expected CFL behaviour. No LLVM IR is used; the
// LLVM Value* pointers inside Node are tagged by the test with unique
// addresses to distinguish them when debugging.
//
// Run: ./test_cfl   (built as part of chain/CMakeLists.txt below)

#include "Automaton.hpp"
#include "Graph.hpp"

#include <cassert>
#include <cstdio>
#include <string>

namespace {

using namespace chain::cfl;

// Fail with a message that includes the file, line and the failing
// expression. Keeps the test output small so a failure is easy to spot.
#define EXPECT(cond, msg)                                               \
  do {                                                                  \
    if (!(cond)) {                                                      \
      std::fprintf(stderr, "FAIL %s:%d: %s (%s)\n",                     \
                   __FILE__, __LINE__, msg, #cond);                     \
      ++g_failures;                                                     \
      return;                                                           \
    }                                                                   \
  } while (0)

int g_tests = 0;
int g_failures = 0;

// Count the number of configurations in `cs` whose field+ctx stacks are
// empty and derivation is Flows (i.e. accepting at a Cell).
int countAccepting(const Transitions &cs) {
  int n = 0;
  for (const Config &c : cs)
    if (isAccepting(c))
      ++n;
  return n;
}

// ----------------------------------------------------------------------
// T1. Graph node identity.
// ----------------------------------------------------------------------
void test_node_identity() {
  ++g_tests;
  Graph g;
  // Two look-ups of the same Value return the same NodeId.
  // We use fake Value* keys; the Graph only uses them as map keys.
  const auto *v1 = reinterpret_cast<const llvm::Value *>(0x1000);
  const auto *v2 = reinterpret_cast<const llvm::Value *>(0x2000);
  NodeId a1 = g.valueNode(v1);
  NodeId a2 = g.valueNode(v1);
  NodeId b1 = g.valueNode(v2);
  EXPECT(a1 == a2, "same Value* -> same NodeId");
  EXPECT(a1 != b1, "different Value* -> different NodeId");
  // Cells are keyed by (obj, off).
  NodeId c1 = g.cellNode(5, 0);
  NodeId c2 = g.cellNode(5, 0);
  NodeId c3 = g.cellNode(5, 8);
  NodeId c4 = g.cellNode(6, 0);
  EXPECT(c1 == c2, "same (obj,off) -> same cell NodeId");
  EXPECT(c1 != c3, "different off -> different cell NodeId");
  EXPECT(c1 != c4, "different obj -> different cell NodeId");
  // Cell and Value share the id space but are different nodes.
  EXPECT(c1 != a1, "cell and value nodes are distinct");
}

// ----------------------------------------------------------------------
// T2. Edge deduplication.
// ----------------------------------------------------------------------
void test_edge_dedup() {
  ++g_tests;
  Graph g;
  NodeId a = g.valueNode(reinterpret_cast<const llvm::Value *>(0x10));
  NodeId b = g.valueNode(reinterpret_cast<const llvm::Value *>(0x20));
  EXPECT(g.addAssign(a, b), "first assign is new");
  EXPECT(!g.addAssign(a, b), "second identical assign is deduped");
  EXPECT(g.addGep(a, b, 8), "gep +8 is a different edge");
  EXPECT(!g.addGep(a, b, 8), "second gep +8 is deduped");
  EXPECT(g.addGep(a, b, 16), "gep +16 is a different edge");
  EXPECT(g.numEdges() == 3, "edge count: assign + gep8 + gep16");
}

// ----------------------------------------------------------------------
// T3. Automaton: pure Assign chain.
// ----------------------------------------------------------------------
void test_assign_chain() {
  ++g_tests;
  // Flow:  cell -alloc-> p -assign-> q -assign-> r
  // Query pts(r)?  Backward: Assign, Assign, Alloc. Accept at cell.
  Config c = initialConfig();
  Transitions t1 = step(c, EdgeLabel::Assign, 0, 0, false);
  EXPECT(t1.size() == 1, "assign -> one successor");
  Transitions t2 = step(t1[0], EdgeLabel::Assign, 0, 0, false);
  EXPECT(t2.size() == 1, "assign -> one successor");
  Transitions t3 = step(t2[0], EdgeLabel::Alloc, 0, 0, true);
  EXPECT(t3.size() == 1, "alloc -> one successor");
  EXPECT(isAccepting(t3[0]), "alloc with empty stacks accepts");
}

// ----------------------------------------------------------------------
// T4. Automaton: Gep push/pop balance.
// ----------------------------------------------------------------------
void test_gep_balance() {
  ++g_tests;
  // A gep +8 pushes; a matching gep -8 pops.
  Config c = initialConfig();
  Transitions t1 = step(c, EdgeLabel::Gep, 8, 0, false);
  // Two successors: push +8 and (pop attempt that fails on empty stack).
  EXPECT(t1.size() == 1, "gep on empty stack -> only push");
  EXPECT(t1[0].fields.size() == 1 && t1[0].fields.back().off == 8,
         "push left +8 on top");
  Transitions t2 = step(t1[0], EdgeLabel::Gep, -8, 0, false);
  // Two successors: pop (matches +8) and push (-8 added).
  // At least one must have empty field stack.
  bool pop_found = false;
  for (const Config &x : t2)
    if (x.fields.empty())
      pop_found = true;
  EXPECT(pop_found, "gep -8 after gep +8 pops");
  EXPECT(t2.size() == 2, "gep against matched top -> pop + push alternatives");
}

// ----------------------------------------------------------------------
// T5. Automaton: Store / Load match.
// ----------------------------------------------------------------------
void test_store_load_match() {
  ++g_tests;
  // Walk from result backward:
  //   Load_8 pushes 8;  Store_8 pops it.  Then Assign, Alloc.
  Config c = initialConfig();
  Transitions after_load = step(c, EdgeLabel::Load, 8, 0, false);
  EXPECT(after_load.size() == 1, "load -> one successor (push)");
  EXPECT(after_load[0].fields.size() == 1 && after_load[0].fields.back().off == 8,
         "load pushed +8");
  Transitions after_store = step(after_load[0], EdgeLabel::Store, 8, 0, false);
  EXPECT(after_store.size() == 1, "store with matching top -> pop");
  EXPECT(after_store[0].fields.empty(), "store popped the pending load");
  Transitions after_alloc = step(after_store[0], EdgeLabel::Alloc, 0, 0, true);
  EXPECT(after_alloc.size() == 1 && isAccepting(after_alloc[0]),
         "alloc after balanced store/load accepts");
}

// ----------------------------------------------------------------------
// T6. Automaton: Store without pending Load is rejected.
// ----------------------------------------------------------------------
void test_store_without_load() {
  ++g_tests;
  Config c = initialConfig();
  Transitions t = step(c, EdgeLabel::Store, 8, 0, false);
  EXPECT(t.empty(), "store on empty stack is rejected");
}

// ----------------------------------------------------------------------
// T7. Automaton: Load / Store with mismatched offset is rejected.
// ----------------------------------------------------------------------
void test_offset_mismatch() {
  ++g_tests;
  Config c = initialConfig();
  Transitions after_load = step(c, EdgeLabel::Load, 8, 0, false);
  EXPECT(after_load.size() == 1, "load +8 pushes");
  Transitions after_store = step(after_load[0], EdgeLabel::Store, 16, 0, false);
  EXPECT(after_store.empty(), "store +16 does not match load +8");
}

// ----------------------------------------------------------------------
// T8. Automaton: Any wildcard matches any offset (field blur).
// ----------------------------------------------------------------------
void test_any_wildcard() {
  ++g_tests;
  Config c = initialConfig();
  // Load with Any
  Transitions after_load = step(c, EdgeLabel::Load, kAny, 0, false);
  EXPECT(after_load.size() == 1, "load any pushes");
  Transitions after_store = step(after_load[0], EdgeLabel::Store, 8, 0, false);
  EXPECT(after_store.size() == 1, "store 8 matches any-top");

  // Store with Any
  Config c2 = initialConfig();
  Transitions al2 = step(c2, EdgeLabel::Load, 8, 0, false);
  Transitions as2 = step(al2[0], EdgeLabel::Store, kAny, 0, false);
  EXPECT(as2.size() == 1, "store any matches load 8");
}

// ----------------------------------------------------------------------
// T9. Automaton: Call / Return push context.
// ----------------------------------------------------------------------
void test_call_return() {
  ++g_tests;
  Config c = initialConfig();
  Transitions t1 = step(c, EdgeLabel::Call, 0, /*cs=*/42, false);
  EXPECT(t1.size() == 1, "call pushes context");
  EXPECT(t1[0].ctxs.size() == 1 && t1[0].ctxs.back().cs == 42,
         "ctx 42 on top");
  Transitions t2 = step(t1[0], EdgeLabel::Alloc, 0, 0, true);
  EXPECT(t2.size() == 1, "alloc succeeds");
  // But isAccepting is false because ctx stack is non-empty.
  EXPECT(!isAccepting(t2[0]), "non-empty ctx stack is not accepting");
}

// ----------------------------------------------------------------------
// T10. Stats smoke test. `describe()` of a Value node is only exercised on
// real LLVM Values (where hasName() is safe); the fake Value* used
// elsewhere in these tests would crash hasName(). Cell describe uses no
// Value*, so it is safe to exercise here.
// ----------------------------------------------------------------------
void test_describe_cell_and_stats() {
  ++g_tests;
  Graph g;
  NodeId v = g.valueNode(reinterpret_cast<const llvm::Value *>(0x10));
  NodeId c = g.cellNode(3, 16);
  g.addAssign(v, c);  // weird but just to test an edge
  const std::string sc = g.describe(c);
  EXPECT(sc.find("C(obj=3") != std::string::npos, "cell describe has C(obj=3");
  const std::string st = g.stats();
  EXPECT(st.find("nodes=") != std::string::npos, "stats has nodes");
  EXPECT(st.find("edges=1") != std::string::npos, "stats has edges=1");
}

} // namespace

int main() {
  std::printf("T1 node_identity\n"); std::fflush(stdout);
  test_node_identity();
  std::printf("T2 edge_dedup\n"); std::fflush(stdout);
  test_edge_dedup();
  std::printf("T3 assign_chain\n"); std::fflush(stdout);
  test_assign_chain();
  std::printf("T4 gep_balance\n"); std::fflush(stdout);
  test_gep_balance();
  std::printf("T5 store_load_match\n"); std::fflush(stdout);
  test_store_load_match();
  std::printf("T6 store_without_load\n"); std::fflush(stdout);
  test_store_without_load();
  std::printf("T7 offset_mismatch\n"); std::fflush(stdout);
  test_offset_mismatch();
  std::printf("T8 any_wildcard\n"); std::fflush(stdout);
  test_any_wildcard();
  std::printf("T9 call_return\n"); std::fflush(stdout);
  test_call_return();
  std::printf("T10 describe_cell_and_stats\n"); std::fflush(stdout);
  test_describe_cell_and_stats();

  std::printf("ran %d tests, %d failures\n", g_tests, g_failures);
  return g_failures == 0 ? 0 : 1;
}
