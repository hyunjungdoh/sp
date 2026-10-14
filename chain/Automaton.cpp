#include "Automaton.hpp"

#include <sstream>

namespace chain {
namespace cfl {

Config initialConfig() {
  Config c;
  c.dir = Direction::Backward;
  c.deriv = Derivation::Flows;
  return c;
}

bool isAccepting(const Config &c) {
  // A points-to answer is: an empty balanced walk from the query in Flows,
  // ending at a Cell node reached by an Alloc edge. The step() caller is
  // responsible for the "ends at a Cell by Alloc" part; we here answer
  // the balance condition.
  return c.deriv == Derivation::Flows &&
         c.fields.empty() &&
         c.ctxs.empty();
}

static Config pushField(const Config &c, Offset off) {
  Config n = c;
  FieldFrame f;
  f.off = off;
  n.fields.push_back(f);
  return n;
}

static std::optional<Config> popField(const Config &c, Offset expected_neg) {
  // Pops the top of the field stack iff it matches -expected_neg.
  // Used when a Gep_{-k} is seen that should close a Gep_{+k}, or when
  // a Load_k closes a Store_k.
  if (c.fields.empty())
    return std::nullopt;
  const Offset top = c.fields.back().off;
  // Any-offset wildcards: a field pushed as kAny matches any pop; a pop
  // of kAny closes any top. This is the standard "field blur" when the
  // offset is dynamic.
  if (top == kAny || expected_neg == kAny) {
    Config n = c;
    n.fields.pop_back();
    return n;
  }
  if (top != expected_neg)
    return std::nullopt;
  Config n = c;
  n.fields.pop_back();
  return n;
}

static Config pushCtx(const Config &c, CallSiteId cs) {
  Config n = c;
  CtxFrame f;
  f.cs = cs;
  n.ctxs.push_back(f);
  return n;
}

static std::optional<Config> popCtx(const Config &c, CallSiteId expected) {
  if (c.ctxs.empty())
    return std::nullopt;
  const CallSiteId top = c.ctxs.back().cs;
  if (expected != kNoCall && top != kNoCall && top != expected)
    return std::nullopt;
  Config n = c;
  n.ctxs.pop_back();
  return n;
}

Transitions step(const Config &from,
                 EdgeLabel label,
                 Offset field_off,
                 CallSiteId call_site,
                 bool /*dst_is_cell*/) {
  // The walk is strictly backward in this phase of the implementation.
  // Forward walks are only needed inside Alias (store/load matching); we
  // encode that as a direction change inside the derivation state. Day
  // 1 keeps direction fixed to Backward and only handles the balanced
  // bracket pushes/pops. Forward support lands with Store/Load pair
  // handling in Day 2.
  //
  // For Day 1 we accept the three building blocks required by Query.cpp
  // to run smoke tests on the pure "Assign + Gep + Call/Return + Alloc"
  // sub-language:
  //
  //   Assign       : stay
  //   Alloc        : terminal; delivered as "ends at Cell" by caller
  //   Gep (back)   : push +k; match later Gep -k that pops it
  //   Call (back)  : push context c
  //   Return (back): push context c
  //
  // Store/Load matching with Alias is implemented in a follow-up patch
  // (Day 2) and will produce multiple successors (one that opens Alias,
  // one that attempts to pop a field already on the stack as a direct
  // match).
  Transitions out;
  switch (label) {
    case EdgeLabel::Assign:
      // Pure assignment: no stack change, same derivation.
      out.push_back(from);
      break;

    case EdgeLabel::Alloc:
      // Alloc reaches a Cell. Keep the configuration; the caller tests
      // isAccepting() against it.
      out.push_back(from);
      break;

    case EdgeLabel::Gep: {
      // Backward over a Gep_{+k} means we are reading a pointer that
      // was v + k. The matching close is a later Gep_{-k} or Load_k.
      // Push +k onto the field stack.
      //
      // Alternatively, if the top of the field stack is already -k, this
      // Gep closes an earlier push and we pop.
      if (!from.fields.empty() &&
          (from.fields.back().off == -field_off ||
           from.fields.back().off == kAny ||
           field_off == kAny)) {
        Config popped = from;
        popped.fields.pop_back();
        out.push_back(popped);
      }
      // Always allow the push alternative too; the query engine will
      // explore both and prune by acceptance.
      out.push_back(pushField(from, field_off));
      break;
    }

    case EdgeLabel::Call: {
      // Backward over a Call edge means we are at a formal parameter and
      // the edge takes us back to the actual argument at call site c.
      // Push the context.
      out.push_back(pushCtx(from, call_site));
      break;
    }

    case EdgeLabel::Return: {
      // Backward over a Return edge: we are at the call-site result and
      // the edge takes us back into the callee's returned value. Push
      // the context.
      out.push_back(pushCtx(from, call_site));
      break;
    }

    case EdgeLabel::Load: {
      // Backward over a Load edge means we are at `result = *(cell+k)` and
      // the backward walk takes us from `result` to `cell`. In the grammar
      // this opens the right half of `store_k Alias load_k`: we must then
      // find a matching Store_k that defined this cell.
      //
      // We push k onto the field stack. The matching Store below will pop
      // it. If no Store on the backward walk matches, the walk terminates
      // without acceptance (stack never balances).
      //
      // Note: Day 2 keeps the Alias derivation implicit — if the Load's
      // source cell and some Store's destination cell are the *same* Graph
      // node, the match is direct. Alias through pointer dataflow (two
      // different Value nodes pointing to the same cell via distinct Alloc
      // chains) is already handled by the Graph: cells are shared across
      // pointer paths, so the walk naturally meets at the shared cell.
      out.push_back(pushField(from, field_off));
      break;
    }

    case EdgeLabel::Store: {
      // Backward over a Store edge means we are at `cell[k] = value` and
      // the backward walk takes us from `cell` to `value`. For this to
      // continue a valid Flows derivation, the top of the field stack must
      // already carry a pending Load_k (pushed by a backward Load earlier).
      //
      // Match semantics for the offset:
      //   top == field_off               -> exact match
      //   top == kAny or field_off==kAny -> wildcard match (field blur)
      //   otherwise                      -> no match, edge rejected
      if (from.fields.empty())
        break;
      const Offset top = from.fields.back().off;
      const bool match = (top == field_off) || (top == kAny) || (field_off == kAny);
      if (!match)
        break;
      Config n = from;
      n.fields.pop_back();
      out.push_back(n);
      break;
    }
  }
  return out;
}

std::string show(const Config &c) {
  std::ostringstream o;
  o << (c.dir == Direction::Backward ? "B" : "F") << "/";
  switch (c.deriv) {
    case Derivation::Flows:    o << "Flows"; break;
    case Derivation::Alias:    o << "Alias"; break;
    case Derivation::AliasFwd: o << "AliasF"; break;
  }
  o << "[F:";
  for (const FieldFrame &f : c.fields) {
    o << ' ';
    if (f.off == kAny) o << "ANY"; else o << f.off;
  }
  o << "][C:";
  for (const CtxFrame &x : c.ctxs)
    o << ' ' << x.cs;
  o << "]";
  return o.str();
}

std::string show(EdgeLabel l) {
  switch (l) {
    case EdgeLabel::Assign: return "assign";
    case EdgeLabel::Store:  return "store";
    case EdgeLabel::Load:   return "load";
    case EdgeLabel::Gep:    return "gep";
    case EdgeLabel::Call:   return "call";
    case EdgeLabel::Return: return "ret";
    case EdgeLabel::Alloc:  return "alloc";
  }
  return "?";
}

} // namespace cfl
} // namespace chain
