#pragma once

#include "llvm/ADT/SparseBitVector.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace chain {

// Inclusion-based points-to over both modules, by allocation site and byte
// offset. A location is a pair (object, offset); the objects are the
// allocas, the globals, the allocating calls, one object per function (for
// pointers to code), and one object for all memory outside both modules:
// the memory the harness supplies through an export's formals, the memory
// a bodiless callee returns or writes, a pointer made from an integer, the
// formals of a function nothing here calls. The points-to set of a pointer
// is the least set closed under the instructions: an address points to its
// object; a getelementptr with constant indices moves the offset by the
// indexed size, otherwise the offset is any; a displacement of a pointer
// that already names two offsets of one object names the whole object;
// phi, select and casts copy; a
// load reads the locations its address points to; a store writes the
// locations its address points to; an actual flows to the formal of every
// callee the call can reach, directly or through the functions its callee
// operand points to; a return flows to each call of the function; a byte
// copy moves the contents of the source locations to the destination
// locations at the same distance; a reallocation is fresh memory holding
// the contents of the memory it replaces; an initializer fills a global's
// locations. Memory outside both modules holds pointers to itself.
//
// Two kinds of function are analysed once per call site rather than once:
// a function that returns fresh memory (an allocation it made, directly or
// through another such function), and a function whose whole effect is a
// library byte copy or fill. Merging the call sites of the former would
// make all memory allocated through it one object; merging the latter's
// would relate every source of the copy to every destination. The call
// sites of such a function are its contexts; the values, allocas and
// allocating calls of its body are distinct per context. A context is the
// chain of such call sites, which is finite because recursive functions of
// those kinds are analysed once like every other function.
//
// The solution is computed by demand: asking for a pointer's set seeds the
// objects it can derive from and propagates them forward through every
// use, so a pointer no asked-for object reaches is never materialized.
class Points {
public:
  enum class Kind { Alloca, Global, Alloc, Func, Outside };
  struct Obj {
    Kind kind = Kind::Outside;
    const llvm::Value *site = nullptr;  // alloca, global, call, function; null for Outside
    unsigned ctx = 0;                   // the context the site was analysed in
  };
  static constexpr int64_t Any = INT64_MIN;
  struct Loc {
    unsigned obj = 0;
    int64_t off = 0;
  };
  // A write into an object: a store, a byte copy or reallocation whose
  // destination is the object, or a memset. off is the offset written, or
  // Any; ctx the context the writing instruction was analysed in.
  struct Write {
    const llvm::Instruction *inst = nullptr;
    int64_t off = 0;
    int64_t len = -1;  // bytes written from off, or -1 when unknown
    unsigned ctx = 0;
  };
  struct PtrLoad {
    const llvm::LoadInst *inst = nullptr;
    int64_t off = 0;
  };
  struct Hooks {
    // Callees the surrounding analysis already resolved for a call.
    std::function<std::vector<const llvm::Function *>(const llvm::CallBase *)> callees;
    // The defining body of a function, here or in the other module.
    std::function<const llvm::Function *(const llvm::Function *)> body;
    // Whether a function is an export the harness can call.
    std::function<bool(const llvm::Function *)> harness;
    // Whether a call allocates fresh memory.
    std::function<bool(const llvm::CallBase *)> allocates;
    // The static size of the memory an allocating call returns, if any.
    std::function<std::optional<uint64_t>(const llvm::CallBase *)> allocSize;
    // The operands of an allocating call that give its size: the element
    // size and, when present, the element count.
    std::function<std::optional<std::pair<unsigned, std::optional<unsigned>>>(const llvm::CallBase *)> allocSizeArgs;
    // The memory whose contents an allocating call's result holds (a
    // reallocation), if any.
    std::function<const llvm::Value *(const llvm::CallBase *)> allocSource;
    // Whether a call copies bytes from src to dst.
    std::function<bool(const llvm::CallBase *, const llvm::Value *&, const llvm::Value *&)> byteCopy;
  };

  Points(const llvm::Module &M, const llvm::Module &U, Hooks h);

  // The solution for every pointer of both modules at once. The demand
  // solution of a value is the same set; asking for all of them first
  // means later queries find their nodes present and change nothing, so
  // a walk over many queries sees one solution throughout.
  void saturate();

  // The locations a pointer may point to, as location ids, over every
  // context of its function. Solves on demand. The reference is valid
  // until the next query that changes the solution.
  const llvm::SparseBitVector<> &of(const llvm::Value *v);
  // The same, in the contexts entered through the call `site`; all
  // contexts when the function is analysed once or no context has that
  // site.
  const llvm::SparseBitVector<> &of(const llvm::Value *v, const llvm::CallBase *site);
  // The call a context was entered through, or null.
  const llvm::CallBase *site(unsigned ctx) const { return ctxs[ctx].site; }
  Loc loc(unsigned id) const {
    if (id >= kQuiet) {
      const auto &q = quiets[id - kQuiet];
      return Loc{q.first, q.second};
    }
    return locs[id];
  }
  const Obj &obj(unsigned o) const { return objs[o]; }
  const std::vector<Write> &writes(unsigned o);
  const std::vector<PtrLoad> &ptrLoads(unsigned o);
  // Calls that hand a pointer into the object to code with no body here that
  // may write memory.
  const std::vector<const llvm::CallBase *> &escapes(unsigned o);
  // The functions a call can reach: resolved statically or through the
  // functions its callee operand points to.
  std::vector<const llvm::Function *> callees(const llvm::CallBase *C);
  // Whether a call may reach code with no body here: a callee with no body,
  // or a callee operand that may point outside the functions known here.
  bool unresolved(const llvm::CallBase *C);
  // The calls that can reach a function, directly or through pointers.
  const std::vector<const llvm::CallBase *> &callers(const llvm::Function *F);
  // Whether the function is analysed once per call. A value of any other
  // function denotes the same bytes in every context.
  bool perCall(const llvm::Function *F) const { return F && cloned.count(F); }
  // One write into an object, as a definition of its bytes.
  struct Def {
    const llvm::Instruction *inst = nullptr;
    unsigned ctx = 0;
    int64_t off = 0;   // start of the write, or Any
    int64_t len = -1;  // bytes from off, or -1 when unknown
  };
  // The writes partition an object's offsets into regions: every offset
  // in a region is covered by the same writes. Region i is
  // [bounds[i], bounds[i+1]); the last runs to +inf. Offsets below the
  // first bound are covered only by writes at offset Any.
  // The regions of an object: between two consecutive write ends the set
  // of covering writes is constant. Region i is [bounds[i], bounds[i+1]),
  // the last unbounded; region -1 is below bounds[0]. The regions are the
  // leaves of a segment tree (leaf k is region k - 1; node 1 the root;
  // the children of node k are 2k and 2k+1). Each write covers a run of
  // regions and is kept at the nodes whose spans tile that run, so the
  // writes covering a byte range are the lists at the nodes tiling the
  // range and at their ancestors, plus the writes at offset Any, which
  // cover every byte.
  struct Regions {
    uint64_t epoch = 0;
    std::vector<int64_t> bounds;
    size_t leaves = 1;                   // power of two >= number of regions
    std::vector<std::vector<Def>> tree;  // 2 * leaves node lists
    std::vector<Def> any;                // writes at offset Any
  };
  const Regions &regions(unsigned o);
  // The region holding off: -1 below the first bound.
  static int regionIndex(const Regions &r, int64_t off);
  // The leaves [lo, hi] of node k.
  static void nodeLeaves(const Regions &r, size_t k, size_t &lo, size_t &hi);
  // The bytes [lo, hi) of leaves [a, b]; unbounded ends are flagged.
  static void leafBytes(const Regions &r, size_t a, size_t b, int64_t &lo, bool &loInf, int64_t &hi,
                        bool &hiInf);
  // The number of the current solution. It grows when a query extends the
  // solution; a walk that cached parts of the old one must start over.
  uint64_t solution() {
    solve();
    return epoch;
  }

private:
  struct Edge {
    unsigned to = 0;
    bool gep = false;
    bool cyclic = false;  // gep: lies on a cycle of the graph
    int64_t off = 0;      // gep: offset added, or Any
  };
  struct Ctx {
    unsigned parent = 0;
    const llvm::CallBase *site = nullptr;
    const llvm::Function *fn = nullptr;
  };
  const llvm::Module &M;
  const llvm::Module &U;
  Hooks hooks;
  const llvm::DataLayout &DL;

  struct PairHash {
    size_t operator()(const std::pair<unsigned, int64_t> &p) const noexcept {
      size_t h = p.first;
      h ^= static_cast<size_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
    size_t operator()(const std::pair<const llvm::Value *, unsigned> &p) const noexcept {
      size_t h = reinterpret_cast<uintptr_t>(p.first);
      h ^= static_cast<size_t>(p.second) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      return h;
    }
  };
  std::vector<Obj> objs;
  std::vector<Loc> locs;  // location id -> (obj, off)
  std::unordered_map<std::pair<unsigned, int64_t>, unsigned, PairHash> locId;  // (obj, off) -> location id
  std::vector<std::vector<unsigned>> objLocs;              // object -> its location ids
  std::vector<int64_t> objExt;                             // object -> offsets below this are kept apart
  std::unordered_map<std::pair<const llvm::Value *, unsigned>, unsigned, PairHash> objOf;  // (site, ctx) -> object
  unsigned outsideObj = 0;  // the one object for memory outside both modules

  // Contexts.
  std::vector<Ctx> ctxs;  // ctxs[0]: no context
  std::map<std::tuple<unsigned, const llvm::CallBase *, const llvm::Function *>, unsigned> ctxId;
  std::unordered_set<const llvm::Function *> cloned;  // functions analysed per call site
  std::unordered_map<const llvm::Function *, std::vector<unsigned>> ctxsOf;  // cloned fn -> contexts entered
  std::set<std::pair<const llvm::Function *, unsigned>> entered;
  std::unordered_set<const llvm::Function *> demandedFn;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> staticCallers;

  // Nodes: location ids first (as created), value nodes interleaved; one
  // points-to set per node. The elements are split by their high 16 bits
  // into chunks; a chunk is a sorted vector of the low 16 bits while it
  // holds at most kArray of them, and a bitmap of 65536 bits past that.
  // A copied set shares that representation until one side is changed, so
  // a value carried unchanged along many edges is stored once.
  struct PtsSet {
    static constexpr size_t kArray = 4096;
    static constexpr size_t kWords = 1024;  // 65536 bits
    struct Chunk {
      uint32_t hi = 0;  // element >> 16
      uint32_t n = 0;
      std::vector<uint16_t> arr;   // sorted low halves, while bits is empty
      std::vector<uint64_t> bits;  // kWords words once past kArray elements
      bool bitmap() const { return !bits.empty(); }
      static size_t bitHash(unsigned bit) {
        size_t x = static_cast<size_t>(bit) * 0x9e3779b97f4a7c15ull;
        return x ^ (x >> 32);
      }
      bool test(uint16_t lo) const {
        if (bitmap())
          return (bits[lo >> 6] & (uint64_t{1} << (lo & 63))) != 0;
        return std::binary_search(arr.begin(), arr.end(), lo);
      }
      void toBitmap() {
        bits.assign(kWords, 0);
        for (uint16_t lo : arr)
          bits[lo >> 6] |= uint64_t{1} << (lo & 63);
        std::vector<uint16_t>().swap(arr);
      }
      void toArray() {
        arr.clear();
        arr.reserve(n);
        for (size_t w = 0; w < kWords; ++w) {
          uint64_t x = bits[w];
          while (x) {
            arr.push_back(static_cast<uint16_t>(w * 64 + static_cast<unsigned>(__builtin_ctzll(x))));
            x &= x - 1;
          }
        }
        std::vector<uint64_t>().swap(bits);
      }
      bool set(uint16_t lo) {
        if (bitmap()) {
          uint64_t &w = bits[lo >> 6];
          const uint64_t m = uint64_t{1} << (lo & 63);
          if (w & m)
            return false;
          w |= m;
          ++n;
          return true;
        }
        const auto it = std::lower_bound(arr.begin(), arr.end(), lo);
        if (it != arr.end() && *it == lo)
          return false;
        arr.insert(it, lo);
        ++n;
        if (n > kArray)
          toBitmap();
        return true;
      }
      // Union with another chunk of the same high half. When `neu` is
      // given, it receives the elements that were not already here.
      bool unite(const Chunk &o, Chunk *neu = nullptr) {
        if (o.n == 0)
          return false;
        if (n == 0) {
          *this = o;
          if (neu)
            *neu = o;
          return true;
        }
        const uint32_t before = n;
        if (!bitmap() && !o.bitmap()) {
          std::vector<uint16_t> out;
          std::vector<uint16_t> added;
          out.reserve(arr.size() + o.arr.size());
          if (!neu) {
            std::set_union(arr.begin(), arr.end(), o.arr.begin(), o.arr.end(), std::back_inserter(out));
          } else {
            size_t i = 0, j = 0;
            while (i < arr.size() && j < o.arr.size()) {
              if (arr[i] == o.arr[j]) {
                out.push_back(arr[i]);
                ++i;
                ++j;
              } else if (arr[i] < o.arr[j]) {
                out.push_back(arr[i++]);
              } else {
                out.push_back(o.arr[j]);
                added.push_back(o.arr[j]);
                ++j;
              }
            }
            while (i < arr.size())
              out.push_back(arr[i++]);
            while (j < o.arr.size()) {
              out.push_back(o.arr[j]);
              added.push_back(o.arr[j]);
              ++j;
            }
          }
          if (out.size() == arr.size())
            return false;
          arr.swap(out);
          n = static_cast<uint32_t>(arr.size());
          if (n > kArray)
            toBitmap();
          if (neu && !added.empty()) {
            neu->hi = hi;
            neu->arr.swap(added);
            neu->n = static_cast<uint32_t>(neu->arr.size());
          }
          return true;
        }
        if (!bitmap())
          toBitmap();
        if (!o.bitmap()) {
          for (uint16_t lo : o.arr) {
            uint64_t &w = bits[lo >> 6];
            const uint64_t m = uint64_t{1} << (lo & 63);
            if (w & m)
              continue;
            w |= m;
            ++n;
            if (neu)
              neu->set(lo);
          }
          if (neu)
            neu->hi = hi;
          return n != before;
        }
        for (size_t w = 0; w < kWords; ++w) {
          const uint64_t added = o.bits[w] & ~bits[w];
          if (!added)
            continue;
          bits[w] |= added;
          const auto cnt = static_cast<uint32_t>(__builtin_popcountll(added));
          n += cnt;
          if (!neu)
            continue;
          if (neu->bits.empty())
            neu->bits.assign(kWords, 0);
          neu->bits[w] |= added;
          neu->n += cnt;
          neu->hi = hi;
        }
        return n != before;
      }
      // Remove the elements of another chunk of the same high half.
      void subtract(const Chunk &o) {
        if (o.n == 0 || n == 0)
          return;
        if (!bitmap() && !o.bitmap()) {
          // A word map of the subtracted side avoids a comparison call per
          // element. The two-pointer walk is the same answer for short chunks.
          if (n > 128 && o.n > 128) {
            uint64_t word[1024] = {};
            for (uint16_t lo : o.arr)
              word[lo >> 6] |= uint64_t{1} << (lo & 63);
            size_t w = 0;
            for (size_t r = 0; r < arr.size(); ++r) {
              const uint16_t lo = arr[r];
              if ((word[lo >> 6] & (uint64_t{1} << (lo & 63))) == 0)
                arr[w++] = lo;
            }
            arr.resize(w);
            n = static_cast<uint32_t>(w);
            return;
          }
          size_t i = 0, j = 0, w = 0;
          while (i < arr.size() && j < o.arr.size()) {
            if (arr[i] == o.arr[j]) {
              ++i;
              ++j;
            } else if (arr[i] < o.arr[j]) {
              arr[w++] = arr[i++];
            } else {
              ++j;
            }
          }
          while (i < arr.size())
            arr[w++] = arr[i++];
          arr.resize(w);
          n = static_cast<uint32_t>(w);
          return;
        }
        if (!bitmap()) {
          std::vector<uint16_t> out;
          for (uint16_t lo : arr)
            if (!o.test(lo))
              out.push_back(lo);
          arr.swap(out);
          n = static_cast<uint32_t>(arr.size());
          return;
        }
        if (!o.bitmap()) {
          for (uint16_t lo : o.arr) {
            uint64_t &w = bits[lo >> 6];
            const uint64_t m = uint64_t{1} << (lo & 63);
            if (w & m) {
              w &= ~m;
              --n;
            }
          }
        } else {
          for (size_t w = 0; w < kWords; ++w) {
            const uint64_t removed = bits[w] & o.bits[w];
            if (removed) {
              bits[w] &= ~removed;
              n -= static_cast<uint32_t>(__builtin_popcountll(removed));
            }
          }
        }
        if (n <= kArray / 2)
          toArray();
      }
      // Whether some element here is missing from the other chunk.
      bool anyNotIn(const Chunk &o) const {
        if (n == 0)
          return false;
        if (o.n == 0 || n > o.n)
          return true;
        if (!bitmap()) {
          for (uint16_t lo : arr)
            if (!o.test(lo))
              return true;
          return false;
        }
        if (!o.bitmap()) {
          for (size_t w = 0; w < kWords; ++w) {
            uint64_t x = bits[w];
            while (x) {
              if (!o.test(static_cast<uint16_t>(w * 64 + static_cast<unsigned>(__builtin_ctzll(x)))))
                return true;
              x &= x - 1;
            }
          }
          return false;
        }
        for (size_t w = 0; w < kWords; ++w)
          if (bits[w] & ~o.bits[w])
            return true;
        return false;
      }
    };
    struct Body {
      std::vector<Chunk> chunks;  // sorted by hi
      size_t n = 0;
      size_t hash = 0;
      bool hashFresh = false;
      bool interned = false;  // in the shared pool; immutable
      // The hash is a function of the elements only, so equal sets land in
      // one bucket. It is recomputed when the set has changed, not as the
      // bits are turned on.
      size_t computeHash() const {
        size_t h = 0;
        for (const Chunk &c : chunks) {
          if (!c.bitmap()) {
            for (uint16_t lo : c.arr)
              h ^= Chunk::bitHash((c.hi << 16) | lo);
            continue;
          }
          for (size_t w = 0; w < kWords; ++w) {
            const uint64_t x = c.bits[w];
            if (!x)
              continue;
            size_t k = x ^ (static_cast<size_t>(c.hi) << 16) ^ (w * 0x9e3779b97f4a7c15ull);
            k *= 0x9e3779b97f4a7c15ull;
            h ^= k ^ (k >> 32);
          }
        }
        return h;
      }
      const Chunk *chunk(uint32_t hi) const {
        const size_t n = chunks.size();
        if (n == 0)
          return nullptr;
        if (n == 1)
          return chunks[0].hi == hi ? &chunks[0] : nullptr;
        const auto it = std::lower_bound(chunks.begin(), chunks.end(), hi,
                                         [](const Chunk &c, uint32_t h) { return c.hi < h; });
        return it != chunks.end() && it->hi == hi ? &*it : nullptr;
      }
      Chunk &chunkFor(uint32_t hi) {
        auto it = std::lower_bound(chunks.begin(), chunks.end(), hi,
                                   [](const Chunk &c, uint32_t h) { return c.hi < h; });
        if (it != chunks.end() && it->hi == hi)
          return *it;
        it = chunks.insert(it, Chunk{});
        it->hi = hi;
        return *it;
      }
    };
    // Shared until a mutating operation; nullptr is the empty set.
    // `over` holds elements that were added while the body was shared, so a
    // one-element addition does not copy the body. It stays disjoint from
    // the body and sorted.
    std::shared_ptr<Body> b;
    std::vector<unsigned> over;

    static std::unordered_map<size_t, std::vector<std::shared_ptr<Body>>> &pool() {
      static auto *p = new std::unordered_map<size_t, std::vector<std::shared_ptr<Body>>>();
      return *p;
    }
    static bool same(const Body &a, const Body &b) {
      if (a.n != b.n || a.chunks.size() != b.chunks.size())
        return false;
      for (size_t i = 0; i < a.chunks.size(); ++i) {
        const Chunk &x = a.chunks[i];
        const Chunk &y = b.chunks[i];
        if (x.hi != y.hi || x.n != y.n || x.bitmap() != y.bitmap())
          return false;
        if (x.bitmap() ? x.bits != y.bits : x.arr != y.arr)
          return false;
      }
      return true;
    }
    static void unintern(const std::shared_ptr<Body> &body) {
      auto &v = pool()[body->hash];
      for (auto it = v.begin(); it != v.end(); ++it) {
        if (it->get() == body.get()) {
          body->interned = false;
          v.erase(it);
          return;
        }
      }
      body->interned = false;
    }
    // Large equal sets are one body. The elements do not change.
    void internLarge() {
      // Equal sets of a few dozen elements are one body. Smaller sets are
      // left private: hashing them costs more than the copy it saves.
      if (!b || b->n < 64 || b->interned)
        return;
      if (!b->hashFresh) {
        b->hash = b->computeHash();
        b->hashFresh = true;
      }
      auto &v = pool()[b->hash];
      for (const auto &e : v) {
        if (e.get() == b.get() || same(*e, *b)) {
          b = e;
          b->interned = true;
          return;
        }
      }
      b->interned = true;
      v.push_back(b);
    }
    Body &mut() {
      if (!b) {
        b = std::make_shared<Body>();
        return *b;
      }
      if (!b->interned && b.use_count() == 1)
        return *b;
      auto copy = std::make_shared<Body>(*b);
      copy->interned = false;
      if (b->interned && b.use_count() == 2)
        unintern(b);
      b = std::move(copy);
      return *b;
    }
    // Record one element beside a shared body. A long side list is folded
    // into a private body once, not on every insertion.
    bool addOver(unsigned bit) {
      const auto it = std::lower_bound(over.begin(), over.end(), bit);
      over.insert(it, bit);
      if (over.size() > 256)
        flush();
      return true;
    }
    void flush() {
      if (over.empty())
        return;
      std::vector<unsigned> add;
      add.swap(over);
      Body &dst = mut();
      for (unsigned bit : add) {
        Chunk &c = dst.chunkFor(bit >> 16);
        if (c.set(static_cast<uint16_t>(bit & 0xffff)))
          ++dst.n;
      }
      dst.hashFresh = false;
    }

    struct Iter {
      std::shared_ptr<Body> b;
      const std::vector<unsigned> *over = nullptr;
      size_t ci = 0;   // chunk
      size_t pos = 0;  // index in arr, or bit index in bits
      size_t xi = 0;   // index in over, once the body is exhausted
      bool inOver = false;
      void seek() {
        if (!inOver && b) {
          while (ci < b->chunks.size()) {
            const Chunk &c = b->chunks[ci];
            if (!c.bitmap()) {
              if (pos < c.arr.size())
                return;
            } else {
              while (pos < 65536) {
                const uint64_t x = c.bits[pos >> 6] >> (pos & 63);
                if (x) {
                  pos += static_cast<unsigned>(__builtin_ctzll(x));
                  return;
                }
                pos = (pos | 63) + 1;
              }
            }
            ++ci;
            pos = 0;
          }
        }
        inOver = true;
      }
      unsigned operator*() const {
        if (inOver)
          return (*over)[xi];
        const Chunk &c = b->chunks[ci];
        const unsigned lo = c.bitmap() ? static_cast<unsigned>(pos) : c.arr[pos];
        return (c.hi << 16) | lo;
      }
      Iter &operator++() {
        if (inOver) {
          ++xi;
          return *this;
        }
        ++pos;
        seek();
        return *this;
      }
      bool operator!=(const Iter &o) const {
        return inOver != o.inOver || ci != o.ci || pos != o.pos || xi != o.xi;
      }
    };

    bool empty() const { return over.empty() && (!b || b->n == 0); }
    const void *bodyPtr() const { return b.get(); }
    bool sideEmpty() const { return over.empty(); }
    size_t count() const { return (b ? b->n : 0) + over.size(); }
    bool test(unsigned bit) const {
      if (std::binary_search(over.begin(), over.end(), bit))
        return true;
      if (!b)
        return false;
      const Chunk *c = b->chunk(bit >> 16);
      return c && c->test(static_cast<uint16_t>(bit & 0xffff));
    }
    void clear() {
      b.reset();
      over.clear();
    }
    Iter begin() const {
      Iter it;
      it.b = b;
      it.over = &over;
      it.seek();
      return it;
    }
    Iter end() const {
      Iter it;
      it.b = b;
      it.over = &over;
      it.ci = b ? b->chunks.size() : 0;
      it.inOver = true;
      it.xi = over.size();
      return it;
    }

    // `ids` is sorted and unique. One chunk per high half, no per-element insert.
    void assignSorted(const std::vector<unsigned> &ids) {
      clear();
      if (ids.empty())
        return;
      b = std::make_shared<Body>();
      Chunk c;
      c.hi = ids[0] >> 16;
      auto flushChunk = [&]() {
        if (c.n > kArray)
          c.toBitmap();
        b->n += c.n;
        b->chunks.push_back(std::move(c));
        c = Chunk{};
      };
      for (unsigned id : ids) {
        const uint32_t hi = id >> 16;
        if (hi != c.hi) {
          flushChunk();
          c.hi = hi;
        }
        c.arr.push_back(static_cast<uint16_t>(id & 0xffff));
        ++c.n;
      }
      flushChunk();
      internLarge();
    }
    bool set(unsigned bit) {
      if (test(bit))
        return false;
      if (b && (b->interned || b.use_count() != 1))
        return addOver(bit);
      Body &dst = mut();
      Chunk &c = dst.chunkFor(bit >> 16);
      if (!c.set(static_cast<uint16_t>(bit & 0xffff)))
        return false;
      ++dst.n;
      dst.hashFresh = false;
      return true;
    }
    void reset(unsigned bit) {
      if (!test(bit))
        return;
      PtsSet one;
      one.set(bit);
      intersectWithComplement(one);
    }
    bool operator|=(const PtsSet &o) {
      if (o.empty())
        return false;
      if (empty()) {
        b = o.b;
        over = o.over;
        internLarge();
        return true;
      }
      if (b == o.b) {
        bool grew = false;
        for (unsigned id : o.over)
          if (!test(id)) {
            addOver(id);
            grew = true;
          }
        if (!grew)
          internLarge();
        return grew;
      }
      if (b && (b->interned || b.use_count() != 1) && o.count() <= 256) {
        bool grew = false;
        for (unsigned id : o)
          if (!test(id)) {
            addOver(id);
            grew = true;
          }
        return grew;
      }
      if (!over.empty())
        flush();
      if (!o.over.empty()) {
        PtsSet tmp = o;
        tmp.flush();
        return *this |= tmp;
      }
      if (!o.b || o.b->n == 0)
        return false;
      if (!b) {
        b = o.b;
        internLarge();
        return true;
      }
      Body &dst = mut();
      bool grew = false;
      size_t i = 0;
      for (const Chunk &oc : o.b->chunks) {
        while (i < dst.chunks.size() && dst.chunks[i].hi < oc.hi)
          ++i;
        if (i < dst.chunks.size() && dst.chunks[i].hi == oc.hi) {
          const uint32_t before = dst.chunks[i].n;
          if (dst.chunks[i].unite(oc)) {
            dst.n += dst.chunks[i].n - before;
            grew = true;
          }
        } else {
          dst.chunks.insert(dst.chunks.begin() + static_cast<std::ptrdiff_t>(i), oc);
          dst.n += oc.n;
          grew = true;
        }
        ++i;
      }
      if (grew)
        dst.hashFresh = false;
      if (grew)
        internLarge();
      return grew;
    }
    // Merge `src` into this set. Elements that were missing are also merged
    // into `extra`, so a later pass can carry just those.
    bool absorb(const PtsSet &src, PtsSet &extra) {
      if (src.empty())
        return false;
      if (empty()) {
        b = src.b;
        over = src.over;
        extra |= *this;
        internLarge();
        return true;
      }
      if (b == src.b) {
        bool grew = false;
        for (unsigned id : src.over) {
          if (test(id))
            continue;
          addOver(id);
          extra.addOver(id);
          grew = true;
        }
        if (!grew)
          internLarge();
        return grew;
      }
      if (b && (b->interned || b.use_count() != 1) && src.count() <= 256) {
        bool grew = false;
        for (unsigned id : src) {
          if (test(id))
            continue;
          addOver(id);
          extra.addOver(id);
          grew = true;
        }
        return grew;
      }
      if (!over.empty())
        flush();
      if (!src.over.empty()) {
        PtsSet tmp = src;
        tmp.flush();
        return absorb(tmp, extra);
      }
      if (!src.b || src.b->n == 0)
        return false;
      if (!b) {
        b = src.b;
        extra |= *this;
        internLarge();
        return true;
      }
      Body &dst = mut();
      bool grew = false;
      size_t i = 0;
      for (const Chunk &oc : src.b->chunks) {
        while (i < dst.chunks.size() && dst.chunks[i].hi < oc.hi)
          ++i;
        if (i < dst.chunks.size() && dst.chunks[i].hi == oc.hi) {
          const uint32_t before = dst.chunks[i].n;
          Chunk neu;
          neu.hi = oc.hi;
          if (dst.chunks[i].unite(oc, &neu)) {
            dst.n += dst.chunks[i].n - before;
            grew = true;
            if (neu.n != 0)
              extra.keep(neu);
          }
        } else {
          dst.chunks.insert(dst.chunks.begin() + static_cast<std::ptrdiff_t>(i), oc);
          dst.n += oc.n;
          grew = true;
          extra.keep(oc);
        }
        ++i;
      }
      if (grew)
        dst.hashFresh = false;
      if (grew)
        internLarge();
      return grew;
    }
    void keep(const Chunk &c) {
      if (c.n == 0)
        return;
      Body &dst = mut();
      size_t i = 0;
      while (i < dst.chunks.size() && dst.chunks[i].hi < c.hi)
        ++i;
      if (i < dst.chunks.size() && dst.chunks[i].hi == c.hi) {
        const uint32_t before = dst.chunks[i].n;
        if (dst.chunks[i].unite(c))
          dst.n += dst.chunks[i].n - before;
      } else {
        dst.chunks.insert(dst.chunks.begin() + static_cast<std::ptrdiff_t>(i), c);
        dst.n += c.n;
      }
      dst.hashFresh = false;
    }
    void intersectWithComplement(const PtsSet &o) {
      if (!o.over.empty()) {
        PtsSet sub = o;
        sub.flush();
        intersectWithComplement(sub);
        return;
      }
      if (!over.empty())
        flush();
      if (!b || b->n == 0 || !o.b || o.b->n == 0)
        return;
      if (b == o.b) {
        b.reset();
        return;
      }
      Body &dst = mut();
      size_t i = 0;
      for (const Chunk &oc : o.b->chunks) {
        while (i < dst.chunks.size() && dst.chunks[i].hi < oc.hi)
          ++i;
        if (i == dst.chunks.size())
          break;
        if (dst.chunks[i].hi != oc.hi)
          continue;
        const uint32_t before = dst.chunks[i].n;
        dst.chunks[i].subtract(oc);
        dst.hashFresh = false;
        dst.n -= before - dst.chunks[i].n;
        if (dst.chunks[i].n == 0)
          dst.chunks.erase(dst.chunks.begin() + static_cast<std::ptrdiff_t>(i));
        else
          ++i;
      }
      if (dst.n == 0)
        b.reset();
      else
        internLarge();
    }
    // Whether some element here is missing from the other set.
    bool anyNotIn(const PtsSet &o) const {
      if (empty())
        return false;
      if (!over.empty() || !o.over.empty()) {
        if (o.count() < count())
          return true;
        for (unsigned id : *this)
          if (!o.test(id))
            return true;
        return false;
      }
      if (!b || b->n == 0)
        return false;
      if (!o.b || o.b->n < b->n)
        return true;
      if (b == o.b)
        return false;
      for (const Chunk &c : b->chunks) {
        const Chunk *oc = o.b->chunk(c.hi);
        if (!oc || c.anyNotIn(*oc))
          return true;
      }
      return false;
    }
  };
  // Nodes on a cycle of copy edges hold the same set at the fixpoint, so
  // they are one class with one set, one list of edges and one place in
  // the worklist; rep names the class and members its nodes. Per-node
  // facts (the value, the location, the hooks) stay with the member.
  std::vector<unsigned> rep;
  std::vector<std::vector<unsigned>> members;  // of a class representative; empty = itself alone
  std::vector<unsigned> merged;                // classes joined since the hooks last ran
  std::vector<PtsSet> pts;
  std::vector<PtsSet> seen;   // elements already carried along the class's edges
  std::vector<PtsSet> delta;  // in pts, not carried yet
  std::vector<PtsSet> gained;  // elements gained this round, for the hooks
  // Copy edges of one class. Insertion is hashed; seq is the stable
  // order the solver and the cycle search walk.
  struct OutEdges {
    std::vector<unsigned> seq;
    std::unordered_set<unsigned> has;
    bool set(unsigned t) {
      if (!has.insert(t).second)
        return false;
      seq.push_back(t);
      return true;
    }
    void reset(unsigned t) {
      if (!has.erase(t))
        return;
      seq.erase(std::remove(seq.begin(), seq.end(), t), seq.end());
    }
    void clear() {
      seq.clear();
      has.clear();
    }
    OutEdges &operator|=(const OutEdges &o) {
      for (unsigned t : o.seq)
        set(t);
      return *this;
    }
  };
  std::vector<OutEdges> copyTo;
  std::vector<std::vector<Edge>> gepTo;        // offset edges
  // An offset edge names the locations of its source, shifted. Those
  // locations are not stored on every copy of the pointer. `symAt` records
  // the source and the offset; a load, a store or a call builds the
  // locations when it needs them. Copy predecessors carry that image.
  struct Sym {
    unsigned src = 0;
    int64_t off = 0;
    bool cyclic = false;
  };
  std::vector<std::vector<Sym>> symAt;
  std::vector<std::vector<unsigned>> symUser;  // source -> nodes that shift it
  std::vector<std::vector<unsigned>> copyFrom; // SSA copy predecessors
  std::vector<char> storeSink;                 // store summary: keep the whole image
  std::vector<char> concreteOnly;              // cell, union, load or store summary
  std::vector<char> imgDirty;
  std::vector<unsigned> imgQ;
  std::vector<PtsSet> hookedSym;               // symbolic locations already given to hooks
  std::vector<PtsSet> imgCache;
  std::vector<unsigned> imgSeen;
  unsigned imgEpoch = 1;
  bool solving = false;
  struct ShiftKey {
    const void *body = nullptr;
    int64_t off = 0;
    bool cyclic = false;
    bool operator==(const ShiftKey &o) const {
      return body == o.body && off == o.off && cyclic == o.cyclic;
    }
  };
  struct ShiftHash {
    size_t operator()(const ShiftKey &k) const noexcept {
      size_t h = reinterpret_cast<uintptr_t>(k.body);
      h ^= static_cast<size_t>(k.off) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      h ^= static_cast<size_t>(k.cyclic);
      return h;
    }
  };
  std::unordered_map<ShiftKey, PtsSet, ShiftHash> shiftCache;
  std::vector<unsigned> unionOf;               // object -> node holding the union of its cells, or 0
  std::vector<bool> isLoc;
  // A large points-to set is one id: the unshifted roots, an offset, and
  // whether the offset is cyclic. Copies carry the id. The locations are
  // built when a load, a store, a call, or a query asks.
  std::vector<char> isSlice;
  struct Slice {
    // Roots are the unshifted locations of one source node. Every gep of
    // that node by the same offset is this slice, including after the
    // source set grows. `derived` slices shift those same roots further.
    PtsSet roots;
    unsigned src = UINT32_MAX;
    int64_t off = 0;
    bool cyclic = false;
    bool seeded = false;
    bool growing = false;
    bool replaying = false;  // a holder of this copy is walking the source set
    const void *folded = nullptr;  // body of the largest root set already folded
    size_t foldN = 0;
    PtsSet image;
    bool ready = false;
    // The cells are (object, shifted offset). They are not nodes. Pointer
    // values stored through the slice meet in `mem`.
    bool indexed = false;
    bool haveMem = false;
    unsigned mem = 0;
    // One node holds the contents of every cell. Each load of a holder reads
    // it, so the cells are not walked again per load.
    bool haveFeed = false;
    unsigned feed = 0;
    bool fed = false;
    std::vector<std::pair<unsigned, int64_t>> cells;
    std::unordered_map<unsigned, size_t> cellOf;  // object -> index in cells
    std::vector<unsigned> funcs;
    std::vector<unsigned> users;    // address nodes whose hooks were applied
    std::vector<unsigned> derived;  // further shifts of the same roots
    std::vector<unsigned> same;     // slices unified onto this one
    struct FactKey {
      const llvm::Instruction *inst = nullptr;
      unsigned ctx = 0;
      char kind = 0;
      bool operator==(const FactKey &o) const {
        return inst == o.inst && ctx == o.ctx && kind == o.kind;
      }
    };
    struct FactHash {
      size_t operator()(const FactKey &k) const noexcept {
        return reinterpret_cast<uintptr_t>(k.inst) ^ (static_cast<size_t>(k.ctx) << 1) ^
               static_cast<size_t>(k.kind);
      }
    };
    std::unordered_set<FactKey, FactHash> factSeen;
    // Loads, stores, escapes, memsets and copies through the slice. The
    // per-object record is built when a query asks about that object.
    struct Fact {
      const llvm::Instruction *inst = nullptr;
      unsigned ctx = 0;
      int64_t len = -1;
      char kind = 0;
    };
    std::vector<Fact> facts;
  };
  // Only a real slice has an entry. A solver node does not carry one.
  std::unordered_map<unsigned, Slice> sliceOf;
  std::unordered_map<ShiftKey, unsigned, ShiftHash> sliceId;
  // One slice per points-to class and displacement. A later element of the
  // class joins the same slice; it does not allocate another node.
  struct SliceKey {
    unsigned src = 0;
    int64_t off = 0;
    bool cyclic = false;
    bool operator==(const SliceKey &o) const {
      return src == o.src && off == o.off && cyclic == o.cyclic;
    }
  };
  struct SliceKeyHash {
    size_t operator()(const SliceKey &k) const noexcept {
      size_t h = k.src;
      h ^= static_cast<size_t>(k.off) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
      h ^= static_cast<size_t>(k.cyclic);
      return h;
    }
  };
  std::unordered_map<SliceKey, unsigned, SliceKeyHash> sliceBySrc;
  std::vector<std::vector<unsigned>> slicesFrom;
  struct SliceHit {
    int64_t off = 0;
    unsigned slice = 0;
  };
  std::vector<std::vector<SliceHit>> sliceAt;  // object -> slices that name it
  std::vector<char> objRealized;
  void realize(unsigned o);
  // A cell named only by a slice. It is not a solver node: the witness
  // reads its object and offset, and the object's writes, through loc().
  static constexpr unsigned kQuiet = 0x80000000u;
  std::vector<std::pair<unsigned, int64_t>> quiets;
  struct OOHash {
    size_t operator()(const std::pair<unsigned, int64_t> &p) const noexcept {
      return static_cast<size_t>(p.first) ^ (static_cast<size_t>(p.second) << 1);
    }
  };
  std::unordered_map<std::pair<unsigned, int64_t>, unsigned, OOHash> quietLoc;
  unsigned quietId(unsigned o, int64_t off);
  std::unordered_map<std::pair<const llvm::Value *, unsigned>, unsigned, PairHash> valNode;  // (value, ctx) -> node
  std::unordered_map<const llvm::Value *, std::vector<unsigned>> valNodes;  // value -> its nodes
  std::vector<const llvm::Value *> nodeVal;
  std::vector<unsigned> nodeCtx;
  std::vector<bool> usersDone;

  // Hooks on a node's points-to set.
  struct StoreAt {
    unsigned value = UINT32_MAX;
    const llvm::StoreInst *inst = nullptr;
    unsigned ctx = 0;
  };
  struct CallAt {
    const llvm::CallBase *call = nullptr;
    unsigned ctx = 0;
  };
  std::unordered_map<unsigned, std::vector<unsigned>> loadsAt;                    // address node -> load nodes
  // Every load of one pointer reads the same cells. The cells flow into one
  // node and each load copies that node, so the edges are one per cell plus
  // one per load. A store through one pointer writes the same values into
  // each cell; the values meet in one node and each cell copies it.
  std::unordered_map<unsigned, unsigned> loadSum;
  std::unordered_map<unsigned, unsigned> storeSum;
  std::unordered_map<unsigned, std::vector<StoreAt>> storesAt;
  std::unordered_map<unsigned, std::vector<CallAt>> callsAt;                      // callee operand node -> calls
  std::unordered_map<unsigned, std::vector<const llvm::CallBase *>> escapesAt;    // arg node -> external calls
  std::unordered_map<unsigned, std::vector<unsigned>> copyDstAt;  // dst pointer node -> copies
  std::unordered_map<unsigned, std::vector<unsigned>> copySrcAt;  // src pointer node -> copies
  std::unordered_map<unsigned, std::vector<CallAt>> memsetAt;
  std::set<std::pair<const llvm::StoreInst *, unsigned>> storeSeen;
  std::set<std::pair<const llvm::CallBase *, unsigned>> callSeen;
  std::vector<CallAt> indirectCalls;
  std::set<std::pair<const llvm::CallBase *, unsigned>> externalCalls;  // calls treated as reaching code with no body
  std::set<std::pair<const llvm::CallBase *, unsigned>> resolvedCalls;  // indirect calls that hold a function
  unsigned nEdges = 0;   // copy and offset edges added
  unsigned cycSeen = 0;  // nEdges last covered by the cycle search
  bool atFix = false;    // work is empty and every indirect call has been judged
  size_t drainedCalls = 0;
  // Everything a query can observe, counted; a solve that moves none of
  // it leaves the solution as it was.
  size_t nWrites = 0, nPtrLoads = 0, nEscapes = 0;
  // Query cache. epoch grows whenever a solve changes the solution, so a
  // cached points-to set is reused only while that solution still stands.
  uint64_t epoch = 1;
  std::vector<uint64_t> queryEpoch;
  std::vector<llvm::SparseBitVector<>> querySet;
  // The union asked for by of(), kept while epoch stands so a witness
  // step does not rebuild it.
  struct OfKey {
    const llvm::Value *v = nullptr;
    const llvm::CallBase *site = nullptr;
    bool operator==(const OfKey &o) const { return v == o.v && site == o.site; }
  };
  struct OfHash {
    size_t operator()(const OfKey &k) const {
      return std::hash<const void *>{}(k.v) ^ (std::hash<const void *>{}(k.site) * 0x9e3779b97f4a7c15ULL);
    }
  };
  std::unordered_map<OfKey, llvm::SparseBitVector<>, OfHash> ofCache;
  uint64_t ofEpoch = 0;
  // Boundaries of the write regions of an object. Ready after the first
  // query; the writes only grow before the solution is asked.
  std::vector<Regions> regionsOf;
  std::set<std::tuple<const llvm::CallBase *, unsigned, const llvm::Function *>> bound;
  // A byte copy: the places its pointers may point, the constant length
  // when there is one, and the nodes that carry cells between them: one
  // per distance for a copy of known length, one for the whole for a copy
  // of unknown length. A destination marked whole takes the source as a
  // whole: the copy closes a cycle of copies there.
  struct Copy {
    const llvm::CallBase *call = nullptr;
    unsigned ctx = 0;
    int64_t len = -1;
    std::vector<std::pair<Loc, bool>> dsts;
    std::vector<Loc> srcs;
    std::unordered_set<unsigned> dstSeen, srcSeen;
    std::map<int64_t, unsigned> mid;
    unsigned whole = 0;
  };
  std::vector<Copy> copies;
  std::unordered_map<unsigned, std::vector<std::pair<unsigned, int64_t>>> copyRel;  // src obj -> (copy, src off)
  // Byte-copy reachability. Objects on a cycle of copies are one component,
  // because each then reaches the others. Edges between components are a DAG,
  // and an edge is stored only when it adds a path. A search on that DAG
  // answers whether cells of one object are carried into another.
  std::vector<unsigned> copyRep;
  std::vector<std::vector<unsigned>> copySucc;
  std::vector<std::vector<unsigned>> copyPred;
  std::vector<PtsSet> copyHit;  // queried root -> roots it reaches
  std::vector<char> copyHave;   // 1 when copyHit is current
  std::unordered_set<uint64_t> copyAsked;  // object pairs already applied
  std::vector<unsigned> copyMark;
  unsigned copyStamp = 1;
  struct DedupHash {
    size_t operator()(const std::pair<unsigned, unsigned> &p) const noexcept {
      return (static_cast<size_t>(p.first) << 32) ^ p.second;
    }
    size_t operator()(
        const std::tuple<unsigned, int64_t, int64_t, const llvm::Instruction *, unsigned> &t) const noexcept {
      size_t h = std::get<0>(t);
      auto mix = [&](size_t x) { h ^= x + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2); };
      mix(static_cast<size_t>(std::get<1>(t)));
      mix(static_cast<size_t>(std::get<2>(t)));
      mix(static_cast<uintptr_t>(reinterpret_cast<uintptr_t>(std::get<3>(t))));
      mix(std::get<4>(t));
      return h;
    }
  };
  std::unordered_map<unsigned, std::vector<Write>> writesOf;
  std::unordered_set<std::tuple<unsigned, int64_t, int64_t, const llvm::Instruction *, unsigned>, DedupHash>
      writeSeen;
  std::unordered_map<unsigned, std::vector<PtrLoad>> ptrLoadsOf;
  std::unordered_set<std::pair<unsigned, unsigned>, DedupHash> ptrLoadSeen;  // (load node, location) recorded
  std::unordered_map<unsigned, std::vector<const llvm::CallBase *>> escapesOf;
  std::set<std::pair<unsigned, const llvm::CallBase *>> escapeSeen;

  std::unordered_map<const llvm::Function *, std::vector<const llvm::CallBase *>> callersOf;
  std::unordered_map<const llvm::Function *, std::vector<const llvm::ReturnInst *>> returnsOf;

  std::vector<unsigned> work;
  std::vector<bool> inWork;
  std::unordered_set<unsigned> demanded;

  void findCloned();
  bool localAlloca(const llvm::AllocaInst *AI);
  std::optional<int64_t> evalConst(const llvm::Value *v, unsigned ctx, unsigned depth = 0);
  const llvm::Function *fnOf(const llvm::Value *v) const;
  unsigned ctxOf(const llvm::Value *v, unsigned ctx) const;
  unsigned context(unsigned parent, const llvm::CallBase *site, const llvm::Function *F);
  void enter(const llvm::Function *F, unsigned ctx);
  void demandFn(const llvm::Function *F);
  unsigned newObj(Kind k, const llvm::Value *site, unsigned ctx, std::optional<int64_t> size);
  unsigned siteObj(Kind k, const llvm::Value *site, unsigned ctx, std::optional<int64_t> size = std::nullopt);
  void escape(unsigned o, const llvm::CallBase *C);
  unsigned location(unsigned o, int64_t off);
  unsigned locateQuiet(unsigned o, int64_t off);
  unsigned node(const llvm::Value *v, unsigned ctx);
  unsigned newNode(const llvm::Value *v, unsigned ctx);
  void edge(unsigned from, unsigned to, bool gep = false, int64_t off = 0);
  void retargetSlices(unsigned from, unsigned to);
  unsigned unionNode(unsigned o);
  unsigned loadSummary(unsigned addr);
  unsigned storeSummary(unsigned addr);
  void linkLoad(unsigned addr, unsigned L, unsigned id);
  void pourLoad(unsigned summary, unsigned id);
  void noteLoad(unsigned L, unsigned id);
  void seed(unsigned n, unsigned o);
  void materializeUsers(unsigned n);
  void bindCall(const llvm::CallBase *C, unsigned ctx, const llvm::Function *F);
  void registerCall(const llvm::CallBase *C, unsigned ctx);
  void registerCopy(const llvm::CallBase *C, unsigned ctx, unsigned dn, unsigned sn, int64_t len);
  void treatExternal(const llvm::CallBase *C, unsigned ctx);
  const llvm::Function *target(const llvm::CallBase *C, unsigned o) const;
  void registerStore(const llvm::StoreInst *St, unsigned ctx);
  void onPts(unsigned n, const PtsSet &fresh);
  void hookCells(unsigned n, const PtsSet &ids, bool doLoads = true);
  void feedCopy(unsigned sid, const PtsSet &ids);
  unsigned sliceFeed(unsigned sid);
  void attachLoads(unsigned sid, unsigned n);
  void shareLoads(unsigned sid, unsigned loader, unsigned n);
  // A copy of a large set is one reference to that set. Holders that load,
  // store, or call still see each new location of the source.
  void syncCopyUsers(unsigned n, const PtsSet &fresh);
  void replayCopy(unsigned sid, unsigned n);
  void apply(const Edge &e, const PtsSet &set, unsigned src);
  PtsSet shift(const PtsSet &set, int64_t off, bool cyclic, unsigned src = UINT32_MAX);
  PtsSet shiftElems(const PtsSet &set, int64_t off, bool cyclic);
  bool isSliceId(unsigned id) const;
  unsigned makeSlice(PtsSet roots, int64_t off, bool cyclic);
  unsigned stableSlice(unsigned src, int64_t off, bool cyclic);
  void growSlice(unsigned sid, const PtsSet &ids);
  void materializeSlice(unsigned sid);
  void pour(unsigned sid, const PtsSet &roots, int64_t base, bool cyclic, std::unordered_set<unsigned> &seen);
  void expandHeld(unsigned id, llvm::SparseBitVector<> &one, std::unordered_set<unsigned> &seen);
  void addSliceCell(unsigned sid, unsigned obj, int64_t off);
  void addSliceFunc(unsigned sid, unsigned obj);
  void connectSlice(unsigned sid, unsigned obj, int64_t off);
  unsigned composeSlice(unsigned id, int64_t off, bool cyclic);
  PtsSet sliceImage(unsigned id);
  PtsSet expandAddrs(const PtsSet &set);
  unsigned sliceMem(unsigned sid);
  void ensureSlice(unsigned sid);
  void onPtsSlice(unsigned n, unsigned sid);
  void bridgeCell(unsigned locId);
  PtsSet pointees(unsigned n);
  void touchImage(unsigned n);
  void symbolicHooks();
  bool hasHooks(unsigned n) const;
  void hookMembers(unsigned n, const PtsSet &fresh);
  void solve();
  const llvm::SparseBitVector<> &storeOf(const llvm::Value *v, const llvm::CallBase *site,
                                         llvm::SparseBitVector<> out);
  void findCycles();
  std::vector<unsigned> components(bool withOffsets);
  void collapse();
  unsigned find(unsigned n);
  void unify(unsigned a, unsigned b);
  PtsSet &P(unsigned n) { return pts[find(n)]; }
  void push(unsigned n);
  bool pending(unsigned n) const;
  void fillGlobal(const llvm::GlobalVariable *G);
  void fillConstant(unsigned o, int64_t off, const llvm::Constant *C);
  int64_t gepOffset(const llvm::GEPOperator *G);
  bool pointerLike(const llvm::Type *T) const;
  bool writable(unsigned o) const;
  void addWrite(unsigned o, int64_t off, int64_t len, const llvm::Instruction *I, unsigned ctx);
  unsigned copyMid(unsigned ci, int64_t k);
  unsigned copyWhole(unsigned ci);
  int64_t memsetLen(const llvm::CallBase *C, unsigned ctx);
  void copySrc(unsigned ci, unsigned srcLoc);
  void copyDst(unsigned ci, unsigned dstLoc);
  bool copiesInto(unsigned from, unsigned to);
  void addCopyEdge(unsigned from, unsigned to);
  void copyEnsure(unsigned n);
  unsigned copyFind(unsigned x);
  unsigned copyFresh();
  void copyFill(unsigned from);
  void copyDrop();
  void copyInvalidateAbove(unsigned from);
  void mergeCopyCycle(unsigned from, unsigned to);
  const llvm::Function *bodyOf(const llvm::Function *F);
  bool external(const llvm::CallBase *C, std::vector<const llvm::Function *> &cs);
  llvm::SparseBitVector<> unionPts(const std::vector<unsigned> &nodes);
  std::vector<const llvm::Function *> calleesOf(const llvm::CallBase *C);
};

} // namespace chain
