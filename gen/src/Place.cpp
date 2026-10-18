#include "gen/Place.hpp"

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Module.h"

#include <algorithm>
#include <map>
#include <unordered_map>

namespace gen {

namespace {

std::string canonical(llvm::StringRef n) {
  auto dot = n.rfind('.');
  if (dot == llvm::StringRef::npos || dot + 1 >= n.size())
    return n.str();
  for (size_t i = dot + 1; i < n.size(); ++i)
    if (n[i] < '0' || n[i] > '9')
      return n.str();
  return n.substr(0, dot).str();
}

llvm::Module *layoutAlso = nullptr;

llvm::StructType *findStruct(llvm::Module &M, const std::string &want) {
  struct Cache {
    const llvm::Module *m = nullptr;
    const llvm::Module *also = nullptr;
    std::unordered_map<std::string, llvm::StructType *> exact;
    std::unordered_map<std::string, llvm::StructType *> canon;
  };
  static Cache cache;
  if (cache.m != &M || cache.also != layoutAlso) {
    cache = Cache{};
    cache.m = &M;
    cache.also = layoutAlso;
    llvm::Module *also = layoutAlso;
    auto index = [&](llvm::Module &Mod) {
      for (llvm::StructType *S : Mod.getIdentifiedStructTypes()) {
        if (!S->hasName())
          continue;
        cache.exact.emplace(S->getName().str(), S);
        cache.canon.emplace(canonical(S->getName()), S);
      }
    };
    index(M);
    if (also)
      index(*also);
  }
  auto it = cache.exact.find(want);
  if (it != cache.exact.end())
    return it->second;
  auto c = cache.canon.find(want);
  return c == cache.canon.end() ? nullptr : c->second;
}

struct Graph {
  std::vector<Object> objects;
  std::map<std::pair<int, int64_t>, int> childAt;
  llvm::StructType *rootTy = nullptr;
};

struct Cursor {
  int alloc = 0;
  uint64_t origin = 0;
  llvm::StructType *ty = nullptr;
};

int internChild(Graph &g, llvm::Module &M, const llvm::DataLayout &DL, int parent, int64_t at, const std::string &type,
                bool choice) {
  auto key = std::make_pair(parent, at);
  auto it = g.childAt.find(key);
  if (it != g.childAt.end()) {
    int id = it->second;
    llvm::StructType *S = findStruct(M, type);
    if (S && !S->isOpaque()) {
      uint64_t n = DL.getTypeAllocSize(S);
      uint64_t al = DL.getABITypeAlign(S).value();
      if (n > g.objects[id].size)
        g.objects[id].size = n;
      if (al > g.objects[id].align)
        g.objects[id].align = al;
      if (g.objects[id].type == "struct.slot" || g.objects[id].type.empty())
        g.objects[id].type = type;
    }
    for (Edge &e : g.objects[parent].edges)
      if (e.at == at && e.child == id && !choice)
        e.choice = false;
    return id;
  }
  llvm::StructType *S = findStruct(M, type);
  Object o;
  o.type = type;
  if (S && !S->isOpaque()) {
    o.size = DL.getTypeAllocSize(S);
    o.align = DL.getABITypeAlign(S).value();
  }
  int id = static_cast<int>(g.objects.size());
  g.objects.push_back(std::move(o));
  g.objects[parent].edges.push_back(Edge{at, id, choice});
  g.childAt.emplace(key, id);
  return id;
}

bool addField(Graph &g, llvm::Module &M, const llvm::DataLayout &DL, const Field &field, int choiceStep,
              int64_t *atOut = nullptr, int *allocOut = nullptr) {
  if (field.steps.empty() || (field.len <= 0 && field.fn.empty() && !field.self))
    return false;
  const Step &first = field.steps[0];
  if (g.objects.empty()) {
    g.rootTy = findStruct(M, first.type);
    Object o;
    o.type = first.type;
    if (g.rootTy && !g.rootTy->isOpaque()) {
      o.size = DL.getTypeAllocSize(g.rootTy);
      o.align = DL.getABITypeAlign(g.rootTy).value();
    }
    g.objects.push_back(std::move(o));
  } else if (g.objects[0].type != first.type) {
    return false;
  }
  Cursor cur{0, 0, g.rootTy};
  for (size_t i = 0; i < field.steps.size(); ++i) {
    const Step &step = field.steps[i];
    // An unknown offset is not a byte of this object. A pointer load still
    // names the pointee, whose own fields start at that object's base.
    if (step.any) {
      if (i == 0 || !(step.neu || step.both))
        return false;
      Field neu = field;
      neu.steps[i].any = false;
      neu.steps[i].off = 0;
      neu.steps[i].both = false;
      neu.steps[i].neu = true;
      return addField(g, M, DL, neu, static_cast<int>(i));
    }
    if (step.off < 0)
      return false;
    if (step.both && i > 0) {
      Field neu = field;
      neu.steps[i].both = false;
      neu.steps[i].neu = true;
      Field emb = field;
      emb.steps[i].both = false;
      emb.steps[i].neu = false;
      bool okN = addField(g, M, DL, neu, static_cast<int>(i));
      bool okE = addField(g, M, DL, emb, choiceStep);
      return okN || okE;
    }
    if (i > 0 && step.neu) {
      int child = internChild(g, M, DL, cur.alloc, static_cast<int64_t>(cur.origin), step.type,
                              choiceStep == static_cast<int>(i));
      if (child < 0)
        return false;
      cur = Cursor{child, 0, findStruct(M, step.type)};
    }
    bool last = i + 1 == field.steps.size();
    if (last && field.self) {
      uint64_t at = cur.origin + static_cast<uint64_t>(step.off);
      g.objects[cur.alloc].backs.push_back(static_cast<int64_t>(at));
      uint64_t end = at + DL.getPointerSize(0);
      if (end > g.objects[cur.alloc].size)
        g.objects[cur.alloc].size = end;
      if (atOut)
        *atOut = static_cast<int64_t>(at);
      if (allocOut)
        *allocOut = cur.alloc;
    } else if (last && !field.fn.empty()) {
      uint64_t at = cur.origin + static_cast<uint64_t>(step.off);
      g.objects[cur.alloc].fns.push_back(Object::FnPtr{static_cast<int64_t>(at), field.fn});
      uint64_t end = at + DL.getPointerSize(0);
      if (end > g.objects[cur.alloc].size)
        g.objects[cur.alloc].size = end;
      if (atOut)
        *atOut = static_cast<int64_t>(at);
      if (allocOut)
        *allocOut = cur.alloc;
    } else if (last) {
      uint64_t at = cur.origin + static_cast<uint64_t>(step.off);
      g.objects[cur.alloc].ranges.push_back(Range{static_cast<int64_t>(at), field.len});
      if (field.pin && field.len > 0)
        g.objects[cur.alloc].pins.push_back(
            Object::Pin{static_cast<int64_t>(at), field.pinVal, static_cast<uint64_t>(field.len)});
      if (field.assumePred != 0 && !field.assumeVals.empty() && field.len > 0)
        g.objects[cur.alloc].assumes.push_back(
            Object::Assume{static_cast<int64_t>(at), -1, -1, -1, static_cast<uint64_t>(field.len), field.assumePred,
                           field.assumeVals, field.mask});
      if (atOut)
        *atOut = static_cast<int64_t>(at);
      if (allocOut)
        *allocOut = cur.alloc;
      uint64_t end = at + static_cast<uint64_t>(field.len);
      if (end > g.objects[cur.alloc].size)
        g.objects[cur.alloc].size = end;
    } else if (field.steps[i + 1].neu) {
      cur.origin += static_cast<uint64_t>(step.off);
      uint64_t ptr = DL.getPointerSize(0);
      uint64_t end = cur.origin + ptr;
      if (end > g.objects[cur.alloc].size)
        g.objects[cur.alloc].size = end;
    } else {
      cur.origin += static_cast<uint64_t>(step.off);
    }
  }
  return true;
}

// One range is one load. Two loads stay two ranges.
void mergeRanges(std::vector<Range> &ranges) {
  if (ranges.empty())
    return;
  std::sort(ranges.begin(), ranges.end(), [](const Range &a, const Range &b) {
    if (a.off != b.off)
      return a.off < b.off;
    return a.len < b.len;
  });
  std::vector<Range> out;
  for (const Range &r : ranges) {
    if (!out.empty() && out.back().off == r.off && out.back().len == r.len)
      continue;
    out.push_back(r);
  }
  ranges = std::move(out);
}

bool stringObject(const std::string &type) {
  return type.find("basic_string") != std::string::npos || type.find("string_view") != std::string::npos;
}

// A string or string_view cell at the pointer word is the address of the
// characters, and the following word is their count. The slice names those
// two words. The characters are a separate object, the pointer is stored at
// offset 0, and the count is the size of that object. A basic_string also
// stores that size as its capacity word.
void tieString(Graph &g, const llvm::DataLayout &DL) {
  uint64_t ptr = DL.getPointerSize(0);
  if (ptr == 0)
    return;
  std::vector<int> parents;
  for (int i = 0; i < static_cast<int>(g.objects.size()); ++i) {
    Object &o = g.objects[i];
    if (!stringObject(o.type))
      continue;
    bool pointed = false;
    for (const auto &e : o.edges)
      if (e.at == 0)
        pointed = true;
    if (pointed)
      continue;
    bool saw = false;
    std::vector<Range> keep;
    for (const Range &r : o.ranges) {
      uint64_t off = static_cast<uint64_t>(r.off < 0 ? 0 : r.off);
      uint64_t end = off + static_cast<uint64_t>(r.len < 0 ? 0 : r.len);
      if (off < ptr * 2 && end > off && off < ptr) {
        saw = true;
        continue;
      }
      if (off < ptr * 2 && end > ptr)
        continue;
      if (o.size > ptr * 2 && off < ptr * 3 && end > ptr * 2)
        continue;
      keep.push_back(r);
    }
    if (!saw)
      continue;
    o.ranges = std::move(keep);
    o.words.push_back({static_cast<int64_t>(ptr), ptr});
    if (o.size > ptr * 2)
      o.words.push_back({static_cast<int64_t>(ptr * 2), ptr});
    uint64_t need = ptr * (o.size > ptr * 2 ? 3 : 2);
    if (o.size < need)
      o.size = need;
    parents.push_back(i);
  }
  for (int parent : parents) {
    Object buf;
    buf.type = "char";
    buf.size = ptr;
    buf.align = 1;
    buf.ranges.push_back(Range{0, static_cast<int64_t>(ptr)});
    int id = static_cast<int>(g.objects.size());
    g.objects.push_back(std::move(buf));
    g.objects[parent].edges.push_back(Edge{0, id, false});
  }
}

void takeShape(PlacedArg &arg, Graph &g, const llvm::DataLayout &DL) {
  if (g.objects.empty())
    return;
  tieString(g, DL);
  for (Object &o : g.objects)
    mergeRanges(o.ranges);
  Shape s;
  s.objects = std::move(g.objects);
  s.root = 0;
  arg.shapes.push_back(std::move(s));
}

} // namespace

std::vector<Placed> placeAll(const std::vector<Driver> &drivers, llvm::Module &library, llvm::Module *upstream) {
  const llvm::DataLayout &DL = library.getDataLayout();
  layoutAlso = upstream;
  findStruct(library, "");
  std::vector<Placed> out;
  for (const Driver &d : drivers) {
    Placed p;
    p.func = d.func;
    p.fileBytes = d.fileBytes;
    for (const Argument &a : d.args) {
      PlacedArg arg;
      arg.index = a.index;
      std::map<std::string, Graph> plain;
      std::map<std::string, std::vector<const Field *>> kept;
      for (const Field &f : a.fields) {
        if (f.steps.empty()) {
          ++arg.dropped;
          continue;
        }
        const std::string &root = f.steps[0].type;
        Graph &g = plain[root];
        if (!addField(g, library, DL, f, -1)) {
          ++arg.dropped;
          Graph rebuilt;
          for (const Field *old : kept[root])
            addField(rebuilt, library, DL, *old, -1);
          g = std::move(rebuilt);
        } else {
          kept[root].push_back(&f);
        }
      }
      for (const Rel &rel : d.rels) {
        if (rel.arg != a.index || rel.otherArg != a.index || rel.left.empty() || rel.right.empty())
          continue;
        if (rel.left[0].type != rel.right[0].type)
          continue;
        Graph &g = plain[rel.left[0].type];
        Field left, right;
        left.steps = rel.left;
        left.len = rel.len;
        right.steps = rel.right;
        right.len = rel.len;
        int64_t ao = 0, bo = 0;
        int aa = 0, bb = 0;
        if (!addField(g, library, DL, left, -1, &ao, &aa) || !addField(g, library, DL, right, -1, &bo, &bb))
          continue;
        Object::Assume as;
        as.off = ao;
        as.otherAlloc = bb;
        as.otherOff = bo;
        as.bytes = static_cast<unsigned>(rel.len);
        as.pred = rel.pred;
        g.objects[aa].assumes.push_back(std::move(as));
      }
      auto swapPred = [](unsigned p) -> unsigned {
        switch (p) {
        case llvm::CmpInst::ICMP_UGT: return llvm::CmpInst::ICMP_ULT;
        case llvm::CmpInst::ICMP_UGE: return llvm::CmpInst::ICMP_ULE;
        case llvm::CmpInst::ICMP_ULT: return llvm::CmpInst::ICMP_UGT;
        case llvm::CmpInst::ICMP_ULE: return llvm::CmpInst::ICMP_UGE;
        case llvm::CmpInst::ICMP_SGT: return llvm::CmpInst::ICMP_SLT;
        case llvm::CmpInst::ICMP_SGE: return llvm::CmpInst::ICMP_SLE;
        case llvm::CmpInst::ICMP_SLT: return llvm::CmpInst::ICMP_SGT;
        case llvm::CmpInst::ICMP_SLE: return llvm::CmpInst::ICMP_SGE;
        default: return p;
        }
      };
      for (const Rel &rel : d.rels) {
        bool leftInt = rel.left.empty();
        bool rightInt = rel.right.empty();
        if (leftInt == rightInt)
          continue;
        const std::vector<Step> &fieldSteps = leftInt ? rel.right : rel.left;
        int fieldArg = leftInt ? rel.otherArg : rel.arg;
        int intArg = leftInt ? rel.arg : rel.otherArg;
        if (fieldArg != a.index || fieldSteps.empty() || fieldSteps[0].type.empty())
          continue;
        unsigned pred = leftInt ? swapPred(rel.pred) : rel.pred;
        if (pred == 0 || rel.len <= 0)
          continue;
        Field field;
        field.steps = fieldSteps;
        field.len = rel.len;
        int64_t off = 0;
        int alloc = 0;
        Graph &g = plain[field.steps[0].type];
        if (!addField(g, library, DL, field, -1, &off, &alloc))
          continue;
        if (alloc < 0 || alloc >= (int)g.objects.size())
          continue;
        Object::Assume as;
        as.off = off;
        as.otherArg = intArg;
        as.bytes = static_cast<uint64_t>(rel.len);
        as.pred = pred;
        g.objects[alloc].assumes.push_back(std::move(as));
      }
      for (auto &kv : plain)
        takeShape(arg, kv.second, DL);
      p.args.push_back(std::move(arg));
    }
    out.push_back(std::move(p));
  }
  return out;
}

} // namespace gen
