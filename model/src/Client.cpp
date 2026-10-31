// The must side: a harness that is itself a client of the downstream.
//
// A client calls interface functions only: the functions D's (or U's) shared
// object exports. Every argument is a value a client holds. A handle is a
// pointer to a type whose definition is not in an installed header; a client
// holds one only as a value an interface function returned or wrote through
// an out-parameter. Any other value the client chooses: integers, its own
// buffers, its own functions, and the fields of public structs it allocates.
// The heap the harness builds is therefore reachable by some client, so a
// sink the harness reaches is reached through the interface.
//
// The search over clients is directed by the may side. The sequence names
// the function the sink is reached from; the residual formula names the
// cells its entry state needs. A cell of an opaque type is set only by the
// interface functions whose calls store to that field (its writers). A cell
// of a public type the client writes itself.
//
// Producible types are the least fixpoint of
//   Prod(T) <= f returns or writes out a T, and every handle f takes is Prod,
// with the cost of T the fewest interface calls that make one (Knuth's
// generalisation of Dijkstra's algorithm to and-or grammars). A producer
// only takes handles of strictly cheaper types, so the harness makes them
// in cost order and each exists before it is used.

#include "Client.h"
#include "Close.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/TargetParser/Triple.h"

#include <charconv>
#include <cstdio>
#include <functional>
#include <queue>
#include <sstream>

namespace {

std::string baseName(const std::string &p) {
  auto s = p.find_last_of('/');
  return s == std::string::npos ? p : p.substr(s + 1);
}

std::string jsonString(const std::string &text, const std::string &key, size_t from = 0) {
  auto k = text.find("\"" + key + "\"", from);
  if (k == std::string::npos)
    return "";
  auto c = text.find(':', k);
  auto q = text.find('"', c);
  auto e = text.find('"', q + 1);
  return text.substr(q + 1, e - q - 1);
}

// The functions so exports, and with data its objects too.
std::set<std::string> dynamicSymbols(const std::string &so, bool data = false) {
  static const std::set<std::string> objects = {"D", "B", "R", "V", "u"};
  std::set<std::string> out;
  std::string cmd = "nm -D --defined-only '" + so + "' 2>/dev/null";
  FILE *p = popen(cmd.c_str(), "r");
  if (!p)
    return out;
  char line[4096];
  while (fgets(line, sizeof line, p)) {
    std::istringstream in(line);
    std::string addr, kind, name;
    in >> addr >> kind >> name;
    if (kind != "T" && kind != "W" && !(data && objects.count(kind)))
      continue;
    auto at = name.find('@');
    out.insert(at == std::string::npos ? name : name.substr(0, at));
  }
  pclose(p);
  return out;
}

std::set<std::string> installedHeaders(const fs::path &include) {
  std::set<std::string> out;
  std::error_code ec;
  if (!fs::exists(include, ec))
    return out;
  for (auto it = fs::recursive_directory_iterator(include, ec); it != fs::recursive_directory_iterator(); it.increment(ec))
    if (it->is_regular_file(ec))
      out.insert(it->path().filename().string());
  return out;
}

// The identifiers the installed headers mention: an exported function is
// part of the interface only if a header declares it to clients.
std::set<std::string> headerIdentifiers(const fs::path &include) {
  std::set<std::string> out;
  std::error_code ec;
  if (!fs::exists(include, ec))
    return out;
  for (auto it = fs::recursive_directory_iterator(include, ec); it != fs::recursive_directory_iterator(); it.increment(ec)) {
    if (!it->is_regular_file(ec))
      continue;
    std::ifstream in(it->path());
    std::string text((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
    for (size_t i = 0; i < text.size();) {
      if (std::isalpha((unsigned char)text[i]) || text[i] == '_') {
        size_t j = i;
        while (j < text.size() && (std::isalnum((unsigned char)text[j]) || text[j] == '_'))
          ++j;
        out.insert(text.substr(i, j - i));
        i = j;
      } else if (std::isdigit((unsigned char)text[i])) {
        while (i < text.size() && (std::isalnum((unsigned char)text[i]) || text[i] == '_'))
          ++i;
      } else
        ++i;
    }
  }
  return out;
}

const DIType *strip(const DIType *T) {
  while (auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
    auto tag = D->getTag();
    if (tag != dwarf::DW_TAG_typedef && tag != dwarf::DW_TAG_const_type && tag != dwarf::DW_TAG_volatile_type &&
        tag != dwarf::DW_TAG_restrict_type && tag != dwarf::DW_TAG_atomic_type)
      break;
    T = D->getBaseType();
  }
  return T;
}

bool isPointer(const DIType *T) {
  auto *D = dyn_cast_or_null<DIDerivedType>(T);
  return D && (D->getTag() == dwarf::DW_TAG_pointer_type || D->getTag() == dwarf::DW_TAG_reference_type ||
               D->getTag() == dwarf::DW_TAG_rvalue_reference_type);
}

// The object a pointer parameter T points to, or null when it is const
// (the callee may not write it) or T is not a pointer.
const DIType *writablePointee(const DIType *T) {
  T = strip(T);
  if (!isPointer(T))
    return nullptr;
  const DIType *U = cast<DIDerivedType>(T)->getBaseType();
  for (auto *D = dyn_cast_or_null<DIDerivedType>(U); D; D = dyn_cast_or_null<DIDerivedType>(D->getBaseType())) {
    if (D->getTag() == dwarf::DW_TAG_const_type)
      return nullptr;
    if (D->getTag() != dwarf::DW_TAG_typedef && D->getTag() != dwarf::DW_TAG_volatile_type)
      break;
  }
  return strip(U);
}

// A3 for results: a writable byte pointer slot (T** with T void or a byte)
// directly followed by a writable integer slot is an out buffer and its
// length. Returns the integer width, or 0.
unsigned outBufferPair(const DIType *buf, const DIType *len) {
  const DIType *P = writablePointee(buf);
  if (!P || !isPointer(P))
    return 0;
  const DIType *E = strip(cast<DIDerivedType>(P)->getBaseType());
  auto *EB = dyn_cast_or_null<DIBasicType>(E);
  if (E && !(EB && EB->getSizeInBits() == 8))
    return 0;
  auto *L = dyn_cast_or_null<DIBasicType>(writablePointee(len));
  if (!L || (L->getEncoding() != dwarf::DW_ATE_unsigned && L->getEncoding() != dwarf::DW_ATE_signed))
    return 0;
  return (unsigned)L->getSizeInBits();
}

// Whether a comparison of a pointer with null gives null a meaning: some
// branch on it sends null to a block from which the function can return.
// A test whose null side cannot return (an assertion) states that null is
// outside the contract.
bool nullReturns(ICmpInst *C) {
  bool branched = false;
  for (User *U : C->users()) {
    auto *Br = dyn_cast<BranchInst>(U);
    if (!Br || !Br->isConditional())
      return true;
    branched = true;
    BasicBlock *to = Br->getSuccessor(C->getPredicate() == CmpInst::ICMP_EQ ? 0 : 1);
    std::set<BasicBlock *> seen{to};
    std::vector<BasicBlock *> work{to};
    while (!work.empty()) {
      BasicBlock *B = work.back();
      work.pop_back();
      if (isa<ReturnInst>(B->getTerminator()) || isa<ResumeInst>(B->getTerminator()))
        return true;
      for (BasicBlock *S : successors(B))
        if (seen.insert(S).second)
          work.push_back(S);
    }
  }
  return !branched;
}

} // namespace

// The source-level name of an IR struct type: struct.tiff -> tiff,
// struct.tiff.123 -> tiff, class.ns::C -> ns::C.
std::string Client::irName(const std::string &t) {
  std::string key = t;
  for (const char *pre : {"struct.", "class.", "union."})
    if (key.rfind(pre, 0) == 0)
      key = key.substr(strlen(pre));
  auto dot = key.find_last_of('.');
  if (dot != std::string::npos && dot + 1 < key.size() &&
      key.find_first_not_of("0123456789", dot + 1) == std::string::npos)
    key = key.substr(0, dot);
  return key;
}

// The Itanium typeinfo name of a record whose scopes are named namespaces
// and records, or "" for any other scope (templates, anonymous, local).
static std::string typeinfoName(const DICompositeType *C) {
  std::vector<std::string> parts;
  for (const DIScope *S = C; S && !isa<DICompileUnit>(S) && !isa<DIFile>(S); S = S->getScope()) {
    StringRef n = S->getName();
    if (n.empty() || n.contains('<') || (!isa<DINamespace>(S) && !isa<DICompositeType>(S)))
      return "";
    parts.push_back(n.str());
  }
  std::reverse(parts.begin(), parts.end());
  std::string body;
  size_t from = 0;
  bool inStd = parts.size() > 1 && parts[0] == "std";
  if (inStd)
    from = 1;
  for (size_t i = from; i < parts.size(); ++i)
    body += std::to_string(parts[i].size()) + parts[i];
  if (parts.size() - from == 1)
    return "_ZTS" + std::string(inStd ? "St" : "") + body;
  return "_ZTSN" + std::string(inStd ? "St" : "") + body + "E";
}

// A record's identity is its ODR identifier, the typeinfo name. Clang omits
// it from the definition of a class whose vtable has external linkage,
// while declarations of the same class carry it; the definition is that
// class when its typeinfo name is an identifier the modules carry.
std::string Client::typeKey(const DIType *T) const {
  auto *C = dyn_cast_or_null<DICompositeType>(T);
  if (!C)
    return "";
  if (!C->getIdentifier().empty())
    return C->getIdentifier().str();
  if (C->getVTableHolder())
    if (std::string id = typeinfoName(C); !id.empty() && identifiers.count(id))
      return id;
  return C->getName().str();
}

// A composite is public when an installed header defines it. A forward
// declaration names the type but does not open its fields to the client.
bool Client::isPublic(const std::string &key) const {
  auto it = defined.find(key);
  return it != defined.end() && it->second;
}

// The definition of a composite type, through a forward declaration.
const DICompositeType *Client::definition(const DIType *T) const {
  auto *C = dyn_cast_or_null<DICompositeType>(strip(T));
  if (C && C->isForwardDecl()) {
    auto it = composite.find(typeKey(C));
    return it == composite.end() ? nullptr : it->second;
  }
  return C;
}

std::string Client::owned(const DIType *A) const {
  auto resolve = [&](const DIType *T) { return definition(T); };
  const DICompositeType *C = resolve(A);
  if (!C || C->getTemplateParams().empty())
    return "";
  auto *TP = dyn_cast<DITemplateTypeParameter>(C->getTemplateParams()[0]);
  const DICompositeType *T = TP ? resolve(TP->getType()) : nullptr;
  if (!T || T->getTag() == dwarf::DW_TAG_enumeration_type)
    return "";
  std::string key = typeKey(T);
  // A T* at offset 0, through the members and bases that start there.
  std::vector<const DICompositeType *> work{C};
  std::set<const DICompositeType *> seen{C};
  while (!work.empty()) {
    const DICompositeType *D = work.back();
    work.pop_back();
    for (const DINode *N : D->getElements()) {
      auto *M = dyn_cast<DIDerivedType>(N);
      if (!M || M->isStaticMember() || M->getOffsetInBits() != 0 ||
          (M->getTag() != dwarf::DW_TAG_member && M->getTag() != dwarf::DW_TAG_inheritance))
        continue;
      const DIType *MT = strip(M->getBaseType());
      if (isPointer(MT)) {
        auto *P = resolve(cast<DIDerivedType>(MT)->getBaseType());
        if (P && typeKey(P) == key)
          return key;
        continue;
      }
      if (auto *E = resolve(MT))
        if (seen.insert(E).second)
          work.push_back(E);
    }
  }
  return "";
}

std::string Client::constructs(Function *F) const {
  DISubprogram *SP = F->getSubprogram();
  if (!SP)
    return "";
  DISubprogram *Decl = SP->getDeclaration() ? SP->getDeclaration() : SP;
  const DICompositeType *C = dyn_cast_or_null<DICompositeType>(Decl->getScope());
  if (!C || C->getName().empty() || SP->getName() != C->getName())
    return "";
  if (C->isForwardDecl())
    if (auto it = composite.find(typeKey(C)); it != composite.end())
      C = it->second;
  std::string key = typeKey(C);
  // An abstract class has no objects of its own: its constructor runs only
  // inside a derived one's.
  for (const DINode *N : C->getElements())
    if (auto *M = dyn_cast<DISubprogram>(N); M && M->getVirtuality() == dwarf::DW_VIRTUALITY_pure_virtual)
      return "";
  // A copy or move constructor takes the class it makes.
  auto types = SP->getType()->getTypeArray();
  for (unsigned i = 2; i < types.size(); ++i) {
    const DIType *T = strip(types[i]);
    if (isPointer(T))
      if (auto *P = dyn_cast_or_null<DICompositeType>(strip(cast<DIDerivedType>(T)->getBaseType())))
        if (typeKey(P) == key)
          return "";
  }
  return key;
}

Client::Kind Client::classify(const DIType *T, std::string &key) const {
  key.clear();
  T = strip(T);
  if (!T)
    return Kind::Bytes;
  if (isa<DIBasicType>(T))
    return Kind::Scalar;
  if (auto *C = dyn_cast<DICompositeType>(T)) {
    if (C->getTag() == dwarf::DW_TAG_enumeration_type)
      return Kind::Scalar;
    if (C->isForwardDecl())
      if (auto it = composite.find(typeKey(C)); it != composite.end())
        C = it->second;
    key = typeKey(C);
    return Kind::Aggregate;
  }
  if (!isPointer(T))
    return Kind::Scalar;
  const DIType *P = strip(cast<DIDerivedType>(T)->getBaseType());
  if (!P)
    return Kind::Bytes;
  if (isa<DISubroutineType>(P))
    return Kind::Callback;
  if (auto *B = dyn_cast<DIBasicType>(P)) {
    auto enc = B->getEncoding();
    return enc == dwarf::DW_ATE_signed_char && B->getName() == "char" ? Kind::Text : Kind::Bytes;
  }
  if (auto *C = dyn_cast<DICompositeType>(P)) {
    if (C->getTag() == dwarf::DW_TAG_enumeration_type)
      return Kind::Bytes;
    key = typeKey(C);
    return isPublic(key) ? Kind::Object : Kind::Handle;
  }
  if (isPointer(P)) {
    const DIType *Q = strip(cast<DIDerivedType>(P)->getBaseType());
    if (auto *C = dyn_cast_or_null<DICompositeType>(Q)) {
      key = typeKey(C);
      return isPublic(key) ? Kind::Bytes : Kind::Out;
    }
  }
  return Kind::Bytes;
}

std::vector<Client::Param> Client::signature(Function *F) const {
  auto cached = sigs.find(F);
  if (cached != sigs.end())
    return cached->second;
  std::vector<Param> &out = sigs[F];
  DISubprogram *SP = F->getSubprogram();
  auto *ST = SP ? SP->getType() : nullptr;
  if (!ST)
    return out;
  auto types = ST->getTypeArray();
  // types[0] is the result; a member function's 'this' is the first formal
  // and is listed like any other parameter.
  for (unsigned i = 1; i < types.size(); ++i) {
    // A null entry is the "..." of a variadic function (DW_TAG_unspecified_
    // parameters): not a typed formal, so it adds no source parameter.
    if (!types[i])
      continue;
    Param p;
    p.kind = classify(types[i], p.type);
    const DIType *T = strip(types[i]);
    if (isPointer(T))
      if (const DIType *E = strip(cast<DIDerivedType>(T)->getBaseType())) {
        p.elem = std::max<uint64_t>(1, E->getSizeInBits() / 8);
        p.va = isa<DICompositeType>(E) && E->getName() == "__va_list_tag";
      }
    if (T)
      p.size = T->getSizeInBits() / 8;
    // The record's calling convention (DW_CC_pass_by_*) when the compiler
    // records it; a C structure has none, and is in memory past 16 bytes.
    if (auto *C = definition(T)) {
      p.size = C->getSizeInBits() / 8;
      bool byRef = C->getFlags() & DINode::FlagTypePassByReference;
      bool byVal = C->getFlags() & DINode::FlagTypePassByValue;
      p.indirect = p.kind == Kind::Aggregate && (byRef || p.size > 16 || (!byVal && (C->getFlags() & DINode::FlagNonTrivial)));
    }
    p.di = types[i];
    out.push_back(p);
  }
  if (std::string k = constructs(F); !k.empty() && !out.empty()) {
    out[0].kind = Kind::Storage;
    out[0].type = k;
    return out;
  }
  // A pointer the function treats as a larger record than its declared
  // pointee (a downcast, or a void* the function knows the type of)
  // requires an object of that record.
  auto at = lower(F, out);
  const Formals &fs = formalsOf(F);
  for (unsigned j = 0; j < at.size(); ++j) {
    if (at[j] < 0 || !fs.as[j] || out[at[j]].kind == Kind::Callback || out[at[j]].kind == Kind::Out)
      continue;
    Param &p = out[at[j]];
    const DIType *T = strip(p.di);
    if (!isPointer(T))
      continue;
    const DIType *R = strip(cast<DIDerivedType>(strip(fs.as[j]))->getBaseType());
    uint64_t declared = 0;
    if (const DIType *E = strip(cast<DIDerivedType>(T)->getBaseType()))
      declared = E->getSizeInBits();
    if (!R || R->getSizeInBits() <= declared)
      continue;
    p.kind = classify(fs.as[j], p.type);
    p.elem = std::max<uint64_t>(1, R->getSizeInBits() / 8);
    p.di = fs.as[j];
  }
  return out;
}

std::vector<int> Client::irParams(Function *F) const { return lower(F, signature(F)); }

// The source parameter each IR parameter of F carries, -1 for none. An
// aggregate passed by value that the ABI does not pass in memory occupies
// consecutive IR parameters until their sizes cover it; the rest take one.
// All -1 when the declared parameters do not cover the IR ones.
std::vector<int> Client::lower(Function *F, const std::vector<Param> &sig) {
  unsigned n = F->arg_size();
  unsigned i = F->hasParamAttribute(0, Attribute::StructRet) ? 1 : 0;
  std::vector<int> at(n, -1);
  const DataLayout &dl = F->getParent()->getDataLayout();
  for (unsigned k = 0; k < sig.size(); ++k) {
    if (i >= n)
      return std::vector<int>(n, -1);
    at[i] = (int)k;
    if (sig[k].kind == Kind::Aggregate && !sig[k].indirect && !F->hasParamAttribute(i, Attribute::ByVal) && sig[k].size) {
      uint64_t got = dl.getTypeAllocSize(F->getArg(i++)->getType());
      while (got < sig[k].size && i < n)
        got += dl.getTypeAllocSize(F->getArg(i++)->getType());
    } else {
      ++i;
    }
  }
  return i == n ? at : std::vector<int>(n, -1);
}

Client::Param Client::result(Function *F) const {
  Param p;
  p.kind = Kind::Scalar;
  DISubprogram *SP = F->getSubprogram();
  auto *ST = SP ? SP->getType() : nullptr;
  if (!ST || ST->getTypeArray().size() == 0 || !ST->getTypeArray()[0])
    return p;
  p.kind = classify(ST->getTypeArray()[0], p.type);
  return p;
}

std::set<std::string> Client::downstreamInterface(const fs::path &dir) {
  std::ifstream js(dir / "surfaces.json");
  std::string text((std::istreambuf_iterator<char>(js)), std::istreambuf_iterator<char>());
  std::string so = caseFile(dir, jsonString(text, "so", text.find("\"ds_core\""))).string();
  return so.empty() ? std::set<std::string>{} : dynamicSymbols(so);
}

std::set<std::string> Client::publicInterface(Module &down, Module &up, const fs::path &dir) {
  Client c(down, up, dir);
  std::set<std::string> names;
  for (Function *F : c.ifaceD)
    names.insert(F->getName().str());
  return names;
}

// P1 starts: interface functions the client can actually invoke with
// producible held arguments. A symbol that is only null-callable for an
// unproducible handle is not a start — sequences begin at a real entry so
// φ is projected onto that entry's arguments (P1 ⇒ P2 without elevation).
std::set<std::string> Client::entryInterface(Module &down, Module &up, const fs::path &dir) {
  Client c(down, up, dir);
  std::set<std::string> names;
  for (Function *F : c.ifaceD)
    if (c.entryCallable(F))
      names.insert(F->getName().str());
  return names;
}

std::set<std::string> Client::installedExports(const fs::path &dir) {
  std::ifstream js(dir / "surfaces.json");
  std::string text((std::istreambuf_iterator<char>(js)), std::istreambuf_iterator<char>());
  std::set<std::string> out, seen;
  for (size_t k = text.find("\"so\""); k != std::string::npos; k = text.find("\"so\"", k + 1))
    if (std::string so = caseFile(dir, jsonString(text, "so", k)).string(); !so.empty() && seen.insert(so).second) {
      std::string cmd = "nm --defined-only '" + so + "' 2>/dev/null";
      FILE *p = popen(cmd.c_str(), "r");
      if (!p)
        continue;
      char line[4096];
      while (fgets(line, sizeof line, p)) {
        std::istringstream in(line);
        std::string addr, kind, name;
        in >> addr >> kind >> name;
        if (!name.empty() && std::string("TtWDdBbRrVu").find(kind) != std::string::npos)
          out.insert(name.substr(0, name.find('@')));
      }
      pclose(p);
    }
  return out;
}

Client::Client(Module &down, Module &up, const fs::path &dir) : down(down), up(up), dl(down.getDataLayout()) {
  std::ifstream js(dir / "surfaces.json");
  std::string text((std::istreambuf_iterator<char>(js)), std::istreambuf_iterator<char>());
  std::string dso = caseFile(dir, jsonString(text, "so", text.find("\"ds_core\""))).string();
  std::string uso = caseFile(dir, jsonString(text, "so", text.find("\"us\""))).string();
  for (const std::string &so : {dso, uso}) {
    if (so.empty())
      continue;
    auto names = dynamicSymbols(so);
    (so == dso ? dsyms : usyms).insert(names.begin(), names.end());
    auto inc = installedHeaders(fs::path(so).parent_path().parent_path() / "include");
    headers.insert(inc.begin(), inc.end());
    auto ids = headerIdentifiers(fs::path(so).parent_path().parent_path() / "include");
    declared.insert(ids.begin(), ids.end());
  }
  std::set<std::string> seen;
  for (size_t k = text.find("\"so\""); k != std::string::npos; k = text.find("\"so\"", k + 1)) {
    std::string so = caseFile(dir, jsonString(text, "so", k)).string();
    if (so.empty() || !seen.insert(so).second)
      continue;
    fs::path rel = fs::path(so).lexically_relative(fs::absolute(dir).lexically_normal());
    Library L;
    L.key = rel.empty() || *rel.begin() == ".." ? so : "/" + rel.generic_string();
    std::error_code ec;
    L.link = fs::is_symlink(so, ec);
    L.exports = dynamicSymbols(so, true);
    installed.push_back(std::move(L));
  }
  for (Module *M : {&down, &up})
    for (Function &F : *M) {
      if (F.isDeclaration())
        continue;
      bodies.emplace(F.getName().str(), &F);
    }
  std::vector<DebugInfoFinder> finders(2);
  finders[0].processModule(down);
  finders[1].processModule(up);
  for (const DebugInfoFinder &fin : finders)
    for (DIType *T : fin.types())
      if (auto *C = dyn_cast<DICompositeType>(T); C && !C->getIdentifier().empty())
        identifiers.insert(C->getIdentifier().str());
  // Which composite types an installed header defines.
  for (const DebugInfoFinder &fin : finders) {
    for (DIType *T : fin.types()) {
      auto *C = dyn_cast<DICompositeType>(T);
      if (!C)
        continue;
      std::string key = typeKey(C);
      if (key.empty())
        continue;
      bool full = !(C->getFlags() & DINode::FlagFwdDecl);
      bool pub = full && C->getFile() && headers.count(baseName(C->getFile()->getFilename().str()));
      auto &d = defined[key];
      d = d || pub;
      if (full && !composite.count(key))
        composite[key] = C;
    }
  }
  for (const auto &kv : bodies) {
    bool inD = dsyms.count(kv.first), inU = usyms.count(kv.first);
    DISubprogram *SP = kv.second->getSubprogram();
    // A function an installed header defines inline is compiled into the
    // client that includes it: it is interface without being exported.
    bool inline_ = kv.second->hasLinkOnceODRLinkage() && SP && SP->getFile() &&
                   headers.count(baseName(SP->getFile()->getFilename().str()));
    if (inline_ && !inD && !inU) {
      inD = kv.second->getParent() == &down;
      inU = !inD;
    }
    if (!inD && !inU)
      continue;
    if (!inline_ && kv.second->getLinkage() != GlobalValue::ExternalLinkage &&
        kv.second->getLinkage() != GlobalValue::WeakAnyLinkage && kv.second->getLinkage() != GlobalValue::WeakODRLinkage)
      continue;
    std::string name = SP && !SP->getName().empty() ? SP->getName().str() : kv.first;
    if (!declared.count(name))
      continue;
    // A member is callable by the clients that see its class.
    DISubprogram *Decl = SP && SP->getDeclaration() ? SP->getDeclaration() : SP;
    if (auto *C = Decl ? dyn_cast_or_null<DICompositeType>(Decl->getScope()) : nullptr)
      if (!isPublic(typeKey(C)))
        continue;
    (inD ? ifaceD : ifaceU).insert(kv.second);
  }
  buildCalls();
  buildStores();
  buildModRef();
  buildReleases();
  buildWrites();
  buildProducers();
  buildCallbackTypes();
  buildNullFields();
  buildFieldLengths();
}

// The type a library calls a function-pointer formal with. Formal i of F
// flows to the fields F stores it to and to the formals of the functions F
// passes it to; the type is that of a call through one of those fields, or
// of a direct call of the formal.
void Client::buildCallbackTypes() {
  std::map<std::pair<std::string, int64_t>, FunctionType *> callAt;
  for (const auto &kv : bodies)
    for (Instruction &I : instructions(*kv.second)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || CB->getCalledFunction())
        continue;
      if (auto *L = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts()))
        for (const auto &f : accessFields(*L, L->getPointerOperand()))
          callAt.emplace(f, CB->getFunctionType());
    }
  std::function<FunctionType *(Function *, unsigned, std::set<std::pair<Function *, unsigned>> &)> flow =
      [&](Function *F, unsigned i, std::set<std::pair<Function *, unsigned>> &seen) -> FunctionType * {
    if (!seen.insert({F, i}).second)
      return nullptr;
    for (Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        if (formalOf(S->getValueOperand()) != (int)i)
          continue;
        for (const auto &f : accessFields(*S, S->getPointerOperand())) {
          auto it = callAt.find(f);
          if (it != callAt.end())
            return it->second;
        }
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      if (formalOf(CB->getCalledOperand()) == (int)i)
        return CB->getFunctionType();
      auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
      Function *G = C ? body(C->getName().str()) : nullptr;
      if (!G)
        continue;
      for (unsigned j = 0; j < CB->arg_size() && j < G->arg_size(); ++j)
        if (formalOf(CB->getArgOperand(j)) == (int)i)
          if (FunctionType *T = flow(G, j, seen))
            return T;
    }
    return nullptr;
  };
  for (Function *F : interface()) {
    auto sig = signature(F);
    auto at = irParams(F);
    auto types = F->getSubprogram()->getType()->getTypeArray();
    for (unsigned j = 0; j < at.size(); ++j) {
      int k = at[j];
      if (k < 0 || sig[k].kind != Kind::Callback)
        continue;
      if (FunctionType *T = fnTypeOf(types[k + 1])) {
        fnTypes[{F, j}] = T;
        fnDecl[{F, j}] = types[k + 1];
        continue;
      }
      std::set<std::pair<Function *, unsigned>> seen;
      if (FunctionType *T = flow(F, j, seen))
        fnTypes[{F, j}] = T;
    }
  }
}

FunctionType *Client::fnTypeOf(const DIType *T) const {
  LLVMContext &ctx = down.getContext();
  // The IR type of a declared source type, for scalars and pointers. A
  // by-value aggregate has no single IR type: its lowering is the ABI's.
  auto irOf = [&](const DIType *T) -> Type * {
    T = strip(T);
    if (!T)
      return Type::getVoidTy(ctx);
    if (isPointer(T))
      return PointerType::get(ctx, 0);
    uint64_t bits = T->getSizeInBits();
    if (auto *B = dyn_cast<DIBasicType>(T)) {
      if (B->getEncoding() == dwarf::DW_ATE_float)
        return bits == 32 ? Type::getFloatTy(ctx) : bits == 64 ? Type::getDoubleTy(ctx) : nullptr;
      return bits ? Type::getIntNTy(ctx, (unsigned)bits) : nullptr;
    }
    if (auto *C = dyn_cast<DICompositeType>(T))
      if (C->getTag() == dwarf::DW_TAG_enumeration_type && bits)
        return Type::getIntNTy(ctx, (unsigned)bits);
    return nullptr;
  };
  T = strip(T);
  if (!isPointer(T))
    return nullptr;
  auto *S = dyn_cast_or_null<DISubroutineType>(strip(cast<DIDerivedType>(T)->getBaseType()));
  if (!S)
    return nullptr;
  auto ts = S->getTypeArray();
  if (ts.size() == 0)
    return nullptr;
  Type *R = irOf(ts[0]);
  std::vector<Type *> ps;
  bool va = false;
  for (unsigned i = 1; i < ts.size(); ++i) {
    if (!ts[i]) {
      va = true;
      break;
    }
    Type *P = irOf(ts[i]);
    if (!P || P->isVoidTy())
      return nullptr;
    ps.push_back(P);
  }
  return R ? FunctionType::get(R, ps, va) : nullptr;
}

// A1 for fields (§2.2): NullOK(S, off) = Cmp_0 and not Call_0. Cmp_0: a load
// of the field whose value, directly or through the -O0 slot it is stored
// to, is compared with null. Call_0: a function calls such a value and
// compares no value of that field with null.
void Client::buildNullFields() {
  auto isNull = [](Value *V) { return isa<ConstantPointerNull>(V); };
  auto fieldsLoaded = [&](Value *V) {
    std::set<std::pair<std::string, int64_t>> out;
    auto *L = dyn_cast<LoadInst>(V->stripPointerCasts());
    if (!L)
      return out;
    std::vector<LoadInst *> loads{L};
    if (auto *Al = dyn_cast<AllocaInst>(fieldAddress(L->getPointerOperand())))
      for (User *U : Al->users())
        if (auto *S = dyn_cast<StoreInst>(U))
          if (S->getPointerOperand()->stripPointerCasts() == Al)
            if (auto *F = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts()))
              loads.push_back(F);
    for (LoadInst *X : loads)
      for (const auto &f : accessFields(*X, X->getPointerOperand()))
        out.insert(f);
    return out;
  };
  for (const auto &kv : bodies) {
    std::set<std::pair<std::string, int64_t>> tested, called;
    for (Instruction &I : instructions(*kv.second)) {
      if (auto *CB = dyn_cast<CallBase>(&I)) {
        if (!isa<Function>(CB->getCalledOperand()->stripPointerCasts()) && !CB->isInlineAsm())
          for (const auto &f : fieldsLoaded(CB->getCalledOperand()))
            called.insert(f);
        continue;
      }
      auto *C = dyn_cast<ICmpInst>(&I);
      if (!C || !C->isEquality() || !(isNull(C->getOperand(0)) || isNull(C->getOperand(1))))
        continue;
      auto fs = fieldsLoaded(isNull(C->getOperand(0)) ? C->getOperand(1) : C->getOperand(0));
      tested.insert(fs.begin(), fs.end());
      if (nullReturns(C))
        nullFields.insert(fs.begin(), fs.end());
    }
    for (const auto &f : called)
      if (!tested.count(f))
        unguardedCalls.insert(f);
  }
  for (const auto &f : unguardedCalls)
    nullFields.erase(f);
}

// A3 for fields: integer field b of S bounds pointer field a of S when the
// library advances a pointer loaded from a by a value derived from one
// loaded from b, or passes them to a memory function as buffer and length.
void Client::buildFieldLengths() {
  auto loaded = [&](Value *V) {
    std::set<std::pair<std::string, int64_t>> out;
    std::set<Value *> seen;
    std::vector<Value *> work{V};
    while (!work.empty() && seen.size() < 64) {
      Value *U = work.back()->stripPointerCasts();
      work.pop_back();
      if (!seen.insert(U).second)
        continue;
      if (auto *L = dyn_cast<LoadInst>(U)) {
        if (auto *Al = dyn_cast<AllocaInst>(fieldAddress(L->getPointerOperand()))) {
          for (User *W : Al->users())
            if (auto *S = dyn_cast<StoreInst>(W); S && S->getPointerOperand()->stripPointerCasts() == Al)
              work.push_back(S->getValueOperand());
        } else
          for (const auto &f : accessFields(*L, L->getPointerOperand()))
            out.insert(f);
      } else if (auto *C = dyn_cast<CastInst>(U)) {
        work.push_back(C->getOperand(0));
      } else if (auto *B = dyn_cast<BinaryOperator>(U)) {
        work.push_back(B->getOperand(0));
        work.push_back(B->getOperand(1));
      }
    }
    return out;
  };
  for (const auto &kv : bodies)
    for (Instruction &I : instructions(*kv.second)) {
      std::vector<std::pair<Value *, Value *>> uses;
      if (auto *G = dyn_cast<GetElementPtrInst>(&I)) {
        if (G->getNumIndices() == 1 && !isa<Constant>(G->getOperand(1)))
          uses.push_back({G->getPointerOperand(), G->getOperand(1)});
      } else if (auto *M = dyn_cast<MemTransferInst>(&I)) {
        uses.push_back({M->getRawDest(), M->getLength()});
        uses.push_back({M->getRawSource(), M->getLength()});
      } else if (auto *M = dyn_cast<MemSetInst>(&I)) {
        uses.push_back({M->getRawDest(), M->getLength()});
      }
      for (const auto &[p, n] : uses) {
        auto fa = loaded(p), fb = loaded(n);
        for (const auto &a : fa)
          for (const auto &b : fb)
            if (a.first == b.first && a.second != b.second)
              fieldLen.emplace(a, b.second);
      }
    }
}

// Through pointer casts only. An all-zero GEP stays: it addresses the first field.
Value *Client::fieldAddress(Value *P) const {
  while (auto *O = dyn_cast<Operator>(P)) {
    if (O->getOpcode() != Instruction::BitCast && O->getOpcode() != Instruction::AddrSpaceCast)
      break;
    P = O->getOperand(0);
  }
  return P;
}

// The fields (S, off) a GEP may address, at every struct level its indices
// (and those of the GEP it indexes into) pass, innermost last; a variable
// array index names every element. A GEP of one zero index only
// reinterprets the pointer; the first field's GEP has a second index.
std::vector<std::pair<std::string, int64_t>> Client::fieldsOf(Value *P) const {
  P = fieldAddress(P);
  auto *G = dyn_cast<GEPOperator>(P);
  if (!G || (G->hasAllZeroIndices() && G->getNumIndices() < 2))
    return {};
  auto out = source::levels(G, dl);
  if (!out.empty())
    return out;
  // Optimised IR addresses a field as a byte GEP (i8*, constant offset).
  // Recover the source record and offset from π(base) and the byte displacement.
  if (!G->hasAllConstantIndices() || G->getNumIndices() != 1)
    return out;
  Type *ST = G->getSourceElementType();
  if (!ST->isIntegerTy(8) && !ST->isIntegerTy(1))
    return out;
  auto *CI = dyn_cast<ConstantInt>(G->getOperand(1));
  if (!CI)
    return out;
  int64_t off = CI->getSExtValue() * (int64_t)dl.getTypeAllocSize(ST).getFixedValue();
  const DIType *D = source::pointee(G->getPointerOperand());
  std::string n = source::name(D);
  if (n.empty())
    return out;
  if (n.rfind("struct.", 0) != 0 && n.rfind("class.", 0) != 0)
    n = "struct." + n;
  out.push_back({n, off});
  return out;
}

// Call edges (§3.10): a direct call is its callee, an indirect call goes to
// the targets the may layer resolved (Tgt, klee/Support/CallTargets.h).
void Client::buildCalls() {
  targets.index(down);
  targets.index(up);
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &out = calls[F];
    for (Instruction &I : instructions(*F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || isa<IntrinsicInst>(CB) || CB->isInlineAsm())
        continue;
      if (const Function *C = klee::calls::callee(*CB)) {
        if (Function *B = body(C->getName().str()))
          out.insert(B);
        continue;
      }
      for (Function *T : targets.of(*CB))
        if (Function *B = body(T->getName().str()))
          out.insert(B);
    }
  }
}

Function *Client::body(const std::string &name) const {
  auto it = bodies.find(name);
  return it == bodies.end() ? nullptr : it->second;
}

std::vector<Client::Field> Client::accessFields(const Instruction &I, Value *P) const {
  std::vector<Field> fs = fieldsOf(P);
  if (!fs.empty())
    return fs;
  // TBAA operand 0 is the base type node, operand 2 the offset; the base
  // node's name is the source struct (C11 6.5p7).
  const MDNode *T = I.getMetadata(LLVMContext::MD_tbaa);
  if (!T || T->getNumOperands() < 3)
    return {};
  const MDNode *B = dyn_cast<MDNode>(T->getOperand(0));
  auto *O = mdconst::dyn_extract<ConstantInt>(T->getOperand(2));
  auto *N = B && B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
  if (!N || !O)
    return {};
  std::string n = N->getString().str();
  if (n.empty() || n == "omnipotent char" || n == "any pointer" || n == "Simple C/C++ TBAA")
    return {};
  if (n.rfind("struct.", 0) != 0 && n.rfind("class.", 0) != 0)
    n = "struct." + n;
  return {{n, O->getSExtValue()}};
}

std::optional<std::tuple<std::string, int64_t, int64_t>> Client::zeroFill(const MemSetInst &MS) {
  auto *b = dyn_cast<ConstantInt>(MS.getValue());
  if (!b || !b->isZero())
    return std::nullopt;
  const DIType *D = source::pointee(MS.getRawDest());
  if (!D)
    return std::nullopt;
  std::string n = source::name(D);
  if (n.empty())
    return std::nullopt;
  if (n.rfind("struct.", 0) != 0 && n.rfind("class.", 0) != 0)
    n = "struct." + n;
  auto *L = dyn_cast<ConstantInt>(MS.getLength());
  int64_t len = L && L->getBitWidth() <= 64 ? L->getSExtValue() : INT64_MAX;
  return std::make_tuple(n, int64_t(0), len);
}

// Each constant-offset GEP a store writes through names the field at every
// struct level its indices pass: (S, offset of the address inside S).
void Client::buildStores() {
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &out = stores[F];
    auto &in = inputStores[F];
    auto &cp = copyStores[F];
    for (Instruction &I : instructions(*F)) {
      Value *P = nullptr;
      std::string v = "*";
      bool copy = false;
      std::vector<Field> fs;
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        P = S->getPointerOperand();
        v = abstractValue(S->getValueOperand());
        std::set<Field> src = copySources(S);
        copy = !src.empty();
        fs = accessFields(I, P);
        for (const Field &d : fs)
          for (const Field &s : src)
            if (d != s)
              cp[d].insert(s);
        // A local update (store of a value computed from a load of the same
        // field) is not an input write: §3.6's closed-world step applies only
        // when the non-constant is neither a copy nor the field's own prior
        // value. Increments and similar stay library state, not file content.
        if (v == "*" && !copy && !fs.empty()) {
          Value *X = S->getValueOperand();
          while (auto *C = dyn_cast<CastInst>(X))
            X = C->getOperand(0);
          if (auto *BO = dyn_cast<BinaryOperator>(X)) {
            for (unsigned i = 0; i < 2 && !copy; ++i) {
              Value *Op = BO->getOperand(i);
              while (auto *C = dyn_cast<CastInst>(Op))
                Op = C->getOperand(0);
              if (auto *L = dyn_cast<LoadInst>(Op))
                for (const Field &s : accessFields(*L, L->getPointerOperand()))
                  for (const Field &d : fs)
                    if (s == d)
                      copy = true;
            }
          }
        }
      } else if (auto *MS = dyn_cast<MemSetInst>(&I)) {
        P = MS->getRawDest();
        auto *b = dyn_cast<ConstantInt>(MS->getValue());
        v = b && b->isZero() ? "0" : "*";
        fs = accessFields(I, P);
        // A typed zero-fill with no field GEP still zeros every offset in the
        // object (GetImageInfo's memset of ImageInfo).
        if (fs.empty())
          if (auto z = zeroFill(*MS))
            ranges[F].push_back(*z);
      } else if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
        P = MI->getRawDest();
        fs = accessFields(I, P);
      }
      if (!P)
        continue;
      if (fs.empty())
        fs = fieldsOf(P);
      for (const auto &f : fs) {
        out.insert({f, v});
        if (v == "*" && !copy)
          in.insert(f);
      }
      if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
        auto *L = dyn_cast<ConstantInt>(MI->getLength());
        int64_t len = L && L->getBitWidth() <= 64 ? L->getSExtValue() : INT64_MAX;
        for (const auto &f : fs)
          ranges[F].push_back({f.first, f.second, len});
      }
    }
  }
}

void Client::buildModRef() {
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &m = mods[F], &r = refs[F];
    auto add = [&](auto &set, const Instruction &I, Value *P) {
      for (const auto &f : accessFields(I, P))
        set.insert(f);
    };
    for (Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I))
        add(m, I, S->getPointerOperand());
      else if (auto *L = dyn_cast<LoadInst>(&I))
        add(r, I, L->getPointerOperand());
      else if (auto *MI = dyn_cast<MemTransferInst>(&I)) {
        add(m, I, MI->getRawDest());
        add(r, I, MI->getRawSource());
      } else if (auto *MS = dyn_cast<MemSetInst>(&I))
        add(m, I, MS->getRawDest());
      else if (auto *CB = dyn_cast<CallBase>(&I)) {
        if (isa<IntrinsicInst>(CB))
          continue;
        for (Value *A : CB->args())
          if (A->getType()->isPointerTy()) {
            add(m, I, A);
            add(r, I, A);
          }
      }
    }
    // Control references: the fields a branch condition reads, through the
    // backward data slice of the condition. SSA operands are followed, a
    // load of a field ends the slice at that field, and a load of an -O0
    // slot continues with the values stored to it.
    auto &c = crefs[F];
    std::vector<Value *> work;
    std::set<Value *> seen;
    for (Instruction &I : instructions(*F)) {
      Value *cond = nullptr;
      if (auto *Br = dyn_cast<BranchInst>(&I))
        cond = Br->isConditional() ? Br->getCondition() : nullptr;
      else if (auto *Sw = dyn_cast<SwitchInst>(&I))
        cond = Sw->getCondition();
      if (cond && seen.insert(cond).second)
        work.push_back(cond);
    }
    while (!work.empty()) {
      Value *V = work.back();
      work.pop_back();
      auto push = [&](Value *W) {
        if (seen.insert(W).second)
          work.push_back(W);
      };
      if (auto *L = dyn_cast<LoadInst>(V)) {
        Value *P = L->getPointerOperand()->stripPointerCasts();
        if (auto *Al = dyn_cast<AllocaInst>(P)) {
          for (User *U : Al->users())
            if (auto *S = dyn_cast<StoreInst>(U))
              if (S->getPointerOperand()->stripPointerCasts() == Al)
                push(S->getValueOperand());
          continue;
        }
        add(c, *L, P);
        continue;
      }
      if (isa<CallBase>(V) || isa<Argument>(V) || isa<Constant>(V))
        continue;
      if (auto *I = dyn_cast<Instruction>(V))
        for (Value *O : I->operands())
          push(O);
    }
  }
}

const std::set<std::pair<std::string, int64_t>> &Client::controlRefs(Function *F) const {
  auto it = crefOf.find(F);
  if (it != crefOf.end())
    return it->second;
  auto &out = crefOf[F];
  for (Function *G : innerClosure(F)) {
    auto c = crefs.find(G);
    if (c != crefs.end())
      out.insert(c->second.begin(), c->second.end());
  }
  return out;
}

const std::set<std::pair<std::string, int64_t>> &Client::transitive(Function *F, bool mod) const {
  auto key = std::make_pair(F, mod);
  auto it = modRefOf.find(key);
  if (it != modRefOf.end())
    return it->second;
  std::set<std::pair<std::string, int64_t>> out;
  const auto &src = mod ? mods : refs;
  for (Function *G : innerClosure(F)) {
    auto s = src.find(G);
    if (s == src.end())
      continue;
    for (const auto &f : s->second)
      // Fields of the language runtime's containers say nothing about
      // which library state a call establishes.
      if (f.first.find("std::") == std::string::npos && f.first.find("__gnu_cxx") == std::string::npos)
        out.insert(f);
  }
  return modRefOf[key] = std::move(out);
}

// The one position all of vs agree on, those only being evaluated aside
// (greatest fixpoint, as rootOf).
Client::Position Client::agreed(const std::vector<Position> &vs) {
  Position at{-2};
  for (const Position &k : vs) {
    if (k.root == -2)
      continue;
    if (k.root < 0 ||
        (at.root != -2 && (k.root != at.root || k.path != at.path || k.off != at.off || k.exact != at.exact)))
      return {};
    at = k;
  }
  return at;
}

// Where pointer V of a function points, through -O0 slots, address
// arithmetic and the results of calls; off is not exact past a variable
// index. cut is set where a call already being evaluated was met, so that
// what depends on it is not kept as final.
Client::Position Client::positionOf(Value *V, std::set<AllocaInst *> &open, bool &cut) const {
  V = V->stripPointerCasts();
  if (auto *A = dyn_cast<Argument>(V))
    return {(int)A->getArgNo(), {}, 0, true};
  if (auto *G = dyn_cast<GEPOperator>(V)) {
    Position p = positionOf(G->getPointerOperand(), open, cut);
    const DataLayout &DL = dl;
    APInt o(DL.getIndexTypeSizeInBits(G->getType()), 0);
    if (p.root >= 0 && p.exact && G->accumulateConstantOffset(DL, o))
      p.off += o.getSExtValue();
    else
      p.exact = false;
    return p;
  }
  if (!V->getType()->isPointerTy())
    return {};
  if (auto *CB = dyn_cast<CallBase>(V)) {
    // The callee returns a place of one of its formals: the same place
    // seen from the argument.
    auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
    Function *B = C ? (C->isDeclaration() ? body(C->getName().str()) : C) : nullptr;
    if (!B || B->isDeclaration())
      return {};
    Position r = returnOf(B, cut);
    if (r.root < 0 || (unsigned)r.root >= CB->arg_size())
      return {r.root == -2 ? -2 : -1};
    Position p = positionOf(CB->getArgOperand(r.root), open, cut);
    if (p.root < 0)
      return p;
    if (r.path.empty()) {
      p.off += r.off;
      p.exact = p.exact && r.exact;
      return p;
    }
    if (!p.exact)
      return {};
    p.path.push_back(p.off + r.path[0]);
    p.path.insert(p.path.end(), r.path.begin() + 1, r.path.end());
    p.off = r.off;
    p.exact = r.exact;
    return p;
  }
  auto *L = dyn_cast<LoadInst>(V);
  if (!L)
    return {};
  Value *A = L->getPointerOperand()->stripPointerCasts();
  auto *Al = dyn_cast<AllocaInst>(A);
  if (Al && Al->getAllocatedType()->isPointerTy()) {
    // A spill slot holds the position all its stores agree on.
    if (!open.insert(Al).second)
      return {-2};
    std::vector<Position> vs;
    for (User *U : Al->users()) {
      auto *S = dyn_cast<StoreInst>(U);
      if (S && S->getPointerOperand()->stripPointerCasts() == Al)
        vs.push_back(positionOf(S->getValueOperand(), open, cut));
    }
    open.erase(Al);
    return agreed(vs);
  }
  Position p = positionOf(A, open, cut);
  if (p.root < 0 || !p.exact)
    return {};
  p.path.push_back(p.off);
  p.off = 0;
  return p;
}

// Where F's pointer result points, seen from its formals: the position all
// its returns agree on. Kept only when no call being evaluated was met, so
// the result does not depend on the order of the queries.
Client::Position Client::returnOf(Function *F, bool &cut) const {
  auto it = returnOfFn.find(F);
  if (it != returnOfFn.end())
    return it->second;
  if (!returnOpen.insert(F).second) {
    cut = true;
    return {-2};
  }
  bool inner = false;
  std::vector<Position> vs;
  for (BasicBlock &BB : *F)
    if (auto *R = dyn_cast<ReturnInst>(BB.getTerminator()))
      if (Value *V = R->getReturnValue()) {
        std::set<AllocaInst *> slots;
        vs.push_back(positionOf(V, slots, inner));
      }
  returnOpen.erase(F);
  Position r = agreed(vs);
  if (r.root == -2)
    r = {};
  if (inner)
    cut = true;
  else
    returnOfFn[F] = r;
  return r;
}

// The string constants the text at path from formal i of F is compared
// against with the C library's comparisons: where the text, or a pointer
// into it, is an argument of a comparison, the constants among its other
// arguments; where it, or an object on the way to it, is passed on to a
// function the library defines, those of the text's place in the callee;
// where it names a file the library opens, or it or an object holding it is
// stored to memory other than a spill slot, the input file's name: what the
// library compares it with later is unknown. Nearest first (breadth-first
// from F), at most 32. The texts that meet none of these form one class,
// which a fresh text represents, so the classes only refine the texts. They
// are what the whole call can tell apart: the search does not stop at other
// interface functions the way the attribution of effects does.
//
// A pointer at offset o of an object reaches the field at x of it only for
// 0 <= o <= x, at x - o: the offsets only fall, so the places are finite.
const std::vector<std::string> &Client::compared(Function *F, unsigned i, const std::vector<int64_t> &path) const {
  TextPlace key{F, i, path};
  auto it = comparedOf.find(key);
  if (it != comparedOf.end())
    return it->second;
  static const std::set<std::string> cmp{"strcmp", "strncmp", "strcasecmp", "strncasecmp", "memcmp",
                                         "bcmp",   "strstr",  "strcasestr", "strcoll"};
  static const std::set<std::string> open{"fopen", "fopen64", "freopen", "open", "open64", "openat", "creat",
                                          "stat",  "stat64",  "lstat",   "access"};
  std::vector<TextPlace> order{key};
  std::set<TextPlace> queued{key};
  std::vector<std::string> out;
  std::set<std::string> seen;
  auto file = [&] {
    if (seen.insert("f").second)
      out.push_back("f");
  };
  for (size_t q = 0; q < order.size() && out.size() < 32; ++q) {
    auto [G, j, P] = order[q];
    // How V stands to the text: 0 it is the text or points into it, 1 it
    // points into an object on the way, the text at rest from it; -1
    // neither.
    auto relate = [&](Value *V, std::vector<int64_t> &rest) -> int {
      if (!V->getType()->isPointerTy())
        return -1;
      std::set<AllocaInst *> slots;
      bool cut = false;
      Position p = positionOf(V, slots, cut);
      if (p.root != (int)j || p.path.size() > P.size() || !std::equal(p.path.begin(), p.path.end(), P.begin()))
        return -1;
      if (p.path.size() == P.size())
        return 0;
      int64_t x = P[p.path.size()];
      if (!p.exact || p.off < 0 || p.off > x)
        return -1;
      rest.assign(P.begin() + p.path.size(), P.end());
      rest[0] = x - p.off;
      return 1;
    };
    // First byte of the text as a discriminator (e.g. _TIFFgetMode's
    // switch(mode[0]) on 'r'/'w'/'a'): those constants are Cmp texts too.
    // strcmp-style collection below misses them because they never reach a
    // comparison call. Only small switches over the text itself: a large
    // switch on file-magic bytes shares no strcmp site either, but is not a
    // classification of this formal (auxiliary lemma T: same Cmp result).
    auto addChar = [&](int64_t v) {
      if (v <= 0 || v > 127 || out.size() >= 32)
        return;
      std::string s(1, (char)v);
      if (seen.insert(s).second)
        out.push_back(std::move(s));
    };
    auto loadOfText = [&](Value *V) -> bool {
      V = V->stripPointerCasts();
      while (auto *C = dyn_cast<CastInst>(V))
        V = C->getOperand(0)->stripPointerCasts();
      auto *L = dyn_cast<LoadInst>(V);
      if (!L)
        return false;
      Value *P = L->getPointerOperand()->stripPointerCasts();
      if (auto *GEP = dyn_cast<GEPOperator>(P)) {
        for (auto It = GEP->idx_begin(), E = GEP->idx_end(); It != E; ++It) {
          auto *CI = dyn_cast<ConstantInt>(It->get());
          if (!CI || !CI->isZero())
            return false;
        }
        P = GEP->getPointerOperand()->stripPointerCasts();
      }
      std::vector<int64_t> rest;
      return relate(P, rest) == 0;
    };
    for (Instruction &I : instructions(*G)) {
      std::vector<int64_t> rest;
      if (auto *Sw = dyn_cast<SwitchInst>(&I)) {
        if (loadOfText(Sw->getCondition())) {
          unsigned n = 0;
          for (auto &Case : Sw->cases()) {
            int64_t v = Case.getCaseValue()->getSExtValue();
            if (v <= 0 || v > 127 || ++n > 8) {
              n = 100;
              break;
            }
          }
          if (n <= 8)
            for (auto &Case : Sw->cases())
              addChar(Case.getCaseValue()->getSExtValue());
        }
        continue;
      }
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        auto *Al = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts());
        bool spill = Al && Al->getAllocatedType()->isPointerTy();
        if (!spill && relate(S->getValueOperand(), rest) >= 0)
          file();
        continue;
      }
      if (auto *M = dyn_cast<MemTransferInst>(&I)) {
        if (relate(M->getRawSource(), rest) == 1)
          file();
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      auto *C = CB ? dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts()) : nullptr;
      if (!C)
        continue;
      bool isCmp = cmp.count(bareName(C->getName().str())) > 0;
      bool isOpen = open.count(bareName(C->getName().str())) > 0;
      Function *B = C->isDeclaration() ? body(C->getName().str()) : C;
      bool follow = !isCmp && B && !B->isDeclaration();
      for (unsigned a = 0; a < CB->arg_size(); ++a) {
        int r = relate(CB->getArgOperand(a), rest);
        if (r < 0)
          continue;
        if (r == 1) {
          if (follow && a < B->arg_size() && queued.insert({B, a, rest}).second)
            order.push_back({B, a, rest});
          continue;
        }
        if (isOpen)
          file();
        if (!isCmp) {
          if (follow && a < B->arg_size() && queued.insert({B, a, {}}).second)
            order.push_back({B, a, {}});
          continue;
        }
        for (unsigned b = 0; b < CB->arg_size(); ++b) {
          auto *GV = dyn_cast<GlobalVariable>(getUnderlyingObject(CB->getArgOperand(b)));
          auto *D = GV && GV->hasInitializer() ? dyn_cast<ConstantDataSequential>(GV->getInitializer()) : nullptr;
          if (b == a || !D || !D->isCString())
            continue;
          std::string s = D->getAsCString().str();
          if (!s.empty() && out.size() < 32 && seen.insert(s).second)
            out.push_back(s);
        }
      }
    }
  }
  return comparedOf[key] = out;
}

// §2.4 Key(t): the names a function t is registered under, where an indirect
// call can reach it. A store of t into a field of an object some call made
// names t by the text constants passed to that call; a constant record that
// holds t names it by the text constants beside it. A name is a token
// (letters and digits, at most 16), since the client spells it as the
// extension of the input file's name.
std::vector<std::string> Client::keysOf(Function *T) const {
  std::vector<std::string> out;
  std::set<std::string> seen;
  auto add = [&](Value *V) {
    auto *GV = dyn_cast<GlobalVariable>(getUnderlyingObject(V));
    auto *D = GV && GV->hasInitializer() ? dyn_cast<ConstantDataSequential>(GV->getInitializer()) : nullptr;
    if (!D || !D->isCString())
      return;
    std::string s = D->getAsCString().str();
    bool token = !s.empty() && s.size() <= 16;
    for (char c : s)
      token = token && std::isalnum((unsigned char)c);
    if (token && out.size() < 8 && seen.insert(s).second)
      out.push_back(s);
  };
  auto maker = [&](Value *Base, auto &self, int depth) -> void {
    if (auto *CB = dyn_cast<CallBase>(Base)) {
      for (Value *A : CB->args())
        add(A);
      return;
    }
    auto *L = dyn_cast<LoadInst>(Base);
    auto *Al = L ? dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
    if (!Al || depth > 0)
      return;
    for (User *U : Al->users())
      if (auto *S = dyn_cast<StoreInst>(U))
        if (S->getPointerOperand()->stripPointerCasts() == Al)
          self(getUnderlyingObject(S->getValueOperand()), self, depth + 1);
  };
  for (Module *M : {&down, &up}) {
    for (Function &G : *M)
      for (Instruction &I : instructions(G))
        if (auto *S = dyn_cast<StoreInst>(&I))
          if (S->getValueOperand()->stripPointerCasts() == T)
            maker(getUnderlyingObject(S->getPointerOperand()), maker, 0);
    std::function<void(Constant *)> record = [&](Constant *C) {
      if (!C || !isa<ConstantAggregate>(C))
        return;
      bool holds = false;
      for (Use &U : C->operands())
        holds = holds || U.get()->stripPointerCasts() == T;
      for (Use &U : C->operands()) {
        if (holds)
          add(U.get());
        record(dyn_cast<Constant>(U.get()));
      }
    };
    for (GlobalVariable &GV : M->globals())
      if (GV.hasInitializer())
        record(GV.getInitializer());
  }
  return out;
}

FnSet Client::installers(Function *T) const {
  FnSet out;
  StringRef name = T->getName();
  auto isT = [&](Value *V) {
    auto *F = dyn_cast<Function>(V->stripPointerCasts());
    return F && F->getName() == name;
  };
  // A record holds t when its initializer reaches t through aggregates and
  // the addresses of records that hold t (a table of driver classes).
  std::set<const GlobalVariable *> holders;
  std::function<bool(Constant *)> holds = [&](Constant *C) {
    if (!C)
      return false;
    if (isT(C))
      return true;
    if (auto *G = dyn_cast<GlobalVariable>(C->stripPointerCasts()))
      return holders.count(G) > 0;
    if (!isa<ConstantAggregate>(C))
      return false;
    for (Use &U : C->operands())
      if (holds(dyn_cast<Constant>(U.get())))
        return true;
    return false;
  };
  for (bool grew = true; grew && holders.size() < 4096;) {
    grew = false;
    for (Module *M : {&down, &up})
      for (GlobalVariable &GV : M->globals())
        if (GV.hasInitializer() && !holders.count(&GV) && holds(GV.getInitializer()))
          grew = holders.insert(&GV).second || grew;
  }
  auto addUser = [&](Instruction *I) {
    if (Function *B = body(I->getFunction()->getName().str()))
      out.insert(B);
  };
  for (Module *M : {&down, &up}) {
    for (Function &G : *M)
      for (Instruction &I : instructions(G)) {
        auto *CB = dyn_cast<CallBase>(&I);
        for (Use &U : I.operands())
          if (isT(U.get()) && !(CB && CB->isCallee(&U)))
            addUser(&I);
      }
    for (GlobalVariable &GV : M->globals()) {
      if (!holders.count(&GV))
        continue;
      std::vector<User *> work(GV.user_begin(), GV.user_end());
      std::set<User *> seen;
      while (!work.empty()) {
        User *U = work.back();
        work.pop_back();
        if (!seen.insert(U).second)
          continue;
        if (auto *I = dyn_cast<Instruction>(U))
          addUser(I);
        else if (isa<ConstantExpr>(U))
          work.insert(work.end(), U->user_begin(), U->user_end());
      }
    }
  }
  return out;
}

// A serialized input is a sequence of bytes: a pointer to void or to a
// one-byte integer. A pointer to wider elements is an array of client
// values, not an encoding of the input.
static bool byteSequence(const DIType *T) {
  T = strip(T);
  if (!T || !isPointer(T))
    return false;
  const DIType *E = strip(cast<DIDerivedType>(T)->getBaseType());
  return !E || (isa<DIBasicType>(E) && E->getSizeInBits() == 8);
}

// The ones F's code bounds by j, and without such evidence the byte buffer
// right before it. An unbounded length would let the library read past the
// client's buffer, an error no client makes.
std::vector<unsigned> Client::boundBy(Function *F, unsigned j) const {
  std::vector<unsigned> out;
  for (auto [b, k] : formalsOf(F).len)
    if (k == j)
      out.push_back(b);
  if (out.empty() && j > 0 && F->getArg(j)->getType()->isIntegerTy() && F->getArg(j - 1)->getType()->isPointerTy()) {
    auto sig = signature(F);
    auto at = irParams(F);
    if (at[j - 1] >= 0 && at[j] >= 0 && at[j] == at[j - 1] + 1 && sig[at[j - 1]].kind == Kind::Bytes)
      out.push_back(j - 1);
  }
  return out;
}

void Client::ensureIoReach() const {
  if (ioReachReady)
    return;
  ioReachReady = true;
  static const std::set<std::string> open{"fopen", "fopen64", "freopen", "open", "open64", "openat", "creat"};
  static const std::set<StringRef> io{"read",   "pread",    "pread64",       "readv",   "preadv",
                                      "recv",   "recvfrom", "recvmsg",       "fread",   "fread_unlocked",
                                      "fgetc",  "getc",     "getc_unlocked", "getchar", "fgets",
                                      "fgetws", "getline",  "getdelim",      "mmap",    "mmap64"};
  FnMap<FnSet> preds;
  for (const auto &kv : calls)
    for (Function *C : kv.second)
      preds[C].insert(kv.first);
  std::vector<Function *> openWork, readWork;
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    bool hitOpen = false, hitRead = false;
    for (Instruction &I : instructions(*F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
      if (!C)
        continue;
      if (!hitOpen && open.count(bareName(C->getName().str())))
        hitOpen = true;
      if (!hitRead && io.count(C->getName()))
        hitRead = true;
      if (hitOpen && hitRead)
        break;
    }
    if (hitOpen) {
      reachesOpen.insert(F);
      openWork.push_back(F);
    }
    if (hitRead) {
      reachesRead.insert(F);
      readWork.push_back(F);
    }
  }
  auto flood = [&](std::vector<Function *> &work, FnSet &reach) {
    while (!work.empty()) {
      Function *G = work.back();
      work.pop_back();
      auto it = preds.find(G);
      if (it == preds.end())
        continue;
      for (Function *P : it->second)
        if (reach.insert(P).second)
          work.push_back(P);
    }
  };
  flood(openWork, reachesOpen);
  flood(readWork, reachesRead);
}

Client::Channel Client::channel(Function *F) const {
  if (auto it = channelOf.find(F); it != channelOf.end())
    return it->second;
  auto sig = signature(F);
  auto at = irParams(F);
  for (unsigned j = 0; j < F->arg_size(); ++j)
    if (F->getArg(j)->getType()->isIntegerTy())
      for (unsigned b : boundBy(F, j))
        if (at[b] >= 0 && sig[at[b]].kind == Kind::Bytes && byteSequence(sig[at[b]].di))
          return channelOf[F] = Channel::Passed;
  for (const Param &p : sig) {
    if (p.kind != Kind::Callback || !isPointer(strip(p.di)))
      continue;
    auto *S = dyn_cast_or_null<DISubroutineType>(strip(cast<DIDerivedType>(strip(p.di))->getBaseType()));
    auto ts = S ? S->getTypeArray() : DITypeRefArray();
    for (unsigned i = 1; i + 1 < ts.size(); ++i)
      if (byteSequence(ts[i]) && isa_and_nonnull<DIBasicType>(strip(ts[i + 1])))
        return channelOf[F] = Channel::Passed;
  }
  ensureIoReach();
  if (reachesOpen.count(F) || reachesRead.count(F))
    return channelOf[F] = Channel::Named;
  return channelOf[F] = Channel::None;
}

unsigned Client::callCost(Function *F) const {
  unsigned c = 1;
  for (const Param &p : signature(F))
    if (held(p))
      if (auto it = cost.find(p.type); it != cost.end())
        c += it->second;
  return c;
}

unsigned Client::freeArgs(Function *F) const {
  unsigned n = 0;
  for (const Param &p : signature(F))
    n += !held(p) && p.kind != Kind::Out;
  return n;
}

// Whether obtaining a held U can require obtaining T.
bool Client::needs(const std::string &U, const std::string &T, std::set<std::string> &seen) const {
  if (U == T)
    return true;
  if (!seen.insert(U).second)
    return false;
  auto it = producers.find(U);
  if (it == producers.end())
    return false;
  for (const Producer &pr : it->second)
    for (const Param &p : signature(pr.fn))
      if (held(p) && needs(p.type, T, seen))
        return true;
  return false;
}

// The dependences of producer P of T (as in Palus's method dependence): the
// callable interface functions that modify a field a branch of P reads,
// through an object the client holds and passes to both. Calling one first can
// establish the state P needs to produce. Releases are excluded, and so are
// functions whose arguments would need T itself. As with writers, both
// sides stop at other callable interface functions: an effect reached
// through g is g's own, and the client calls g directly. Effects also stop
// at destructors: a destructor ends the lifetime of the object it runs on,
// so its stores establish no state.
std::vector<Function *> Client::dependences(Function *P, const std::string &T) const {
  std::set<std::string> share;
  for (const Param &p : signature(P))
    if (held(p))
      share.insert(p.type);
  std::vector<Function *> out;
  if (share.empty())
    return out;
  // State outlives a call only in objects the shared handles reach: the
  // source types reachable from theirs through members, pointers, bases
  // and template arguments.
  std::set<std::string> persists;
  {
    std::set<const DIType *> seen;
    std::vector<const DIType *> work;
    for (const std::string &k : share)
      if (auto it = composite.find(k); it != composite.end())
        work.push_back(it->second);
    while (!work.empty()) {
      const DIType *D = strip(work.back());
      work.pop_back();
      while (D && (isPointer(D) || (isa<DIDerivedType>(D) && cast<DIDerivedType>(D)->getTag() == dwarf::DW_TAG_member) ||
                   (isa<DIDerivedType>(D) && cast<DIDerivedType>(D)->getTag() == dwarf::DW_TAG_inheritance)))
        D = strip(cast<DIDerivedType>(D)->getBaseType());
      auto *C = dyn_cast_or_null<DICompositeType>(D);
      if (!C)
        continue;
      if (C->isForwardDecl())
        if (auto it = composite.find(typeKey(C)); it != composite.end())
          C = it->second;
      if (!seen.insert(C).second)
        continue;
      persists.insert(source::name(C));
      if (C->getTag() == dwarf::DW_TAG_array_type) {
        work.push_back(C->getBaseType());
        continue;
      }
      for (const DINode *N : C->getElements())
        if (auto *M = dyn_cast<DIDerivedType>(N))
          if (M->getTag() == dwarf::DW_TAG_member || M->getTag() == dwarf::DW_TAG_inheritance)
            work.push_back(M->getBaseType());
      for (const DINode *N : C->getTemplateParams())
        if (auto *TP = dyn_cast<DITemplateTypeParameter>(N))
          work.push_back(TP->getType());
    }
  }
  // Only a field that decides a branch of P can decide whether P produces.
  // W's effects (the stores of what W reaches without entering a callable
  // interface function or a destructor) meet those fields iff W reaches a
  // function that stores one: search back from those functions, not passing
  // to the callers of a function the search does not enter.
  if (modifiers.empty())
    for (const auto &[G, fs] : mods)
      for (const auto &f : fs)
        modifiers[f].push_back(G);
  if (callersOf.empty())
    for (const auto &kv : calls)
      for (Function *C : kv.second)
        callersOf[C].insert(kv.first);
  auto ends = [](Function *G) {
    DISubprogram *SP = G->getSubprogram();
    return SP && SP->getName().starts_with("~");
  };
  std::unordered_set<Function *> reach;
  std::vector<Function *> work;
  for (const auto &f : controlRefs(P))
    if (persists.count(f.first))
      if (auto m = modifiers.find(f); m != modifiers.end())
        for (Function *G : m->second)
          if (reach.insert(G).second)
            work.push_back(G);
  while (!work.empty()) {
    Function *G = work.back();
    work.pop_back();
    if (((ifaceD.count(G) || ifaceU.count(G)) && callable(G)) || ends(G))
      continue;
    if (auto it = callersOf.find(G); it != callersOf.end())
      for (Function *C : it->second)
        if (reach.insert(C).second)
          work.push_back(C);
  }
  for (Function *W : ifaceD) {
    if (W == P || !callable(W))
      continue;
    auto sig = signature(W);
    bool shares = false, cyc = false, rel = false;
    for (unsigned i = 0; i < sig.size(); ++i) {
      if (!held(sig[i]))
        continue;
      shares = shares || share.count(sig[i].type);
      std::set<std::string> seen;
      cyc = cyc || needs(sig[i].type, T, seen);
      rel = rel || releases.count({W, i});
    }
    if (!shares || cyc || rel)
      continue;
    if (reach.count(W))
      out.push_back(W);
  }
  // §3.11 Definition O: a dependence that takes the input comes first, in
  // channel order; among equals, the one whose stores meet more of the
  // persisting fields P's branches read, then the cheaper call, then the one
  // that leaves fewer values to the client.
  std::set<std::pair<std::string, int64_t>> ctl;
  for (const auto &f : controlRefs(P))
    if (persists.count(f.first))
      ctl.insert(f);
  std::map<Function *, unsigned> meets;
  for (Function *W : out) {
    std::set<std::pair<std::string, int64_t>> hit;
    for (Function *G : innerClosure(W))
      if (auto m = mods.find(G); m != mods.end())
        for (const auto &f : m->second)
          if (ctl.count(f))
            hit.insert(f);
    meets[W] = hit.size();
  }
  std::sort(out.begin(), out.end(), [&](Function *a, Function *b) {
    return std::make_tuple(channel(a), -(int64_t)meets[a], callCost(a), freeArgs(a), a->getName()) <
           std::make_tuple(channel(b), -(int64_t)meets[b], callCost(b), freeArgs(b), b->getName());
  });
  return out;
}

// The value a store writes, in the constant lattice: an integer constant,
// a function's source name, 0 for null, or * for any other value.
std::string Client::abstractValue(Value *V) {
  V = V->stripPointerCasts();
  if (auto *C = dyn_cast<ConstantInt>(V))
    return C->getBitWidth() <= 64 ? std::to_string(C->getSExtValue()) : "*";
  if (isa<ConstantPointerNull>(V))
    return "0";
  if (auto *F = dyn_cast<Function>(V))
    return bareName(F->getName().str());
  return "*";
}

// A name without the numeric suffix linking gives a renamed internal symbol.
std::string Client::bareName(const std::string &n) {
  auto dot = n.find_last_of('.');
  if (dot != std::string::npos && dot + 1 < n.size() && n.find_first_not_of("0123456789", dot + 1) == std::string::npos)
    return n.substr(0, dot);
  return n;
}

// Whether a store of abstract value v can leave the cell satisfying its
// constraint. Also the sign-agnostic match of an integer constant against
// a value printed unsigned.
bool Client::satisfies(const std::string &v, const Cell &c) {
  if (v == "*")
    return true;
  // §3.8 정의 3.8.1: 상수 k는 has m이면 k & m = m, lacks m이면 k & m = 0일 때 만족한다.
  if (c.op == "has" || c.op == "lacks") {
    auto k = asU64(v);
    if (!k)
      if (auto s = asI64(v))
        k = (uint64_t)*s;
    if (!k || c.values.empty())
      return !k;
    auto m = asU64(c.values[0]);
    if (!m)
      return false;
    return c.op == "has" ? (*k & *m) == *m : (*k & *m) == 0;
  }
  auto same = [&](const std::string &a, const std::string &b) {
    if (bareName(a) == bareName(b))
      return true;
    auto x = asI64(a), y = asI64(b);
    if (x && y)
      return (uint32_t)*x == (uint32_t)*y;
    return false;
  };
  bool in = false;
  for (const std::string &w : c.values)
    in = in || same(v, w);
  return c.op == "=" ? in : !in;
}

// Whether F gives a null argument i a meaning: in F's SSA form the formal
// itself is compared against null, and null can return (A1).
bool Client::nullTested(Function *F, unsigned i) const {
  // A reference, or a formal the compiler knows is nonnull, has no null.
  if (i < F->arg_size() && F->hasParamAttribute(i, Attribute::NonNull))
    return false;
  const Formals &f = formalsOf(F);
  return i < f.null.size() && f.null[i];
}

const Client::LocalFormals &Client::localFormalsOf(Function *F) const {
  auto it = localFormals.find(F);
  if (it != localFormals.end())
    return it->second;
  LocalFormals &local = localFormals[F];
  Formals &out = local.f;
  out.null.assign(F->arg_size(), false);
  out.as.assign(F->arg_size(), nullptr);
  if (F->isDeclaration())
    return local;
  ValueToValueMapTy VM;
  Function *G = CloneFunction(F, VM);
  std::vector<AllocaInst *> slots;
  for (Instruction &I : G->getEntryBlock())
    if (auto *A = dyn_cast<AllocaInst>(&I))
      if (isAllocaPromotable(A))
        slots.push_back(A);
  if (!slots.empty()) {
    DominatorTree DT(*G);
    PromoteMemToReg(slots, DT);
  }
  for (unsigned i = 0; i < G->arg_size(); ++i) {
    if (!G->getArg(i)->getType()->isPointerTy())
      continue;
    std::vector<Value *> work{G->getArg(i)};
    std::set<Value *> seen{G->getArg(i)};
    uint64_t widest = 0;
    while (!work.empty()) {
      Value *V = work.back();
      work.pop_back();
      SmallVector<DbgValueInst *, 4> dvs;
      findDbgValues(dvs, V);
      for (DbgValueInst *D : dvs) {
        const DIType *T = strip(D->getVariable()->getType());
        if (!isPointer(T))
          continue;
        auto *C = dyn_cast_or_null<DICompositeType>(strip(cast<DIDerivedType>(T)->getBaseType()));
        if (C && C->isForwardDecl()) {
          auto c = composite.find(typeKey(C));
          C = c == composite.end() ? nullptr : c->second;
        }
        if (C && C->getTag() != dwarf::DW_TAG_enumeration_type && C->getSizeInBits() > widest) {
          widest = C->getSizeInBits();
          out.as[i] = D->getVariable()->getType();
        }
      }
      for (User *U : V->users()) {
        if (auto *C = dyn_cast<ICmpInst>(U)) {
          if (C->isEquality() && (isa<ConstantPointerNull>(C->getOperand(0)) || isa<ConstantPointerNull>(C->getOperand(1))))
            out.null[i] = out.null[i] || nullReturns(C);
        } else if (isa<CastInst>(U) && seen.insert(U).second) {
          work.push_back(U);
        }
      }
    }
  }
  // A3: integer formal j bounds pointer formal i when F computes an address
  // p_i + e with e derived from j, passes p_i to a memory function with a
  // length derived from j, indexes p_i with a variable compared against
  // one derived from j, or passes both to a callee in which the same holds
  // (the transfer through calls is closed in formalsOf).
  auto intFormal = [](Value *V) -> int {
    for (;;) {
      if (auto *A = dyn_cast<Argument>(V))
        return A->getType()->isIntegerTy() ? (int)A->getArgNo() : -1;
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        return -1;
      if (isa<CastInst>(I))
        V = I->getOperand(0);
      else if (auto *B = dyn_cast<BinaryOperator>(I)) {
        bool c0 = isa<Constant>(B->getOperand(0)), c1 = isa<Constant>(B->getOperand(1));
        if (c0 == c1)
          return -1;
        V = c0 ? B->getOperand(1) : B->getOperand(0);
      } else
        return -1;
    }
  };
  auto ptrFormal = [](Value *V) -> int {
    for (;;) {
      V = V->stripPointerCasts();
      if (auto *A = dyn_cast<Argument>(V))
        return A->getType()->isPointerTy() ? (int)A->getArgNo() : -1;
      auto *G = dyn_cast<GEPOperator>(V);
      if (!G)
        return -1;
      V = G->getPointerOperand();
    }
  };
  auto bound = [&](int i, int j) {
    if (i >= 0 && j >= 0)
      out.len.insert({(unsigned)i, (unsigned)j});
  };
  for (Instruction &I : instructions(*G)) {
    if (auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
      // Pointer arithmetic, not a field access: one index over an element.
      if (GEP->getNumIndices() != 1 || GEP->getSourceElementType()->isStructTy())
        continue;
      int i = ptrFormal(GEP->getPointerOperand());
      if (i < 0)
        continue;
      Value *x = GEP->getOperand(1);
      bound(i, intFormal(x));
      while (auto *C = dyn_cast<CastInst>(x))
        x = C->getOperand(0);
      if (auto *Phi = dyn_cast<PHINode>(x))
        for (User *U : Phi->users())
          for (User *W : (isa<CastInst>(U) || isa<BinaryOperator>(U)) ? U->users() : Phi->users())
            if (auto *Cmp = dyn_cast<ICmpInst>(W))
              for (Value *O : Cmp->operands())
                bound(i, intFormal(O));
      continue;
    }
    auto *CB = dyn_cast<CallBase>(&I);
    if (!CB)
      continue;
    if (auto *MI = dyn_cast<MemIntrinsic>(CB)) {
      bound(ptrFormal(MI->getRawDest()), intFormal(MI->getLength()));
      if (auto *MT = dyn_cast<MemTransferInst>(MI))
        bound(ptrFormal(MT->getRawSource()), intFormal(MI->getLength()));
      continue;
    }
    auto *Callee = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
    Function *B = Callee ? body(Callee->getName().str()) : nullptr;
    if (!B)
      continue;
    LenCall call{B, {}, {}};
    bool p = false, n = false;
    for (Value *A : CB->args()) {
      call.ptr.push_back(ptrFormal(A));
      call.num.push_back(intFormal(A));
      p = p || call.ptr.back() >= 0;
      n = n || call.num.back() >= 0;
    }
    if (p && n)
      local.calls.push_back(std::move(call));
  }
  G->eraseFromParent();
  return local;
}

// Len is the least relation with
//   Len(F) ⊇ direct evidence in F
//   Len(F) ⊇ {(ptr_c(a), num_c(b)) | (a, b) ∈ Len(callee_c)} for each call c of F,
// computed over the functions reachable from F by such calls. That set is
// closed under callees, so the fixpoint is exact for every member and all of
// them are recorded.
const Client::Formals &Client::formalsOf(Function *F) const {
  auto it = formals.find(F);
  if (it != formals.end())
    return it->second;
  std::vector<Function *> region;
  FnMap<std::set<std::pair<unsigned, unsigned>>> len;
  FnMap<std::vector<Function *>> callers;
  std::vector<Function *> stack{F};
  FnSet seen{F};
  while (!stack.empty()) {
    Function *G = stack.back();
    stack.pop_back();
    region.push_back(G);
    const LocalFormals &l = localFormalsOf(G);
    len[G] = l.f.len;
    for (const LenCall &c : l.calls) {
      callers[c.callee].push_back(G);
      if (!formals.count(c.callee) && seen.insert(c.callee).second)
        stack.push_back(c.callee);
    }
  }
  auto lenOf = [&](Function *G) -> const std::set<std::pair<unsigned, unsigned>> & {
    auto f = formals.find(G);
    return f != formals.end() ? f->second.len : len[G];
  };
  std::vector<Function *> work(region.begin(), region.end());
  FnSet queued(region.begin(), region.end());
  while (!work.empty()) {
    Function *G = work.back();
    work.pop_back();
    queued.erase(G);
    auto &mine = len[G];
    size_t before = mine.size();
    for (const LenCall &c : localFormalsOf(G).calls)
      for (auto [a, b] : lenOf(c.callee))
        if (a < c.ptr.size() && b < c.num.size() && c.ptr[a] >= 0 && c.num[b] >= 0)
          mine.insert({(unsigned)c.ptr[a], (unsigned)c.num[b]});
    if (mine.size() == before)
      continue;
    for (Function *H : callers[G])
      if (seen.count(H) && queued.insert(H).second)
        work.push_back(H);
  }
  for (Function *G : region) {
    Formals f = localFormalsOf(G).f;
    f.len = std::move(len[G]);
    formals[G] = std::move(f);
  }
  return formals[F];
}

// The formal whose value V is: the argument itself, or an -O0 reload of the
// one slot that argument was spilled to.
int Client::formalOf(Value *V) {
  V = V->stripPointerCasts();
  if (auto *A = dyn_cast<Argument>(V))
    return (int)A->getArgNo();
  auto *L = dyn_cast<LoadInst>(V);
  auto *Al = L ? dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
  if (!Al)
    return -1;
  int at = -1;
  for (User *U : Al->users())
    if (auto *S = dyn_cast<StoreInst>(U))
      if (S->getPointerOperand()->stripPointerCasts() == Al) {
        auto *A = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
        if (!A || (at != -1 && at != (int)A->getArgNo()))
          return -1;
        at = (int)A->getArgNo();
      }
  return at;
}

// The formal whose object V points into: through casts, constant or
// variable GEPs, and -O0 slots every store to which points into the same
// formal's object.
int Client::rootOf(Value *V, std::set<AllocaInst *> &open) {
  V = V->stripPointerCasts();
  if (auto *A = dyn_cast<Argument>(V))
    return (int)A->getArgNo();
  if (auto *G = dyn_cast<GEPOperator>(V))
    return rootOf(G->getPointerOperand(), open);
  auto *L = dyn_cast<LoadInst>(V);
  auto *Al = L ? dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
  if (!Al)
    return -1;
  // A slot already being evaluated adds no root of its own (greatest
  // fixpoint over the slots' mutual stores).
  if (!open.insert(Al).second)
    return -2;
  int at = -1;
  bool ok = true, skipped = false;
  for (User *U : Al->users()) {
    auto *S = dyn_cast<StoreInst>(U);
    if (!S || S->getPointerOperand()->stripPointerCasts() != Al)
      continue;
    int k = rootOf(S->getValueOperand(), open);
    if (k == -2) {
      skipped = true;
      continue;
    }
    if (k < 0 || (at != -1 && at != k)) {
      ok = false;
      break;
    }
    at = k;
  }
  open.erase(Al);
  if (!ok)
    return -1;
  return at == -1 && skipped ? -2 : at;
}

// The formals whose objects F's result comes from: through -O0 slots,
// selects and address arithmetic, a returned pointer into memory a formal
// points to, or read out of it.
std::set<int> Client::loadedFrom(Function *F) const {
  std::set<int> out;
  std::set<Value *> seen;
  std::vector<Value *> work;
  for (Instruction &I : instructions(*F))
    if (auto *R = dyn_cast<ReturnInst>(&I))
      if (Value *V = R->getReturnValue())
        work.push_back(V);
  while (!work.empty()) {
    Value *V = work.back()->stripPointerCasts();
    work.pop_back();
    if (!seen.insert(V).second)
      continue;
    if (auto *P = dyn_cast<PHINode>(V)) {
      for (Value *In : P->incoming_values())
        work.push_back(In);
      continue;
    }
    if (auto *S = dyn_cast<SelectInst>(V)) {
      work.push_back(S->getTrueValue());
      work.push_back(S->getFalseValue());
      continue;
    }
    if (auto *G = dyn_cast<GEPOperator>(V)) {
      work.push_back(G->getPointerOperand());
      continue;
    }
    if (auto *A = dyn_cast<Argument>(V)) {
      out.insert((int)A->getArgNo());
      continue;
    }
    auto *L = dyn_cast<LoadInst>(V);
    if (!L)
      continue;
    if (auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
      for (User *U : Al->users())
        if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Al)
          work.push_back(S->getValueOperand());
      continue;
    }
    std::set<AllocaInst *> open;
    if (int k = rootOf(L->getPointerOperand(), open); k >= 0)
      out.insert(k);
  }
  return out;
}

// Whether F stores through formal i.
bool Client::writesThrough(Function *F, unsigned i) const { return writes.count({F, i}) > 0; }

// W, the pairs (F, i) such that F stores through formal i, is the least set
// closed under
//   (F, i) in W  if a store of F writes to memory rooted at i;
//   (F, i) in W  if F calls D passing a pointer rooted at i as argument a,
//                and (D, a) in W.
// The stores give the base; each pair then reaches the call sites that pass
// into it along the reversed second rule, once per pair, so the set is
// independent of the order functions are visited in.
void Client::buildWrites() {
  std::map<std::pair<Function *, unsigned>, std::vector<std::pair<Function *, unsigned>>> into;
  std::vector<std::pair<Function *, unsigned>> work;
  auto add = [&](Function *F, int i) {
    if (i >= 0 && writes.insert({F, (unsigned)i}).second)
      work.push_back({F, (unsigned)i});
  };
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    for (Instruction &I : instructions(*F)) {
      std::set<AllocaInst *> open;
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        add(F, rootOf(S->getPointerOperand(), open));
        continue;
      }
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
      Function *D = C ? body(C->getName().str()) : nullptr;
      if (!D)
        continue;
      for (unsigned a = 0; a < CB->arg_size() && a < D->arg_size(); ++a) {
        if (!CB->getArgOperand(a)->getType()->isPointerTy())
          continue;
        open.clear();
        if (int k = rootOf(CB->getArgOperand(a), open); k >= 0)
          into[{D, a}].push_back({F, (unsigned)k});
      }
    }
  }
  while (!work.empty()) {
    auto p = work.back();
    work.pop_back();
    auto it = into.find(p);
    if (it == into.end())
      continue;
    for (const auto &[F, k] : it->second)
      add(F, (int)k);
  }
}

// A function releases formal k when it passes a pointer into k's object to
// free or to a formal another function releases (least fixpoint). Releasing ends the
// handle's lifetime, so it never establishes a cell the sink needs. An
// indirect call goes to its targets in the call relation (§3.10).
void Client::buildReleases() {
  for (bool grew = true; grew;) {
    grew = false;
    for (const auto &kv : bodies) {
      Function *F = kv.second;
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        std::vector<Function *> ts;
        bool frees = false;
        auto add = [&](const Function *T) {
          if (Function *B = body(T->getName().str()))
            ts.push_back(B);
          else
            frees = frees || T->getName() == "free";
        };
        if (const Function *C = klee::calls::callee(*CB))
          add(C);
        else if (!CB->isInlineAsm())
          for (Function *T : targets.of(*CB))
            add(T);
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          bool rel = frees;
          for (Function *B : ts)
            rel = rel || releases.count({B, i});
          if (!rel)
            continue;
          std::set<AllocaInst *> open;
          int k = rootOf(CB->getArgOperand(i), open);
          if (k >= 0 && releases.insert({F, (unsigned)k}).second)
            grew = true;
        }
      }
    }
  }
}

FnSet Client::interface() const {
  FnSet all(ifaceD);
  all.insert(ifaceU.begin(), ifaceU.end());
  return all;
}

// A held input is a parameter the client fills with a value it holds from
// an earlier call rather than one it chooses: a handle, or a public object
// of a type the interface constructs. A type with a constructor is an
// abstract data type whose representation invariant that constructor
// establishes, so the client obtains it from the constructor and never
// assembles one itself. A handle type no interface function constructs is
// one no client can obtain: every client passes null for it, so a function
// taking it is callable only with null, and that is what the client passes.
bool Client::held(const Param &p) const {
  // A class passed by value that the interface constructs is held too: the
  // client has one only from its constructor (V-Adt).
  return (p.kind == Kind::Handle || p.kind == Kind::Object || p.kind == Kind::Aggregate) && constructed.count(p.type);
}

static std::vector<std::pair<Value *, Instruction *>> returnDefs(Function &F);

void Client::buildProducers() {
  // Producers: an interface function whose result or out-parameter is a
  // handle of type T.
  std::map<std::string, std::vector<std::pair<Function *, int>>> makes;
  for (Function *F : interface()) {
    Param r = result(F);
    if (r.kind == Kind::Handle || r.kind == Kind::Object)
      makes[r.type].push_back({F, -1});
    if (r.kind == Kind::Aggregate && F->hasParamAttribute(0, Attribute::StructRet))
      if (std::string T = owned(F->getSubprogram()->getType()->getTypeArray()[0]); !T.empty())
        makes[T].push_back({F, Owner});
    if (std::string T = constructs(F); !T.empty())
      makes[T].push_back({F, Construct});
    auto sig = signature(F);
    auto at = irParams(F);
    for (unsigned i = 0; i < at.size(); ++i)
      if (at[i] >= 0 && sig[at[i]].kind == Kind::Out && writesThrough(F, i))
        makes[sig[at[i]].type].push_back({F, at[i]});
  }
  makes.erase("");
  for (const auto &kv : makes)
    constructed.insert(kv.first);
  // A result read out of memory the client built (an object field by field,
  // or bytes such as a list it passes) is a value the client put there: the
  // function returns it, it makes none. Nor does a function whose every
  // return value is the null constant.
  for (auto &kv : makes) {
    auto &ps = kv.second;
    ps.erase(std::remove_if(ps.begin(), ps.end(),
                            [&](const std::pair<Function *, int> &fp) {
                              if (fp.second != -1)
                                return false;
                              const auto &sig = signature(fp.first);
                              auto at = irParams(fp.first);
                              for (int k : loadedFrom(fp.first))
                                if ((size_t)k < at.size() && at[k] >= 0 &&
                                    (sig[at[k]].kind == Kind::Object || sig[at[k]].kind == Kind::Bytes) &&
                                    !held(sig[at[k]]))
                                  return true;
                              auto defs = returnDefs(*fp.first);
                              return !defs.empty() && std::all_of(defs.begin(), defs.end(), [](const auto &d) {
                                return isa<ConstantPointerNull>(d.first);
                              });
                            }),
             ps.end());
  }
  for (auto it = makes.begin(); it != makes.end();)
    if (it->second.empty()) {
      constructed.erase(it->first);
      it = makes.erase(it);
    } else
      ++it;
  // Knuth's algorithm: settle the cheapest type whose producer has all its
  // held inputs settled.
  for (bool grew = true; grew;) {
    grew = false;
    std::string best;
    unsigned bestCost = ~0u;
    Producer bestP;
    for (const auto &kv : makes) {
      if (cost.count(kv.first))
        continue;
      for (const auto &fp : kv.second) {
        unsigned c = 1;
        bool ok = callable(fp.first);
        for (const Param &p : signature(fp.first)) {
          if (!held(p))
            continue;
          auto it = cost.find(p.type);
          if (it == cost.end()) {
            ok = false;
            break;
          }
          c += it->second;
        }
        if (ok && c < bestCost) {
          bestCost = c;
          best = kv.first;
          bestP = Producer{fp.first, fp.second, c};
        }
      }
    }
    if (best.empty())
      break;
    cost[best] = bestCost;
    grew = true;
  }
  // Every producer whose held inputs are strictly cheaper than its output
  // is admissible; the harness chooses among them. A copy constructor takes
  // the type it makes, so it is never the one that first makes it.
  for (const auto &kv : makes) {
    auto ct = cost.find(kv.first);
    if (ct == cost.end())
      continue;
    for (const auto &fp : kv.second) {
      bool ok = callable(fp.first);
      unsigned c = 1;
      for (const Param &p : signature(fp.first)) {
        if (!held(p))
          continue;
        auto it = cost.find(p.type);
        if (it == cost.end() || it->second >= ct->second) {
          ok = false;
          break;
        }
        c += it->second;
      }
      if (ok)
        producers[kv.first].push_back(Producer{fp.first, fp.second, c});
    }
    // §3.11 Definition O: a producer that takes the input comes first, then
    // the cheaper one, then the one that leaves fewer values to the client.
    // Precompute keys once — channel() used to run closureOf per comparison.
    using Key = std::tuple<Channel, unsigned, unsigned, std::string>;
    std::vector<std::pair<Key, Producer>> keyed;
    keyed.reserve(producers[kv.first].size());
    for (const Producer &p : producers[kv.first])
      keyed.push_back({{channel(p.fn), p.cost, freeArgs(p.fn), p.fn->getName().str()}, p});
    std::sort(keyed.begin(), keyed.end(),
              [](const auto &a, const auto &b) { return a.first < b.first; });
    producers[kv.first].clear();
    for (auto &e : keyed)
      producers[kv.first].push_back(std::move(e.second));
  }
}

FnSet Client::closure(Function *F) const {
  FnSet seen{F};
  std::vector<Function *> work{F};
  while (!work.empty()) {
    Function *G = work.back();
    work.pop_back();
    auto it = calls.find(G);
    if (it == calls.end())
      continue;
    for (Function *C : it->second)
      if (seen.insert(C).second)
        work.push_back(C);
  }
  return seen;
}

const FnSet &Client::closureOf(Function *F) const {
  auto it = closures.find(F);
  if (it != closures.end())
    return it->second;
  return closures[F] = closure(F);
}

// What F reaches without entering another callable interface function.
const FnSet &Client::innerClosure(Function *F) const {
  auto it = inner.find(F);
  if (it != inner.end())
    return it->second;
  FnSet seen{F};
  std::vector<Function *> work{F};
  while (!work.empty()) {
    Function *G = work.back();
    work.pop_back();
    auto c = calls.find(G);
    if (c == calls.end())
      continue;
    for (Function *C : c->second) {
      if ((ifaceD.count(C) || ifaceU.count(C)) && callable(C))
        continue;
      if (seen.insert(C).second)
        work.push_back(C);
    }
  }
  return inner[F] = seen;
}

// A call is constructible when every argument has a value: a held type
// needs a producer, and a handle the client cannot obtain leaves only null,
// which a formal without a null contract does not admit.
bool Client::callable(Function *F) const {
  if (!F->getSubprogram())
    return false;
  const auto &sig = signature(F);
  auto at = irParams(F);
  for (unsigned i = 0; i < at.size(); ++i) {
    if (at[i] < 0)
      continue;
    const Param &p = sig[at[i]];
    // A1: a pointer F compares with null, null returning, has the client
    // value NULL even when no producer of its type can be built.
    bool nullArg = (p.kind == Kind::Handle || p.kind == Kind::Object) && F->getArg(i)->getType()->isPointerTy() &&
                   nullTested(F, i);
    if (held(p) && !cost.count(p.type) && !nullArg)
      return false;
    // §2.2 V-Opaque 정제: 생성자가 없는 불투명 포인터(핸들로 분류되나 생산자 없음)는
    // 클라이언트가 가질 수 있는 값이 NULL뿐이다. 어떤 클라이언트도 그 타입의 non-null
    // 값을 만들 수 없으므로 NULL 전달이 유일하고 충실한 선택이고(H1 보존), 따라서 그
    // 인자는 호출 가능성을 막지 않는다. (라이브러리가 opaque optional 인자를 NULL로
    // 쓰라는 계약을 opaque·무생성자 타입으로 표현한 경우가 이에 해당한다.)
  }
  return true;
}

bool Client::entryCallable(Function *F) const {
  if (!F->getSubprogram())
    return false;
  const auto &sig = signature(F);
  auto at = irParams(F);
  for (unsigned i = 0; i < at.size(); ++i) {
    if (at[i] < 0)
      continue;
    const Param &p = sig[at[i]];
    if (held(p) && !cost.count(p.type))
      return false;
  }
  return true;
}

// The interface functions of D through which the client reaches the
// sequence: E itself when it is an entryCallable one, otherwise the
// entryCallable ones at the least call distance from which E is reached.
// callable() alone is not enough: a π₀ that is only null-callable for an
// unproducible handle would soft-accept and never elevate to the real E.
std::vector<Function *> Client::entries(Function *E) const {
  if (ifaceD.count(E) && entryCallable(E))
    return {E};
  FnMap<FnSet> callers;
  for (const auto &kv : calls)
    for (Function *C : kv.second)
      callers[C].insert(kv.first);
  FnMap<unsigned> dist{{E, 0}};
  std::deque<Function *> q{E};
  std::vector<Function *> out;
  unsigned found = ~0u;
  while (!q.empty()) {
    Function *G = q.front();
    q.pop_front();
    unsigned d = dist[G];
    if (d > found)
      break;
    if (G != E && ifaceD.count(G) && entryCallable(G)) {
      found = d;
      out.push_back(G);
      continue;
    }
    for (Function *C : callers[G])
      if (dist.emplace(C, d + 1).second)
        q.push_back(C);
  }
  std::sort(out.begin(), out.end(), [](Function *a, Function *b) { return a->getName() < b->getName(); });
  return out;
}

// Writers of a constrained cell: the callable interface functions of D whose
// calls store to its field a value that can satisfy the constraint, other
// than those that release a handle they take. Only minimal ones are kept:
// those that reach the store without passing through another callable
// interface function. A call that reaches the store through interface
// function g is g called with particular arguments, so the client calling
// g with symbolic ones subsumes it.
std::vector<Function *> Client::writers(const Cell &c) const {
  std::pair<std::string, int64_t> key{c.type, c.off};
  // F's inner closure holds a satisfying store iff F reaches one in the call
  // graph without edges into callable interface functions: search back from
  // the stores, not entering the callers of those functions.
  if (callersOf.empty())
    for (const auto &kv : calls)
      for (Function *C : kv.second)
        callersOf[C].insert(kv.first);
  FnSet reach;
  std::vector<Function *> work;
  for (const auto &[G, st] : stores)
    for (auto s = st.lower_bound({key, ""}); s != st.end() && s->first == key; ++s)
      if (satisfies(s->second, c)) {
        if (reach.insert(G).second)
          work.push_back(G);
        break;
      }
  while (!work.empty()) {
    Function *G = work.back();
    work.pop_back();
    if ((ifaceD.count(G) || ifaceU.count(G)) && callable(G))
      continue;
    if (auto it = callersOf.find(G); it != callersOf.end())
      for (Function *P : it->second)
        if (reach.insert(P).second)
          work.push_back(P);
  }
  std::vector<Function *> out;
  for (Function *F : ifaceD) {
    if (!reach.count(F) || !callable(F))
      continue;
    bool rel = false;
    auto sig = signature(F);
    auto at = irParams(F);
    for (unsigned j = 0; j < at.size(); ++j)
      rel = rel || (at[j] >= 0 && held(sig[at[j]]) && releases.count({F, j}));
    if (!rel)
      out.push_back(F);
  }
  std::sort(out.begin(), out.end(), [](Function *a, Function *b) { return a->getName() < b->getName(); });
  return out;
}

bool Client::everStored(const std::string &type, int64_t off) const {
  if (!storedBuilt) {
    for (const auto &kv : stores)
      for (const auto &s : kv.second)
        storedFields.insert(s.first);
    storedBuilt = true;
  }
  return storedFields.count({type, off}) > 0;
}

const char *Client::kindName(Kind k) {
  switch (k) {
  case Kind::Scalar:
    return "scalar";
  case Kind::Text:
    return "text";
  case Kind::Bytes:
    return "bytes";
  case Kind::Callback:
    return "callback";
  case Kind::Object:
    return "object";
  case Kind::Handle:
    return "handle";
  case Kind::Out:
    return "out";
  case Kind::Aggregate:
    return "aggregate";
  case Kind::Storage:
    return "storage";
  }
  return "?";
}

// A cell's constraint is necessary at the entry when the entry cannot
// change the cell: no function the entry reaches stores to its field, and
// no memory intrinsic it reaches covers the field at any struct level of
// the path. The value the witness's branch reads is then the value the
// cell has when the entry starts, so a client execution that reaches the
// sink along the witness satisfies it there. Guards are such constraints
// on integer fields embedded in an entry argument, with no pointer on the
// path; assuming them prunes only executions that cannot follow the
// witness.
// Where a cell lies inside its root object when every struct on its path is
// embedded in the one before (no pointer is followed): the byte offset from
// the root and the type of the field.
bool Client::place(const Cell &c, int64_t &off, Type *&field) const {
  std::istringstream in(c.text);
  std::string tok;
  in >> tok >> tok;
  std::vector<std::pair<std::string, int64_t>> steps;
  while (in >> tok && tok != "=" && tok != "!=" && tok[0] != '<' && tok[0] != '>') {
    auto p = tok.rfind('+');
    if (p == std::string::npos || p == 0)
      return false;
    auto o = asI64(tok.substr(p + 1));
    if (!o || *o < 0)
      return false;
    steps.push_back({tok.substr(0, p), *o});
  }
  if (steps.empty())
    return false;
  int64_t total = 0;
  Type *T = nullptr;
  for (size_t i = 0; i < steps.size(); ++i) {
    StructType *S = source::irType(steps[i].first);
    if (!S)
      S = StructType::getTypeByName(down.getContext(), steps[i].first);
    if (!S || S->isOpaque() || !S->isSized())
      return false;
    const StructLayout *L = dl.getStructLayout(S);
    if ((uint64_t)steps[i].second >= L->getSizeInBytes())
      return false;
    unsigned idx = L->getElementContainingOffset((uint64_t)steps[i].second);
    if (L->getElementOffset(idx) != (uint64_t)steps[i].second)
      return false;
    T = S->getElementType(idx);
    total += steps[i].second;
    if (i + 1 < steps.size() && !T->isStructTy())
      return false;
  }
  off = total;
  field = T;
  return true;
}

bool Client::guardOf(Function *E, const Cell &c, Guard &g, bool config) const {
  if (c.root < 0 || (c.op != "=" && c.op != "!="))
    return false;
  int64_t total = 0;
  Type *T = nullptr;
  if (!place(c, total, T))
    return false;
  if (!T->isIntegerTy() || T->getIntegerBitWidth() > 64)
    return false;
  std::vector<std::pair<std::string, int64_t>> steps;
  {
    std::istringstream in(c.text);
    std::string tok;
    in >> tok >> tok;
    while (in >> tok && tok != "=" && tok != "!=") {
      auto p = tok.rfind('+');
      steps.push_back({tok.substr(0, p), *asI64(tok.substr(p + 1))});
    }
  }
  std::vector<int64_t> vs;
  if (!intValues(c, vs))
    return false;
  // The offset of the field inside each level of the path.
  std::vector<int64_t> within(steps.size());
  for (size_t i = steps.size(), acc = 0; i-- > 0;) {
    acc += (size_t)steps[i].second;
    within[i] = (int64_t)acc;
  }
  // A configuration field is the client's own and it sets it before the
  // call; the may side already fixed the value the entry must start with,
  // so a later store by the entry does not disqualify it.
  for (Function *G : config ? FnSet{} : closureOf(E)) {
    auto it = stores.find(G);
    if (it != stores.end()) {
      auto st = it->second.lower_bound({steps.back(), ""});
      if (st != it->second.end() && st->first == steps.back())
        return false;
    }
    auto r = ranges.find(G);
    if (r == ranges.end())
      continue;
    for (const auto &[t, o, len] : r->second)
      for (size_t i = 0; i < steps.size(); ++i)
        if (t == steps[i].first && o <= within[i] && (len == INT64_MAX || within[i] - o < len))
          return false;
  }
  g.root = c.root;
  g.off = total;
  g.width = T->getIntegerBitWidth();
  g.eq = c.op == "=";
  g.values = vs;
  g.text = c.text;
  g.config = config;
  return true;
}

// ---------------------------------------------------------------------------
// §3.9 The plan: steering and realization.

const char *Client::realizeName(Realize r) {
  switch (r) {
  case Realize::Own:
    return "own";
  case Realize::Lever:
    return "lever";
  case Realize::Key:
    return "key";
  case Realize::Write:
    return "write";
  case Realize::Construct:
    return "construct";
  case Realize::File:
    return "file";
  case Realize::Open:
    return "open";
  }
  return "?";
}

bool Client::intValues(const Cell &c, std::vector<int64_t> &vs) {
  vs.clear();
  for (const std::string &v : c.values) {
    if (auto s = asI64(v))
      vs.push_back(*s);
    else if (auto u = asU64(v))
      vs.push_back((int64_t)*u);
    else {
      vs.clear();
      return false;
    }
  }
  return !vs.empty();
}

std::string Client::heldType(Function *E, int root) const {
  auto sig = signature(E);
  auto at = irParams(E);
  if (root < 0 || (size_t)root >= at.size() || at[root] < 0 || (size_t)at[root] >= sig.size())
    return "";
  const Param &p = sig[at[root]];
  return held(p) ? p.type : "";
}

bool Client::own(Function *E, const Cell &c) const {
  auto sig = signature(E);
  auto at = irParams(E);
  if (c.root < 0 || (size_t)c.root >= at.size() || at[c.root] < 0 || (size_t)at[c.root] >= sig.size() ||
      sig[at[c.root]].kind != Kind::Object)
    return false;
  for (const std::string &t : c.path)
    if (!isPublic(irName(t)))
      return false;
  // §3.11: a field of a held object is the client's own only when the
  // library leaves it to the client. A producer that stores a computed value
  // to it makes it argument or input state, which the client's write would
  // replace.
  const Param &p = sig[at[c.root]];
  if (held(p))
    if (auto it = producers.find(p.type); it != producers.end())
      for (const Producer &pr : it->second)
        for (Function *G : closureOf(pr.fn))
          if (auto s = stores.find(G); s != stores.end() && s->second.count({fieldOf(c), "*"}))
            return false;
  return true;
}

// A store of a value loaded from another field, through casts: the entry
// building a crossing object from its handle's settings, as libtiff's
// JPEGPreEncode does with cinfo.image_width = td_imagewidth.
const std::map<Client::Field, std::set<Client::Field>> &Client::copies(Function *F) const {
  auto it = copiesOf.find(F);
  if (it != copiesOf.end())
    return it->second;
  auto &out = copiesOf[F];
  for (Function *G : innerClosure(F))
    if (auto it = copyStores.find(G); it != copyStores.end())
      for (const auto &[d, src] : it->second)
        out[d].insert(src.begin(), src.end());
  return out;
}

const std::map<Client::Field, std::set<Client::Field>> &Client::allCopies(Function *F) const {
  auto it = allCopiesOf.find(F);
  if (it != allCopiesOf.end())
    return it->second;
  auto &out = allCopiesOf[F];
  for (Function *G : closureOf(F))
    if (auto it = copyStores.find(G); it != copyStores.end())
      for (const auto &[d, src] : it->second)
        out[d].insert(src.begin(), src.end());
  return out;
}

std::set<Client::Field> Client::copySources(StoreInst *S) const {
  Value *V = S->getValueOperand();
  while (auto *C = dyn_cast<CastInst>(V))
    V = C->getOperand(0);
  auto *L = dyn_cast<LoadInst>(V);
  if (!L)
    return {};
  auto fs = accessFields(*L, L->getPointerOperand());
  return {fs.begin(), fs.end()};
}

std::vector<Function *> Client::copySetters(Function *F, const Cell &c) const {
  const auto &cm = copies(F);
  auto it = cm.find(fieldOf(c));
  if (it == cm.end())
    return {};
  FnSet out;
  for (const Field &d : it->second) {
    Cell src;
    src.type = d.first;
    src.off = d.second;
    src.op = "!=";
    for (Function *W : writers(src))
      if (W != F)
        out.insert(W);
  }
  return {out.begin(), out.end()};
}

// Intraprocedural: through value operations, local slots and loads, not
// into callees.
bool Client::returnsArg(Function *F, unsigned j) const {
  auto key = std::make_pair(F, j);
  if (auto it = returnsOf.find(key); it != returnsOf.end())
    return it->second;
  bool &res = returnsOf[key] = false;
  if (F->isDeclaration() || j >= F->arg_size())
    return res;
  std::set<Value *> tv;
  std::vector<Value *> work;
  auto taint = [&](Value *v) {
    if (tv.insert(v).second)
      work.push_back(v);
  };
  taint(F->getArg(j));
  while (!work.empty()) {
    Value *v = work.back();
    work.pop_back();
    for (User *U : v->users()) {
      if (auto *R = dyn_cast<ReturnInst>(U)) {
        if (R->getReturnValue() == v)
          return res = true;
      } else if (auto *S = dyn_cast<StoreInst>(U)) {
        if (S->getValueOperand() == v)
          if (auto *A = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
            taint(A);
      } else if (auto *L = dyn_cast<LoadInst>(U)) {
        if (L->getPointerOperand() == v)
          taint(L);
      } else if (!isa<CallBase>(U) && isa<Instruction>(U)) {
        taint(U);
      }
    }
  }
  return res;
}

// Forward from the formals over W's closure. A value operation, a load
// through a derived pointer and a local slot (§3.8 taint (i)) carry the
// value; an argument carries it into the callee's formal, and the result
// of a callee that returns it (iii) or of a declaration given it (iv).
const std::set<Client::Field> &Client::argStores(Function *W, int only) const {
  if (auto it = argStoresOf.find({W, only}); it != argStoresOf.end())
    return it->second;
  std::set<Field> &out = argStoresOf[{W, only}];
  auto sig = signature(W);
  auto at = irParams(W);
  std::map<Function *, std::set<unsigned>> argT;
  for (unsigned i = 0; i < W->arg_size(); ++i) {
    if (only >= 0 && (unsigned)only != i)
      continue;
    Type *T = W->getArg(i)->getType();
    int k = i < at.size() ? at[i] : -1;
    Kind kd = k >= 0 ? sig[k].kind : (T->isIntegerTy() ? Kind::Scalar : Kind::Object);
    if (T->isIntegerTy() || kd == Kind::Scalar || kd == Kind::Bytes || kd == Kind::Text)
      argT[W].insert(i);
  }
  FnSet queued;
  std::vector<Function *> fwork;
  auto enqueue = [&](Function *F) {
    if (queued.insert(F).second)
      fwork.push_back(F);
  };
  enqueue(W);
  while (!fwork.empty()) {
    Function *F = fwork.back();
    fwork.pop_back();
    queued.erase(F);
    if (F->isDeclaration())
      continue;
    std::set<Value *> tv;
    std::vector<Value *> work;
    auto taint = [&](Value *v) {
      if (tv.insert(v).second)
        work.push_back(v);
    };
    for (unsigned i : argT[F])
      if (i < F->arg_size())
        taint(F->getArg(i));
    while (!work.empty()) {
      Value *v = work.back();
      work.pop_back();
      for (User *U : v->users()) {
        if (auto *S = dyn_cast<StoreInst>(U)) {
          if (S->getValueOperand() == v) {
            for (const Field &f : accessFields(*S, S->getPointerOperand()))
              out.insert(f);
            if (auto *A = dyn_cast<AllocaInst>(S->getPointerOperand()->stripPointerCasts()))
              taint(A);
          }
        } else if (auto *L = dyn_cast<LoadInst>(U)) {
          if (L->getPointerOperand() == v)
            taint(L);
        } else if (auto *CB = dyn_cast<CallBase>(U)) {
          auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
          if (!C)
            continue;
          if (Function *Bd = body(C->getName().str())) {
            bool ret = false;
            for (unsigned j = 0; j < CB->arg_size() && j < Bd->arg_size(); ++j)
              if (CB->getArgOperand(j) == v) {
                if (argT[Bd].insert(j).second)
                  enqueue(Bd);
                ret = ret || returnsArg(Bd, j);
              }
            if (ret)
              taint(CB);
          } else if (!CB->getType()->isVoidTy()) {
            taint(CB);
          }
        } else if (isa<Instruction>(U)) {
          taint(U);
        }
      }
    }
  }
  return out;
}

bool Client::carries(Function *W, const Cell &c, Function *E) const {
  const auto &ts = argStores(W);
  if (ts.count(fieldOf(c)))
    return true;
  const auto &cm = copies(E);
  if (auto it = cm.find(fieldOf(c)); it != cm.end())
    for (const Field &d : it->second)
      if (ts.count(d))
        return true;
  return false;
}

bool Client::readsInput(Function *F) const {
  if (auto it = readsOf.find(F); it != readsOf.end())
    return it->second;
  ensureIoReach();
  return readsOf[F] = reachesRead.count(F) > 0;
}

bool Client::storesInput(Function *F, const Field &f) const {
  for (Function *G : closureOf(F))
    if (auto it = inputStores.find(G); it != inputStores.end() && it->second.count(f))
      return true;
  return false;
}

bool Client::storesSatisfying(Function *F, const Field &f, const Cell &c) const {
  for (Function *G : closureOf(F))
    if (auto it = stores.find(G); it != stores.end())
      for (auto s = it->second.lower_bound({f, ""}); s != it->second.end() && s->first == f; ++s)
        if (s->second != "*" && satisfies(s->second, c))
          return true;
  return false;
}

bool Client::upOnly(const Field &f) const {
  bool any = false;
  for (const auto &[G, st] : stores) {
    auto s = st.lower_bound({f, ""});
    if (s == st.end() || s->first != f)
      continue;
    if (G->getParent() != &up)
      return false;
    any = true;
  }
  return any;
}

// Lever: a producer of the cell's held root whose integer formal reaches
// the field. The client picks that argument from the values the atom admits.
std::vector<std::pair<Function *, Client::Lever>> Client::leversOf(Function *E, const Cell &c) const {
  std::vector<std::pair<Function *, Lever>> out;
  std::vector<int64_t> vs;
  if (c.file || (c.op != "=" && c.op != "!=") || !intValues(c, vs))
    return out;
  auto pit = producers.find(heldType(E, c.root));
  if (pit == producers.end())
    return out;
  for (const Producer &pr : pit->second)
    for (unsigned i = 0; i < pr.fn->arg_size(); ++i)
      if (pr.fn->getArg(i)->getType()->isIntegerTy() && argStores(pr.fn, (int)i).count(fieldOf(c)))
        out.push_back({pr.fn, {i, c.op == "=", vs, c.text}});
  return out;
}

// Definition 3.8.4: W is an interface function of D other than E, takes
// the handle the cell lies in, and has the tag and variadic shape found.
bool Client::realizable(Function *E, const Keyed &k) const {
  Function *W = body(k.fn);
  if (!W || W == E || !ifaceD.count(W) || k.va != W->isVarArg())
    return false;
  std::string T = heldType(E, k.root);
  if (T.empty())
    return false;
  auto sw = signature(W);
  auto aw = irParams(W);
  if (k.obj >= aw.size() || aw[k.obj] < 0 || sw[aw[k.obj]].type != T)
    return false;
  return k.tag < 0 || ((size_t)k.tag < aw.size() && aw[k.tag] >= 0);
}

// Definition 3.8.6: the setter of lookup G. An interface function of D with
// G's signature, but the value where G has its fallback, of G's result
// type, that is not a lookup and modifies a field G reads. IR positions.
Function *Client::namedSetter(Function *G, unsigned obj, unsigned name, unsigned fallback) const {
  auto sg = signature(G);
  auto ag = irParams(G);
  if (!G->getSubprogram() || obj >= ag.size() || name >= ag.size() || fallback >= ag.size() || ag[obj] < 0 ||
      ag[name] < 0 || ag[fallback] < 0)
    return nullptr;
  const DIType *ret = strip(G->getSubprogram()->getType()->getTypeArray()[0]);
  const auto &reads = transitive(G, false);
  // Fields S writes: its inner closure, plus one hop into non-lookup callees.
  // A thin overload (attribute(name, int) -> attribute(name, TypeDesc, &v)) is
  // itself an interface function whose body only forwards, so innerClosure
  // stops before the callee that GEPs the object; the hop recovers that MOD.
  auto writesOf = [&](Function *S) {
    std::set<std::pair<std::string, int64_t>> w = transitive(S, true);
    for (Instruction &I : instructions(*S)) {
      auto *CB = dyn_cast<CallBase>(&I);
      auto *Cal = CB ? CB->getCalledFunction() : nullptr;
      Function *B = Cal ? body(Cal->getName().str()) : nullptr;
      if (!B || B == S || B->isDeclaration() || lookupOnly(B))
        continue;
      const auto &cw = transitive(B, true);
      w.insert(cw.begin(), cw.end());
    }
    return w;
  };
  for (Function *S : ifaceD) {
    if (S == G || S->arg_size() != G->arg_size() || !callable(S))
      continue;
    auto ss = signature(S);
    if (ss.size() != sg.size() || irParams(S) != ag)
      continue;
    bool same = true;
    for (unsigned i = 0; i < S->arg_size() && same; ++i) {
      Type *T = S->getArg(i)->getType();
      if (i == fallback)
        same = T == G->getReturnType() && strip(ss[ag[i]].di) == ret;
      else
        same = T == G->getArg(i)->getType() && (ag[i] < 0 || (ss[ag[i]].kind == sg[ag[i]].kind && ss[ag[i]].type == sg[ag[i]].type));
    }
    if (!same || !held(ss[ag[obj]]) || ss[ag[name]].kind == Kind::Scalar || lookupOnly(S))
      continue;
    const auto writes = writesOf(S);
    if (std::any_of(writes.begin(), writes.end(), [&](const auto &f) { return reads.count(f); }))
      return S;
  }
  return nullptr;
}

// Definition 3.8.6: the named settings of the lookups each step makes on an
// object it receives. A lookup is a call that writes no memory its caller
// sees (lookupOnly), returns an integer, and can return one argument
// unchanged (its fallback). The name is the constant text another argument
// carries, as the call or the last call before it that fills its slot
// passes it.
std::vector<Client::Named> Client::named(const std::vector<std::string> &seq) const {
  std::vector<Named> out;
  std::set<std::pair<Function *, std::string>> seen;
  auto text = [](Value *V) -> std::string {
    auto *G = dyn_cast<GlobalVariable>(V->stripPointerCasts());
    auto *A = G && G->hasInitializer() ? dyn_cast<ConstantDataArray>(G->getInitializer()) : nullptr;
    return A && A->isCString() ? A->getAsCString().str() : "";
  };
  for (const std::string &n : seq) {
    Function *F = body(n);
    if (!F)
      continue;
    DominatorTree DT(*F);
    for (Instruction &I : instructions(*F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      Function *Cal = CB ? CB->getCalledFunction() : nullptr;
      Function *G = Cal ? body(Cal->getName().str()) : nullptr;
      if (!CB || !Cal || !G || !G->getReturnType()->isIntegerTy() || !lookupOnly(G))
        continue;
      auto fb = fallbackArg(G);
      if (!fb || *fb >= CB->arg_size())
        continue;
      auto sg = signature(G);
      auto ag = irParams(G);
      std::optional<unsigned> obj;
      for (unsigned i = 0; i < ag.size(); ++i)
        if (ag[i] >= 0 && held(sg[ag[i]]) && !obj)
          obj = i;
      if (!obj)
        continue;
      std::set<AllocaInst *> open;
      bool cut = false;
      if (positionOf(CB->getArgOperand(*obj), open, cut).root < 0)
        continue;
      for (unsigned j = 0; j < CB->arg_size(); ++j) {
        if (j == *obj || j == *fb)
          continue;
        Named nm;
        Value *Op = CB->getArgOperand(j);
        nm.key = text(Op);
        if (nm.key.empty())
          if (auto *Slot = dyn_cast<AllocaInst>(Op->stripPointerCasts())) {
            CallBase *best = nullptr;
            for (User *U : Slot->users()) {
              auto *W = dyn_cast<CallBase>(U);
              Function *WF = W ? W->getCalledFunction() : nullptr;
              if (!W || W == CB || !WF || !DT.dominates(W, CB) || (best && !DT.dominates(best, W)))
                continue;
              std::vector<Constant *> as;
              std::optional<unsigned> s, t;
              std::string got;
              for (unsigned a = 0; a < W->arg_size(); ++a) {
                Value *Arg = W->getArgOperand(a);
                if (Arg->stripPointerCasts() == Slot && !s) {
                  s = a;
                  as.push_back(nullptr);
                } else if (std::string k = text(Arg); !k.empty() && !t) {
                  t = a;
                  got = k;
                  as.push_back(nullptr);
                } else if (auto *C = dyn_cast<ConstantInt>(Arg)) {
                  as.push_back(C);
                } else {
                  break;
                }
              }
              if (!s || !t || as.size() != W->arg_size())
                continue;
              best = W;
              nm.key = got;
              nm.init = WF;
              nm.slot = Slot->getAllocatedType();
              nm.initArgs = as;
              nm.slotAt = *s;
              nm.textAt = *t;
            }
          }
        if (nm.key.empty())
          continue;
        bool fixed = true;
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          auto *C = i == *obj || i == j || i == *fb ? nullptr : dyn_cast<ConstantInt>(CB->getArgOperand(i));
          fixed = fixed && (C || i == *obj || i == j || i == *fb);
          nm.rest.push_back(C);
        }
        Function *S = fixed ? namedSetter(G, *obj, j, *fb) : nullptr;
        if (!S || !seen.insert({S, nm.key}).second)
          break;
        nm.setter = S;
        nm.type = sg[ag[*obj]].type;
        nm.obj = *obj;
        nm.name = j;
        nm.value = *fb;
        out.push_back(std::move(nm));
        break;
      }
    }
  }
  return out;
}

const TargetLibraryInfo &Client::libInfo() const {
  if (!libSpec) {
    libImpl = std::make_unique<TargetLibraryInfoImpl>(Triple(down.getTargetTriple()));
    libSpec = std::make_unique<TargetLibraryInfo>(*libImpl);
  }
  return *libSpec;
}

std::string Client::MustState::at(const Field &f) const {
  if (auto it = fixed.find(f); it != fixed.end())
    return it->second;
  if (holes.count(f))
    return "";
  for (auto it = fills.rbegin(); it != fills.rend(); ++it)
    if (it->type == f.first && f.second >= it->off && f.second - it->off < it->len)
      return it->val == "*" ? "" : it->val;
  return "";
}

const BitVector &Client::modsBelow(Function *F) const {
  if (fieldAt.empty()) {
    for (const auto &[G, fs] : mods)
      for (const Field &f : fs)
        if (fieldId.emplace(f, fieldAt.size()).second) {
          fieldsOfType[f.first].push_back({f.second, (unsigned)fieldAt.size()});
          fieldAt.push_back(f);
        }
    for (auto &[T, v] : fieldsOfType)
      std::sort(v.begin(), v.end());
  }
  if (auto it = sccOf.find(F); it != sccOf.end())
    return sccMods[it->second];
  // Tarjan over calls from F; an SCC's bits are its own mods and its
  // callees' finished SCCs.
  auto callees = [&](Function *G) -> const FnSet * {
    auto it = calls.find(G);
    return it == calls.end() ? nullptr : &it->second;
  };
  struct Frame {
    Function *f;
    const FnSet *succ;
    FnSet::const_iterator next;
  };
  DenseMap<Function *, unsigned> index, low;
  DenseSet<Function *> onStack;
  std::vector<Function *> stack;
  std::vector<Frame> frames;
  auto enter = [&](Function *G) {
    index[G] = low[G] = index.size();
    stack.push_back(G);
    onStack.insert(G);
    const FnSet *s = callees(G);
    frames.push_back({G, s, s ? s->begin() : FnSet::const_iterator{}});
  };
  enter(F);
  while (!frames.empty()) {
    Frame &fr = frames.back();
    if (fr.succ && fr.next != fr.succ->end()) {
      Function *C = *fr.next++;
      if (sccOf.count(C))
        continue;
      if (!index.count(C))
        enter(C);
      else if (onStack.count(C))
        low[fr.f] = std::min(low[fr.f], index[C]);
      continue;
    }
    Function *G = fr.f;
    frames.pop_back();
    if (!frames.empty())
      low[frames.back().f] = std::min(low[frames.back().f], low[G]);
    if (low[G] != index[G])
      continue;
    std::vector<Function *> members;
    Function *M;
    do {
      M = stack.back();
      stack.pop_back();
      onStack.erase(M);
      members.push_back(M);
    } while (M != G);
    BitVector bits(fieldAt.size());
    for (Function *X : members) {
      if (auto m = mods.find(X); m != mods.end())
        for (const Field &f : m->second)
          bits.set(fieldId.at(f));
      if (const FnSet *s = callees(X))
        for (Function *C : *s)
          if (auto c = sccOf.find(C); c != sccOf.end())
            bits |= sccMods[c->second];
    }
    unsigned id = sccMods.size();
    sccMods.push_back(std::move(bits));
    for (Function *X : members)
      sccOf[X] = id;
  }
  return sccMods[sccOf.at(F)];
}

// 정의 M: a forward must analysis over the fields, the greatest fixed point
// of the meet that keeps a field only where both sides give one constant.
const Client::MustSummary *Client::mustOnReturn(Function *F) const {
  if (!F || F->isDeclaration())
    return nullptr;
  // One body per name (D∪U). Keying by raw Function* lets the same
  // symbol's down and up copies each start a full analysis and recurse
  // into each other — OIIO blows the stack / heap in Client construction.
  if (Function *B = body(F->getName().str()))
    F = B;
  // Placeholder in mustOf while busy: a recursive edge returns the empty
  // summary instead of re-entering (mustBusy alone is not enough when two
  // Function* share a name across modules).
  if (auto it = mustOf.find(F); it != mustOf.end())
    return &it->second;
  if (!mustBusy.insert(F).second)
    return &mustOf[F];
  MustSummary &S = mustOf[F];
  struct Flow {
    MustState s;
    std::vector<FormalWrite> writes;
    std::set<unsigned> clobbers;
  };
  auto meet = [](const Flow &a, const Flow &b) {
    Flow r;
    if (a.s.fills == b.s.fills)
      r.s.fills = a.s.fills;
    r.s.holes = a.s.holes;
    r.s.holes.insert(b.s.holes.begin(), b.s.holes.end());
    for (const auto *side : {&a.s.fixed, &b.s.fixed})
      for (const auto &[f, v] : *side) {
        std::string x = a.s.at(f), y = b.s.at(f);
        if (!x.empty() && x == y)
          r.s.fixed[f] = x;
        else
          r.s.holes.insert(f);
      }
    if (!r.s.fills.empty())
      for (const auto &[f, v] : r.s.fixed)
        r.s.holes.erase(f);
    r.clobbers = a.clobbers;
    r.clobbers.insert(b.clobbers.begin(), b.clobbers.end());
    if (a.writes == b.writes)
      r.writes = a.writes;
    else
      for (const auto *side : {&a.writes, &b.writes})
        for (const FormalWrite &w : *side)
          r.clobbers.insert(w.formal);
    return r;
  };
  // A slot every store to which stores one value reads that value.
  auto through = [this](Value *V) {
    for (int n = 0; n < 8; ++n) {
      V = fieldAddress(V);
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      auto *L = dyn_cast<LoadInst>(V);
      auto *Al = L ? dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
      if (!Al)
        break;
      Value *one = nullptr;
      for (User *U : Al->users())
        if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Al) {
          if (one && one != S->getValueOperand())
            return V;
          one = S->getValueOperand();
        }
      if (!one)
        break;
      V = one;
    }
    return V;
  };
  auto token = [&](Value *V) -> std::string {
    V = through(V);
    if (auto *A = dyn_cast<Argument>(V))
      return "#" + std::to_string(A->getArgNo());
    return abstractValue(V);
  };
  // A hole only shadows a fill; on a field no fill covers it is invisible to
  // at(), to a meet (equal fills on both sides), and to a later fill (which
  // clears holes it covers), and holding it makes every block's state carry
  // all a callee may touch.
  auto covered = [](const MustState &s, const Field &f) {
    for (const MustFill &x : s.fills)
      if (x.type == f.first && f.second >= x.off && f.second - x.off < x.len)
        return true;
    return false;
  };
  auto setField = [&covered](MustState &s, const Field &f, const std::string &v) {
    if (v == "*") {
      s.fixed.erase(f);
      if (covered(s, f))
        s.holes.insert(f);
    } else {
      s.fixed[f] = v;
      s.holes.erase(f);
    }
  };
  auto fill = [](MustState &s, const std::vector<Field> &at, int64_t len, const std::string &v) {
    for (const auto &[T, o] : at) {
      auto in = [&](const Field &f) { return f.first == T && f.second >= o && f.second - o < len; };
      for (auto it = s.fixed.begin(); it != s.fixed.end();)
        it = in(it->first) ? s.fixed.erase(it) : std::next(it);
      for (auto it = s.holes.begin(); it != s.holes.end();)
        it = in(*it) ? s.holes.erase(it) : std::next(it);
      s.fills.push_back({T, o, len, v});
    }
  };
  // A write of len bytes of v through pointer P: to the fields P addresses,
  // or recorded against the formal P is.
  auto write = [&](Flow &fl, Value *P, int64_t len, int lenFormal, const std::string &v) {
    Value *R = through(P);
    if (auto *A = dyn_cast<Argument>(R)) {
      fl.s = MustState{};
      fl.writes.push_back({A->getArgNo(), v, len, lenFormal});
      return;
    }
    auto at = fieldsOf(R);
    if (!at.empty())
      fill(fl.s, at, lenFormal >= 0 ? INT64_MAX : len, v);
  };
  auto byteValue = [&](Value *B) -> std::string {
    std::string t = token(B);
    return t == "0" || t[0] == '#' ? t : "*";
  };
  auto lengthOf = [&](Value *N, int &lf) -> int64_t {
    std::string t = token(N);
    lf = -1;
    if (!t.empty() && t[0] == '#') {
      lf = std::stoi(t.substr(1));
      return INT64_MAX;
    }
    auto k = asI64(t);
    return k && *k >= 0 ? *k : INT64_MAX;
  };
  auto call = [&](Flow &fl, CallBase *CB, Function *D) {
    if (!D || D->isDeclaration()) {
      if (D && D->onlyReadsMemory())
        return;
      LibFunc lf;
      bool frees = D && libInfo().getLibFunc(*D, lf) && isLibFreeFunction(D, lf);
      for (unsigned j = 0; j < CB->arg_size(); ++j) {
        Value *A = CB->getArgOperand(j);
        if (!A->getType()->isPointerTy() || (frees && j == 0))
          continue;
        if (D && j < D->arg_size() && (D->hasParamAttribute(j, Attribute::ReadOnly) || D->hasParamAttribute(j, Attribute::ReadNone)))
          continue;
        write(fl, A, INT64_MAX, -1, "*");
      }
      return;
    }
    const MustSummary *S = mustOnReturn(D);
    if (!S) {
      fl.s = MustState{};
      return;
    }
    auto actual = [&](const std::string &t) -> std::string {
      if (t.empty() || t[0] != '#')
        return t;
      unsigned j = std::stoul(t.substr(1));
      return j < CB->arg_size() ? byteValue(CB->getArgOperand(j)) : "*";
    };
    for (const FormalWrite &w : S->writes) {
      if (w.formal >= CB->arg_size())
        continue;
      int lf = -1;
      int64_t len = w.lenFormal >= 0 && (unsigned)w.lenFormal < CB->arg_size()
                        ? lengthOf(CB->getArgOperand(w.lenFormal), lf)
                        : w.len;
      write(fl, CB->getArgOperand(w.formal), len, lf, actual(w.val));
    }
    for (unsigned j : S->clobbers)
      if (j < CB->arg_size())
        write(fl, CB->getArgOperand(j), INT64_MAX, -1, "*");
    const BitVector &below = modsBelow(D);
    std::vector<Field> lost;
    for (const auto &[f, v] : fl.s.fixed)
      if (auto id = fieldId.find(f); id != fieldId.end() && below.test(id->second))
        lost.push_back(f);
    for (const MustFill &x : fl.s.fills)
      if (auto t = fieldsOfType.find(x.type); t != fieldsOfType.end())
        for (auto it = std::lower_bound(t->second.begin(), t->second.end(), std::make_pair(x.off, 0u));
             it != t->second.end() && it->first - x.off < x.len; ++it)
          if (below.test(it->second))
            lost.push_back(fieldAt[it->second]);
    for (const Field &f : lost)
      setField(fl.s, f, "*");
    for (const MustFill &x : S->post.fills)
      fill(fl.s, {{x.type, x.off}}, x.len, x.val);
    for (const Field &f : S->post.holes)
      setField(fl.s, f, "*");
    for (const auto &[f, v] : S->post.fixed)
      setField(fl.s, f, v);
  };
  auto step = [&](Flow &fl, Instruction &I) {
    if (auto *S = dyn_cast<StoreInst>(&I)) {
      Value *R = through(S->getPointerOperand());
      std::string v = abstractValue(through(S->getValueOperand()));
      if (isa<Argument>(R)) {
        fl.s = MustState{};
        fl.clobbers.insert(cast<Argument>(R)->getArgNo());
        return;
      }
      for (const Field &f : fieldsOf(R))
        setField(fl.s, f, v);
      return;
    }
    auto *CB = dyn_cast<CallBase>(&I);
    if (!CB || CB->isInlineAsm())
      return;
    if (auto *MS = dyn_cast<MemSetInst>(CB)) {
      int lf = -1;
      int64_t len = lengthOf(MS->getLength(), lf);
      write(fl, MS->getRawDest(), len, lf, byteValue(MS->getValue()));
      return;
    }
    if (auto *MT = dyn_cast<MemTransferInst>(CB)) {
      int lf = -1;
      int64_t len = lengthOf(MT->getLength(), lf);
      write(fl, MT->getRawDest(), len, lf, "*");
      return;
    }
    if (isa<IntrinsicInst>(CB))
      return;
    if (const Function *C = klee::calls::callee(*CB)) {
      Function *B = body(C->getName().str());
      call(fl, CB, B ? B : const_cast<Function *>(C));
      return;
    }
    std::optional<Flow> out;
    for (Function *T : targets.of(*CB)) {
      Flow one = fl;
      Function *B = body(T->getName().str());
      call(one, CB, B ? B : T);
      out = out ? meet(*out, one) : one;
    }
    if (out)
      fl = std::move(*out);
  };
  std::map<BasicBlock *, Flow> outOf;
  std::vector<BasicBlock *> order;
  for (BasicBlock *BB : ReversePostOrderTraversal<Function *>(F))
    order.push_back(BB);
  bool changed = true;
  for (unsigned round = 0; changed && round < 64; ++round) {
    changed = false;
    for (BasicBlock *BB : order) {
      std::optional<Flow> in;
      if (BB == &F->getEntryBlock())
        in = Flow{};
      for (BasicBlock *P : predecessors(BB))
        if (auto it = outOf.find(P); it != outOf.end())
          in = in ? meet(*in, it->second) : it->second;
      if (!in)
        continue;
      for (Instruction &I : *BB)
        step(*in, I);
      auto it = outOf.find(BB);
      if (it == outOf.end() || !(it->second.s.fixed == in->s.fixed && it->second.s.holes == in->s.holes &&
                                 it->second.s.fills == in->s.fills && it->second.writes == in->writes &&
                                 it->second.clobbers == in->clobbers)) {
        outOf[BB] = std::move(*in);
        changed = true;
      }
    }
  }
  std::optional<Flow> ret;
  for (BasicBlock *BB : order)
    if (isa<ReturnInst>(BB->getTerminator()))
      if (auto it = outOf.find(BB); it != outOf.end())
        ret = ret ? meet(*ret, it->second) : it->second;
  if (ret && !changed) {
    S.post = std::move(ret->s);
    S.writes = std::move(ret->writes);
    S.clobbers = std::move(ret->clobbers);
  }
  mustBusy.erase(F);
  return &S;
}

bool Client::contradicts(Function *W, const Cell &c) const {
  if (c.op != "=" && c.op != "!=" && c.op != "has" && c.op != "lacks")
    return false;
  const MustSummary *S = mustOnReturn(W);
  if (!S)
    return false;
  std::string v = S->post.at(fieldOf(c));
  return !v.empty() && !satisfies(v, c);
}

// Wr(c): writers of c and, for a boundary cell, setters of what the entry
// copies into it. A candidate is an interface function of D, not an entry,
// that takes the cell's held root, and for a boundary or prefix cell
// carries a client value into it.
std::vector<Function *> Client::writeCandidates(Function *E, const std::vector<Function *> &es, const Cell &c) const {
  Function *entry = es.empty() ? nullptr : es[0];
  std::string T = heldType(E, c.root);
  FnSet out;
  auto admit = [&](Function *W) {
    if (!ifaceD.count(W) || std::find(es.begin(), es.end(), W) != es.end())
      return;
    if (!T.empty()) {
      bool share = false;
      for (const Param &p : signature(W))
        share = share || (held(p) && p.type == T);
      if (!share)
        return;
    }
    if ((c.boundary || c.prefix) && (!entry || !carries(W, c, entry)))
      return;
    out.insert(W);
  };
  for (Function *W : writers(c))
    admit(W);
  if (c.boundary && entry)
    for (Function *W : copySetters(entry, c))
      admit(W);
  return {out.begin(), out.end()};
}

// The calls of the harness that can write c before or inside the entry: the
// entry, the producers of c's held root, and the calls they depend on.
// Every held layer on c's path is an object the harness must produce when it
// builds that root (Λ3): its producers' stores establish that layer's fields
// (e.g. AcquireCustomStreamInfo writing CustomStreamInfo.signature).
std::vector<Function *> Client::harnessStarts(Function *E, Function *entry, const Cell &c) const {
  std::vector<Function *> out{entry};
  std::set<std::string> have;
  auto addType = [&](std::string T) {
    if (T.rfind("struct.", 0) == 0)
      T = T.substr(7);
    if (T.empty() || !have.insert(T).second)
      return;
    auto pit = producers.find(T);
    if (pit == producers.end())
      return;
    for (const Producer &pr : pit->second) {
      out.push_back(pr.fn);
      for (Function *D : dependences(pr.fn, T))
        out.push_back(D);
    }
  };
  addType(heldType(E, c.root));
  for (const std::string &t : c.path)
    addType(t);
  return out;
}

// Φ_pre completion for establish sequences: a constant compare of a load of
// a tag-settable field is a client obligation even when may dropped it.
void Client::ensureTagSetters() const {
  if (tagSettersReady)
    return;
  tagSettersReady = true;
  // Tag-dispatch setters (정의 3.8.4): store may live in a non-export
  // (JPEGVSetField); climb callers to the interface vararg (TIFFSetField).
  std::unordered_map<Function *, std::vector<Function *>> callersOf;
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    if (!F)
      continue;
    auto it = calls.find(F);
    if (it == calls.end())
      continue;
    for (Function *C : it->second)
      callersOf[C].push_back(F);
  }
  auto oneFormal = [&](Value *V) -> Argument * {
    std::unordered_set<const Value *> seen;
    std::vector<Value *> st{V};
    Argument *found = nullptr;
    while (!st.empty()) {
      Value *X = st.back();
      st.pop_back();
      if (!X || !seen.insert(X).second)
        continue;
      if (auto *A = dyn_cast<Argument>(X->stripPointerCasts())) {
        if (found && found != A)
          return nullptr;
        found = A;
        continue;
      }
      if (auto *C = dyn_cast<CastInst>(X)) {
        st.push_back(C->getOperand(0));
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(X)) {
        auto *Al = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
        if (Al) {
          for (User *U : Al->users()) {
            auto *St = dyn_cast<StoreInst>(U);
            if (St && St->getPointerOperand()->stripPointerCasts() == Al)
              st.push_back(St->getValueOperand());
          }
          continue;
        }
        st.push_back(L->getPointerOperand());
        continue;
      }
      if (auto *G = dyn_cast<GEPOperator>(X)) {
        st.push_back(G->getPointerOperand());
        continue;
      }
    }
    return found;
  };
  auto viaVa = [](Value *V) {
    std::vector<Value *> st{V};
    std::unordered_set<const Value *> seen;
    while (!st.empty()) {
      Value *X = st.back();
      st.pop_back();
      if (!X || !seen.insert(X).second)
        continue;
      if (isa<VAArgInst>(X))
        return true;
      if (auto *C = dyn_cast<CastInst>(X)) {
        st.push_back(C->getOperand(0));
        continue;
      }
      if (auto *P = dyn_cast<PHINode>(X)) {
        for (Value *in : P->incoming_values())
          st.push_back(in);
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(X)) {
        st.push_back(L->getPointerOperand());
        continue;
      }
      if (auto *G = dyn_cast<GEPOperator>(X)) {
        std::string ty;
        raw_string_ostream os(ty);
        G->getSourceElementType()->print(os);
        if (ty.find("va_list") != std::string::npos)
          return true;
        st.push_back(G->getPointerOperand());
      }
    }
    return false;
  };
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    if (!F || F->isDeclaration())
      continue;
    for (BasicBlock &BB : *F) {
      auto *Sw = dyn_cast<SwitchInst>(BB.getTerminator());
      if (!Sw)
        continue;
      Argument *tagArg = oneFormal(Sw->getCondition());
      if (!tagArg || tagArg->getParent() != F)
        continue;
      for (auto &Case : Sw->cases()) {
        if (Case.getCaseValue()->getBitWidth() > 64)
          continue;
        int64_t tagV = Case.getCaseValue()->getSExtValue();
        std::unordered_set<const BasicBlock *> reach{Case.getCaseSuccessor()};
        std::vector<const BasicBlock *> st{Case.getCaseSuccessor()};
        while (!st.empty()) {
          const BasicBlock *B = st.back();
          st.pop_back();
          for (const BasicBlock *S : successors(B))
            if (reach.insert(S).second)
              st.push_back(S);
        }
        for (const BasicBlock *B : reach) {
          for (Instruction &I : *const_cast<BasicBlock *>(B)) {
            auto *S = dyn_cast<StoreInst>(&I);
            if (!S || !viaVa(S->getValueOperand()))
              continue;
            Argument *objArg = oneFormal(S->getPointerOperand());
            if (!objArg || objArg->getParent() != F)
              continue;
            for (const auto &f : accessFields(*S, const_cast<Value *>(S->getPointerOperand()))) {
              struct Node {
                Function *fn;
                Argument *obj;
                Argument *tag;
              };
              std::queue<Node> q;
              std::unordered_set<Function *> seenFn;
              q.push({F, objArg, tagArg});
              while (!q.empty()) {
                Node n = q.front();
                q.pop();
                if (!seenFn.insert(n.fn).second)
                  continue;
                if (ifaceD.count(n.fn) && n.fn->isVarArg() && n.obj && n.tag) {
                  Keyed k;
                  k.fn = n.fn->getName().str();
                  k.obj = n.obj->getArgNo();
                  k.tag = (int)n.tag->getArgNo();
                  k.tagV = tagV;
                  k.va = true;
                  k.root = 0;
                  k.path = {f.first};
                  k.off = f.second;
                  tagSettersOf[f].push_back(k);
                  break;
                }
                auto cit = callersOf.find(n.fn);
                if (cit == callersOf.end())
                  continue;
                for (Function *C : cit->second) {
                  if (n.obj->getArgNo() < C->arg_size() && n.tag->getArgNo() < C->arg_size())
                    q.push({C, C->getArg(n.obj->getArgNo()), C->getArg(n.tag->getArgNo())});
                }
              }
            }
          }
        }
      }
    }
  }
}

// §3.8.5: at a bit-OR site `fields[i] |= 1 << (desc->bit & 31)`, read constant
// arrays of desc's type so each tag constant maps to the (word field, mask) it
// raises. No library-specific layout: the member index is taken from the GEP.
void Client::ensureRegistryRaises() const {
  if (registryReady)
    return;
  registryReady = true;
  ensureTagSetters();
  auto strip = [](Value *V) {
    while (V) {
      if (auto *C = dyn_cast<CastInst>(V)) {
        V = C->getOperand(0);
        continue;
      }
      break;
    }
    return V;
  };
  auto asConstInt = [&](Value *V) -> ConstantInt * {
    V = strip(V);
    return dyn_cast_or_null<ConstantInt>(V);
  };
  for (Module *M : {&down, &up}) {
    for (Function &F : *M) {
      if (F.isDeclaration())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *S = dyn_cast<StoreInst>(&I);
        if (!S)
          continue;
        auto *Or = dyn_cast<BinaryOperator>(strip(S->getValueOperand()));
        if (!Or || Or->getOpcode() != Instruction::Or)
          continue;
        Value *ShlV = nullptr, *OldV = nullptr;
        for (unsigned o = 0; o < 2; ++o) {
          auto *Sh = dyn_cast<BinaryOperator>(strip(Or->getOperand(o)));
          if (Sh && Sh->getOpcode() == Instruction::Shl)
            ShlV = Sh;
          else
            OldV = Or->getOperand(o);
        }
        if (!ShlV || !OldV)
          continue;
        auto *Shl = cast<BinaryOperator>(ShlV);
        if (!asConstInt(Shl->getOperand(0)) || !asConstInt(Shl->getOperand(0))->isOne())
          continue;
        Value *Shift = strip(Shl->getOperand(1));
        auto *And = dyn_cast<BinaryOperator>(Shift);
        if (!And || And->getOpcode() != Instruction::And)
          continue;
        if (!S->getValueOperand()->getType()->isIntegerTy())
          continue;
        const uint64_t lowBits = S->getValueOperand()->getType()->getIntegerBitWidth() - 1;
        Value *BitSrc = nullptr;
        for (unsigned o = 0; o < 2; ++o)
          if (auto *K = asConstInt(And->getOperand(o)); K && K->getZExtValue() == lowBits)
            BitSrc = And->getOperand(1 - o);
        if (!BitSrc)
          continue;
        BitSrc = strip(BitSrc);
        auto *BitLoad = dyn_cast<LoadInst>(BitSrc);
        if (!BitLoad)
          continue;
        auto *BitGep = dyn_cast<GEPOperator>(BitLoad->getPointerOperand()->stripPointerCasts());
        if (!BitGep || BitGep->getNumIndices() < 2)
          continue;
        auto *BitIdx = dyn_cast<ConstantInt>(BitGep->idx_begin()[BitGep->getNumIndices() - 1]);
        if (!BitIdx || BitIdx->getBitWidth() > 64)
          continue;
        unsigned bitMember = (unsigned)BitIdx->getZExtValue();
        auto *StTy = dyn_cast<StructType>(BitGep->getSourceElementType());
        if (!StTy || bitMember >= StTy->getNumElements())
          continue;
        auto *OldLoad = dyn_cast<LoadInst>(strip(OldV));
        if (!OldLoad || OldLoad->getPointerOperand()->stripPointerCasts() !=
                            S->getPointerOperand()->stripPointerCasts())
          continue;
        // The word index must be bit / wordBits of the same bit load.
        auto *WordGep = dyn_cast<GEPOperator>(S->getPointerOperand()->stripPointerCasts());
        if (!WordGep || WordGep->getNumIndices() < 1)
          continue;
        unsigned wordBits = S->getValueOperand()->getType()->getIntegerBitWidth();
        if (!wordBits)
          continue;
        {
          Value *Ix = strip(WordGep->idx_begin()[WordGep->getNumIndices() - 1]);
          auto *Div = dyn_cast<BinaryOperator>(Ix);
          if (!Div || (Div->getOpcode() != Instruction::SDiv && Div->getOpcode() != Instruction::UDiv &&
                       Div->getOpcode() != Instruction::LShr))
            continue;
          auto *K = asConstInt(Div->getOperand(1));
          uint64_t d = K ? K->getZExtValue() : 0;
          if (!(Div->getOpcode() == Instruction::LShr ? (1ull << d) == wordBits : d == wordBits))
            continue;
          auto *L = dyn_cast<LoadInst>(strip(Div->getOperand(0)));
          auto *G2 = L ? dyn_cast<GEPOperator>(L->getPointerOperand()->stripPointerCasts()) : nullptr;
          if (!G2 || G2->getSourceElementType() != StTy || G2->getNumIndices() != BitGep->getNumIndices() ||
              !std::equal(G2->idx_begin() + 1, G2->idx_end(), BitGep->idx_begin() + 1))
            continue;
        }
        auto words = accessFields(*S, const_cast<Value *>(S->getPointerOperand()));
        if (words.empty())
          continue;
        // Every level the word lies in, with the array's base offset there.
        std::map<std::string, int64_t> baseOf;
        for (const auto &w : words) {
          auto [it, added] = baseOf.try_emplace(w.first, w.second);
          if (!added)
            it->second = std::min(it->second, w.second);
        }
        unsigned wordBytes = wordBits / 8;
        for (GlobalVariable &G : M->globals()) {
          if (!G.isConstant() || !G.hasInitializer())
            continue;
          auto *CA = dyn_cast<ConstantArray>(G.getInitializer());
          auto *CAgg = dyn_cast<ConstantAggregate>(G.getInitializer());
          unsigned n = 0;
          auto elem = [&](unsigned i) -> Constant * {
            if (CA)
              return CA->getOperand(i);
            return CAgg ? CAgg->getAggregateElement(i) : nullptr;
          };
          Type *elemTy = nullptr;
          if (CA) {
            n = CA->getNumOperands();
            elemTy = CA->getType()->getElementType();
          } else if (auto *CDS = dyn_cast<ConstantDataArray>(G.getInitializer())) {
            continue;
          } else if (CAgg && G.getValueType()->isArrayTy()) {
            n = G.getValueType()->getArrayNumElements();
            elemTy = G.getValueType()->getArrayElementType();
          } else
            continue;
          if (elemTy != StTy)
            continue;
          for (unsigned i = 0; i < n; ++i) {
            Constant *E = elem(i);
            if (!E)
              continue;
            Constant *TagC = E->getAggregateElement(0u);
            Constant *BitC = E->getAggregateElement(bitMember);
            auto *TagI = dyn_cast_or_null<ConstantInt>(TagC);
            auto *BitI = dyn_cast_or_null<ConstantInt>(BitC);
            if (!TagI || !BitI || TagI->getBitWidth() > 64 || BitI->getBitWidth() > 64)
              continue;
            int64_t tag = TagI->getSExtValue();
            uint64_t bit = BitI->getZExtValue();
            uint64_t mask = 1ull << (bit % wordBits);
            auto &vec = raisesOfTag[tag];
            for (const auto &[ty, base] : baseOf) {
              Field word{ty, base + (int64_t)((bit / wordBits) * wordBytes)};
              if (std::find(vec.begin(), vec.end(), std::make_pair(word, mask)) == vec.end())
                vec.push_back({word, mask});
            }
          }
        }
      }
    }
  }
}

std::vector<Client::Keyed> Client::keyedGatesAlong(const std::vector<std::string> &seq, Function *E) const {
  ensureTagSetters();
  const auto &tagSetters = tagSettersOf;
  std::vector<Keyed> out;
  auto add = [&](Keyed k, const std::string &op, int64_t v) {
    k.preds = {{op, v}};
    Function *Setter = body(k.fn);
    if (!Setter)
      return;
    auto sw = signature(Setter);
    auto aw = irParams(Setter);
    std::string T = heldType(E, 0);
    if (k.obj < aw.size() && aw[k.obj] >= 0 && !T.empty() && sw[aw[k.obj]].type == T)
      k.root = 0;
    else {
      auto sig = signature(E);
      for (size_t i = 0; i < sig.size(); ++i)
        if (held(sig[i]) && k.obj < aw.size() && aw[k.obj] >= 0 && sig[i].type == sw[aw[k.obj]].type) {
          k.root = (int)i;
          break;
        }
    }
    for (const Keyed &o : out)
      if (o.fn == k.fn && o.tag == k.tag && o.tagV == k.tagV && o.preds == k.preds)
        return;
    out.push_back(std::move(k));
  };
  for (const std::string &n : seq) {
    Function *F = body(n);
    if (!F)
      continue;
    for (Instruction &I : instructions(*F)) {
      auto *Cmp = dyn_cast<ICmpInst>(&I);
      // Only EQ: NE on the same field is the complementary branch and would
      // install an excluding key (e.g. JPEGCOLORMODE != RGB) that fights the
      // enabling one. The harness oneOf already allows skipping the setter.
      if (!Cmp || Cmp->getPredicate() != ICmpInst::ICMP_EQ)
        continue;
      for (int side = 0; side < 2; ++side) {
        Value *A = const_cast<Value *>(Cmp->getOperand((unsigned)side)->stripPointerCasts());
        while (auto *C = dyn_cast<CastInst>(A))
          A = const_cast<Value *>(C->getOperand(0)->stripPointerCasts());
        auto *L = dyn_cast<LoadInst>(A);
        auto *CI = dyn_cast<ConstantInt>(Cmp->getOperand(1u - (unsigned)side));
        if (!L || !CI || CI->getBitWidth() > 64)
          continue;
        int64_t v = CI->getSExtValue();
        for (const auto &f : accessFields(*L, const_cast<Value *>(L->getPointerOperand()))) {
          auto it = tagSetters.find(f);
          if (it == tagSetters.end())
            continue;
          for (const Keyed &base : it->second)
            add(base, "=", v);
        }
      }
    }
  }
  return out;
}

// §3.9 정의 E. The plan of the may sequence from starts to the line, if one
// is satisfiable and its plan passes. A query met again while it is being
// computed is a cycle and does not establish (least fixed point).
const Client::WitnessPlan *Client::established(const std::string &file, unsigned line,
                                               const std::vector<Function *> &starts) const {
  std::set<std::string> names;
  for (Function *F : starts)
    names.insert(F->getName().str());
  auto key = std::make_tuple(file, line, names);
  if (auto it = estOf.find(key); it != estOf.end())
    return it->second.get();
  if (!reach)
    return nullptr;
  if (auto b = estBusy.find(key); b != estBusy.end()) {
    estLow = std::min(estLow, b->second);
    return nullptr;
  }
  const int depth = estBusy.size();
  estBusy.emplace(key, depth);
  const int outer = estLow;
  estLow = INT_MAX;
  // 정의 E is existential over sequences: a sequence whose plan is open
  // does not refute the store, so the satisfiable sequences are taken in
  // cost order until one plan passes or the path budget runs out.
  std::unique_ptr<WitnessPlan> plan;
  for (int from = 0; !plan;) {
    std::string log = file + ":" + std::to_string(line);
    auto w = reach(file, line, names, from);
    if (!w || w->seq.empty()) {
      estLog.push_back(log + (from ? " : exhausted" : " : none"));
      break;
    }
    for (const std::string &n : w->seq)
      log += " " + n;
    if (Function *S = body(w->seq.front())) {
      plan = std::make_unique<WitnessPlan>(realize(S, w->phi, w->keyed, w->rets, true));
      std::string open;
      for (const auto *rs : {&plan->cells, &plan->returns})
        for (const Realized &r : *rs)
          if (r.how == Realize::Open)
            open += " " + r.cell.type + "+" + std::to_string(r.cell.off) + " " + r.cell.op + " " +
                    (r.cell.values.empty() ? "-" : r.cell.values[0]) + " [" + r.why + "]";
      log += plan->pass ? " : pass" : " : open" + open;
      if (!plan->pass)
        plan.reset();
      else
        plan->seq = w->seq;
    }
    estLog.push_back(log);
    if (w->index < from)
      break;
    from = w->index + 1;
  }
  estBusy.erase(key);
  const int low = estLow;
  estLow = std::min(outer, low);
  // A pass is monotone in the answers it assumed; a failure is final only
  // when every cycle it met closes at this query or deeper (its SCC root).
  if (!plan && low < depth)
    return nullptr;
  return (estOf[key] = std::move(plan)).get();
}

bool Client::mayStore(const std::vector<Function *> &fns, const Field &f) const {
  for (Function *R : fns) {
    if (!R)
      continue;
    for (Function *G : closureOf(R)) {
      if (auto it = stores.find(G); it != stores.end())
        if (auto s = it->second.lower_bound({f, ""}); s != it->second.end() && s->first == f)
          return true;
      if (auto it = ranges.find(G); it != ranges.end())
        for (const auto &[ty, off, len] : it->second)
          if (ty == f.first && off <= f.second && f.second - off < len)
            return true;
    }
  }
  return false;
}

// Construct: no function stores the field, or Definition E. Under Lemma E
// (no non-constant store, 0 does not satisfy) a store of S+ must run, so the
// cell is established only through the passing plan of a sequence reaching
// one. Otherwise the earlier inference: only U stores the field (정리 B(a)),
// or a store of S+ exists.
bool Client::establishedBy(Function *E, Function *entry, const Cell &c, const WitnessPlan *&via,
                           std::string &at) const {
  via = nullptr;
  Field f = fieldOf(c);
  const char *dbgEst = getenv("SP_DBG_EST");
  bool dbg = dbgEst && (f.first + "+" + std::to_string(f.second)).find(dbgEst) != std::string::npos;
  if (dbg)
    errs() << "DBG_EST " << f.first << "+" << f.second << " op " << c.op << " everStored "
           << everStored(f.first, f.second) << " upOnly " << upOnly(f) << " boundary " << c.boundary
           << " prefix " << c.prefix << " reach " << (bool)reach << "\n";
  if (!everStored(f.first, f.second))
    return true;
  // Λ3 (DESIGN §3.11): library-internal Construct is Definition E, not a
  // path-insensitive may-store in a producer's closure. A producer the
  // harness already calls may store φ_c only on some paths (e.g.
  // jinit_upsampler writes h2v2_upsample iff !do_fancy); treating that as
  // Construct skips the return constraints of the store and marks a
  // witness realized when execution installs a different method
  // (h2v2_fancy_upsample) that never reaches the sink. harnessStarts
  // already puts those producers in the establish scope below.
  bool up = upOnly(f);
  if (!entry)
    return false;
  // Entry state the library alone stores: φ_c must hold when the entry is
  // called, so only a call the harness makes before it (a producer or its
  // dependence, never the entry) can establish it, and only through a
  // passing sequence to a satisfying store. satisfies is exact on value
  // atoms only.
  const bool pre = !up && !(c.boundary || c.prefix);
  if (pre && c.op != "=" && c.op != "!=" && c.op != "has" && c.op != "lacks")
    return false;
  std::set<Field> fs{f};
  if (c.boundary)
    if (auto it = copies(entry).find(f); it != copies(entry).end())
      fs.insert(it->second.begin(), it->second.end());
  std::vector<Function *> starts = harnessStarts(E, entry, c);
  if (pre)
    starts.erase(std::remove(starts.begin(), starts.end(), entry), starts.end());
  if (starts.empty())
    return false;
  FnSet scope;
  for (Function *F : starts)
    scope.insert(closureOf(F).begin(), closureOf(F).end());
  bool nonConst = false, anySat = false;
  // S+ in the cost order of the sequences reaching it: the call distance
  // from the starts to the store's function, then position.
  std::map<Function *, unsigned> dist;
  {
    std::deque<Function *> q;
    for (Function *F : starts)
      if (dist.emplace(F, 0).second)
        q.push_back(F);
    while (!q.empty()) {
      Function *F = q.front();
      q.pop_front();
      if (auto it = calls.find(F); it != calls.end())
        for (Function *G : it->second)
          if (dist.emplace(G, dist.at(F) + 1).second)
            q.push_back(G);
    }
  }
  std::vector<std::tuple<unsigned, std::string, unsigned>> plus;
  auto touches = [&](Function *G) {
    if (auto it = stores.find(G); it != stores.end())
      for (const Field &d : fs)
        if (auto s = it->second.lower_bound({d, ""}); s != it->second.end() && s->first == d)
          return true;
    if (auto it = ranges.find(G); it != ranges.end())
      for (const auto &r : it->second)
        for (const Field &d : fs)
          if (std::get<0>(r) == d.first && std::get<1>(r) <= d.second &&
              d.second - std::get<1>(r) < std::get<2>(r))
            return true;
    return false;
  };
  for (size_t seen = 0; seen != fs.size();) {
    seen = fs.size();
    nonConst = anySat = false;
    plus.clear();
    for (Function *G : scope) {
      if (!touches(G))
        continue;
      for (Instruction &I : instructions(*G)) {
        bool hit = false;
        std::string v = "*";
        if (auto *S = dyn_cast<StoreInst>(&I)) {
          for (const Field &g : accessFields(*S, S->getPointerOperand()))
            hit = hit || fs.count(g);
          if (!hit)
            continue;
          std::set<Field> src = copySources(S);
          if (!src.empty()) {
            fs.insert(src.begin(), src.end());
            continue;
          }
          v = abstractValue(S->getValueOperand());
        } else if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
          auto *L = dyn_cast<ConstantInt>(MI->getLength());
          int64_t len = L && L->getBitWidth() <= 64 ? L->getSExtValue() : INT64_MAX;
          std::vector<std::tuple<std::string, int64_t, int64_t>> span;
          for (const Field &g : accessFields(*MI, MI->getRawDest()))
            span.push_back({g.first, g.second, len});
          if (span.empty())
            if (auto *MS = dyn_cast<MemSetInst>(MI))
              if (auto z = zeroFill(*MS))
                span.push_back(*z);
          for (const auto &[ty, off, n] : span)
            for (const Field &d : fs)
              hit = hit || (ty == d.first && off <= d.second && d.second - off < n);
          if (!hit)
            continue;
          auto *MS = dyn_cast<MemSetInst>(MI);
          auto *b = MS ? dyn_cast<ConstantInt>(MS->getValue()) : nullptr;
          v = b && b->isZero() ? "0" : "*";
        } else
          continue;
        const DebugLoc &dl = I.getDebugLoc();
        if (v == "*" || (satisfies(v, c) && !dl))
          nonConst = true; // a satisfying store with no position cannot be queried
        else if (satisfies(v, c)) {
          anySat = true;
          auto d = dist.find(G);
          plus.push_back({d == dist.end() ? ~0u : d->second, dl->getFilename().str(), dl.getLine()});
        }
      }
    }
  }
  // Definition E before the nonConst short-circuit. A field that also has
  // non-constant stores used to return here with Construct and no via plan,
  // dropping the path conditions of the constant store (including client
  // keyed setters that dominate it). Prefer a passing establish of S+ when
  // one exists; only then fall back to up/anySat.
  // Lemma E: when S+ is non-empty, Construct requires a passing establish
  // sequence to one of those stores. Falling back to anySat after every
  // sequence failed would mark unrealizable installers Construct (e.g.
  // jinit_merged when every path to its store is open).
  std::sort(plus.begin(), plus.end());
  plus.erase(std::unique(plus.begin(), plus.end()), plus.end());
  if (dbg) {
    errs() << "DBG_EST   fs " << fs.size() << " nonConst " << nonConst << " anySat " << anySat << " plus";
    for (const auto &[d, file, line] : plus)
      errs() << " " << file << ":" << line;
    errs() << " starts";
    for (Function *F : starts)
      errs() << " " << F->getName();
    errs() << "\n";
  }
  if (reach) {
    for (const auto &[d, file, line] : plus)
      if ((via = established(file, line, starts))) {
        at = file + ":" + std::to_string(line);
        return true;
      }
    if (!plus.empty())
      return false;
  }
  if (pre)
    return false;
  if (nonConst || satisfies("0", c) || !reach)
    return up || anySat;
  return false;
}

// File: F reads the input and stores an input value to the field, to a
// field copied into it transitively, or, for a bound, to the field the
// bound names.
bool Client::fills(Function *F, const Cell &c) const {
  if (!F || !opensFile(F))
    return false;
  const auto &cm = allCopies(F);
  std::set<Field> seen{fieldOf(c)};
  for (std::vector<Field> work{fieldOf(c)}; !work.empty();) {
    Field d = work.back();
    work.pop_back();
    if (storesInput(F, d))
      return true;
    if (auto it = cm.find(d); it != cm.end())
      for (const Field &s : it->second)
        if (seen.insert(s).second)
          work.push_back(s);
  }
  static const std::set<std::string> bound{"ult", "ule", "ugt", "uge", "slt", "sle",
                                           "sgt", "sge", "<",   ">",   "<=",  ">="};
  if (!bound.count(c.op) || c.values.empty())
    return false;
  const std::string &other = c.values.back();
  auto p = other.rfind('+');
  if (p == std::string::npos || p == 0)
    return false;
  auto o = asI64(other.substr(p + 1));
  return o && storesInput(F, {other.substr(0, p), *o});
}

// The call that fills the cell from the input: the entry, or a producer of
// the cell's held root or a call it depends on.
Function *Client::inputFiller(Function *E, Function *entry, const Cell &c) const {
  if (fills(entry, c))
    return entry;
  std::string T = heldType(E, c.root);
  auto pit = producers.find(T);
  if (pit == producers.end())
    return nullptr;
  for (const Producer &pr : pit->second) {
    if (fills(pr.fn, c))
      return pr.fn;
    for (Function *D : dependences(pr.fn, T))
      if (fills(D, c))
        return D;
  }
  return nullptr;
}

// 정의 R: the values F returns, each with the instruction that fixes it:
// the stores to a return slot only loads and stores use (-O0), otherwise
// the returned value, through phis and selects.
static std::vector<std::pair<Value *, Instruction *>> returnDefs(Function &F) {
  std::vector<std::pair<Value *, Instruction *>> out, work;
  std::set<std::pair<Value *, Instruction *>> seen;
  for (Instruction &I : instructions(F))
    if (auto *R = dyn_cast<ReturnInst>(&I))
      if (Value *v = R->getReturnValue())
        work.push_back({v, R});
  while (!work.empty()) {
    auto [v, at] = work.back();
    work.pop_back();
    if (!seen.insert({v, at}).second)
      continue;
    if (auto *P = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0; i < P->getNumIncomingValues(); ++i)
        work.push_back({P->getIncomingValue(i), P->getIncomingBlock(i)->getTerminator()});
      continue;
    }
    if (auto *S = dyn_cast<SelectInst>(v)) {
      work.push_back({S->getTrueValue(), S});
      work.push_back({S->getFalseValue(), S});
      continue;
    }
    if (auto *L = dyn_cast<LoadInst>(v))
      if (auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        std::vector<StoreInst *> st;
        bool local = true;
        for (User *U : A->users()) {
          if (auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == A)
            st.push_back(S);
          else if (!isa<LoadInst>(U) && !isa<DbgInfoIntrinsic>(U))
            local = false;
        }
        if (local) {
          for (StoreInst *S : st)
            work.push_back({S->getValueOperand(), S});
          continue;
        }
      }
    out.push_back({v, at});
  }
  return out;
}

// Whether the constant c meets `pred k` at c's width; none when k is not an
// integer or pred is not a comparison.
static std::optional<bool> retHolds(const APInt &c, const std::string &pred, const std::string &k) {
  int64_t kv = 0;
  if (std::from_chars(k.data(), k.data() + k.size(), kv).ec != std::errc())
    return std::nullopt;
  APInt K(c.getBitWidth(), (uint64_t)kv, true);
  if (pred == "==")
    return c.eq(K);
  if (pred == "!=")
    return c.ne(K);
  if (pred == "ugt")
    return c.ugt(K);
  if (pred == "uge")
    return c.uge(K);
  if (pred == "ult")
    return c.ult(K);
  if (pred == "ule")
    return c.ule(K);
  if (pred == "sgt")
    return c.sgt(K);
  if (pred == "sge")
    return c.sge(K);
  if (pred == "slt")
    return c.slt(K);
  if (pred == "sle")
    return c.sle(K);
  return std::nullopt;
}

// 정의 R: may decides the witness with each call result free, so the
// obligation `callee pred k` refines exactly that freedom: some execution
// of the callee returns a value meeting it. A constant definition can meet
// it exactly when it satisfies the predicate; a returned direct call's
// result passes the obligation on to that callee; any other value is not
// refuted by the definition alone. Each remaining definition is probed from
// the callee: 1 a satisfiable sequence reaches it, 0 every sequence was
// tried and none is satisfiable. The obligation is refuted (0) only when
// every definition is; a callee with no body, an unpositioned definition,
// or an exhausted budget leaves it unknown (-1), which does not refute.
int Client::returnedBy(const Ret &r, std::string &why, std::set<std::string> &busy) const {
  Function *C = body(r.callee);
  if (!C || C->isDeclaration())
    return -1;
  const std::string key = r.callee + " " + r.pred + " " + r.k;
  if (!busy.insert(key).second) {
    why = "cycle " + r.callee;
    return 0;
  }
  struct Def {
    int rank;
    std::string file;
    unsigned line;
    Function *next;
    bool operator<(const Def &o) const {
      return std::tie(rank, file, line, next) < std::tie(o.rank, o.file, o.line, o.next);
    }
  };
  std::set<Def> defs;
  bool unpositioned = false;
  for (auto [v, at] : returnDefs(*C)) {
    int rank = 2;
    Function *next = nullptr;
    if (auto *K = dyn_cast<ConstantInt>(v)) {
      if (auto h = retHolds(K->getValue(), r.pred, r.k); h && !*h)
        continue;
      rank = 0;
    } else if (isa<ConstantPointerNull>(v)) {
      if (auto h = retHolds(APInt(64, 0), r.pred, r.k); h && !*h)
        continue;
      rank = 0;
    } else if (auto *CB = dyn_cast<CallBase>(v)) {
      if (Function *G = CB->getCalledFunction(); G && !G->isIntrinsic() && CB->getType() == C->getReturnType()) {
        next = G;
        rank = 1;
      }
    }
    const DebugLoc &dl = at->getDebugLoc();
    if (!dl) {
      unpositioned = true;
      continue;
    }
    defs.insert({rank, dl->getFilename().str(), dl.getLine(), next});
  }
  int best = unpositioned ? -1 : 0;
  const std::set<std::string> from{C->getName().str()};
  for (const Def &d : defs) {
    int p = probeFrom ? probeFrom(d.file, d.line, from) : -1;
    if (p != 0 && d.next) {
      std::string w;
      int q = returnedBy({d.next->getName().str(), r.pred, r.k, r.callee, d.line}, w, busy);
      if (q == 0)
        why = w;
      p = q == 0 ? 0 : std::min(p, q);
    }
    // Disjunction over definitions in the order 0 < -1 < 1.
    if (p == 1 || (p == -1 && best == 0))
      best = p;
    if (best == 1)
      break;
  }
  if (best == 0 && why.empty())
    why = (defs.empty() ? "return-unsat " : "return-unreached ") + r.callee;
  busy.erase(key);
  return best;
}

Client::WitnessPlan Client::realize(Function *E, const std::vector<Cell> &phi, const std::vector<Keyed> &keyed,
                                    const std::vector<Ret> &rets, bool decide) const {
  WitnessPlan W;
  W.first = E;
  W.entries = entries(E);
  Function *entry = W.entries.empty() ? nullptr : W.entries[0];
  W.iface = entry && ifaceD.count(entry);
  if (decide && !W.iface)
    return W;
  W.direct = W.entries.size() == 1 && entry == E;
  std::vector<const Cell *> ob;
  for (const Cell &c : phi)
    if (!c.type.empty() && !c.op.empty() && !(c.crossing && !c.boundary && !c.prefix && !(W.direct && own(E, c))))
      ob.push_back(&c);
  // 정의 M: a call the plan adds before the entry must not leave an
  // obligation at a value its atom rejects.
  std::set<Function *> barred;
  auto admitted = [&](Function *F) {
    if (!F)
      return false;
    if (barred.count(F))
      return false;
    for (const Cell *c : ob)
      if (contradicts(F, *c)) {
        barred.insert(F);
        std::string got;
        if (const MustSummary *MS = mustOnReturn(F))
          got = MS->post.at(fieldOf(*c));
        W.excluded.push_back(F->getName().str() + " " + c->type + "+" + std::to_string(c->off) + " " + got);
        return false;
      }
    return true;
  };
  auto admittedWriters = [&](const Cell &c) {
    std::vector<Function *> out;
    for (Function *F : writeCandidates(E, W.entries, c))
      if (admitted(F))
        out.push_back(F);
    return out;
  };
  std::vector<Keyed> kw;
  for (const Keyed &k : keyed)
    if (realizable(E, k) && admitted(body(k.fn)))
      kw.push_back(k);
  // §3.8.5: a has/lacks cell on a bitfield word is discharged by the same
  // tag-dispatch Key that the constant registry maps to that mask.
  ensureRegistryRaises();
  auto addBitKeys = [&](const Cell &c) {
    // OR raises establish has, not lacks (they never clear bits).
    if (c.op != "has")
      return;
    auto m = c.values.empty() ? std::nullopt : asU64(c.values[0]);
    if (!m)
      return;
    Field f = fieldOf(c);
    for (const auto &[tag, raises] : raisesOfTag) {
      bool hit = false;
      for (const auto &[word, mask] : raises) {
        if (word != f)
          continue;
        // The tag raises `mask`; it discharges has m when mask covers m.
        if ((*m & mask) != *m)
          continue;
        hit = true;
        break;
      }
      if (!hit)
        continue;
      for (const auto &kv : tagSettersOf) {
        for (const Keyed &base : kv.second) {
          if (base.tagV != tag)
            continue;
          Keyed k = base;
          k.root = c.root;
          k.path = c.path;
          k.off = c.off;
          if (!realizable(E, k) || !admitted(body(k.fn)))
            continue;
          bool dup = false;
          for (const Keyed &o : kw)
            if (o.fn == k.fn && o.tag == k.tag && o.tagV == k.tagV && o.covers(c))
              dup = true;
          if (!dup)
            kw.push_back(std::move(k));
        }
      }
    }
  };
  for (const Cell &c : phi)
    addBitKeys(c);
  if (std::getenv("SP_DBG_BITS")) {
    size_t nr = 0;
    for (const auto &kv : raisesOfTag)
      nr += kv.second.size();
    errs() << "DBG_BITS raises " << raisesOfTag.size() << " tags " << nr << " words, keyed " << kw.size() << "\n";
    for (const Cell &c : phi)
      if (c.op == "has")
        for (const auto &[tag, rs] : raisesOfTag)
          for (const auto &[w, m] : rs)
            if (w == fieldOf(c))
              errs() << "DBG_BITS   " << c.type << "+" << c.off << " has " << (c.values.empty() ? "-" : c.values[0])
                     << " <- tag " << tag << " mask " << m << " setters "
                     << std::count_if(tagSettersOf.begin(), tagSettersOf.end(), [&](const auto &kv) {
                          return std::any_of(kv.second.begin(), kv.second.end(),
                                             [&](const Keyed &k) { return k.tagV == tag; });
                        })
                     << "\n";
  }
  auto valueAtom = [](const Cell &c) { return c.op == "=" || c.op == "!=" || c.op == "has" || c.op == "lacks"; };
  std::map<size_t, std::vector<Function *>> cand;
  std::map<size_t, std::pair<const WitnessPlan *, std::string>> vias;
  auto addKeyed = [&](Function *F, const Keyed &k) {
    for (const auto &[G, o] : W.keyed)
      if (G == F && o.tag == k.tag && o.tagV == k.tagV && o.preds == k.preds)
        return;
    W.keyed.push_back({F, k});
  };
  // 정의 M: Key select that only excludes (≠, lacks) yields to File.
  auto excludesOnly = [](const Keyed &x) {
    if (!x.va || x.preds.empty())
      return false;
    for (const auto &[op, _] : x.preds)
      if (op != "!=" && op != "lacks")
        return false;
    return true;
  };
  for (const Cell &c : phi) {
    if (c.type.empty() || c.op.empty())
      continue;
    bool mine = W.direct && own(E, c);
    std::vector<std::pair<Function *, Lever>> lv;
    if (!mine)
      lv = leversOf(E, c);
    W.levers.insert(W.levers.end(), lv.begin(), lv.end());
    if (c.crossing && !c.boundary && !c.prefix && !mine)
      continue;
    Guard g;
    if (W.direct && !c.file && guardOf(E, c, g, mine))
      W.guards.push_back(g);
    if (mine && c.file)
      W.files.push_back(c);
    Realized r{c};
    std::string at;
    const Keyed *k = nullptr;
    for (const Keyed &x : kw)
      if (!k && x.covers(c))
        k = &x;
    std::vector<Function *> wr;
    Function *fileBy = (!c.file && (c.boundary || c.prefix)) ? inputFiller(E, entry, c) : nullptr;
    if (mine) {
      r.how = Realize::Own;
    } else if (!lv.empty()) {
      r.how = Realize::Lever;
      r.by = lv.front().first;
    } else if (k && !(excludesOnly(*k) && fileBy)) {
      r.how = Realize::Key;
      r.by = body(k->fn);
      addKeyed(r.by, *k);
    } else if (valueAtom(c) && !(wr = admittedWriters(c)).empty()) {
      r.how = Realize::Write;
      cand[W.cells.size()] = wr;
    } else if (const WitnessPlan *via = nullptr; !c.file && establishedBy(E, entry, c, via, at)) {
      r.how = Realize::Construct;
      if (via) {
        vias[W.cells.size()] = {via, c.type + "+" + std::to_string(c.off) + " at " + at};
        r.by = body(via->seq.back());
      }
    } else if (fileBy) {
      r.how = Realize::File;
      r.by = fileBy;
    } else if (k) {
      r.how = Realize::Key;
      r.by = body(k->fn);
      addKeyed(r.by, *k);
    }
    if (r.how == Realize::Open)
      r.why = "no-route";
    W.cells.push_back(r);
    if (decide && r.how == Realize::Open)
      return W;
  }
  std::set<std::tuple<std::string, std::string, std::string, unsigned>> seenRet;
  for (const Ret &rt : rets) {
    if (!seenRet.insert({rt.callee, rt.pred, rt.k, rt.line}).second)
      continue;
    Cell c;
    c.type = "return " + rt.callee;
    c.off = rt.line;
    c.op = rt.pred;
    c.values = {rt.k};
    c.text = rt.caller;
    Realized r{c};
    const std::string key = rt.callee + " " + rt.pred + " " + rt.k;
    auto it = retOf.find(key);
    if (it == retOf.end()) {
      std::set<std::string> busy;
      std::string why;
      int g = returnedBy(rt, why, busy);
      it = retOf.emplace(key, std::make_pair(g, why)).first;
    }
    int got = it->second.first;
    r.why = it->second.second;
    if (got != 0) {
      r.how = Realize::Construct;
      r.by = body(rt.callee);
      r.why = got == 1 ? "" : "unknown";
    }
    W.returns.push_back(r);
    if (decide && r.how == Realize::Open)
      return W;
  }
  // Greedy set cover of the Write cells by at most writerSlots functions,
  // the writer calls the §4 grammar makes before the entry.
  auto covers = [&](size_t i, Function *F) { return std::find(cand[i].begin(), cand[i].end(), F) != cand[i].end(); };
  std::vector<size_t> left;
  FnSet pool;
  for (const auto &[i, wr] : cand) {
    left.push_back(i);
    pool.insert(wr.begin(), wr.end());
  }
  while (!left.empty() && W.cover.size() < writerSlots) {
    Function *best = nullptr;
    size_t got = 0;
    for (Function *F : pool) {
      size_t n = std::count_if(left.begin(), left.end(), [&](size_t i) { return covers(i, F); });
      if (n > got) {
        got = n;
        best = F;
      }
    }
    if (!best)
      break;
    W.cover.push_back(best);
    pool.erase(best);
    std::vector<size_t> rest;
    for (size_t i : left)
      if (covers(i, best))
        W.cells[i].by = best;
      else
        rest.push_back(i);
    left.swap(rest);
  }
  for (size_t i : left) {
    W.cells[i].how = Realize::Open;
    W.cells[i].why = "writer-slots";
  }
  // 정의 E: a cell a store establishes brings the calls the reaching
  // sequence's plan realizes; the merged cover stays within the K slots.
  // A via plan that reaches S+ under a φ incompatible with this witness
  // (same field, conflicting atoms) does not establish — otherwise exclusive
  // library branches (e.g. fancy=0 only on raw, jinit_merged only on !raw)
  // would each pass in isolation and wrongly Compose as Construct.
  // The via runs before the witness: its atoms hold before it, the
  // witness's after it. Two atoms on one field must hold together only when
  // the field keeps its value across the via (frame rule), so a conflict
  // refutes the composition only when nothing the via runs may store it.
  auto cellClash = [&](const Cell &a, const Cell &b) {
    if (a.type != b.type || a.off != b.off)
      return false;
    if (a.op == "=" && b.op == "=") {
      for (const std::string &v : a.values)
        if (satisfies(v, b))
          return false;
      return !a.values.empty() && !b.values.empty();
    }
    if (a.op == "=" && b.op == "!=") {
      for (const std::string &v : a.values)
        if (satisfies(v, b))
          return false;
      return !a.values.empty();
    }
    if (a.op == "!=" && b.op == "=") {
      for (const std::string &v : b.values)
        if (satisfies(v, a))
          return false;
      return !b.values.empty();
    }
    return false;
  };
  auto compose = [&](Realized &target, const WitnessPlan *via, const std::string &where) {
    std::vector<Function *> runs = via->cover;
    for (const std::string &n : via->seq)
      runs.push_back(body(n));
    for (const auto &kf : via->keyed)
      runs.push_back(kf.first);
    bool clash = false;
    std::string clashWith;
    for (const Realized &vr : via->cells)
      for (const Realized &wr : W.cells)
        if (!clash && cellClash(vr.cell, wr.cell) && !mayStore(runs, fieldOf(vr.cell))) {
          clash = true;
          clashWith = vr.cell.type + "+" + std::to_string(vr.cell.off) + " " + vr.cell.op;
        }
    if (clash) {
      target.how = Realize::Open;
      target.why = "clash " + where + " " + clashWith;
      return false;
    }
    std::vector<Function *> cover = W.cover;
    for (Function *F : via->cover)
      if (std::find(cover.begin(), cover.end(), F) == cover.end())
        cover.push_back(F);
    if (cover.size() > writerSlots) {
      target.how = Realize::Open;
      target.why = "via-slots " + where + " " + std::to_string(cover.size());
      return false;
    }
    W.cover = cover;
    for (const auto &[F, k] : via->keyed)
      addKeyed(F, k);
    // Φ_pre / 정의 3.8.4: may can leave a keyed-only field out of residual φ
    // when both sides of a branch still reach the goal (so the branch is not
    // a sequence condition). The establish sequence still loads and tests
    // that field; expose the matching key setter so the harness can set it.
    for (const Keyed &k : keyedGatesAlong(via->seq, E))
      if (realizable(E, k) && admitted(body(k.fn)))
        addKeyed(body(k.fn), k);
    W.levers.insert(W.levers.end(), via->levers.begin(), via->levers.end());
    std::string line = where + " via";
    for (const std::string &n : via->seq)
      line += " " + n;
    W.established.push_back(line);
    W.established.insert(W.established.end(), via->established.begin(), via->established.end());
    return true;
  };
  for (const auto &[i, v] : vias)
    compose(W.cells[i], v.first, v.second);
  W.pass = W.iface;
  for (const auto *rs : {&W.cells, &W.returns})
    for (const Realized &r : *rs)
      W.pass = W.pass && r.how != Realize::Open;
  return W;
}

// The client for a set of may witnesses. The sink is reachable when one of
// them is, so the plan is the union of their steering and of the calls that
// realize the witnesses that pass.
Client::Plan Client::plan(const Witnesses &ws) const {
  Plan P;
  FnSet entrySet, unguarded, writerSet;
  for (size_t wi = 0; wi < ws.size(); ++wi) {
    const auto &[seq, phi] = ws[wi];
    Function *E = seq.empty() ? nullptr : body(seq.front());
    if (!E)
      continue;
    WitnessPlan W = realize(E, phi, wi < keyedIn.size() ? keyedIn[wi] : std::vector<Keyed>{},
                            wi < retsIn.size() ? retsIn[wi] : std::vector<Ret>{});
    if (std::find(P.firsts.begin(), P.firsts.end(), E) == P.firsts.end())
      P.firsts.push_back(E);
    for (Function *F : W.entries)
      if (entrySet.insert(F).second)
        P.entries.push_back(F);
    // The witness's arguments are the entry's only when it starts there.
    if (W.direct)
      P.guards[E].push_back(W.guards);
    else
      unguarded.insert(W.entries.begin(), W.entries.end());
    for (const auto &[F, l] : W.levers) {
      auto &ls = P.levers[F];
      bool dup = false;
      for (const Lever &o : ls)
        dup = dup || (o.formal == l.formal && o.text == l.text);
      if (!dup)
        ls.push_back(l);
    }
    // File name cells install on the callable entry main calls (§4), which
    // is an elevated E when π₀ itself is not callable — not on π₀ alone.
    for (Function *F : W.entries)
      for (const Cell &c : W.files) {
        auto &fs = P.files[F];
        bool dup = false;
        for (const Cell &d : fs)
          dup = dup || d.text == c.text;
        if (!dup)
          fs.push_back(c);
      }
    // Definition 3.8.6: a setting is the client's own choice, like a lever,
    // at every entry that receives the object the lookup reads.
    for (const Named &n : named(seq))
      for (Function *F : W.entries) {
        auto sf = signature(F);
        if (std::none_of(sf.begin(), sf.end(), [&](const Param &p) { return held(p) && p.type == n.type; }))
          continue;
        auto &ns = P.named[F];
        if (std::none_of(ns.begin(), ns.end(), [&](const Named &o) { return o.setter == n.setter && o.key == n.key; }))
          ns.push_back(n);
      }
    if (W.pass) {
      writerSet.insert(W.cover.begin(), W.cover.end());
      // Key setters likewise bind to the elevated callable entry, so the
      // harness that calls that entry installs them before the call.
      for (Function *Ent : W.entries) {
        auto &ks = P.keyed[Ent];
        for (const auto &[F, k] : W.keyed) {
          bool dup = false;
          for (const auto &[G, o] : ks)
            dup = dup || (G == F && o.tag == k.tag && o.tagV == k.tagV && o.preds == k.preds);
          if (!dup)
            ks.push_back({F, k});
        }
        if (ks.empty())
          P.keyed.erase(Ent);
      }
    }
    P.witnesses.push_back(std::move(W));
  }
  // A witness that starts elsewhere constrains nothing at this entry: it is
  // an alternative with no configuration and no guard.
  for (Function *F : unguarded)
    if (P.guards.count(F))
      P.guards[F].push_back({});
  for (auto it = P.guards.begin(); it != P.guards.end();) {
    std::set<std::vector<std::tuple<int, int64_t, unsigned, bool, std::vector<int64_t>, bool>>> seen;
    std::vector<std::vector<Guard>> distinct;
    bool any = false;
    for (const auto &conj : it->second) {
      std::vector<std::tuple<int, int64_t, unsigned, bool, std::vector<int64_t>, bool>> key;
      for (const Guard &g : conj)
        key.emplace_back(g.root, g.off, g.width, g.eq, g.values, g.config);
      std::sort(key.begin(), key.end());
      if (seen.insert(key).second)
        distinct.push_back(conj);
      any = any || !conj.empty();
    }
    it->second = distinct;
    it = any ? std::next(it) : P.guards.erase(it);
  }
  P.writers.assign(writerSet.begin(), writerSet.end());
  grammar(P);
  dispatch(ws, P);
  // §5 / P2: realized ⇔ entryCallable E exists (pass.iface) ∧ cell opens 0
  // (pass) ∧ dispatch opens 0 ∧ the plan is not a vacuous elevation.
  // A π₀ that is only null-callable elevates; if that E installs nothing
  // (no cell, file, lever, key, or named), counting it as pass soft-accepts.
  // Direct starts with zero client cells remain realized when dispatch is closed
  // ("의무 없음" at a real entry). Elevated vacuous plans stay unrealized.
  for (WitnessPlan &W : P.witnesses) {
    bool install = !W.cells.empty() || !W.files.empty() || !W.levers.empty() || !W.keyed.empty();
    for (Function *F : W.entries) {
      auto nit = P.named.find(F);
      if (nit != P.named.end() && !nit->second.empty())
        install = true;
    }
    W.realized = W.pass && W.dispatchOpen == 0 && (W.direct || install);
  }
  return P;
}

// The nonterminals the entries, writers and key setters demand: their held
// inputs, closed under the held inputs of every producer and of the calls
// it depends on. One execution expands only the producers it picks.
void Client::grammar(Plan &P) const {
  std::set<std::string> need;
  auto want = [&](Function *F) {
    for (const Param &p : signature(F))
      if (held(p) && cost.count(p.type))
        need.insert(p.type);
  };
  auto wantType = [&](std::string t) {
    if (t.rfind("struct.", 0) == 0)
      t = t.substr(7);
    else if (t.rfind("class.", 0) == 0)
      t = t.substr(6);
    if (cost.count(t) && producers.count(t))
      need.insert(t);
  };
  for (Function *F : P.entries)
    want(F);
  for (Function *F : P.writers)
    want(F);
  for (const auto &[E, ks] : P.keyed)
    for (const auto &[W, k] : ks)
      want(W);
  for (const auto &[E, ns] : P.named)
    for (const Named &n : ns)
      want(n.setter);
  // Nested held objects φ names under an entry argument (e.g. CustomStreamInfo
  // under ImageInfo) are not entry formals, but the harness must still make them.
  for (const WitnessPlan &W : P.witnesses)
    for (const Realized &r : W.cells)
      wantType(r.cell.type);
  for (std::vector<std::string> work(need.begin(), need.end()); !work.empty();) {
    std::string T = work.back();
    work.pop_back();
    auto it = producers.find(T);
    if (it == producers.end())
      continue;
    for (const Producer &pr : it->second) {
      std::vector<Function *> fs{pr.fn};
      auto ds = dependences(pr.fn, T);
      if (!ds.empty())
        P.deps[{pr.fn, T}] = ds;
      fs.insert(fs.end(), ds.begin(), ds.end());
      for (Function *F : fs)
        for (const Param &p : signature(F))
          if (held(p) && cost.count(p.type) && need.insert(p.type).second)
            work.push_back(p.type);
    }
  }
  std::vector<std::string> order(need.begin(), need.end());
  std::sort(order.begin(), order.end(), [&](const std::string &a, const std::string &b) {
    unsigned ca = cost.count(a) ? cost.at(a) : ~0u, cb = cost.count(b) ? cost.at(b) : ~0u;
    return ca != cb ? ca < cb : a < b;
  });
  for (const std::string &T : order) {
    auto it = producers.find(T);
    P.handles.push_back({T, it == producers.end() ? std::vector<Producer>{} : it->second});
  }
}

// §3.7 / P1 gate: which indirect edges of seq Definition D leaves open when
// the plan is the empty-φ plan at seq[0] (producers of the entry, no writers).
std::vector<std::pair<std::string, std::string>> Client::openDispatchEdges(const std::vector<std::string> &seq) const {
  if (seq.empty())
    return {};
  Plan P = plan({{seq, {}}});
  std::vector<std::pair<std::string, std::string>> open;
  for (const std::string &line : P.obligations) {
    if (line.find(" OPEN") == std::string::npos || line.rfind("  D ", 0) != 0)
      continue;
    // "  D A -> B st N OPEN" or "  D A -> B st N OPEN ..."
    std::string rest = line.substr(4);
    auto arrow = rest.find(" -> ");
    auto st = rest.find(" st ");
    if (arrow == std::string::npos || st == std::string::npos || arrow >= st)
      continue;
    bool refuted = line.find(" OPEN refuted") != std::string::npos;
    open.emplace_back(refuted ? std::string() : rest.substr(0, arrow), rest.substr(arrow + 4, st - arrow - 4));
  }
  return open;
}

bool Client::installRefuted(Function *T, const std::set<std::string> &starts) const {
  if (!probe || !T)
    return false;
  auto key = std::make_pair(T->getName().str(), starts);
  if (auto it = refutedOf.find(key); it != refutedOf.end())
    return it->second;
  bool &out = refutedOf[key];
  out = false;
  // Every use of T's address other than a call of it must be a store with a
  // position; any other use (a table, an argument) installs T by a route
  // the store queries do not cover.
  std::set<std::pair<std::string, unsigned>> at;
  for (Module *M : {&down, &up}) {
    Function *G = M->getFunction(T->getName());
    if (!G)
      continue;
    std::vector<const User *> work(G->user_begin(), G->user_end());
    std::set<const User *> seen;
    while (!work.empty()) {
      const User *U = work.back();
      work.pop_back();
      if (!seen.insert(U).second)
        continue;
      if (auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand()->stripPointerCasts() == G)
        continue;
      if (auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand()->stripPointerCasts() == G) {
        const DebugLoc &dl = S->getDebugLoc();
        if (!dl)
          return false;
        at.insert({dl->getFilename().str(), dl.getLine()});
        continue;
      }
      if (auto *CE = dyn_cast<ConstantExpr>(U); CE && CE->isCast()) {
        work.insert(work.end(), CE->user_begin(), CE->user_end());
        continue;
      }
      return false;
    }
  }
  if (at.empty())
    return false;
  for (const auto &[file, line] : at)
    if (int r = probe(file, line, starts); r != 0) {
      estLog.push_back("install " + T->getName().str() + " at " + file + ":" + std::to_string(line) +
                       (r > 0 ? " reachable" : " unknown") + " from " + std::to_string(starts.size()));
      return false;
    }
  estLog.push_back("refuted " + T->getName().str() + " stores " + std::to_string(at.size()));
  return out = true;
}

// §2.4 Key and §3.7: an edge a -> b of a witness is indirect when a has no
// call of b. Definition D realizes its dispatch by a key (1), by a call of
// the harness installing b while the harness reads the input (2), or by a
// writer or key setter the harness calls installing it (3). Each of these
// only installs b if one of b's installing stores can run: when every
// sequence from the harness calls to each of them is unsatisfiable, the
// edge is open whatever closure contains the installer.
void Client::dispatch(const Witnesses &ws, Plan &P) const {
  FnSet made, setters(P.writers.begin(), P.writers.end());
  for (const auto &h : P.handles)
    for (const Producer &pr : h.second)
      made.insert(pr.fn);
  for (const auto &[k, ds] : P.deps)
    made.insert(ds.begin(), ds.end());
  for (const auto &[E, ks] : P.keyed)
    for (const auto &[W, k] : ks)
      setters.insert(W);
  std::set<std::string> keySeen;
  // P.witnesses holds one plan per witness plan() did not skip, in ws order;
  // plan() skips exactly the witnesses with no first function.
  size_t wpi = 0;
  for (const auto &[seq, phi] : ws) {
    Function *E = seq.empty() ? nullptr : body(seq[0]);
    FnSet called = made;
    if (E)
      called.insert(E);
    bool file = false;
    for (Function *H : called)
      file = file || opensFile(H);
    std::vector<std::string> notes;
    // Π_I (DESIGN-D): mark every installer on the witness's *first*
    // input-dispatch edge (`input:F`) that carries a choice (below).
    // Do not shrink to later edges' smaller
    // St sets — those are nested inits (jinit_*) that never appear in a keyed
    // dispatch table, so gateKeys stays empty and the codec init on the first
    // edge (TIFFInitJPEGCommon / RegisterTIFFImage) is never approached as T_st.
    // Marking the whole first-edge St is intentional: any one of them opens the
    // gate; picking a singleton by set size made the choice order-dependent
    // (HEIF) and dropped the table-keyed installer (libtiff JPEG).
    std::vector<std::set<std::string>> inputGates;
    unsigned indirect = 0, open = 0;
    for (size_t i = 0; i + 1 < seq.size(); ++i) {
      Function *A = body(seq[i]), *T = body(seq[i + 1]);
      if (!A || !T)
        continue;
      bool direct = false;
      for (Instruction &I : instructions(*A))
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts()))
            direct = direct || C->getName() == T->getName();
      if (direct)
        continue;
      ++indirect;
      // The targets an indirect site of A that may call T may call. One
      // target that several installers all install is no choice: a method
      // every subclass inherits has every subclass constructor in St. A sole
      // installer of a sole target is still a step the input must take.
      std::set<std::string> choices;
      for (Instruction &I : instructions(*A))
        if (auto *CB = dyn_cast<CallBase>(&I); CB && klee::calls::indirect(*CB)) {
          const auto &tg = targets.of(*CB);
          if (std::any_of(tg.begin(), tg.end(), [&](Function *G) { return G->getName() == T->getName(); }))
            for (Function *G : tg)
              choices.insert(G->getName().str());
        }
      std::vector<std::string> ks = keysOf(T);
      for (const std::string &k : ks)
        if (P.keys.size() < 16 && keySeen.insert(k).second)
          P.keys.push_back(k);
      FnSet St = installers(T);
      std::string how;
      if (!ks.empty() && file)
        how += " key";
      if (file) {
        std::set<std::string> by;
        for (Function *H : called)
          for (Function *G : St)
            if (closureOf(H).count(G))
              by.insert(G->getName().str());
        for (const std::string &g : by)
          how += " input:" + g;
        if (!by.empty() && !(choices.size() == 1 && St.size() > 1))
          inputGates.push_back(std::move(by));
      }
      for (Function *W : setters) {
        bool by = false;
        for (Function *G : St)
          by = by || closureOf(W).count(G) > 0;
        if (by) {
          how += " writer:" + W->getName().str();
          break;
        }
      }
      bool refuted = false;
      if (!how.empty() && probe) {
        std::set<std::string> sn;
        for (Function *H : called)
          sn.insert(H->getName().str());
        for (Function *W : setters)
          sn.insert(W->getName().str());
        refuted = installRefuted(T, sn);
        if (refuted)
          how.clear();
      }
      open += how.empty();
      notes.push_back("  D " + A->getName().str() + " -> " + T->getName().str() + " st " +
                      std::to_string(St.size()) + " tg " + std::to_string(choices.size()) +
                      (how.empty() ? (refuted ? " OPEN refuted" : " OPEN") : how));
    }
    std::set<std::string> gate;
    if (!inputGates.empty())
      gate.insert(inputGates[0].begin(), inputGates[0].end());
    for (const std::string &g : gate)
      if (std::find(P.stInstallers.begin(), P.stInstallers.end(), g) == P.stInstallers.end())
        P.stInstallers.push_back(g);
    P.obligations.push_back("obligations " + (seq.empty() ? std::string("-") : seq[0]) + " edges " +
                            std::to_string(seq.empty() ? 0 : seq.size() - 1) + " indirect " +
                            std::to_string(indirect) + " open " + std::to_string(open) + " file " +
                            std::to_string(file ? 1 : 0));
    P.obligations.insert(P.obligations.end(), notes.begin(), notes.end());
    // Realization (W.realized) is decided in plan() after named/files bind.
    if (E && wpi < P.witnesses.size())
      P.witnesses[wpi++].dispatchOpen = open;
  }
}

void Client::report(const Plan &P, raw_ostream &out) const {
  out << "interface D " << ifaceD.size() << " U " << ifaceU.size() << " headers " << headers.size() << "\n";
  out << "producible";
  for (const auto &kv : cost)
    out << " " << kv.first << ":" << kv.second;
  out << "\n";
  auto sig = [&](Function *F) {
    std::string s;
    for (const Param &p : signature(F)) {
      s += s.empty() ? "" : ",";
      s += kindName(p.kind);
      if (!p.type.empty())
        s += ":" + p.type;
    }
    return s;
  };
  for (Function *F : P.firsts) {
    out << "first " << F->getName() << " iface " << ifaceD.count(F) << " callable " << callable(F)
        << " entry-callable " << entryCallable(F) << " (" << sig(F) << ")";
    const auto &ps = signature(F);
    auto at = irParams(F);
    for (unsigned i = 0; i < at.size(); ++i)
      if (at[i] >= 0 && held(ps[at[i]]) && !cost.count(ps[at[i]].type))
        out << " unproducible " << at[i] << ":" << ps[at[i]].type << (nullTested(F, i) ? "(null)" : "");
    out << "\n";
  }
  for (const auto &[F, disj] : P.guards)
    for (size_t w = 0; w < disj.size(); ++w)
      for (const Guard &g : disj[w])
        out << (g.config ? "config " : "guard ") << F->getName() << " witness " << w << " arg" << g.root << "+"
            << g.off << " i" << g.width << (g.eq ? " = " : " != ") << g.values[0] << (g.values.size() > 1 ? " ..." : "")
            << "\n";
  for (const auto &[k, ds] : P.deps) {
    out << "depend " << k.first->getName() << " " << k.second << " " << ds.size() << ":";
    for (size_t i = 0; i < ds.size(); ++i)
      out << " " << ds[i]->getName();
    out << "\n";
  }
  for (const auto &[F, cs] : P.files)
    for (const Cell &c : cs)
      out << "file " << F->getName() << " " << c.type << "+" << c.off << "\n";
  for (const std::string &k : P.keys)
    out << "key " << k << "\n";
  for (Function *F : P.entries)
    out << "entry " << F->getName() << " (" << sig(F) << ")\n";
  for (const auto &h : P.handles) {
    out << "handle " << h.first << " cost " << (cost.count(h.first) ? std::to_string(cost.at(h.first)) : "-")
        << " producers " << h.second.size() << "\n";
    for (size_t i = 0; i < h.second.size() && i < 6; ++i)
      out << "  make " << h.second[i].fn->getName() << (h.second[i].out >= 0 ? " out " + std::to_string(h.second[i].out) : "")
          << " (" << sig(h.second[i].fn) << ")\n";
  }
  out << "writers " << P.writers.size();
  for (Function *W : P.writers)
    out << " " << W->getName();
  out << "\n";
  for (const auto &[W, ls] : P.levers)
    for (const Lever &l : ls) {
      out << "lever " << W->getName() << " arg" << l.formal << " " << (l.eq ? "=" : "!=");
      for (int64_t v : l.values)
        out << " " << v;
      out << " : " << l.text << "\n";
    }
  for (const auto &[E, ks] : P.keyed)
    for (const auto &[W, k] : ks) {
      out << "keyed " << E->getName() << " " << W->getName() << " obj " << k.obj;
      if (k.tag >= 0)
        out << " tag arg" << k.tag << " = " << k.tagV;
      for (const auto &[op, v] : k.preds)
        out << " va " << op << " " << v;
      out << " : " << k.target << "\n";
    }
  for (const auto &[E, ns] : P.named)
    for (const Named &n : ns)
      out << "named " << E->getName() << " " << n.setter->getName() << " obj " << n.obj << " \"" << n.key
          << "\" value arg" << n.value << "\n";
  for (const WitnessPlan &W : P.witnesses) {
    std::map<Realize, unsigned> n;
    for (const Realized &r : W.cells)
      ++n[r.how];
    out << "witness " << W.first->getName() << " " << (W.realized ? "realized" : W.pass ? "pass" : "open")
        << " iface " << W.iface << " dispatch-open " << W.dispatchOpen;
    for (Realize r : {Realize::Own, Realize::Lever, Realize::Key, Realize::Write, Realize::Construct, Realize::File,
                      Realize::Open})
      out << " " << realizeName(r) << " " << n[r];
    out << " cover";
    for (Function *F : W.cover)
      out << " " << F->getName();
    out << "\n";
    for (const Realized &r : W.cells)
      out << "  cell " << r.cell.type << "+" << r.cell.off << " " << r.cell.op << " "
          << (r.cell.values.empty() ? "-" : r.cell.values[0]) << " " << realizeName(r.how)
          << (r.by ? " " + r.by->getName().str() : "") << (r.how == Realize::Open ? " [" + r.why + "]" : "")
          << "\n";
    for (const Realized &r : W.returns)
      out << "  " << r.cell.type << " " << r.cell.op << " " << r.cell.values[0] << " at " << r.cell.text << " line "
          << r.cell.off << " " << realizeName(r.how) << (r.by ? " " + r.by->getName().str() : "")
          << (r.why.empty() ? "" : " [" + r.why + "]") << "\n";
    for (const std::string &e : W.established)
      out << "  established " << e << "\n";
    for (const std::string &e : W.excluded)
      out << "  excluded " << e << "\n";
  }
  out << "realized " << std::count_if(P.witnesses.begin(), P.witnesses.end(), [](const WitnessPlan &W) { return W.realized; })
      << " of " << P.witnesses.size() << "\n";
  for (const std::string &o : P.obligations)
    out << o << "\n";
  out << "establish " << estLog.size() << "\n";
  for (const std::string &e : estLog)
    out << "establish " << e << "\n";
  out << "st-installers " << P.stInstallers.size() << "\n";
  for (const std::string &n : P.stInstallers)
    out << "st-installer " << n << "\n";
  out << "null-fields " << nullFields.size() << " unguarded-calls " << unguardedCalls.size() << "\n";
}

// ---------------------------------------------------------------------------
// The harness: main() of one client.
//
//   writers  K calls, each a symbolic choice of skip or one writer;
//   entry    a symbolic choice among the entries.
//
// The client grammar has one nonterminal per held type T and one
// production per admissible producer of T, whose held inputs are its
// nonterminals. Choosing a producer is an or-node; obtaining its inputs is an
// and-node. A call obtains each held input from make_T, which returns the
// handle the client already holds, and otherwise expands T: it picks one
// producer symbolically, obtains that producer's inputs, and calls it. Only
// the producers a path picks are expanded, so a type no picked producer
// takes is never made. Inputs are strictly cheaper than the output, so the
// expansion is well-founded. A client continues only once a construction
// succeeded, so the assumption that the handle is not null sits after the
// producer it guards.
//
// Arguments follow the parameter's kind. A held input comes from make_T. Other public objects
// are client allocations of the struct's size whose constrained fields
// are symbolic. Integers and floats are symbolic. Text is a symbolic
// string. A byte buffer is n symbolic bytes, and an integer right after it
// is its length, at most n. A callback is a function of the harness: given
// a buffer and a length it delivers the next bytes of an n-byte symbolic
// input and returns their count; otherwise it returns a symbolic value. An
// out-parameter is a slot the call fills. The file "f" of the environment
// holds the same n bytes (FileEnv), so every byte the library reads, from
// an argument, a callback, or the file, is the client's choice.

namespace {

struct Builder {
  Module &H;
  LLVMContext &ctx;
  const DataLayout &dl;
  // Bounds of the client search (small scope): input bytes, text length.
  uint64_t n;
  unsigned textBound;
  FunctionCallee mkSym, silentExit, mallocF, memcpyF;
  GlobalVariable *data = nullptr, *cursor = nullptr;
  unsigned names = 0;
  std::map<std::tuple<FunctionType *, const void *, const void *>, Function *> callbacks;

  Builder(Module &H, const DataLayout &dl, uint64_t n, unsigned L)
      : H(H), ctx(H.getContext()), dl(dl), n(n ? n : 1), textBound(L) {
    auto *p0 = PointerType::get(ctx, 0);
    auto *i64 = Type::getInt64Ty(ctx);
    mkSym = H.getOrInsertFunction("klee_make_symbolic", FunctionType::get(Type::getVoidTy(ctx), {p0, i64, p0}, false));
    silentExit = H.getOrInsertFunction("klee_silent_exit", FunctionType::get(Type::getVoidTy(ctx), {Type::getInt32Ty(ctx)}, false));
    mallocF = H.getOrInsertFunction("malloc", FunctionType::get(p0, {i64}, false));
    memcpyF = H.getOrInsertFunction("memcpy", FunctionType::get(p0, {p0, p0, i64}, false));
    auto *arr = ArrayType::get(Type::getInt8Ty(ctx), this->n);
    data = new GlobalVariable(H, arr, false, GlobalValue::PrivateLinkage, ConstantAggregateZero::get(arr), "client.input");
    cursor = new GlobalVariable(H, i64, false, GlobalValue::PrivateLinkage, ConstantInt::get(i64, 0), "client.cursor");
  }

  void start(IRBuilder<> &B) { B.CreateCall(mkSym, {data, B.getInt64(n), B.CreateGlobalStringPtr("input")}); }

  Value *symbolic(IRBuilder<> &B, Type *T, const std::string &what) {
    if (T->isVoidTy())
      return nullptr;
    AllocaInst *A = entryAlloca(B, T);
    B.CreateCall(mkSym, {A, B.getInt64(dl.getTypeAllocSize(T)), B.CreateGlobalStringPtr(what + "." + std::to_string(names++))});
    return B.CreateLoad(T, A);
  }

  AllocaInst *entryAlloca(IRBuilder<> &B, Type *T) {
    Function *F = B.GetInsertBlock()->getParent();
    IRBuilder<> E(&F->getEntryBlock(), F->getEntryBlock().begin());
    return E.CreateAlloca(T);
  }

  // A path on which the client cannot proceed is not a client: it ends
  // silently rather than as an infeasible assumption.
  void require(IRBuilder<> &B, Value *cond) {
    Function *F = B.GetInsertBlock()->getParent();
    auto *ok = BasicBlock::Create(ctx, "ok", F);
    auto *no = BasicBlock::Create(ctx, "no", F);
    B.CreateCondBr(cond, ok, no);
    IRBuilder<> N(no);
    N.CreateCall(silentExit, {N.getInt32(0)});
    N.CreateUnreachable();
    B.SetInsertPoint(ok);
  }

  Value *text(IRBuilder<> &B) {
    const unsigned n = textBound;
    Value *p = B.CreateCall(mallocF, {B.getInt64(n + 1)});
    B.CreateCall(mkSym, {p, B.getInt64(n + 1), B.CreateGlobalStringPtr("text." + std::to_string(names++))});
    B.CreateStore(B.getInt8(0), B.CreateGEP(B.getInt8Ty(), p, B.getInt64(n)));
    return p;
  }

  // A text the client chooses among representatives of the classes the
  // library can tell apart. Single-character Cmp constants (e.g. open mode
  // "r" from switch(mode[0])) come first so the seed path opens; then a
  // fresh short string; then longer Cmp/Open constants (paths, keys). Fresh
  // before long names preserves seed paths that already reached without a
  // mode discriminator (Magick/HEIF).
  Value *text(IRBuilder<> &B, const std::vector<std::string> &named) {
    if (named.empty())
      return text(B);
    AllocaInst *slot = entryAlloca(B, PointerType::get(ctx, 0));
    std::vector<std::function<void(IRBuilder<> &)>> alts;
    auto addNamed = [&](const std::string &s) {
      alts.push_back([&, slot, s](IRBuilder<> &C) {
        Value *p = C.CreateCall(mallocF, {C.getInt64(s.size() + 1)});
        C.CreateCall(memcpyF, {p, C.CreateGlobalStringPtr(s), C.getInt64(s.size() + 1)});
        C.CreateStore(p, slot);
      });
    };
    for (const std::string &s : named)
      if (s.size() == 1)
        addNamed(s);
    alts.push_back([&, slot](IRBuilder<> &C) { C.CreateStore(text(C), slot); });
    for (const std::string &s : named)
      if (s.size() != 1)
        addNamed(s);
    oneOf(B, alts, "text");
    return B.CreateLoad(PointerType::get(ctx, 0), slot);
  }

  // A buffer of elements of the given size: as many as the input bound
  // allows within 64 KiB, and at least one. Returns the count it holds.
  uint64_t capacity(uint64_t elem) const { return std::max<uint64_t>(1, std::min<uint64_t>(n, 65536 / elem)); }
  Value *bytes(IRBuilder<> &B, uint64_t elem = 1) {
    uint64_t size = capacity(elem) * elem;
    Value *p = B.CreateCall(mallocF, {B.getInt64(size)});
    lastBytes = "bytes." + std::to_string(names++);
    B.CreateCall(mkSym, {p, B.getInt64(size), B.CreateGlobalStringPtr(lastBytes)});
    return p;
  }
  std::string lastBytes;

  // A fresh object of size bytes, every byte the client's choice.
  Value *object(IRBuilder<> &B, uint64_t size) {
    Value *p = B.CreateCall(mallocF, {B.getInt64(size ? size : 1)});
    B.CreateCall(mkSym, {p, B.getInt64(size ? size : 1), B.CreateGlobalStringPtr("object." + std::to_string(names++))});
    return p;
  }

  // A harness function of type FT: the most general callback the client
  // passes. Its shape decides its effect. A read, (buffer, length) returning
  // a count, fills a non-null buffer with the next input bytes. A seek,
  // (handle, offset, whence), moves the input cursor. A size (handle)→i64
  // returns the input bound; a close (handle)→i32 returns 0. A function
  // whose declared result is a pointer of source type returns a client
  // value of that type, which 'result' builds (key names the declared
  // type). Another function returning a pointer returns fresh memory as
  // large as its largest size argument. A callback writes nothing into memory
  // it is given, except an out buffer and its length (outBufferPair, from
  // the source type ST): there it stores the input bytes and their count.
  Function *callback(FunctionType *FT, const void *key = nullptr,
                     const std::function<Value *(IRBuilder<> &)> &result = nullptr,
                     const DISubroutineType *ST = nullptr) {
    auto it = callbacks.find({FT, key, ST});
    if (it != callbacks.end())
      return it->second;
    Function *F = Function::Create(FT, GlobalValue::InternalLinkage, "client.callback." + std::to_string(callbacks.size()), &H);
    callbacks[{FT, key, ST}] = F;
    auto *BB = BasicBlock::Create(ctx, "entry", F);
    IRBuilder<> B(BB);
    if (auto ts = ST ? ST->getTypeArray() : DITypeRefArray(); ST && ts.size() == F->arg_size() + 1)
      for (unsigned i = 0; i + 1 < F->arg_size(); ++i) {
        unsigned bits = outBufferPair(ts[i + 1], ts[i + 2]);
        Argument *buf = F->getArg(i), *len = F->getArg(i + 1);
        if (!bits || !buf->getType()->isPointerTy() || !len->getType()->isPointerTy())
          continue;
        auto *put = BasicBlock::Create(ctx, "out", F), *next = BasicBlock::Create(ctx, "out.done", F);
        B.CreateCondBr(B.CreateOr(B.CreateIsNull(buf), B.CreateIsNull(len)), next, put);
        B.SetInsertPoint(put);
        B.CreateStore(data, buf);
        B.CreateStore(B.getIntN(bits, n), len);
        B.CreateBr(next);
        B.SetInsertPoint(next);
        ++i;
      }
    Type *R = FT->getReturnType();
    if (R->isPointerTy() && result) {
      B.CreateRet(result(B));
      return F;
    }
    if (R->isPointerTy()) {
      Value *size = B.getInt64(textBound + 1);
      for (Argument &a : F->args())
        if (a.getType()->isIntegerTy()) {
          Value *v = B.CreateZExtOrTrunc(&a, B.getInt64Ty());
          size = B.CreateSelect(B.CreateICmpUGT(v, size), v, size);
        }
      B.CreateRet(B.CreateCall(mallocF, {size}));
      return F;
    }
    Value *count = nullptr;
    for (unsigned i = 0; i + 1 < F->arg_size(); ++i) {
      Argument *buf = F->getArg(i), *len = F->getArg(i + 1);
      if (!buf->getType()->isPointerTy() || !len->getType()->isIntegerTy())
        continue;
      // Seek is (handle, offset, whence): ptr then two ints. That is not a
      // read — the middle integer is a file position, not a byte count.
      if (i == 0 && i + 2 < F->arg_size() && F->getArg(i + 2)->getType()->isIntegerTy())
        continue;
      Value *at = B.CreateLoad(B.getInt64Ty(), cursor);
      Value *left = B.CreateSub(B.getInt64(n), at);
      Value *want = B.CreateSExtOrTrunc(len, B.getInt64Ty());
      Value *neg = B.CreateICmpSLT(want, B.getInt64(0));
      want = B.CreateSelect(neg, B.getInt64(0), want);
      Value *got = B.CreateSelect(B.CreateICmpULT(want, left), want, left);
      got = B.CreateSelect(B.CreateIsNull(buf), B.getInt64(0), got);
      auto *copy = BasicBlock::Create(ctx, "copy", F), *done = BasicBlock::Create(ctx, "done", F);
      B.CreateCondBr(B.CreateIsNull(buf), done, copy);
      B.SetInsertPoint(copy);
      B.CreateCall(memcpyF, {buf, B.CreateGEP(B.getInt8Ty(), data, at), got});
      B.CreateBr(done);
      B.SetInsertPoint(done);
      B.CreateStore(B.CreateAdd(at, got), cursor);
      count = got;
      break;
    }
    // Seek (handle, off, whence) → new cursor in the input, like POSIX lseek.
    if (!count && F->arg_size() == 3 && F->getArg(0)->getType()->isPointerTy() &&
        F->getArg(1)->getType()->isIntegerTy() && F->getArg(2)->getType()->isIntegerTy() &&
        R->isIntegerTy()) {
      Value *off = B.CreateSExtOrTrunc(F->getArg(1), B.getInt64Ty());
      Value *w = B.CreateSExtOrTrunc(F->getArg(2), B.getInt64Ty());
      Value *cur = B.CreateLoad(B.getInt64Ty(), cursor);
      Value *base = B.CreateSelect(B.CreateICmpEQ(w, B.getInt64(1)), cur,
                                   B.CreateSelect(B.CreateICmpEQ(w, B.getInt64(2)), B.getInt64(n), B.getInt64(0)));
      Value *to = B.CreateAdd(base, off);
      to = B.CreateSelect(B.CreateICmpSLT(to, B.getInt64(0)), B.getInt64(0), to);
      to = B.CreateSelect(B.CreateICmpUGT(to, B.getInt64(n)), B.getInt64(n), to);
      B.CreateStore(to, cursor);
      B.CreateRet(B.CreateSExtOrTrunc(to, R));
      return F;
    }
    // Size (handle) → input bound. Close (handle) → 0. Distinguish by width:
    // TIFFSizeProc is toff_t (i64); TIFFCloseProc is int (i32).
    if (!count && F->arg_size() == 1 && F->getArg(0)->getType()->isPointerTy() && R->isIntegerTy()) {
      if (R->getIntegerBitWidth() >= 64)
        B.CreateRet(B.CreateZExtOrTrunc(B.getInt64(n), R));
      else
        B.CreateRet(ConstantInt::get(R, 0));
      return F;
    }
    if (R->isVoidTy())
      B.CreateRetVoid();
    else if (count && R->isIntegerTy())
      B.CreateRet(B.CreateSExtOrTrunc(count, R));
    else
      B.CreateRet(symbolic(B, R, "callback"));
    return F;
  }

  // Branch on a symbolic index among n alternatives; each emits into its
  // own block and falls through to the join.
  void oneOf(IRBuilder<> &B, const std::vector<std::function<void(IRBuilder<> &)>> &alts, const std::string &what) {
    if (alts.empty())
      return;
    Function *F = B.GetInsertBlock()->getParent();
    if (alts.size() == 1) {
      alts[0](B);
      return;
    }
    Value *k = symbolic(B, B.getInt32Ty(), what);
    require(B, B.CreateICmpULT(k, B.getInt32((unsigned)alts.size())));
    auto *join = BasicBlock::Create(ctx, what + ".join", F);
    auto *sw = B.CreateSwitch(k, join, (unsigned)alts.size());
    for (unsigned i = 0; i < alts.size(); ++i) {
      auto *bb = BasicBlock::Create(ctx, what + "." + std::to_string(i), F);
      sw->addCase(B.getInt32(i), bb);
      IRBuilder<> A(bb);
      alts[i](A);
      A.CreateBr(join);
    }
    B.SetInsertPoint(join);
  }
};

// The environment E (§7): the file system holds one file, "f", whose bytes
// are the client's input. Each file call D or U makes without a body takes
// its POSIX meaning over those bytes: opening "f" yields a descriptor or a
// stream, reads deliver the bytes at the position, writes store into them
// up to the input bound, and any other path names no file. Standard streams
// are outside the file: reading them meets the end, writing them succeeds.
struct FileEnv {
  static constexpr unsigned Slots = 4, FileBytes = 256;
  static constexpr int64_t FirstFd = 3;
  Builder &K;
  Module &H;
  LLVMContext &ctx;
  Type *i8, *i32, *i64;
  PointerType *p0;
  // Per open: in use, position, end seen. The streams are FileBytes-byte
  // objects, zero so that an inlined getc finds an empty buffer.
  GlobalVariable *used, *pos, *eof, *files, *size;

  FileEnv(Builder &K)
      : K(K), H(K.H), ctx(K.ctx), i8(Type::getInt8Ty(ctx)), i32(Type::getInt32Ty(ctx)), i64(Type::getInt64Ty(ctx)),
        p0(PointerType::get(ctx, 0)) {
    auto table = [&](Type *T, unsigned n, const char *name) {
      auto *A = ArrayType::get(T, n);
      return new GlobalVariable(H, A, false, GlobalValue::PrivateLinkage, ConstantAggregateZero::get(A), name);
    };
    used = table(i8, Slots, "client.file.used");
    pos = table(i64, Slots, "client.file.pos");
    eof = table(i8, Slots, "client.file.eof");
    files = table(ArrayType::get(i8, FileBytes), Slots, "client.file.stream");
    size = new GlobalVariable(H, i64, false, GlobalValue::PrivateLinkage, ConstantInt::get(i64, K.n), "client.file.size");
  }

  Value *at(IRBuilder<> &B, GlobalVariable *G, Value *s) {
    return B.CreateGEP(G->getValueType(), G, {B.getInt64(0), s});
  }
  Value *byte(IRBuilder<> &B, Value *off) { return B.CreateGEP(i8, K.data, off); }
  Value *zext(IRBuilder<> &B, Value *v) { return B.CreateZExtOrTrunc(v, i64); }
  Value *sext(IRBuilder<> &B, Value *v) { return B.CreateSExtOrTrunc(v, i64); }
  Value *umin(IRBuilder<> &B, Value *a, Value *b) { return B.CreateSelect(B.CreateICmpULT(a, b), a, b); }

  void ret(IRBuilder<> &B, Function *F, Value *v) {
    Type *R = F->getReturnType();
    if (R->isVoidTy())
      B.CreateRetVoid();
    else if (R->isPointerTy())
      B.CreateRet(v->getType()->isPointerTy() ? v : B.CreateIntToPtr(v, R));
    else
      B.CreateRet(B.CreateSExtOrTrunc(v, R));
  }
  // Return v unless cond holds; continue where it does.
  void unless(IRBuilder<> &B, Function *F, Value *cond, Value *v) {
    auto *ok = BasicBlock::Create(ctx, "ok", F), *no = BasicBlock::Create(ctx, "no", F);
    B.CreateCondBr(cond, ok, no);
    IRBuilder<> N(no);
    ret(N, F, v);
    B.SetInsertPoint(ok);
  }
  Value *minus1() { return ConstantInt::getSigned(i64, -1); }
  Value *null() { return ConstantPointerNull::get(p0); }

  // The open a descriptor or a stream names, clamped into the tables.
  Value *slotOfFd(IRBuilder<> &B, Value *fd, Value *&ok) {
    Value *i = B.CreateSub(sext(B, fd), B.getInt64(FirstFd));
    Value *in = B.CreateICmpULT(i, B.getInt64(Slots));
    Value *s = B.CreateSelect(in, i, B.getInt64(0));
    ok = B.CreateAnd(in, B.CreateICmpNE(B.CreateLoad(i8, at(B, used, s)), B.getInt8(0)));
    return s;
  }
  Value *slotOfStream(IRBuilder<> &B, Value *fp, Value *&ok) {
    Value *d = B.CreateSub(B.CreatePtrToInt(fp, i64), B.CreatePtrToInt(files, i64));
    Value *in = B.CreateAnd(B.CreateICmpULT(d, B.getInt64(Slots * FileBytes)),
                            B.CreateICmpEQ(B.CreateURem(d, B.getInt64(FileBytes)), B.getInt64(0)));
    Value *s = B.CreateSelect(in, B.CreateUDiv(d, B.getInt64(FileBytes)), B.getInt64(0));
    ok = B.CreateAnd(in, B.CreateICmpNE(B.CreateLoad(i8, at(B, used, s)), B.getInt8(0)));
    return s;
  }
  Value *stream(IRBuilder<> &B, Value *s) { return at(B, files, s); }
  Value *fd(IRBuilder<> &B, Value *s) { return B.CreateAdd(s, B.getInt64(FirstFd)); }

  // The path is "f", or "f." and an extension (§2.4 Key). A shorter string
  // is not read past its end.
  Value *isF(IRBuilder<> &B, Function *F, Value *path) {
    auto *c0 = BasicBlock::Create(ctx, "path0", F), *c1 = BasicBlock::Create(ctx, "path1", F),
         *done = BasicBlock::Create(ctx, "path", F);
    BasicBlock *from = B.GetInsertBlock();
    B.CreateCondBr(B.CreateIsNull(path), done, c0);
    IRBuilder<> A(c0);
    A.CreateCondBr(A.CreateICmpEQ(A.CreateLoad(i8, path), A.getInt8('f')), c1, done);
    IRBuilder<> C(c1);
    Value *c = C.CreateLoad(i8, C.CreateGEP(i8, path, C.getInt64(1)));
    Value *end = C.CreateOr(C.CreateICmpEQ(c, C.getInt8(0)), C.CreateICmpEQ(c, C.getInt8('.')));
    C.CreateBr(done);
    B.SetInsertPoint(done);
    PHINode *r = B.CreatePHI(B.getInt1Ty(), 3);
    r->addIncoming(B.getFalse(), from);
    r->addIncoming(B.getFalse(), c0);
    r->addIncoming(end, c1);
    return r;
  }
  // A fresh open of "f", or the value of a failed open.
  Value *open(IRBuilder<> &B, Function *F, Value *path, Value *failed) {
    unless(B, F, isF(B, F, path), failed);
    Value *s = minus1();
    for (unsigned k = Slots; k-- > 0;)
      s = B.CreateSelect(B.CreateICmpEQ(B.CreateLoad(i8, at(B, used, B.getInt64(k))), B.getInt8(0)), B.getInt64(k), s);
    unless(B, F, B.CreateICmpSGE(s, B.getInt64(0)), failed);
    B.CreateStore(B.getInt8(1), at(B, used, s));
    B.CreateStore(B.getInt64(0), at(B, pos, s));
    B.CreateStore(B.getInt8(0), at(B, eof, s));
    return s;
  }
  void truncate(IRBuilder<> &B, Value *s, Value *trunc, Value *append) {
    B.CreateStore(B.CreateSelect(trunc, B.getInt64(0), B.CreateLoad(i64, size)), size);
    B.CreateStore(B.CreateSelect(append, B.CreateLoad(i64, size), B.CreateLoad(i64, at(B, pos, s))), at(B, pos, s));
  }

  // Move n bytes between buf and the file at the position of open s, or at
  // off when given (which leaves the position). Returns the count moved.
  Value *transfer(IRBuilder<> &B, Value *s, Value *buf, Value *n, Value *off, bool write) {
    Value *p = off ? off : B.CreateLoad(i64, at(B, pos, s));
    Value *end = write ? (Value *)B.getInt64(K.n) : B.CreateLoad(i64, size);
    Value *left = B.CreateSelect(B.CreateICmpULT(p, end), B.CreateSub(end, p), B.getInt64(0));
    Value *k = umin(B, n, left);
    Value *safe = B.CreateSelect(B.CreateICmpULT(p, end), p, B.getInt64(0));
    if (write) {
      B.CreateMemCpy(byte(B, safe), MaybeAlign(1), buf, MaybeAlign(1), k);
      Value *grown = B.CreateAdd(p, k), *sz = B.CreateLoad(i64, size);
      B.CreateStore(B.CreateSelect(B.CreateICmpUGT(grown, sz), grown, sz), size);
    } else
      B.CreateMemCpy(buf, MaybeAlign(1), byte(B, safe), MaybeAlign(1), k);
    if (!off) {
      B.CreateStore(B.CreateAdd(p, k), at(B, pos, s));
      if (!write)
        B.CreateStore(B.CreateZExt(B.CreateICmpULT(k, n), i8), at(B, eof, s));
    }
    return k;
  }
  // The new position of a seek, or -1.
  Value *seek(IRBuilder<> &B, Function *F, Value *s, Value *off, Value *whence, Value *failed) {
    Value *w = sext(B, whence);
    Value *base = B.CreateSelect(B.CreateICmpEQ(w, B.getInt64(1)), B.CreateLoad(i64, at(B, pos, s)),
                                 B.CreateSelect(B.CreateICmpEQ(w, B.getInt64(2)), B.CreateLoad(i64, size), B.getInt64(0)));
    unless(B, F, B.CreateICmpULE(w, B.getInt64(2)), failed);
    Value *to = B.CreateAdd(base, sext(B, off));
    unless(B, F, B.CreateICmpSGE(to, B.getInt64(0)), failed);
    B.CreateStore(to, at(B, pos, s));
    B.CreateStore(B.getInt8(0), at(B, eof, s));
    return to;
  }
  // struct stat of a regular file of the current size (x86-64 Linux).
  void fill(IRBuilder<> &B, Value *st) {
    B.CreateMemSet(st, B.getInt8(0), B.getInt64(144), MaybeAlign(1));
    B.CreateStore(B.getInt64(1), B.CreateGEP(i8, st, B.getInt64(16)));
    B.CreateStore(B.getInt32(0100644), B.CreateGEP(i8, st, B.getInt64(24)));
    B.CreateStore(B.CreateLoad(i64, size), B.CreateGEP(i8, st, B.getInt64(48)));
    B.CreateStore(B.getInt64(4096), B.CreateGEP(i8, st, B.getInt64(56)));
  }
  // The next byte of open s, consumed or not, or -1 at the end.
  Value *next(IRBuilder<> &B, Function *F, Value *s, bool consume) {
    Value *p = B.CreateLoad(i64, at(B, pos, s));
    auto *more = BasicBlock::Create(ctx, "more", F), *end = BasicBlock::Create(ctx, "end", F);
    B.CreateCondBr(B.CreateICmpULT(p, B.CreateLoad(i64, size)), more, end);
    IRBuilder<> E(end);
    E.CreateStore(E.getInt8(1), at(E, eof, s));
    ret(E, F, minus1());
    B.SetInsertPoint(more);
    Value *c = B.CreateZExt(B.CreateLoad(i8, byte(B, p)), i64);
    if (consume)
      B.CreateStore(B.CreateAdd(p, B.getInt64(1)), at(B, pos, s));
    return c;
  }
  // fgets: at most n-1 bytes, through the first newline.
  void fgets(IRBuilder<> &B, Function *F, Value *buf, Value *n, Value *s) {
    Value *m = B.CreateSub(sext(B, n), B.getInt64(1));
    unless(B, F, B.CreateICmpSGE(m, B.getInt64(0)), null());
    BasicBlock *start = B.GetInsertBlock();
    auto *head = BasicBlock::Create(ctx, "head", F), *body = BasicBlock::Create(ctx, "body", F),
         *got = BasicBlock::Create(ctx, "got", F), *done = BasicBlock::Create(ctx, "done", F);
    B.CreateBr(head);
    IRBuilder<> Hd(head);
    PHINode *i = Hd.CreatePHI(i64, 2);
    i->addIncoming(Hd.getInt64(0), start);
    Hd.CreateCondBr(Hd.CreateICmpSLT(i, m), body, done);
    IRBuilder<> Bd(body);
    Value *p = Bd.CreateLoad(i64, at(Bd, pos, s));
    Value *more = Bd.CreateICmpULT(p, Bd.CreateLoad(i64, size));
    Bd.CreateStore(Bd.CreateZExt(Bd.CreateNot(more), i8), at(Bd, eof, s));
    Bd.CreateCondBr(more, got, done);
    IRBuilder<> G(got);
    Value *c = G.CreateLoad(i8, byte(G, p));
    G.CreateStore(G.CreateAdd(p, G.getInt64(1)), at(G, pos, s));
    G.CreateStore(c, G.CreateGEP(i8, buf, i));
    Value *i1 = G.CreateAdd(i, G.getInt64(1));
    i->addIncoming(i1, got);
    G.CreateCondBr(G.CreateICmpEQ(c, G.getInt8('\n')), done, head);
    B.SetInsertPoint(done);
    PHINode *count = B.CreatePHI(i64, 3);
    count->addIncoming(i, head);
    count->addIncoming(i, body);
    count->addIncoming(i1, got);
    B.CreateStore(B.getInt8(0), B.CreateGEP(i8, buf, count));
    ret(B, F, B.CreateSelect(B.CreateAnd(B.CreateICmpEQ(count, B.getInt64(0)), B.CreateICmpSGT(m, B.getInt64(0))),
                             null(), buf));
  }

  // The parameters match kinds ('p' pointer, 'i' integer) and the result
  // is 'p', 'i', or 'v'.
  static bool shaped(FunctionType *FT, const std::string &params, char result) {
    if (FT->getNumParams() != params.size())
      return false;
    for (unsigned k = 0; k < params.size(); ++k)
      if ((params[k] == 'p') != FT->getParamType(k)->isPointerTy() ||
          (params[k] == 'i') != FT->getParamType(k)->isIntegerTy())
        return false;
    Type *R = FT->getReturnType();
    return result == 'v' ? R->isVoidTy() : result == 'p' ? R->isPointerTy() : R->isIntegerTy();
  }

  // Defines name with type FT when it is one of the file calls.
  void define(const std::string &name, FunctionType *FT, bool linux64) {
    struct Spec {
      const char *params;
      char result;
      std::function<void(FileEnv &, IRBuilder<> &, Function *)> body;
    };
    using E = FileEnv;
    static const std::map<std::string, Spec> specs = [] {
      std::map<std::string, Spec> m;
      auto openFd = [](E &e, IRBuilder<> &B, Function *F, unsigned path, int flags) {
        Value *s = e.open(B, F, F->getArg(path), e.minus1());
        Value *fl = flags >= 0 ? e.sext(B, F->getArg((unsigned)flags)) : B.getInt64(0);
        e.truncate(B, s, B.CreateICmpNE(B.CreateAnd(fl, B.getInt64(01000)), B.getInt64(0)),
                   B.CreateICmpNE(B.CreateAnd(fl, B.getInt64(02000)), B.getInt64(0)));
        e.ret(B, F, e.fd(B, s));
      };
      for (const char *n : {"open", "open64"})
        m[n] = {"pi", 'i', [=](E &e, IRBuilder<> &B, Function *F) { openFd(e, B, F, 0, 1); }};
      for (const char *n : {"openat", "openat64"})
        m[n] = {"ipi", 'i', [=](E &e, IRBuilder<> &B, Function *F) { openFd(e, B, F, 1, 2); }};
      for (const char *n : {"fopen", "fopen64"})
        m[n] = {"pp", 'p', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *s = e.open(B, F, F->getArg(0), e.null());
                  Value *mode = F->getArg(1);
                  e.unless(B, F, B.CreateIsNotNull(mode), e.null());
                  Value *m0 = B.CreateLoad(e.i8, mode);
                  e.truncate(B, s, B.CreateICmpEQ(m0, B.getInt8('w')), B.CreateICmpEQ(m0, B.getInt8('a')));
                  e.ret(B, F, e.stream(B, s));
                }};
      m["fdopen"] = {"ip", 'p', [](E &e, IRBuilder<> &B, Function *F) {
                       Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                       e.unless(B, F, ok, e.null());
                       e.ret(B, F, e.stream(B, s));
                     }};
      m["fileno"] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                       Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                       e.unless(B, F, ok, e.minus1());
                       e.ret(B, F, e.fd(B, s));
                     }};
      m["read"] = {"ipi", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                     Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                     e.unless(B, F, ok, B.CreateSelect(B.CreateICmpEQ(e.sext(B, F->getArg(0)), B.getInt64(0)), B.getInt64(0), e.minus1()));
                     e.ret(B, F, e.transfer(B, s, F->getArg(1), e.zext(B, F->getArg(2)), nullptr, false));
                   }};
      m["write"] = {"ipi", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                      Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                      Value *n = e.zext(B, F->getArg(2));
                      Value *stdio = B.CreateICmpULE(e.sext(B, F->getArg(0)), B.getInt64(2));
                      e.unless(B, F, ok, B.CreateSelect(stdio, n, e.minus1()));
                      Value *k = e.transfer(B, s, F->getArg(1), n, nullptr, true);
                      e.ret(B, F, B.CreateSelect(B.CreateAnd(B.CreateICmpEQ(k, B.getInt64(0)), B.CreateICmpNE(n, B.getInt64(0))), e.minus1(), k));
                    }};
      for (const char *n : {"pread", "pread64"})
        m[n] = {"ipii", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                  Value *off = e.sext(B, F->getArg(3));
                  e.unless(B, F, B.CreateAnd(ok, B.CreateICmpSGE(off, B.getInt64(0))), e.minus1());
                  e.ret(B, F, e.transfer(B, s, F->getArg(1), e.zext(B, F->getArg(2)), off, false));
                }};
      for (const char *n : {"lseek", "lseek64"})
        m[n] = {"iii", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                  e.unless(B, F, ok, e.minus1());
                  e.ret(B, F, e.seek(B, F, s, F->getArg(1), F->getArg(2), e.minus1()));
                }};
      m["close"] = {"i", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                      Value *ok, *s = e.slotOfFd(B, F->getArg(0), ok);
                      Value *stdio = B.CreateICmpULE(e.sext(B, F->getArg(0)), B.getInt64(2));
                      e.unless(B, F, ok, B.CreateSelect(stdio, B.getInt64(0), e.minus1()));
                      B.CreateStore(B.getInt8(0), e.at(B, e.used, s));
                      e.ret(B, F, B.getInt64(0));
                    }};
      for (const char *n : {"fread", "fread_unlocked"})
        m[n] = {"piip", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(3), ok);
                  Value *sz = e.zext(B, F->getArg(1));
                  e.unless(B, F, B.CreateAnd(ok, B.CreateICmpNE(sz, B.getInt64(0))), B.getInt64(0));
                  Value *k = e.transfer(B, s, F->getArg(0), B.CreateMul(sz, e.zext(B, F->getArg(2))), nullptr, false);
                  e.ret(B, F, B.CreateUDiv(k, sz));
                }};
      for (const char *n : {"fwrite", "fwrite_unlocked"})
        m[n] = {"piip", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(3), ok);
                  Value *sz = e.zext(B, F->getArg(1));
                  e.unless(B, F, ok, F->getArg(2));
                  e.unless(B, F, B.CreateICmpNE(sz, B.getInt64(0)), B.getInt64(0));
                  Value *k = e.transfer(B, s, F->getArg(0), B.CreateMul(sz, e.zext(B, F->getArg(2))), nullptr, true);
                  e.ret(B, F, B.CreateUDiv(k, sz));
                }};
      for (const char *n : {"fgetc", "getc", "_IO_getc", "getc_unlocked", "fgetc_unlocked", "__uflow"})
        m[n] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                  e.unless(B, F, ok, e.minus1());
                  e.ret(B, F, e.next(B, F, s, true));
                }};
      m["__underflow"] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                            Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                            e.unless(B, F, ok, e.minus1());
                            e.ret(B, F, e.next(B, F, s, false));
                          }};
      for (const char *n : {"fgets", "fgets_unlocked"})
        m[n] = {"pip", 'p', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(2), ok);
                  e.unless(B, F, ok, e.null());
                  e.fgets(B, F, F->getArg(0), F->getArg(1), s);
                }};
      for (const char *n : {"feof", "feof_unlocked"})
        m[n] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                  e.unless(B, F, ok, B.getInt64(0));
                  e.ret(B, F, B.CreateZExt(B.CreateLoad(e.i8, e.at(B, e.eof, s)), e.i64));
                }};
      for (const char *n : {"ferror", "ferror_unlocked"})
        m[n] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) { e.ret(B, F, B.getInt64(0)); }};
      for (const char *n : {"clearerr", "clearerr_unlocked", "rewind"})
        m[n] = {"p", 'v', [n](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                  e.unless(B, F, ok, nullptr);
                  B.CreateStore(B.getInt8(0), e.at(B, e.eof, s));
                  if (std::string(n) == "rewind")
                    B.CreateStore(B.getInt64(0), e.at(B, e.pos, s));
                  B.CreateRetVoid();
                }};
      for (const char *n : {"fseek", "fseeko", "fseeko64"})
        m[n] = {"pii", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                  e.unless(B, F, ok, e.minus1());
                  e.seek(B, F, s, F->getArg(1), F->getArg(2), e.minus1());
                  e.ret(B, F, B.getInt64(0));
                }};
      for (const char *n : {"ftell", "ftello", "ftello64"})
        m[n] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                  e.unless(B, F, ok, e.minus1());
                  e.ret(B, F, B.CreateLoad(e.i64, e.at(B, e.pos, s)));
                }};
      m["fclose"] = {"p", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                       Value *ok, *s = e.slotOfStream(B, F->getArg(0), ok);
                       e.unless(B, F, ok, B.getInt64(0));
                       B.CreateStore(B.getInt8(0), e.at(B, e.used, s));
                       e.ret(B, F, B.getInt64(0));
                     }};
      m["access"] = {"pi", 'i', [](E &e, IRBuilder<> &B, Function *F) {
                       e.ret(B, F, B.CreateSelect(e.isF(B, F, F->getArg(0)), B.getInt64(0), e.minus1()));
                     }};
      for (const char *n : {"mmap", "mmap64"})
        m[n] = {"piiiii", 'p', [](E &e, IRBuilder<> &B, Function *F) {
                  Value *len = e.zext(B, F->getArg(1));
                  Value *anon = B.CreateICmpNE(B.CreateAnd(e.sext(B, F->getArg(3)), B.getInt64(0x20)), B.getInt64(0));
                  Value *ok, *s = e.slotOfFd(B, F->getArg(4), ok);
                  Value *off = e.sext(B, F->getArg(5));
                  e.unless(B, F, B.CreateOr(anon, B.CreateAnd(ok, B.CreateICmpSGE(off, B.getInt64(0)))), e.minus1());
                  Value *p = B.CreateCall(e.K.mallocF, {len});
                  B.CreateMemSet(p, B.getInt8(0), len, MaybeAlign(1));
                  e.unless(B, F, B.CreateNot(anon), p);
                  e.transfer(B, s, p, len, off, false);
                  e.ret(B, F, p);
                }};
      m["munmap"] = {"pi", 'i', [](E &e, IRBuilder<> &B, Function *F) { e.ret(B, F, B.getInt64(0)); }};
      return m;
    }();
    static const std::map<std::string, Spec> statSpecs = [] {
      std::map<std::string, Spec> m;
      auto byPath = [](unsigned path, unsigned st) {
        return [=](E &e, IRBuilder<> &B, Function *F) {
          e.unless(B, F, e.isF(B, F, F->getArg(path)), e.minus1());
          e.fill(B, F->getArg(st));
          e.ret(B, F, B.getInt64(0));
        };
      };
      auto byFd = [](unsigned fd, unsigned st) {
        return [=](E &e, IRBuilder<> &B, Function *F) {
          Value *ok;
          e.slotOfFd(B, F->getArg(fd), ok);
          e.unless(B, F, ok, e.minus1());
          e.fill(B, F->getArg(st));
          e.ret(B, F, B.getInt64(0));
        };
      };
      for (const char *n : {"stat", "stat64", "lstat", "lstat64"})
        m[n] = {"pp", 'i', byPath(0, 1)};
      for (const char *n : {"__xstat", "__xstat64", "__lxstat", "__lxstat64"})
        m[n] = {"ipp", 'i', byPath(1, 2)};
      for (const char *n : {"fstat", "fstat64"})
        m[n] = {"ip", 'i', byFd(0, 1)};
      for (const char *n : {"__fxstat", "__fxstat64"})
        m[n] = {"iip", 'i', byFd(1, 2)};
      return m;
    }();
    const Spec *sp = nullptr;
    if (auto it = specs.find(name); it != specs.end())
      sp = &it->second;
    else if (auto it = statSpecs.find(name); linux64 && it != statSpecs.end())
      sp = &it->second;
    if (!sp || !shaped(FT, sp->params, sp->result) || (FT->isVarArg() && name.rfind("open", 0) != 0))
      return;
    Function *F = Function::Create(FT, GlobalValue::ExternalLinkage, name, &H);
    IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
    sp->body(*this, B, F);
  }

  // The functions D or U declares and neither defines. A definition of
  // local linkage is another function of the same name.
  static std::map<std::string, FunctionType *> unbound(Module &down, Module &up) {
    std::map<std::string, FunctionType *> want;
    for (Module *M : {&down, &up})
      for (Function &F : *M)
        if (F.isDeclaration() && !F.isIntrinsic())
          want.emplace(F.getName().str(), F.getFunctionType());
    for (Module *M : {&down, &up})
      for (Function &F : *M)
        if (!F.isDeclaration() && !F.hasLocalLinkage())
          want.erase(F.getName().str());
    return want;
  }
  bool linux64() const {
    Triple T(H.getTargetTriple());
    return T.isOSLinux() && T.getArch() == Triple::x86_64;
  }
  void plant(Module &down, Module &up) {
    for (const auto &[name, FT] : unbound(down, up))
      if (!H.getFunction(name))
        define(name, FT, linux64());
  }
};

// The rest of E (§7): the environment has no variables, and the file system
// also holds the shared libraries the closure installs, at their paths
// relative to the case directory (the tree is relocatable, so a path names
// a library when it ends with that relative path). A directory lists the
// installed libraries in it. Opening a library yields its handle; a symbol
// of a handle is the program's definition of that name when the library
// exports it, and is absent otherwise. Only names the program passes to
// dlsym as constants are resolved; any other name is absent, which loses
// paths and never adds one.
struct LoaderEnv {
  static constexpr unsigned DirentBytes = 280, NameAt = 19, NameBytes = 256;
  FileEnv &E;
  Module &H;
  LLVMContext &ctx;
  const std::vector<Client::Library> &libs;
  std::vector<std::string> dirs;
  // Per directory, its first entry and count; the entries are dirents.
  std::vector<std::pair<unsigned, unsigned>> listing;
  GlobalVariable *handles = nullptr, *ents = nullptr, *dirpos = nullptr, *err = nullptr;
  Function *streqF = nullptr, *endsF = nullptr;

  LoaderEnv(FileEnv &E, const std::vector<Client::Library> &libs) : E(E), H(E.H), ctx(E.ctx), libs(libs) {}

  static std::string parent(const std::string &key) { return key.substr(0, key.rfind('/')); }
  static std::string leaf(const std::string &key) { return key.substr(key.rfind('/') + 1); }

  Constant *cstr(const std::string &s) {
    auto *C = ConstantDataArray::getString(ctx, s);
    return new GlobalVariable(H, C->getType(), true, GlobalValue::PrivateLinkage, C, "client.env.str");
  }
  void build() {
    for (const auto &L : libs)
      if (std::find(dirs.begin(), dirs.end(), parent(L.key)) == dirs.end())
        dirs.push_back(parent(L.key));
    std::vector<Constant *> rows;
    auto *Row = ArrayType::get(E.i8, DirentBytes);
    for (const std::string &d : dirs) {
      listing.push_back({(unsigned)rows.size(), 0});
      for (const auto &L : libs) {
        if (parent(L.key) != d)
          continue;
        std::vector<uint8_t> b(DirentBytes, 0);
        uint64_t ino = rows.size() + 1;
        for (unsigned k = 0; k < 8; ++k)
          b[k] = (ino >> (8 * k)) & 0xff, b[8 + k] = ((ino + 1) >> (8 * k)) & 0xff;
        b[16] = DirentBytes & 0xff, b[17] = DirentBytes >> 8;
        b[18] = L.link ? 10 : 8;
        std::string n = leaf(L.key).substr(0, NameBytes - 1);
        std::copy(n.begin(), n.end(), b.begin() + NameAt);
        rows.push_back(ConstantDataArray::get(ctx, b));
        ++listing.back().second;
      }
    }
    auto table = [&](Type *T, unsigned n, const char *name) {
      auto *A = ArrayType::get(T, std::max(n, 1u));
      return new GlobalVariable(H, A, false, GlobalValue::PrivateLinkage, ConstantAggregateZero::get(A), name);
    };
    handles = table(E.i8, libs.size() + 1, "client.env.lib");
    dirpos = table(E.i64, dirs.size(), "client.env.dirpos");
    auto *A = ArrayType::get(Row, std::max<size_t>(rows.size(), 1));
    ents = new GlobalVariable(H, A, false, GlobalValue::PrivateLinkage,
                              rows.empty() ? ConstantAggregateZero::get(A) : ConstantArray::get(A, rows), "client.env.dirent");
    err = new GlobalVariable(H, E.p0, false, GlobalValue::PrivateLinkage, ConstantPointerNull::get(E.p0),
                             "client.env.error");
    streqF = streq();
    endsF = ends();
  }

  // a and b, both non-null, hold the same string.
  Function *streq() {
    auto *F = Function::Create(FunctionType::get(Type::getInt1Ty(ctx), {E.p0, E.p0}, false), GlobalValue::InternalLinkage,
                               "client.env.streq", &H);
    auto *entry = BasicBlock::Create(ctx, "entry", F), *head = BasicBlock::Create(ctx, "head", F),
         *same = BasicBlock::Create(ctx, "same", F), *done = BasicBlock::Create(ctx, "done", F);
    IRBuilder<> B(entry);
    B.CreateBr(head);
    IRBuilder<> Hd(head);
    PHINode *i = Hd.CreatePHI(E.i64, 2);
    i->addIncoming(Hd.getInt64(0), entry);
    Value *a = Hd.CreateLoad(E.i8, Hd.CreateGEP(E.i8, F->getArg(0), i));
    Value *b = Hd.CreateLoad(E.i8, Hd.CreateGEP(E.i8, F->getArg(1), i));
    Value *eq = Hd.CreateICmpEQ(a, b);
    Hd.CreateCondBr(eq, same, done);
    IRBuilder<> S(same);
    i->addIncoming(S.CreateAdd(i, S.getInt64(1)), same);
    Value *end = S.CreateICmpEQ(a, S.getInt8(0));
    S.CreateCondBr(end, done, head);
    IRBuilder<> D(done);
    PHINode *r = D.CreatePHI(D.getInt1Ty(), 2);
    r->addIncoming(D.getFalse(), head);
    r->addIncoming(D.getTrue(), same);
    D.CreateRet(r);
    return F;
  }
  // p, non-null, ends with the n bytes of s.
  Function *ends() {
    auto *F = Function::Create(FunctionType::get(Type::getInt1Ty(ctx), {E.p0, E.p0, E.i64}, false),
                               GlobalValue::InternalLinkage, "client.env.ends", &H);
    Value *p = F->getArg(0), *s = F->getArg(1), *n = F->getArg(2);
    auto *entry = BasicBlock::Create(ctx, "entry", F), *len = BasicBlock::Create(ctx, "len", F),
         *step = BasicBlock::Create(ctx, "step", F), *cmp = BasicBlock::Create(ctx, "cmp", F),
         *head = BasicBlock::Create(ctx, "head", F), *body = BasicBlock::Create(ctx, "body", F),
         *yes = BasicBlock::Create(ctx, "yes", F), *no = BasicBlock::Create(ctx, "no", F);
    IRBuilder<> B(entry);
    B.CreateBr(len);
    IRBuilder<> L(len);
    PHINode *m = L.CreatePHI(E.i64, 2);
    m->addIncoming(L.getInt64(0), entry);
    L.CreateCondBr(L.CreateICmpEQ(L.CreateLoad(E.i8, L.CreateGEP(E.i8, p, m)), L.getInt8(0)), cmp, step);
    IRBuilder<> St(step);
    m->addIncoming(St.CreateAdd(m, St.getInt64(1)), step);
    St.CreateBr(len);
    IRBuilder<> C(cmp);
    Value *base = C.CreateSub(m, n);
    C.CreateCondBr(C.CreateICmpULT(m, n), no, head);
    IRBuilder<> Hd(head);
    PHINode *j = Hd.CreatePHI(E.i64, 2);
    j->addIncoming(Hd.getInt64(0), cmp);
    Hd.CreateCondBr(Hd.CreateICmpULT(j, n), body, yes);
    IRBuilder<> Bd(body);
    Value *x = Bd.CreateLoad(E.i8, Bd.CreateGEP(E.i8, p, Bd.CreateAdd(base, j)));
    Value *y = Bd.CreateLoad(E.i8, Bd.CreateGEP(E.i8, s, j));
    j->addIncoming(Bd.CreateAdd(j, Bd.getInt64(1)), body);
    Bd.CreateCondBr(Bd.CreateICmpEQ(x, y), head, no);
    IRBuilder<>(yes).CreateRet(ConstantInt::getTrue(ctx));
    IRBuilder<>(no).CreateRet(ConstantInt::getFalse(ctx));
    return F;
  }
  Value *endsWith(IRBuilder<> &B, Value *p, const std::string &key) {
    return B.CreateCall(endsF, {p, cstr(key), B.getInt64(key.size())});
  }
  Value *handle(IRBuilder<> &B, unsigned k) { return E.at(B, handles, B.getInt64(k)); }
  Value *fail(IRBuilder<> &B) {
    B.CreateStore(cstr("not found"), err);
    return E.null();
  }

  // The names D or U pass to dlsym as constant strings.
  static std::set<std::string> looked(Module &down, Module &up) {
    std::set<std::string> out;
    for (Module *M : {&down, &up})
      if (Function *S = M->getFunction("dlsym"))
        for (User *U : S->users())
          if (auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == S && CB->arg_size() == 2)
            if (auto *G = dyn_cast<GlobalVariable>(getUnderlyingObject(CB->getArgOperand(1))))
              if (G->hasInitializer())
                if (auto *C = dyn_cast<ConstantDataArray>(G->getInitializer()); C && C->isCString())
                  out.insert(C->getAsCString().str());
    return out;
  }
  // H's reference to the definition D or U gives name, or null.
  Constant *definition(Module &down, Module &up, const std::string &name) {
    for (Module *M : {&down, &up}) {
      if (Function *F = M->getFunction(name); F && !F->isDeclaration() && !F->hasLocalLinkage())
        return cast<Constant>(H.getOrInsertFunction(name, F->getFunctionType()).getCallee());
      if (GlobalVariable *G = M->getGlobalVariable(name); G && G->hasInitializer() && !G->hasLocalLinkage())
        return H.getOrInsertGlobal(name, G->getValueType());
    }
    return nullptr;
  }

  void plant(Module &down, Module &up) {
    auto want = FileEnv::unbound(down, up);
    bool any = false;
    for (const char *n : {"dlopen", "dlsym", "dlclose", "dlerror", "opendir", "readdir", "readdir64", "closedir"})
      any |= want.count(n) > 0;
    if (any)
      build();
    auto shaped = [&](const char *name, const std::string &params, char result) -> Function * {
      auto it = want.find(name);
      if (it == want.end() || H.getFunction(name) || !FileEnv::shaped(it->second, params, result))
        return nullptr;
      return Function::Create(it->second, GlobalValue::ExternalLinkage, name, &H);
    };
    for (const char *n : {"getenv", "secure_getenv"})
      if (Function *F = shaped(n, "p", 'p')) {
        IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
        B.CreateRet(E.null());
      }
    if (Function *F = shaped("dlopen", "pi", 'p')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      Value *path = F->getArg(0);
      E.unless(B, F, B.CreateIsNotNull(path), handle(B, libs.size()));
      for (unsigned k = 0; k < libs.size(); ++k)
        E.unless(B, F, B.CreateNot(endsWith(B, path, libs[k].key)), handle(B, k));
      B.CreateRet(fail(B));
    }
    if (Function *F = shaped("dlsym", "pp", 'p')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      Value *h = F->getArg(0), *name = F->getArg(1);
      E.unless(B, F, B.CreateIsNotNull(name), E.null());
      Value *global = B.CreateOr(B.CreateOr(B.CreateIsNull(h), B.CreateICmpEQ(h, handle(B, libs.size()))),
                                 B.CreateICmpEQ(B.CreatePtrToInt(h, E.i64), E.minus1()));
      for (const std::string &s : looked(down, up)) {
        Value *mine = global;
        for (unsigned k = 0; k < libs.size(); ++k)
          if (libs[k].exports.count(s))
            mine = B.CreateOr(mine, B.CreateICmpEQ(h, handle(B, k)));
        bool exported = std::any_of(libs.begin(), libs.end(), [&](const auto &L) { return L.exports.count(s) > 0; });
        Constant *def = exported ? definition(down, up, s) : nullptr;
        if (!def)
          continue;
        Value *hit = B.CreateAnd(mine, B.CreateCall(streqF, {name, cstr(s)}));
        E.unless(B, F, B.CreateNot(hit), def);
      }
      B.CreateRet(fail(B));
    }
    if (Function *F = shaped("dlclose", "p", 'i')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      E.ret(B, F, B.getInt64(0));
    }
    if (Function *F = shaped("dlerror", "", 'p')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      Value *m = B.CreateLoad(E.p0, err);
      B.CreateStore(E.null(), err);
      B.CreateRet(m);
    }
    if (Function *F = shaped("opendir", "p", 'p')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      Value *path = F->getArg(0);
      E.unless(B, F, B.CreateIsNotNull(path), E.null());
      for (unsigned d = 0; d < dirs.size(); ++d) {
        Value *at = E.at(B, dirpos, B.getInt64(d));
        auto *open = BasicBlock::Create(ctx, "open", F), *next = BasicBlock::Create(ctx, "next", F);
        B.CreateCondBr(endsWith(B, path, dirs[d]), open, next);
        IRBuilder<> O(open);
        O.CreateStore(O.getInt64(0), at);
        O.CreateRet(at);
        B.SetInsertPoint(next);
      }
      B.CreateRet(E.null());
    }
    for (const char *n : {"readdir", "readdir64"}) {
      Function *F = E.linux64() ? shaped(n, "p", 'p') : nullptr;
      if (!F)
        continue;
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      Value *dp = F->getArg(0);
      Value *off = B.CreateSub(B.CreatePtrToInt(dp, E.i64), B.CreatePtrToInt(dirpos, E.i64));
      Value *d = B.CreateUDiv(off, B.getInt64(8));
      E.unless(B, F,
               B.CreateAnd(B.CreateICmpULT(off, B.getInt64(8 * dirs.size())),
                           B.CreateICmpEQ(B.CreateURem(off, B.getInt64(8)), B.getInt64(0))),
               E.null());
      Value *first = B.getInt64(0), *count = B.getInt64(0);
      for (unsigned k = 0; k < dirs.size(); ++k) {
        Value *is = B.CreateICmpEQ(d, B.getInt64(k));
        first = B.CreateSelect(is, B.getInt64(listing[k].first), first);
        count = B.CreateSelect(is, B.getInt64(listing[k].second), count);
      }
      Value *slot = E.at(B, dirpos, d);
      Value *pos = B.CreateLoad(E.i64, slot);
      E.unless(B, F, B.CreateICmpULT(pos, count), E.null());
      B.CreateStore(B.CreateAdd(pos, B.getInt64(1)), slot);
      B.CreateRet(E.at(B, ents, B.CreateAdd(first, pos)));
    }
    if (Function *F = shaped("closedir", "p", 'i')) {
      IRBuilder<> B(BasicBlock::Create(ctx, "entry", F));
      E.ret(B, F, B.getInt64(0));
    }
  }
};

} // namespace

void Client::emit(const Plan &P, Module &H) const {
  LLVMContext &ctx = H.getContext();
  H.setDataLayout(dl);
  H.setTargetTriple(down.getTargetTriple());
  Builder K(H, dl, inputBound, textBound);
  FileEnv files(K);
  files.plant(down, up);
  LoaderEnv(files, installed).plant(down, up);
  auto *p0 = PointerType::get(ctx, 0);
  // §2.4 Open: the names of the input file. A name carries a format key two
  // canonical ways: as the path's extension "f.k", and as a scheme prefix
  // "k:f". A reader that dispatches by key selects its target from either,
  // and a prefix also spares it from inferring the key from the bytes. The
  // library opens "f" for a prefixed name (it strips the scheme) and "f.k"
  // for an extension, both of which the file environment serves.
  std::vector<std::string> fileNames{"f"};
  for (const std::string &k : P.keys) {
    std::string lo = k;
    for (char &c : lo)
      c = (char)std::tolower((unsigned char)c);
    if (std::find(fileNames.begin(), fileNames.end(), k + ":f") == fileNames.end()) {
      fileNames.push_back(k + ":f");
      fileNames.push_back("f." + lo);
    }
  }
  auto named = [&](const std::vector<std::string> &ts) {
    std::vector<std::string> out = ts;
    if (std::find(ts.begin(), ts.end(), "f") != ts.end())
      for (size_t i = 1; i < fileNames.size(); ++i)
        if (std::find(out.begin(), out.end(), fileNames[i]) == out.end())
          out.push_back(fileNames[i]);
    return out;
  };
  Function *Main = Function::Create(FunctionType::get(Type::getInt32Ty(ctx), false), GlobalValue::ExternalLinkage, "main", &H);
  IRBuilder<> B(BasicBlock::Create(ctx, "entry", Main));
  K.start(B);
  // The handle the client holds for each type, and the generator of each
  // nonterminal of the grammar.
  std::map<std::string, GlobalVariable *> slots;
  auto slotOf = [&](const std::string &T) {
    auto it = slots.find(T);
    if (it != slots.end())
      return it->second;
    return slots[T] = new GlobalVariable(H, p0, false, GlobalValue::PrivateLinkage, ConstantPointerNull::get(p0),
                                         "client.held");
  };
  std::map<std::string, Function *> make;
  for (const auto &h : P.handles)
    if (!h.second.empty())
      make[h.first] = Function::Create(FunctionType::get(p0, false), GlobalValue::InternalLinkage, "client.make", &H);
  auto obtain = [&](IRBuilder<> &C, const std::string &T) -> Value * {
    auto it = make.find(T);
    return it != make.end() ? (Value *)C.CreateCall(it->second) : C.CreateLoad(p0, slotOf(T));
  };
  auto sizeOf = [&](const std::string &T) -> uint64_t {
    auto it = composite.find(T);
    return it == composite.end() ? 0 : it->second->getSizeInBits() / 8;
  };
  auto declare = [&](Function *F) {
    return H.getOrInsertFunction(F->getName(), F->getFunctionType());
  };
  // Val(tau), the values a client can hold of source type tau.
  //   V-Int     a scalar is any bit pattern;
  //   V-Text    char* is a text of at most L characters, one of each class
  //             the call reading it can tell apart (compared), wherever
  //             it lies: a formal or a field of an object the call reads;
  //   V-Fn      a function pointer is the most general callback of its type;
  //   V-Adt     a pointer to a type the interface constructs is a held handle;
  //   V-Obj     a pointer to a public type with pointer fields is one object
  //             of that type, built field by field;
  //   V-Bytes   any other pointer is a buffer of N bytes, each any value;
  //   Null      null, where the library compares the pointer with null (A1).
  // An object's bytes are any value and each pointer field then holds a
  // value of the field's type. Objects nest at most d deep; past it a field
  // points back to an enclosing object of its type, or is null where A1
  // allows; otherwise the client lies outside the bound and the path ends.
  auto def = [&](const DIType *T) { return definition(T); };
  auto members = [&](const DICompositeType *C) {
    std::vector<const DIDerivedType *> out;
    for (const DINode *N : C->getElements()) {
      auto *M = dyn_cast<DIDerivedType>(N);
      if (!M || M->isStaticMember() || M->isBitField() ||
          (M->getTag() != dwarf::DW_TAG_member && M->getTag() != dwarf::DW_TAG_inheritance))
        continue;
      out.push_back(M);
    }
    return out;
  };
  // Whether an object of type T holds a pointer, and whether its fields can
  // be filled at all: a dynamic class's vtable pointer is the constructor's,
  // not a value a client chooses.
  std::map<const DIType *, int> pointerMemo;
  std::function<int(const DIType *)> pointerIn = [&](const DIType *T) -> int {
    T = strip(T);
    if (!T)
      return 0;
    if (isPointer(T))
      return 1;
    auto it = pointerMemo.find(T);
    if (it != pointerMemo.end())
      return it->second;
    int r = 0;
    pointerMemo[T] = 0;
    if (auto *C = def(T)) {
      if (C->getTag() == dwarf::DW_TAG_array_type)
        r = pointerIn(C->getBaseType());
      else if (C->getTag() != dwarf::DW_TAG_enumeration_type)
        for (const DIDerivedType *M : members(C)) {
          if (M->isArtificial() && M->getName().starts_with("_vptr"))
            r = 2;
          r = std::max(r, pointerIn(M->getBaseType()));
        }
    }
    return pointerMemo[T] = r;
  };
  std::vector<std::pair<std::string, Value *>> enclosing;
  // Where a value the client builds is read by the call it is passed to:
  // what formal i of F reaches through path, plus base for an object built
  // in place. An aggregate the ABI splits into eightbytes is read as
  // formals i, i+1, ...; F is null where no call reads it (a callback's
  // result), and the texts there have no classes.
  // The data object the last top-level pointer argument built is, when it
  // is a plain buffer.
  std::string argBytes;
  struct Where {
    Function *F = nullptr;
    unsigned i = 0;
    std::vector<int64_t> path;
    int64_t base = 0;
    bool split = false;
  };
  // The place of the pointer at offset o of the object w describes.
  auto fieldOf = [](const Where &w, int64_t o) -> Where {
    int64_t at = w.base + o;
    if (!w.F || (w.split && at % 8))
      return {};
    if (w.split)
      return {w.F, w.i + (unsigned)(at / 8), {}, 0, false};
    Where f{w.F, w.i, w.path, 0, false};
    f.path.push_back(at);
    return f;
  };
  std::function<Value *(IRBuilder<> &, const DIType *, unsigned, bool, const Where &)> pointer;
  // The allowed set is empty. Null is a value only where the library
  // compares the pointer with null; otherwise no client execution passes
  // it, and the path ends.
  auto empty = [&](IRBuilder<> &C, bool nullable) -> Value * {
    if (nullable)
      return ConstantPointerNull::get(p0);
    K.require(C, C.getFalse());
    return ConstantPointerNull::get(p0);
  };
  std::function<void(IRBuilder<> &, Value *, const DIType *, unsigned, const Where &)> fields;
  // Seed path = choice 0. A nullable pointer the plan can establish must
  // therefore take the non-null arm first: otherwise the seed never installs
  // the configuration the witness requires (config args stay null).
  auto nullOr = [&](IRBuilder<> &C, bool nullable, const std::function<Value *(IRBuilder<> &)> &make) -> Value * {
    if (!nullable)
      return make(C);
    AllocaInst *slot = K.entryAlloca(C, p0);
    K.oneOf(C,
            {[&](IRBuilder<> &D) { D.CreateStore(make(D), slot); },
             [&](IRBuilder<> &D) { D.CreateStore(ConstantPointerNull::get(p0), slot); }},
            "null");
    return C.CreateLoad(p0, slot);
  };
  // The pointer fields of the object of type T at address at, its bytes
  // already the client's.
  fields = [&](IRBuilder<> &C, Value *at, const DIType *T, unsigned d, const Where &w) {
    T = strip(T);
    if (!pointerIn(T))
      return;
    if (isPointer(T)) {
      C.CreateStore(pointer(C, T, d, false, fieldOf(w, 0)), at);
      return;
    }
    auto *S = def(T);
    if (!S)
      return;
    auto inner = [&](int64_t o) {
      Where v = w;
      v.base += o;
      return v;
    };
    if (S->getTag() == dwarf::DW_TAG_array_type) {
      const DIType *E = S->getBaseType();
      uint64_t es = strip(E) ? strip(E)->getSizeInBits() / 8 : 0;
      for (uint64_t o = 0; es && o + es <= S->getSizeInBits() / 8; o += es)
        fields(C, C.CreateGEP(C.getInt8Ty(), at, C.getInt64(o)), E, d, inner((int64_t)o));
      return;
    }
    std::string name = source::name(S);
    auto put = [&](IRBuilder<> &D, const DIDerivedType *M) {
      int64_t o = (int64_t)(M->getOffsetInBits() / 8);
      Value *f = D.CreateGEP(D.getInt8Ty(), at, D.getInt64(o));
      if (isPointer(strip(M->getBaseType())))
        D.CreateStore(pointer(D, M->getBaseType(), d, nullFields.count({name, o}) > 0, fieldOf(w, o)), f);
      else
        fields(D, f, M->getBaseType(), d, inner(o));
    };
    if (S->getTag() == dwarf::DW_TAG_union_type) {
      // A union holds one member: the client picks which.
      std::vector<std::function<void(IRBuilder<> &)>> alts;
      for (const DIDerivedType *M : members(S))
        alts.push_back([&, M](IRBuilder<> &D) { put(D, M); });
      K.oneOf(C, alts, "union");
      return;
    }
    for (const DIDerivedType *M : members(S))
      if (pointerIn(M->getBaseType()))
        put(C, M);
    // A3 for fields: the bounding field stays within what its pointer field
    // was given, by the rule for formals.
    for (const DIDerivedType *M : members(S)) {
      const DIType *MT = strip(M->getBaseType());
      auto fl = fieldLen.find({name, (int64_t)(M->getOffsetInBits() / 8)});
      if (!isPointer(MT) || fl == fieldLen.end())
        continue;
      for (const DIDerivedType *N : members(S)) {
        auto *NB = dyn_cast_or_null<DIBasicType>(strip(N->getBaseType()));
        if (!NB || (int64_t)(N->getOffsetInBits() / 8) != fl->second || !NB->getSizeInBits())
          continue;
        std::string k;
        Kind kind = classify(MT, k);
        const DIType *E = strip(cast<DIDerivedType>(MT)->getBaseType());
        uint64_t n = kind == Kind::Text                    ? textBound
                     : E && pointerIn(E) != 0              ? 1
                                                           : K.capacity(E ? std::max<uint64_t>(1, E->getSizeInBits() / 8) : 1);
        Type *IT = C.getIntNTy(NB->getSizeInBits());
        Value *v = C.CreateLoad(IT, C.CreateGEP(C.getInt8Ty(), at, C.getInt64(fl->second)));
        K.require(C, C.CreateICmpULE(v, ConstantInt::get(IT, n)));
      }
    }
  };
  pointer = [&](IRBuilder<> &C, const DIType *T, unsigned d, bool nullable, const Where &w) -> Value * {
    T = strip(T);
    const DIType *P = isPointer(T) ? strip(cast<DIDerivedType>(T)->getBaseType()) : nullptr;
    if (P && isa<DISubroutineType>(P)) {
      FunctionType *FT = fnTypeOf(T);
      if (!FT)
        return empty(C, nullable);
      auto rs = cast<DISubroutineType>(P)->getTypeArray();
      const DIType *R = rs.size() ? strip(rs[0]) : nullptr;
      auto *RC = R && isPointer(R) ? def(cast<DIDerivedType>(R)->getBaseType()) : nullptr;
      bool record = RC && RC->getTag() != dwarf::DW_TAG_enumeration_type && RC->getTag() != dwarf::DW_TAG_array_type;
      // The callback is a function of its own: it shares no object under
      // construction in the caller.
      auto *ST = cast<DISubroutineType>(P);
      Function *cb = record ? K.callback(FT, R, [&, R](IRBuilder<> &D) {
        auto outer = std::move(enclosing);
        enclosing.clear();
        Value *v = pointer(D, R, d, false, Where{});
        enclosing = std::move(outer);
        return v;
      }, ST)
                                       : K.callback(FT, nullptr, nullptr, ST);
      return nullOr(C, nullable, [cb](IRBuilder<> &) { return cb; });
    }
    if (auto *B = dyn_cast_or_null<DIBasicType>(P))
      if (B->getEncoding() == dwarf::DW_ATE_signed_char && B->getName() == "char")
        return nullOr(C, nullable, [&](IRBuilder<> &D) {
          return w.F ? K.text(D, compared(w.F, w.i, w.path)) : K.text(D);
        });
    auto *S = def(P);
    std::string key = S ? typeKey(S) : "";
    bool record = S && S->getTag() != dwarf::DW_TAG_enumeration_type && S->getTag() != dwarf::DW_TAG_array_type;
    if (record && constructed.count(key)) {
      // V-Adt: a held handle. One the client cannot construct is no value.
      if (!cost.count(key))
        return empty(C, nullable);
      return nullOr(C, nullable, [&](IRBuilder<> &D) { return obtain(D, key); });
    }
    // V-Opaque, and a class whose vptr only a constructor writes: the
    // client has no object of this type.
    int ptrs = pointerIn(P);
    if ((record && (key.empty() ? S->isForwardDecl() : !isPublic(key))) || ptrs == 2)
      return empty(C, nullable);
    if (!ptrs) {
      uint64_t elem = P ? std::max<uint64_t>(1, P->getSizeInBits() / 8) : 1;
      Value *v = nullOr(C, nullable, [&](IRBuilder<> &D) { return K.bytes(D, elem); });
      if (w.F && w.path.empty())
        argBytes = K.lastBytes;
      return v;
    }
    if (d == 0) {
      for (auto it = enclosing.rbegin(); it != enclosing.rend(); ++it)
        if (it->first == key)
          return it->second;
      return empty(C, nullable);
    }
    return nullOr(C, nullable, [&](IRBuilder<> &D) -> Value * {
      Value *o = K.object(D, P->getSizeInBits() / 8);
      enclosing.push_back({key, o});
      fields(D, o, P, d - 1, Where{w.F, w.i, w.path, 0, false});
      enclosing.pop_back();
      return o;
    });
  };
  // One call of F with client arguments. 'made' receives the handle F
  // produces (result or out-parameter) for type T.
  auto call = [&](IRBuilder<> &C, Function *F, const std::string &makesT, int outAt,
                  const std::vector<std::vector<Guard>> *guards = nullptr,
                  const std::vector<Cell> *files = nullptr) {
    auto sig = signature(F);
    FunctionType *FT = F->getFunctionType();
    unsigned shift = F->hasParamAttribute(0, Attribute::StructRet) ? 1 : 0;
    auto at = irParams(F);
    auto declared = [&](int k) -> const DIType * { return k >= 0 ? sig[k].di : nullptr; };
    // An argument the witness reads a cell of is not null.
    std::set<int> rooted;
    if (guards)
      for (const auto &conj : *guards)
        for (const Guard &g : conj)
          rooted.insert(g.root);
    if (files)
      for (const Cell &c : *files)
        rooted.insert(c.root);
    std::vector<Value *> args;
    std::vector<std::pair<AllocaInst *, std::string>> outs;
    Value *storage = nullptr;
    // The data object a raw buffer argument holds, and each length object
    // with the buffers it bounds: a length that bounds one data buffer is
    // the size of the file in it (named length:<data>).
    std::map<unsigned, std::string> dataArg;
    std::vector<std::pair<CallInst *, std::vector<unsigned>>> lengths;
    for (unsigned i = 0; i < FT->getNumParams(); ++i) {
      Type *T = FT->getParamType(i);
      if (i < shift) {
        Type *S = F->getParamStructRetType(i);
        args.push_back(K.entryAlloca(C, S ? S : C.getInt64Ty()));
        continue;
      }
      Param p;
      p.kind = T->isPointerTy() ? Kind::Bytes : Kind::Scalar;
      if (at[i] >= 0)
        p = sig[at[i]];
      // V-Agg: a structure passed by value is built field by field, then
      // lowered as the ABI passes it: in memory (byval), or as consecutive
      // eightbytes.
      if (F->hasParamAttribute(i, Attribute::ByVal) || (at[i] >= 0 && p.kind == Kind::Aggregate)) {
        bool byval = F->hasParamAttribute(i, Attribute::ByVal) || (p.indirect && T->isPointerTy());
        uint64_t size = F->hasParamAttribute(i, Attribute::ByVal) ? dl.getTypeAllocSize(F->getParamByValType(i))
                                                                   : std::max<uint64_t>(p.size, 1);
        unsigned last = i + 1;
        if (!byval)
          while (last < FT->getNumParams() && at[last] < 0)
            ++last;
        uint64_t span = size;
        for (unsigned j = i; !byval && j < last; ++j)
          span = std::max<uint64_t>(span, 8 * (j - i) + dl.getTypeAllocSize(FT->getParamType(j)));
        // V-Adt by value: a class the interface constructs is the value its
        // constructor made, passed as the ABI passes it.
        Value *A = nullptr;
        auto *R = def(declared(at[i]));
        std::string key = R ? typeKey(R) : "";
        if (at[i] >= 0 && constructed.count(key) && make.count(key))
          A = obtain(C, key);
        else {
          A = K.entryAlloca(C, ArrayType::get(C.getInt8Ty(), span));
          C.CreateCall(K.mkSym, {A, C.getInt64(span), C.CreateGlobalStringPtr("aggregate." + std::to_string(K.names++))});
          fields(C, A, declared(at[i]), objectDepth, Where{F, i, {}, 0, !byval});
        }
        if (byval) {
          args.push_back(A);
          continue;
        }
        for (unsigned j = i; j < last; ++j)
          args.push_back(C.CreateLoad(FT->getParamType(j), C.CreateGEP(C.getInt8Ty(), A, C.getInt64(8 * (j - i)))));
        i = last - 1;
        continue;
      }
      Value *v = nullptr;
      bool plainArg = false;
      if (T->isPointerTy() && p.va) {
        // The client's own va_list, started in a variadic function of the
        // client that received no further arguments.
        AllocaInst *A = K.entryAlloca(C, ArrayType::get(C.getInt8Ty(), p.elem));
        C.CreateMemSet(A, C.getInt8(0), C.getInt64(p.elem), MaybeAlign(1));
        args.push_back(A);
        continue;
      }
      if (T->isPointerTy()) {
        bool nullable = nullTested(F, i) && !rooted.count((int)i);
        switch (p.kind) {
        case Kind::Handle:
        case Kind::Object:
          if (held(p) || p.kind == Kind::Handle) {
            if (!cost.count(p.type))
              // §2.2 V-Opaque 정제: 생성자 없는 불투명 포인터의 유일한 클라이언트
              // 값은 NULL이다. 경로를 죽이지 않고 NULL을 넘긴다.
              v = ConstantPointerNull::get(p0);
            else
              v = nullOr(C, nullable, [&](IRBuilder<> &D) { return obtain(D, p.type); });
            break;
          }
          v = pointer(C, declared(at[i]), objectDepth, nullable, Where{F, i});
          break;
        case Kind::Text:
          // The format of a variadic function, or the one before a va_list,
          // is the client's own literal: it passes no further arguments, so
          // the format has no directives.
          if ((FT->isVarArg() && i + 1 == FT->getNumParams()) ||
              (i + 1 < FT->getNumParams() && at[i + 1] >= 0 && sig[at[i + 1]].va)) {
            v = C.CreateGlobalStringPtr("");
            break;
          }
          v = nullOr(C, nullable, [&](IRBuilder<> &D) { return K.text(D, named(compared(F, i))); });
          break;
        case Kind::Callback: {
          auto ct = fnTypes.find({F, i});
          if (ct == fnTypes.end()) {
            v = empty(C, nullable);
            break;
          }
          auto dt = fnDecl.find({F, i});
          if (dt != fnDecl.end()) {
            v = pointer(C, dt->second, objectDepth, nullable, Where{F, i});
            break;
          }
          Function *cb = K.callback(ct->second);
          v = nullOr(C, nullable, [cb](IRBuilder<> &) { return cb; });
          break;
        }
        case Kind::Storage:
          v = storage = K.object(C, std::max<uint64_t>(sizeOf(p.type), 1));
          break;
        case Kind::Out: {
          AllocaInst *A = K.entryAlloca(C, p0);
          C.CreateStore(ConstantPointerNull::get(p0), A);
          outs.push_back({A, p.type});
          v = A;
          break;
        }
        default:
          if (at[i] >= 0) {
            argBytes.clear();
            v = pointer(C, declared(at[i]), objectDepth, nullable, Where{F, i});
            if (!argBytes.empty())
              dataArg[i] = argBytes;
            break;
          }
          v = nullOr(C, nullable, [&](IRBuilder<> &D) { return K.bytes(D, p.elem); });
          dataArg[i] = K.lastBytes;
          break;
        }
      } else if (auto bs = boundBy(F, i); T->isIntegerTy() && !bs.empty()) {
        // The length counts elements or bytes; either way it stays within
        // a buffer when it is at most the element count: a buffer of N
        // bytes, a text of L characters, or the one object V-Obj builds. It
        // must stay within every buffer it bounds.
        uint64_t n = UINT64_MAX;
        for (unsigned b : bs) {
          uint64_t nb = 1;
          if (at[b] >= 0) {
            const Param &q = sig[at[b]];
            const DIType *D = strip(q.di);
            bool one = isPointer(D) && pointerIn(strip(cast<DIDerivedType>(D)->getBaseType())) != 0;
            nb = q.kind == Kind::Text ? textBound : one ? 1 : K.capacity(q.elem);
          }
          n = std::min(n, nb);
        }
        // Choice 0 = full buffer: a zero length satisfies ule n but libraries
        // treat it as empty I/O (e.g. TIFFReadEncodedStrip size→0 skips
        // decode). Seed must exercise the bounded call; symbolic covers the
        // rest of {0..n}.
        AllocaInst *lenSlot = K.entryAlloca(C, T);
        std::vector<std::function<void(IRBuilder<> &)>> lenAlts;
        lenAlts.push_back([&, lenSlot, T, n](IRBuilder<> &A) {
          A.CreateStore(ConstantInt::get(T, n), lenSlot);
        });
        lenAlts.push_back([&, lenSlot, T, n, bs](IRBuilder<> &A) {
          Value *s = K.symbolic(A, T, "length");
          lengths.push_back({cast<CallInst>(cast<Instruction>(s)->getPrevNode()), bs});
          K.require(A, A.CreateICmpULE(s, ConstantInt::get(T, n)));
          A.CreateStore(s, lenSlot);
        });
        K.oneOf(C, lenAlts, "length");
        v = C.CreateLoad(T, lenSlot);
      } else {
        v = K.symbolic(C, T, "arg");
        plainArg = true;
      }
      // §3.6 생성자 레버: 이 형식인자가 경로 셀의 값을 정하면 클라이언트는 셀이
      // 요구하는 값을 고른다 — 설정 가드와 같은 의미로, 경로를 가르지 않고 만족하는
      // 값 중에서(만족하지 않는 symbolic 값은 대표값으로 접는다).
      if (T->isIntegerTy())
        if (auto lit = P.levers.find(F); lit != P.levers.end())
          for (const Lever &l : lit->second) {
            if (l.formal != i)
              continue;
            if (l.eq && l.values.size() == 1 && plainArg) {
              v = ConstantInt::get(T, (uint64_t)l.values[0], true);
              continue;
            }
            Value *m = l.eq ? C.getFalse() : C.getTrue();
            for (int64_t k : l.values) {
              Value *e = C.CreateICmpEQ(v, ConstantInt::get(T, (uint64_t)k, true));
              m = l.eq ? C.CreateOr(m, e) : C.CreateAnd(m, C.CreateNot(e));
            }
            int64_t canon = 0;
            if (l.eq)
              canon = l.values[0];
            else
              while (std::find(l.values.begin(), l.values.end(), canon) != l.values.end())
                ++canon;
            v = C.CreateSelect(m, v, ConstantInt::get(T, (uint64_t)canon, true));
          }
      args.push_back(v);
    }
    for (auto &[mk, bs] : lengths) {
      std::set<std::string> data;
      bool raw = true;
      for (unsigned b : bs) {
        auto d = dataArg.find(b);
        if (d == dataArg.end())
          raw = false;
        else
          data.insert(d->second);
      }
      if (raw && data.size() == 1)
        mk->setArgOperand(2, C.CreateGlobalStringPtr("length:" + *data.begin()));
    }
    // Variadic: the client may pass any further integers.
    if (FT->isVarArg())
      for (unsigned j = 0; j < 2; ++j)
        args.push_back(K.symbolic(C, C.getInt64Ty(), "vararg"));
    // The client names its input file in the fields the entry opens it by.
    if (files)
      for (const Cell &c : *files) {
        int64_t off = 0;
        Type *FT = nullptr;
        if ((size_t)c.root >= args.size() || !args[c.root]->getType()->isPointerTy() || !place(c, off, FT))
          continue;
        Value *at = C.CreateGEP(C.getInt8Ty(), args[c.root], C.getInt64(off));
        auto *AT = dyn_cast<ArrayType>(FT);
        bool array = AT && AT->getElementType()->isIntegerTy(8);
        if (!array && !FT->isPointerTy())
          continue;
        std::vector<std::function<void(IRBuilder<> &)>> alts;
        for (const std::string &s : fileNames) {
          if (array && AT->getNumElements() < s.size() + 1)
            continue;
          alts.push_back([&, at, array, s](IRBuilder<> &D) {
            if (array)
              D.CreateMemCpy(at, MaybeAlign(1), D.CreateGlobalStringPtr(s), MaybeAlign(1), s.size() + 1);
            else
              D.CreateStore(D.CreateGlobalStringPtr(s), at);
          });
        }
        K.oneOf(C, alts, "file");
      }
    // One witness suffices: pick one, set its configuration, and assume
    // its guards.
    if (guards && !guards->empty()) {
      std::vector<std::function<void(IRBuilder<> &)>> wit;
      for (const auto &conj : *guards)
        wit.push_back([&, conj](IRBuilder<> &W) {
          for (const Guard &g : conj) {
            if ((size_t)g.root >= args.size() || !args[g.root]->getType()->isPointerTy())
              continue;
            Type *IT = W.getIntNTy(g.width);
            Value *at = W.CreateGEP(W.getInt8Ty(), args[g.root], W.getInt64(g.off));
            if (g.config && g.eq && g.values.size() == 1) {
              W.CreateStore(ConstantInt::get(IT, (uint64_t)g.values[0], true), at);
              continue;
            }
            Value *v = g.config ? K.symbolic(W, IT, "config") : W.CreateLoad(IT, at);
            Value *m = g.eq ? W.getFalse() : W.getTrue();
            for (int64_t k : g.values) {
              Value *e = W.CreateICmpEQ(v, ConstantInt::get(IT, (uint64_t)k, true));
              m = g.eq ? W.CreateOr(m, e) : W.CreateAnd(m, W.CreateNot(e));
            }
            if (!g.config) {
              K.require(W, m);
              continue;
            }
            // §4 설정: 값은 클라이언트의 것이므로 경로를 가르지 않고 만족하는 값
            // 중에서 고른다 — 만족하지 않는 symbolic 값은 대표값(등식: 첫 값,
            // 부등식: 제외되지 않은 최소 음이 아닌 값)으로 접는다. 시드 경로가
            // 설정을 만족한 채 시작하고(§6), 값 공간은 만족 집합 전체다.
            int64_t canon = 0;
            if (g.eq)
              canon = g.values[0];
            else
              while (std::find(g.values.begin(), g.values.end(), canon) != g.values.end())
                ++canon;
            v = W.CreateSelect(m, v, ConstantInt::get(IT, (uint64_t)canon, true));
            W.CreateStore(v, at);
          }
        });
      K.oneOf(C, wit, "witness");
    }
    // Held producers leave nested pointer fields null. If φ names a nested
    // held type under an entry argument (ImageInfo.custom_stream →
    // CustomStreamInfo for CustomStreamToImage), install that object and
    // fill its pointer fields (reader callbacks) before the call — otherwise
    // the static path dies on the library's null assert and nurs:sink never
    // gets to walk π.
    if (std::find(P.entries.begin(), P.entries.end(), F) != P.entries.end()) {
      auto norm = [](std::string t) {
        if (t.rfind("struct.", 0) == 0)
          t = t.substr(7);
        else if (t.rfind("class.", 0) == 0)
          t = t.substr(6);
        return t;
      };
      std::set<std::string> need;
      for (const WitnessPlan &W : P.witnesses) {
        bool here = W.first == F;
        for (Function *E : W.entries)
          here = here || E == F;
        if (!here)
          continue;
        for (const Realized &r : W.cells) {
          std::string k = norm(r.cell.type);
          if (make.count(k))
            need.insert(k);
        }
      }
      if (!need.empty()) {
        auto ps = signature(F);
        auto atp = irParams(F);
        for (unsigned i = 0; i < args.size() && i < FT->getNumParams(); ++i) {
          if (atp[i] < 0 || !held(ps[atp[i]]) || !args[i]->getType()->isPointerTy())
            continue;
          auto cit = composite.find(ps[atp[i]].type);
          if (cit == composite.end())
            continue;
          for (const DIDerivedType *M : members(cit->second)) {
            const DIType *BT = strip(M->getBaseType());
            if (!isPointer(BT))
              continue;
            auto *Pointee = def(cast<DIDerivedType>(BT)->getBaseType());
            if (!Pointee)
              continue;
            std::string pk = typeKey(Pointee);
            if (!need.count(pk) || !make.count(pk))
              continue;
            int64_t o = (int64_t)(M->getOffsetInBits() / 8);
            Value *slot = C.CreateGEP(C.getInt8Ty(), args[i], C.getInt64(o));
            Value *cur = C.CreateLoad(p0, slot);
            Value *child = obtain(C, pk);
            // Producer sets the representation invariant; fields() installs
            // the function pointers φ/the callee will null-check (reader).
            // Prefer the complete composite: the argument field's pointee is
            // often only a forward declaration in this CU.
            const DIType *full = Pointee;
            if (auto fit = composite.find(pk); fit != composite.end())
              full = fit->second;
            fields(C, child, full, objectDepth, Where{F, i, {}, o, false});
            Value *use = C.CreateSelect(C.CreateICmpEQ(cur, ConstantPointerNull::get(p0)), child, cur);
            C.CreateStore(use, slot);
          }
        }
      }
    }
    Value *r = C.CreateCall(declare(F), args);
    if (!makesT.empty() && outAt == -1 && r->getType()->isPointerTy())
      C.CreateStore(r, slotOf(makesT));
    if (!makesT.empty() && outAt == Owner && shift)
      C.CreateStore(C.CreateLoad(p0, args[0]), slotOf(makesT));
    if (!makesT.empty() && outAt == Construct && storage)
      C.CreateStore(storage, slotOf(makesT));
    for (const auto &o : outs)
      if (!o.second.empty()) {
        Value *got = C.CreateLoad(p0, o.first);
        // A handle the call wrote out replaces the held one of that type.
        Value *nz = C.CreateICmpNE(got, ConstantPointerNull::get(p0));
        GlobalVariable *slot = slotOf(o.second);
        C.CreateStore(C.CreateSelect(nz, got, C.CreateLoad(p0, slot)), slot);
      }
  };
  // Choices are made as late as possible: a handle every alternative of a
  // choice takes is obtained before it, (a and b) or (a and c) = a and (b or
  // c). make_T memoizes, so the alternatives use that same handle, and the
  // library work that constructs it is done once for all of them.
  auto hoist = [&](IRBuilder<> &C, const std::vector<Function *> &alts) {
    std::set<std::string> common;
    for (size_t a = 0; a < alts.size(); ++a) {
      std::set<std::string> need;
      for (const Param &p : signature(alts[a]))
        if (held(p) && make.count(p.type))
          need.insert(p.type);
      if (a == 0)
        common = need;
      else {
        std::set<std::string> both;
        for (const std::string &T : need)
          if (common.count(T))
            both.insert(T);
        common = both;
      }
    }
    std::vector<std::string> order(common.begin(), common.end());
    std::sort(order.begin(), order.end(),
              [&](const std::string &a, const std::string &b) { return cost.at(a) < cost.at(b); });
    for (const std::string &T : order)
      C.CreateCall(make.at(T));
  };
  for (const auto &h : P.handles) {
    auto mk = make.find(h.first);
    if (mk == make.end())
      continue;
    Function *G = mk->second;
    auto *entry = BasicBlock::Create(ctx, "entry", G);
    auto *have = BasicBlock::Create(ctx, "have", G);
    auto *expand = BasicBlock::Create(ctx, "expand", G);
    IRBuilder<> E(entry);
    Value *cur = E.CreateLoad(p0, slotOf(h.first));
    E.CreateCondBr(E.CreateICmpNE(cur, ConstantPointerNull::get(p0)), have, expand);
    IRBuilder<>(have).CreateRet(cur);
    IRBuilder<> X(expand);
    std::vector<Function *> fs;
    for (const Producer &pr : h.second)
      fs.push_back(pr.fn);
    hoist(X, fs);
    std::vector<std::function<void(IRBuilder<> &)>> alts;
    for (const Producer &pr : h.second)
      alts.push_back([&, pr, T = h.first](IRBuilder<> &C) {
        hoist(C, {pr.fn});
        auto d = P.deps.find({pr.fn, T});
        if (d != P.deps.end())
          for (unsigned k = 0; k < depSlots; ++k) {
            // §3.11 Definition O: (l_1 | ... | skip | d_1 | ...), the
            // dependences that take the input before the skip.
            std::vector<std::function<void(IRBuilder<> &)>> pre;
            auto skip = std::find_if(d->second.begin(), d->second.end(),
                                     [&](Function *W) { return channel(W) == Channel::None; });
            for (auto it = d->second.begin(); it != d->second.end(); ++it) {
              if (it == skip)
                pre.push_back([](IRBuilder<> &) {});
              pre.push_back([&, W = *it](IRBuilder<> &D) { call(D, W, "", -1); });
            }
            if (skip == d->second.end())
              pre.push_back([](IRBuilder<> &) {});
            K.oneOf(C, pre, "depend");
          }
        call(C, pr.fn, T, pr.out);
      });
    K.oneOf(X, alts, "make");
    Value *got = X.CreateLoad(p0, slotOf(h.first));
    K.require(X, X.CreateICmpNE(got, ConstantPointerNull::get(p0)));
    X.CreateRet(got);
  }
  hoist(B, P.entries);
  // §4: (skip | w)^K, w ∈ writers (정의 6의 최소 덮개).
  for (unsigned k = 0; k < writerSlots && !P.writers.empty(); ++k) {
    std::vector<std::function<void(IRBuilder<> &)>> alts{[](IRBuilder<> &) {}};
    for (Function *W : P.writers)
      alts.push_back([&, W](IRBuilder<> &C) { call(C, W, "", -1); });
    K.oneOf(B, alts, "write");
  }
  // §3.8 정의 3.8.4 키 세터 레버: entry를 부르기 직전, 보유 핸들 h 위에서 키 세터
  // W(h, 태그, v)를 호출하거나 건너뛴다(§4 (κ | skip)). h는 make_T가 메모한 그 핸들이므로
  // entry가 받는 핸들과 같다. v는 심볼릭 정수에서 may 계층이 준 조건(preds)을 만족하는
  // 값으로 접는다.
  auto keySet = [&](IRBuilder<> &C, Function *W, const Keyed &k) {
    FunctionType *FT = W->getFunctionType();
    auto sig = signature(W);
    auto at = irParams(W);
    std::vector<Value *> args;
    for (unsigned i = 0; i < FT->getNumParams(); ++i) {
      Type *T = FT->getParamType(i);
      if (at[i] == (int)k.obj && T->isPointerTy()) {
        args.push_back(obtain(C, sig[at[i]].type));
      } else if (at[i] == k.tag && T->isIntegerTy()) {
        args.push_back(ConstantInt::get(T, (uint64_t)k.tagV, true));
      } else if (T->isPointerTy()) {
        args.push_back(ConstantPointerNull::get(p0));
      } else {
        args.push_back(K.symbolic(C, T, "arg"));
      }
    }
    if (FT->isVarArg()) {
      // The variadic value the key setter writes into target. One i32 chosen
      // to satisfy preds (=, !=, has, lacks), promoted as the ABI passes it.
      Value *v = K.symbolic(C, C.getInt32Ty(), "keyed");
      Type *IT = v->getType();
      for (const auto &[op, val] : k.preds) {
        if (op == "=") {
          v = ConstantInt::get(IT, (uint64_t)val, true);
        } else if (op == "!=") {
          Value *bad = C.CreateICmpEQ(v, ConstantInt::get(IT, (uint64_t)val, true));
          v = C.CreateSelect(bad, ConstantInt::get(IT, (uint64_t)(val + 1), true), v);
        } else if (op == "has") {
          Value *m = ConstantInt::get(IT, (uint64_t)val, true);
          Value *ok = C.CreateICmpEQ(C.CreateAnd(v, m), m);
          v = C.CreateSelect(ok, v, C.CreateOr(v, m));
        } else if (op == "lacks") {
          Value *m = ConstantInt::get(IT, (uint64_t)val, true);
          Value *ok = C.CreateICmpEQ(C.CreateAnd(v, m), ConstantInt::get(IT, 0));
          v = C.CreateSelect(ok, v, C.CreateAnd(v, C.CreateNot(m)));
        }
      }
      args.push_back(v);
    }
    C.CreateCall(declare(W), args);
  };
  // §3.8 정의 3.8.6 이름 키 설정: entry 직전, entry가 받을 그 핸들 위에서
  // S(o, κ, v)를 부르거나 건너뛴다. κ는 조회 지점이 짓는 그대로 짓고, v는 S가
  // 받는 정수 전체에서 고른다.
  auto nameSet = [&](IRBuilder<> &C, const Named &n) {
    Value *key = C.CreateGlobalStringPtr(n.key);
    if (n.init) {
      AllocaInst *slot = K.entryAlloca(C, n.slot);
      std::vector<Value *> as;
      for (unsigned a = 0; a < n.initArgs.size(); ++a)
        as.push_back(a == n.slotAt ? slot : a == n.textAt ? key : (Value *)n.initArgs[a]);
      C.CreateCall(declare(n.init), as);
      key = slot;
    }
    FunctionType *FT = n.setter->getFunctionType();
    std::vector<Value *> args;
    for (unsigned i = 0; i < FT->getNumParams(); ++i)
      args.push_back(i == n.obj     ? obtain(C, n.type)
                     : i == n.name  ? key
                     : i == n.value ? K.symbolic(C, FT->getParamType(i), "named")
                                    : (Value *)n.rest[i]);
    C.CreateCall(declare(n.setter), args);
  };
  {
    // Primary witness entry only. The plan still records every witness entry
    // for obligations/report, but main must not oneOf across them: equal
    // weight on Write when the primary π₀ is Read burns the concolic budget
    // off the guided path (nurs:sink / sp.wit k=0).
    std::vector<Function *> entries = P.entries;
    if (!P.firsts.empty())
      entries = {P.firsts.front()};
    std::vector<std::function<void(IRBuilder<> &)>> alts;
    for (Function *E : entries)
      alts.push_back([&, E](IRBuilder<> &C) {
        auto kit = P.keyed.find(E);
        if (kit != P.keyed.end())
          for (const auto &[W, k] : kit->second)
            K.oneOf(C, {[&, W = W, &k = k](IRBuilder<> &A) { keySet(A, W, k); }, [](IRBuilder<> &) {}}, "key");
        if (auto nit = P.named.find(E); nit != P.named.end())
          for (const Named &n : nit->second)
            K.oneOf(C, {[&](IRBuilder<> &A) { nameSet(A, n); }, [](IRBuilder<> &) {}}, "named");
        auto g = P.guards.find(E);
        auto f = P.files.find(E);
        call(C, E, "", -1, g == P.guards.end() ? nullptr : &g->second, f == P.files.end() ? nullptr : &f->second);
      });
    K.oneOf(B, alts, "entry");
  }
  B.CreateRet(B.getInt32(0));
}
