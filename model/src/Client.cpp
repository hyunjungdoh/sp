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

#include "llvm/IR/DebugInfoMetadata.h"

#include <cstdio>
#include <functional>
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

std::set<std::string> dynamicSymbols(const std::string &so) {
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
    if (kind != "T" && kind != "W")
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
  std::string so = jsonString(text, "so", text.find("\"ds_core\""));
  return so.empty() ? std::set<std::string>{} : dynamicSymbols(so);
}

Client::Client(Module &down, Module &up, const fs::path &dir) : down(down), up(up), dl(down.getDataLayout()) {
  std::ifstream js(dir / "surfaces.json");
  std::string text((std::istreambuf_iterator<char>(js)), std::istreambuf_iterator<char>());
  std::string dso = jsonString(text, "so", text.find("\"ds_core\""));
  std::string uso = jsonString(text, "so", text.find("\"us\""));
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
        for (const auto &f : fieldsOf(L->getPointerOperand()))
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
        for (const auto &f : fieldsOf(S->getPointerOperand())) {
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

// A1 for fields: a load of field (S, off) whose value, directly or through
// the -O0 slot it is stored to, is compared with null.
void Client::buildNullFields() {
  auto isNull = [](Value *V) { return isa<ConstantPointerNull>(V); };
  for (const auto &kv : bodies)
    for (Instruction &I : instructions(*kv.second)) {
      auto *C = dyn_cast<ICmpInst>(&I);
      if (!C || !C->isEquality() || !(isNull(C->getOperand(0)) || isNull(C->getOperand(1))) || !nullReturns(C))
        continue;
      Value *V = (isNull(C->getOperand(0)) ? C->getOperand(1) : C->getOperand(0))->stripPointerCasts();
      std::vector<LoadInst *> loads;
      if (auto *L = dyn_cast<LoadInst>(V)) {
        loads.push_back(L);
        if (auto *Al = dyn_cast<AllocaInst>(fieldAddress(L->getPointerOperand())))
          for (User *U : Al->users())
            if (auto *S = dyn_cast<StoreInst>(U))
              if (S->getPointerOperand()->stripPointerCasts() == Al)
                if (auto *F = dyn_cast<LoadInst>(S->getValueOperand()->stripPointerCasts()))
                  loads.push_back(F);
      }
      for (LoadInst *L : loads)
        for (const auto &f : fieldsOf(L->getPointerOperand()))
          nullFields.insert(f);
    }
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
          for (const auto &f : fieldsOf(L->getPointerOperand()))
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

// The fields (S, off) a constant-offset GEP addresses, one per struct level
// its indices pass, innermost last. A GEP of one zero index only
// reinterprets the pointer; the first field's GEP has a second index.
std::vector<std::pair<std::string, int64_t>> Client::fieldsOf(Value *P) const {
  P = fieldAddress(P);
  auto *G = dyn_cast<GEPOperator>(P);
  if (!G || (G->hasAllZeroIndices() && G->getNumIndices() < 2))
    return {};
  return source::levels(G, dl);
}

// Function constants a global initializer places in struct fields. D is the
// source type of the object C initializes.
void Client::constFields(Constant *C, Type *T, std::string S, int64_t at, const DIType *D) {
  if (!C)
    return;
  if (auto *F = dyn_cast<Function>(C->stripPointerCasts())) {
    if (!S.empty())
      if (Function *B = body(F->getName().str()))
        fnField[{S, at}].insert(B);
    return;
  }
  if (auto *STy = dyn_cast<StructType>(T)) {
    if (!isa<ConstantStruct>(C))
      return;
    const StructLayout *L = dl.getStructLayout(STy);
    std::string self = STy->hasName() ? source::key(D, STy, dl) : S;
    for (unsigned i = 0; i < STy->getNumElements(); ++i) {
      int64_t o = (int64_t)L->getElementOffset(i);
      Type *E = STy->getElementType(i);
      const DIType *M = D ? source::member(D, (uint64_t)o, E->isSized() ? dl.getTypeAllocSize(E).getFixedValue() : 0)
                          : nullptr;
      constFields(C->getAggregateElement(i), E, self, STy->hasName() ? o : at + o, M);
    }
  } else if (auto *AT = dyn_cast<ArrayType>(T)) {
    if (!isa<ConstantArray>(C))
      return;
    for (unsigned i = 0; i < AT->getNumElements(); ++i)
      constFields(C->getAggregateElement(i), AT->getElementType(), S,
                  at + (int64_t)(i * dl.getTypeAllocSize(AT->getElementType())), source::element(D));
  }
}

// Call edges. A direct call is its callee. An indirect call whose callee is
// loaded from field (S, off) goes to the functions the program stores into
// that field or a global initializer places there (the second layer of
// multi-layer type analysis); any other indirect call, or one through a
// field that holds no function constant, goes to every address-taken
// function of its type (the first layer).
void Client::buildCalls() {
  for (Module *M : {&down, &up})
    for (GlobalVariable &G : M->globals())
      if (G.hasInitializer())
        constFields(G.getInitializer(), G.getValueType(), "", 0, source::ofGlobal(G));
  for (const auto &kv : bodies)
    for (Instruction &I : instructions(*kv.second))
      if (auto *S = dyn_cast<StoreInst>(&I))
        if (auto *F = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts()))
          if (Function *B = body(F->getName().str()))
            for (const auto &f : fieldsOf(S->getPointerOperand()))
              fnField[f].insert(B);
  std::map<FunctionType *, std::vector<Function *>> taken;
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    for (const Use &U : F->uses()) {
      auto *CB = dyn_cast<CallBase>(U.getUser());
      if (!CB || !CB->isCallee(&U)) {
        taken[F->getFunctionType()].push_back(F);
        break;
      }
    }
  }
  // Class hierarchy analysis for virtual calls. A vtable _ZTV<C> holds, in
  // each of its arrays, the offset to top and the type info before the
  // address point, then the virtual functions by slot. A call through slot
  // k of the vtable of an object of static class C goes to slot k of C's
  // vtable and of every class derived from C.
  std::map<std::string, std::map<int64_t, FnSet>> vslots;
  for (Module *M : {&down, &up})
    for (GlobalVariable &G : M->globals()) {
      if (!G.hasInitializer() || !G.getName().starts_with("_ZTV"))
        continue;
      std::string cls = "_ZTS" + G.getName().substr(4).str();
      auto *CS = dyn_cast<ConstantStruct>(G.getInitializer());
      for (unsigned a = 0; CS && a < CS->getNumOperands(); ++a)
        if (auto *CA = dyn_cast<ConstantArray>(CS->getOperand(a)))
          for (unsigned e = 2; e < CA->getNumOperands(); ++e)
            if (auto *Fn = dyn_cast<Function>(CA->getOperand(e)->stripPointerCasts()))
              if (Function *B = body(Fn->getName().str()))
                vslots[cls][(int64_t)e - 2].insert(B);
    }
  std::map<std::string, std::set<std::string>> derived;
  for (const auto &[key, C] : composite)
    for (const DINode *N : C->getElements())
      if (auto *M = dyn_cast<DIDerivedType>(N))
        if (M->getTag() == dwarf::DW_TAG_inheritance)
          if (auto *B = dyn_cast_or_null<DICompositeType>(strip(M->getBaseType())))
            derived[typeKey(B)].insert(key);
  auto below = [&](const std::string &C) {
    std::set<std::string> out{C};
    std::vector<std::string> work{C};
    while (!work.empty()) {
      std::string D = work.back();
      work.pop_back();
      for (const std::string &E : derived[D])
        if (out.insert(E).second)
          work.push_back(E);
    }
    return out;
  };
  // The targets of a virtual call, or none when the callee is not loaded
  // from a vtable slot.
  auto virtualTargets = [&](CallBase *CB, FnSet &fs) {
    auto *L = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
    if (!L)
      return;
    Value *P = L->getPointerOperand()->stripPointerCasts();
    int64_t k = 0;
    bool slot = false;
    if (auto *G = dyn_cast<GEPOperator>(P)) {
      if (!G->getSourceElementType()->isPointerTy())
        return;
      slot = true;
      APInt off(64, 0);
      if (!G->accumulateConstantOffset(dl, off))
        return;
      k = off.getSExtValue() / 8;
      P = G->getPointerOperand()->stripPointerCasts();
    }
    auto *V = dyn_cast<LoadInst>(P);
    if (!V || !V->getType()->isPointerTy())
      return;
    Value *O = V->getPointerOperand()->stripPointerCasts();
    if (isa<AllocaInst>(O))
      return;
    std::string cls;
    if (auto *C = dyn_cast_or_null<DICompositeType>(strip(source::pointee(O))))
      cls = typeKey(C);
    auto add = [&](const std::string &C) {
      auto it = vslots.find(C);
      if (it == vslots.end())
        return;
      auto s = it->second.find(k);
      if (s != it->second.end())
        for (Function *T : s->second)
          if (T->arg_size() == CB->arg_size())
            fs.insert(T);
    };
    if (!cls.empty())
      for (const std::string &C : below(cls))
        add(C);
    if (fs.empty() && slot)
      for (const auto &kv : vslots)
        add(kv.first);
  };
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &out = calls[F];
    for (Instruction &I : instructions(*F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || isa<IntrinsicInst>(CB))
        continue;
      if (auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts())) {
        if (Function *B = body(C->getName().str()))
          out.insert(B);
        continue;
      }
      FnSet fs;
      virtualTargets(CB, fs);
      if (!fs.empty()) {
        out.insert(fs.begin(), fs.end());
        continue;
      }
      if (auto *L = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
        auto fl = fieldsOf(L->getPointerOperand());
        if (!fl.empty()) {
          auto ft = fnField.find(fl.back());
          if (ft != fnField.end())
            for (Function *T : ft->second)
              if (T->getFunctionType() == CB->getFunctionType() || T->arg_size() == CB->arg_size())
                fs.insert(T);
        }
      }
      if (fs.empty()) {
        auto it = taken.find(CB->getFunctionType());
        if (it != taken.end())
          fs.insert(it->second.begin(), it->second.end());
      }
      out.insert(fs.begin(), fs.end());
    }
  }
}

Function *Client::body(const std::string &name) const {
  auto it = bodies.find(name);
  return it == bodies.end() ? nullptr : it->second;
}

// Each constant-offset GEP a store writes through names the field at every
// struct level its indices pass: (S, offset of the address inside S).
void Client::buildStores() {
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &out = stores[F];
    for (Instruction &I : instructions(*F)) {
      Value *P = nullptr;
      std::string v = "*";
      if (auto *S = dyn_cast<StoreInst>(&I)) {
        P = S->getPointerOperand();
        v = abstractValue(S->getValueOperand());
      } else if (auto *MS = dyn_cast<MemSetInst>(&I)) {
        P = MS->getRawDest();
        auto *b = dyn_cast<ConstantInt>(MS->getValue());
        v = b && b->isZero() ? "0" : "*";
      } else if (auto *MI = dyn_cast<MemIntrinsic>(&I))
        P = MI->getRawDest();
      if (!P)
        continue;
      for (const auto &f : fieldsOf(P))
        out.insert({f, v});
      if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
        auto *L = dyn_cast<ConstantInt>(MI->getLength());
        int64_t len = L && L->getBitWidth() <= 64 ? L->getSExtValue() : INT64_MAX;
        for (const auto &f : fieldsOf(P))
          ranges[F].push_back({f.first, f.second, len});
      }
    }
  }
}

void Client::buildModRef() {
  for (const auto &kv : bodies) {
    Function *F = kv.second;
    auto &m = mods[F], &r = refs[F];
    auto add = [&](auto &set, Value *P) {
      for (const auto &f : fieldsOf(P))
        set.insert(f);
    };
    for (Instruction &I : instructions(*F)) {
      if (auto *S = dyn_cast<StoreInst>(&I))
        add(m, S->getPointerOperand());
      else if (auto *L = dyn_cast<LoadInst>(&I))
        add(r, L->getPointerOperand());
      else if (auto *MI = dyn_cast<MemTransferInst>(&I)) {
        add(m, MI->getRawDest());
        add(r, MI->getRawSource());
      } else if (auto *MS = dyn_cast<MemSetInst>(&I))
        add(m, MS->getRawDest());
      else if (auto *CB = dyn_cast<CallBase>(&I)) {
        if (isa<IntrinsicInst>(CB))
          continue;
        for (Value *A : CB->args())
          if (A->getType()->isPointerTy()) {
            add(m, A);
            add(r, A);
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
        add(c, P);
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
    for (Instruction &I : instructions(*G)) {
      std::vector<int64_t> rest;
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
  std::sort(out.begin(), out.end(), [](Function *a, Function *b) { return a->getName() < b->getName(); });
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
// indirect call may reach any address-taken function of its type.
void Client::buildReleases() {
  std::map<FunctionType *, std::vector<Function *>> taken;
  for (const auto &kv : bodies)
    if (kv.second->hasAddressTaken())
      taken[kv.second->getFunctionType()].push_back(kv.second);
  for (bool grew = true; grew;) {
    grew = false;
    for (const auto &kv : bodies) {
      Function *F = kv.second;
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        auto *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
        std::vector<Function *> targets;
        if (C) {
          if (Function *B = body(C->getName().str()))
            targets.push_back(B);
        } else if (!CB->isInlineAsm()) {
          auto it = taken.find(CB->getFunctionType());
          if (it != taken.end())
            targets = it->second;
        }
        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          bool rel = C && C->getName() == "free";
          for (Function *B : targets)
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
  // A result read out of an object the client built field by field is a
  // value the client put there: the function returns it, it makes none.
  for (auto &kv : makes) {
    auto &ps = kv.second;
    ps.erase(std::remove_if(ps.begin(), ps.end(),
                            [&](const std::pair<Function *, int> &fp) {
                              if (fp.second != -1)
                                return false;
                              const auto &sig = signature(fp.first);
                              auto at = irParams(fp.first);
                              for (int k : loadedFrom(fp.first))
                                if ((size_t)k < at.size() && at[k] >= 0 && sig[at[k]].kind == Kind::Object &&
                                    !held(sig[at[k]]))
                                  return true;
                              return false;
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
    std::sort(producers[kv.first].begin(), producers[kv.first].end(),
              [](const Producer &a, const Producer &b) {
                return a.cost != b.cost ? a.cost < b.cost : a.fn->getName() < b.fn->getName();
              });
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
    if (held(p) && !cost.count(p.type))
      return false;
    if (p.kind == Kind::Handle && !cost.count(p.type) && !nullTested(F, i))
      return false;
  }
  return true;
}

// The interface functions of D through which the client reaches the
// sequence: E itself when it is one, otherwise the callable ones at the
// least call distance from which E is reached.
std::vector<Function *> Client::entries(Function *E) const {
  if (ifaceD.count(E) && callable(E))
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
    if (G != E && ifaceD.count(G) && callable(G)) {
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
  for (const std::string &v : c.values) {
    if (auto s = asI64(v))
      vs.push_back(*s);
    else if (auto u = asU64(v))
      vs.push_back((int64_t)*u);
    else
      return false;
  }
  if (vs.empty())
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

// The client for a set of may witnesses. The sink is reachable when one of
// them is, so the client may start at the entry of any of them and may run
// the writers of any of their constrained cells: entries and writers are the
// unions over the witnesses.
Client::Plan Client::plan(const std::vector<std::pair<std::vector<std::string>, std::vector<Cell>>> &ws) const {
  Plan P;
  // The nonterminals of the client grammar the entries and the writers can
  // demand: their held inputs, closed under the held inputs of every
  // producer. This is the grammar the harness carries; one execution
  // expands only the producers it picks.
  std::set<std::string> need;
  auto want = [&](Function *F) {
    for (const Param &p : signature(F))
      if (held(p) && cost.count(p.type))
        need.insert(p.type);
  };
  FnSet entrySet, writerSet, unguarded;
  std::set<std::tuple<std::string, int64_t, std::string, std::vector<std::string>>> cellSet;
  for (const auto &[seq, phi] : ws) {
    if (seq.empty())
      continue;
    Function *E = body(seq.front());
    if (!E)
      continue;
    if (std::find(P.firsts.begin(), P.firsts.end(), E) == P.firsts.end())
      P.firsts.push_back(E);
    auto es = entries(E);
    for (Function *F : es)
      if (entrySet.insert(F).second)
        P.entries.push_back(F);
    // The witness's arguments are the entry's only when it starts there. A
    // cell of a public object the client passes is its configuration; any
    // other cell the entry does not change is a guard.
    std::vector<Guard> conj;
    if (es.size() == 1 && es[0] == E) {
      auto sigG = signature(E);
      auto atG = irParams(E);
      for (const Cell &c : phi) {
        bool own = c.root >= 0 && (size_t)c.root < atG.size() && atG[c.root] >= 0 &&
                   sigG[atG[c.root]].kind == Kind::Object;
        for (const std::string &t : c.path)
          own = own && isPublic(irName(t));
        Guard g;
        if (guardOf(E, c, g, own))
          conj.push_back(g);
      }
    }
    if (es.size() == 1 && es[0] == E)
      P.guards[E].push_back(conj);
    else
      unguarded.insert(es.begin(), es.end());
    // A cell the client writes itself: its root is a public object the
    // client passes to the entry, and every struct on its path is public.
    // Any other cell lies in memory only the library reaches.
    auto sigE = signature(E);
    auto atE = irParams(E);
    for (const Cell &c : phi) {
      if (c.type.empty() || c.op.empty())
        continue;
      bool own = es.size() == 1 && es[0] == E && c.root >= 0 && (size_t)c.root < atE.size() && atE[c.root] >= 0 &&
                 sigE[atE[c.root]].kind == Kind::Object;
      for (const std::string &t : c.path)
        own = own && isPublic(irName(t));
      if (own && c.file) {
        auto &fs = P.files[E];
        bool dup = false;
        for (const Cell &d : fs)
          dup = dup || d.text == c.text;
        if (!dup)
          fs.push_back(c);
      }
      if (!cellSet.insert({c.type, c.off, c.op, c.values}).second)
        continue;
      if (own) {
        P.clientCells.push_back(c);
        continue;
      }
      auto w = writers(c);
      // A writer changes the entry's cell only through the object the cell
      // lies in, and the client shares an object between calls only by
      // passing the instance it holds. A writer that takes no held
      // argument of the root's type writes some other object.
      // When the root is not an object the client holds, the cell can still
      // lie in memory reachable from what it passes to the entry, so the
      // writer must share some held object with an entry.
      if (c.root >= 0 && (size_t)c.root < sigE.size()) {
        std::set<std::string> via;
        if (held(sigE[c.root]))
          via.insert(sigE[c.root].type);
        else
          for (Function *X : es)
            for (const Param &p : signature(X))
              if (held(p))
                via.insert(p.type);
        std::vector<Function *> shared;
        for (Function *W : w) {
          bool s = false;
          for (const Param &p : signature(W))
            s = s || (held(p) && via.count(p.type));
          if (s)
            shared.push_back(W);
        }
        w = shared;
      }
      if (w.empty())
        continue;
      P.cellWriters.push_back({c, w});
      writerSet.insert(w.begin(), w.end());
    }
    // This witness alone. A call discharges a cell when it is an interface
    // function other than the witness entry and its closure stores the
    // cell's value. The entry's own stores are already substituted by the
    // path condition; a cell only the entry stores is not a prefix.
    {
      std::vector<std::pair<Cell, std::vector<Function *>>> local;
      Function *entry = es.empty() ? nullptr : es[0];
      for (const Cell &c : phi) {
        if (c.type.empty() || c.op.empty())
          continue;
        bool own = es.size() == 1 && es[0] == E && c.root >= 0 && (size_t)c.root < atE.size() && atE[c.root] >= 0 &&
                   sigE[atE[c.root]].kind == Kind::Object;
        for (const std::string &t : c.path)
          own = own && isPublic(irName(t));
        if (own)
          continue;
        // A bound or a relation between two cells is an entry obligation.
        // A store of some other value does not discharge it.
        std::vector<Function *> ww;
        if (c.op != "=" && c.op != "!=") {
          local.push_back({c, ww});
          continue;
        }
        for (Function *W : writers(c)) {
          if (W == entry || !ifaceD.count(W))
            continue;
          bool share = true;
          if (c.root >= 0 && (size_t)c.root < sigE.size() && held(sigE[c.root])) {
            share = false;
            for (const Param &p : signature(W))
              share = share || (held(p) && p.type == sigE[c.root].type);
          }
          if (share)
            ww.push_back(W);
        }
        local.push_back({c, ww});
      }
      int uncovered = 0;
      int construct = 0;
      std::string openCells;
      std::vector<Function *> cand;
      std::vector<int> need;
      for (size_t i = 0; i < local.size(); ++i) {
        if (local[i].second.empty()) {
          // A field no defined function writes is set only by the library's
          // static initialization. The necessary condition the model read
          // along the path is that fixed value, the same in every execution,
          // so it is established by construction, not by a client call.
          if (!everStored(local[i].first.type, local[i].first.off)) {
            ++construct;
            continue;
          }
          ++uncovered;
          openCells += " " + local[i].first.type + "+" + std::to_string(local[i].first.off);
          continue;
        }
        need.push_back((int)i);
        for (Function *W : local[i].second)
          if (std::find(cand.begin(), cand.end(), W) == cand.end())
            cand.push_back(W);
      }
      std::sort(cand.begin(), cand.end(), [](Function *A, Function *B) { return A->getName() < B->getName(); });
      std::vector<Function *> word;
      if (!need.empty()) {
        std::vector<int> left = need;
        for (int n = 0; n < 4 && !left.empty(); ++n) {
          Function *best = nullptr;
          int got = -1;
          for (Function *C : cand) {
            int ncover = 0;
            for (int i : left)
              for (Function *W : local[i].second)
                ncover += W == C;
            if (ncover > got) {
              got = ncover;
              best = C;
            }
          }
          if (!best || got <= 0)
            break;
          word.push_back(best);
          std::vector<int> rest;
          for (int i : left) {
            bool hit = false;
            for (Function *W : local[i].second)
              hit = hit || W == best;
            if (!hit)
              rest.push_back(i);
          }
          left.swap(rest);
        }
        if (!left.empty())
          word.clear();
      }
      bool inI = entry && ifaceD.count(entry);
      int calls = (int)word.size() + (inI ? 1 : 0);
      bool pass = inI && uncovered == 0 && (need.empty() || !word.empty()) && calls <= 5;
      std::string line = std::string("result ") + (pass ? "pass" : "open");
      line += " iface " + std::to_string(inI ? 1 : 0);
      line += " lib " + std::to_string(local.size());
      line += " uncovered " + std::to_string(uncovered);
      line += " construct " + std::to_string(construct);
      line += " calls " + std::to_string(calls);
      for (Function *W : word)
        line += " " + W->getName().str();
      if (entry)
        line += " " + entry->getName().str();
      line += openCells;
      P.verdicts.push_back(line);
    }
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
  for (Function *F : P.entries)
    want(F);
  P.writers.assign(writerSet.begin(), writerSet.end());
  std::sort(P.writers.begin(), P.writers.end(), [](Function *a, Function *b) { return a->getName() < b->getName(); });
  for (Function *F : P.writers)
    want(F);
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
  return P;
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
  for (Function *F : P.firsts)
    out << "first " << F->getName() << " iface " << ifaceD.count(F) << " (" << sig(F) << ")\n";
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
  for (Function *F : P.entries)
    out << "entry " << F->getName() << " (" << sig(F) << ")\n";
  for (const auto &h : P.handles) {
    out << "handle " << h.first << " cost " << (cost.count(h.first) ? std::to_string(cost.at(h.first)) : "-")
        << " producers " << h.second.size() << "\n";
    for (size_t i = 0; i < h.second.size() && i < 6; ++i)
      out << "  make " << h.second[i].fn->getName() << (h.second[i].out >= 0 ? " out " + std::to_string(h.second[i].out) : "")
          << " (" << sig(h.second[i].fn) << ")\n";
  }
  for (const Cell &c : P.clientCells)
    out << "client-cell " << c.type << "+" << c.off << " " << c.op << " " << c.values.size() << "\n";
  for (const auto &cw : P.cellWriters) {
 out << "cell " << cw.first.type << "+" << cw.first.off << " " << cw.first.op << " " << (cw.first.values.empty() ? "" : cw.first.values[0]) << " writers " << cw.second.size() << ":";
    for (size_t i = 0; i < cw.second.size() && i < 8; ++i)
      out << " " << cw.second[i]->getName();
    out << "\n";
  }
  out << "writers " << P.writers.size() << "\n";
  for (const std::string &v : P.verdicts)
    out << v << "\n";
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
// out-parameter is a slot the call fills. Every byte the library reads is
// the client's choice, so no input file is assumed.

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
  std::map<std::pair<FunctionType *, const void *>, Function *> callbacks;

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
  // library can tell apart: a fresh short string and each of the given
  // texts. Each is a writable copy.
  Value *text(IRBuilder<> &B, const std::vector<std::string> &named) {
    if (named.empty())
      return text(B);
    AllocaInst *slot = entryAlloca(B, PointerType::get(ctx, 0));
    std::vector<std::function<void(IRBuilder<> &)>> alts;
    alts.push_back([&, slot](IRBuilder<> &C) { C.CreateStore(text(C), slot); });
    for (const std::string &s : named)
      alts.push_back([&, slot, s](IRBuilder<> &C) {
        Value *p = C.CreateCall(mallocF, {C.getInt64(s.size() + 1)});
        C.CreateCall(memcpyF, {p, C.CreateGlobalStringPtr(s), C.getInt64(s.size() + 1)});
        C.CreateStore(p, slot);
      });
    oneOf(B, alts, "text");
    return B.CreateLoad(PointerType::get(ctx, 0), slot);
  }

  // A buffer of elements of the given size: as many as the input bound
  // allows within 64 KiB, and at least one. Returns the count it holds.
  uint64_t capacity(uint64_t elem) const { return std::max<uint64_t>(1, std::min<uint64_t>(n, 65536 / elem)); }
  Value *bytes(IRBuilder<> &B, uint64_t elem = 1) {
    uint64_t size = capacity(elem) * elem;
    Value *p = B.CreateCall(mallocF, {B.getInt64(size)});
    B.CreateCall(mkSym, {p, B.getInt64(size), B.CreateGlobalStringPtr("bytes." + std::to_string(names++))});
    return p;
  }

  // A fresh object of size bytes, every byte the client's choice.
  Value *object(IRBuilder<> &B, uint64_t size) {
    Value *p = B.CreateCall(mallocF, {B.getInt64(size ? size : 1)});
    B.CreateCall(mkSym, {p, B.getInt64(size ? size : 1), B.CreateGlobalStringPtr("object." + std::to_string(names++))});
    return p;
  }

  // A harness function of type FT: the most general callback the client
  // passes. Its shape decides its effect. A read, (buffer, length) returning
  // a count, fills a non-null buffer with the next input bytes. A function
  // whose declared result is a pointer of source type returns a client
  // value of that type, which 'result' builds (key names the declared
  // type). Another function returning a pointer returns fresh memory as
  // large as its largest size argument, and writes nothing into memory it
  // is given.
  Function *callback(FunctionType *FT, const void *key = nullptr,
                     const std::function<Value *(IRBuilder<> &)> &result = nullptr) {
    auto it = callbacks.find({FT, key});
    if (it != callbacks.end())
      return it->second;
    Function *F = Function::Create(FT, GlobalValue::InternalLinkage, "client.callback." + std::to_string(callbacks.size()), &H);
    callbacks[{FT, key}] = F;
    auto *BB = BasicBlock::Create(ctx, "entry", F);
    IRBuilder<> B(BB);
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
      Value *at = B.CreateLoad(B.getInt64Ty(), cursor);
      Value *left = B.CreateSub(B.getInt64(n), at);
      Value *want = B.CreateSExtOrTrunc(len, B.getInt64Ty());
      Value *neg = B.CreateICmpSLT(want, B.getInt64(0));
      want = B.CreateSelect(neg, B.getInt64(0), want);
      Value *n = B.CreateSelect(B.CreateICmpULT(want, left), want, left);
      n = B.CreateSelect(B.CreateIsNull(buf), B.getInt64(0), n);
      auto *copy = BasicBlock::Create(ctx, "copy", F), *done = BasicBlock::Create(ctx, "done", F);
      B.CreateCondBr(B.CreateIsNull(buf), done, copy);
      B.SetInsertPoint(copy);
      B.CreateCall(memcpyF, {buf, B.CreateGEP(B.getInt8Ty(), data, at), n});
      B.CreateBr(done);
      B.SetInsertPoint(done);
      B.CreateStore(B.CreateAdd(at, n), cursor);
      count = n;
      break;
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

} // namespace

void Client::emit(const Plan &P, Module &H) const {
  LLVMContext &ctx = H.getContext();
  H.setDataLayout(dl);
  H.setTargetTriple(down.getTargetTriple());
  Builder K(H, dl, inputBound, textBound);
  auto *p0 = PointerType::get(ctx, 0);
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
  // The pointer formals of F that integer formal j bounds (A3).
  auto lengthOf = [&](Function *F, unsigned j) {
    std::vector<unsigned> out;
    for (auto [b, k] : formalsOf(F).len)
      if (k == j)
        out.push_back(b);
    return out;
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
  auto nullOr = [&](IRBuilder<> &C, bool nullable, const std::function<Value *(IRBuilder<> &)> &make) -> Value * {
    if (!nullable)
      return make(C);
    AllocaInst *slot = K.entryAlloca(C, p0);
    K.oneOf(C,
            {[&](IRBuilder<> &D) { D.CreateStore(ConstantPointerNull::get(p0), slot); },
             [&](IRBuilder<> &D) { D.CreateStore(make(D), slot); }},
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
      Function *cb = record ? K.callback(FT, R, [&, R](IRBuilder<> &D) {
        auto outer = std::move(enclosing);
        enclosing.clear();
        Value *v = pointer(D, R, d, false, Where{});
        enclosing = std::move(outer);
        return v;
      })
                                       : K.callback(FT);
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
      return nullOr(C, nullable, [&](IRBuilder<> &D) { return K.bytes(D, elem); });
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
              v = empty(C, nullable);
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
          v = nullOr(C, nullable, [&](IRBuilder<> &D) { return K.text(D, compared(F, i)); });
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
          v = at[i] >= 0 ? pointer(C, declared(at[i]), objectDepth, nullable, Where{F, i})
                         : nullOr(C, nullable, [&](IRBuilder<> &D) { return K.bytes(D, p.elem); });
          break;
        }
      } else if (auto bs = lengthOf(F, i); T->isIntegerTy() && !bs.empty()) {
        v = K.symbolic(C, T, "length");
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
        K.require(C, C.CreateICmpULE(v, ConstantInt::get(T, n)));
      } else
        v = K.symbolic(C, T, "arg");
      args.push_back(v);
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
        if (AT && AT->getElementType()->isIntegerTy(8) && AT->getNumElements() >= 2) {
          C.CreateStore(C.getInt8('f'), at);
          C.CreateStore(C.getInt8(0), C.CreateGEP(C.getInt8Ty(), at, C.getInt64(1)));
        } else if (FT->isPointerTy())
          C.CreateStore(C.CreateGlobalStringPtr("f"), at);
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
            K.require(W, m);
            if (g.config)
              W.CreateStore(v, at);
          }
        });
      K.oneOf(C, wit, "witness");
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
            std::vector<std::function<void(IRBuilder<> &)>> pre{[](IRBuilder<> &) {}};
            for (Function *W : d->second)
              pre.push_back([&, W](IRBuilder<> &D) { call(D, W, "", -1); });
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
  for (unsigned k = 0; k < writerSlots; ++k) {
    std::vector<std::function<void(IRBuilder<> &)>> alts{[](IRBuilder<> &) {}};
    for (Function *W : P.writers)
      alts.push_back([&, W](IRBuilder<> &C) { call(C, W, "", -1); });
    K.oneOf(B, alts, "write");
  }
  {
    std::vector<std::function<void(IRBuilder<> &)>> alts;
    for (Function *E : P.entries)
      alts.push_back([&, E](IRBuilder<> &C) {
        auto g = P.guards.find(E);
        auto f = P.files.find(E);
        call(C, E, "", -1, g == P.guards.end() ? nullptr : &g->second, f == P.files.end() ? nullptr : &f->second);
      });
    K.oneOf(B, alts, "entry");
  }
  B.CreateRet(B.getInt32(0));
}
