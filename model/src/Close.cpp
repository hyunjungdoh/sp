#include "Close.h"

#include "llvm/BinaryFormat/ELF.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Object/ELFObjectFile.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Object/SymbolicFile.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SourceMgr.h"

#include <dlfcn.h>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <map>
#include <set>

namespace fs = std::filesystem;

using namespace llvm;
using namespace llvm::object;

fs::path caseFile(const fs::path &caseDir, const std::string &recorded) {
  std::error_code ec;
  if (recorded.empty())
    return {};
  if (fs::is_regular_file(recorded, ec))
    return recorded;
  fs::path dir = fs::absolute(caseDir, ec).lexically_normal();
  if (dir.filename().empty())
    dir = dir.parent_path();
  std::string marker = "/" + dir.filename().string() + "/";
  auto pos = recorded.find(marker);
  if (pos == std::string::npos)
    return {};
  fs::path mapped = dir / recorded.substr(pos + marker.size());
  return fs::is_regular_file(mapped, ec) ? mapped : fs::path();
}

namespace {

// One installed ELF image. Section bytes alias the file buffer the image owns.
struct Sec {
  uint64_t addr = 0, size = 0;
  uint64_t flags = 0;
  bool bss = false;
  ArrayRef<uint8_t> bytes;
};
struct Rel {
  uint64_t addr = 0;
  uint32_t type = 0;
  int64_t addend = 0;
  std::string symbol;
};
struct Sym {
  uint64_t addr = 0, size = 0;
  int image = -1;
  int sec = -1;
  bool func = false;
  bool data = false;
};
struct Image {
  unsigned machine = 0;
  std::vector<Sec> secs;
  std::vector<Rel> rels;
  OwningBinary<ObjectFile> owner;
};

constexpr uint64_t kByteCap = 256ull << 20;

std::string stripVersion(StringRef name) {
  auto at = name.find('@');
  return (at == StringRef::npos ? name : name.substr(0, at)).str();
}

} // namespace

// The environment is the target platform's system libraries, listed once in
// env.syms; the host the model runs on has no say in it.
bool environmentSymbol(const std::string &name) {
  static const std::set<std::string> syms = [] {
    std::set<std::string> s;
    std::ifstream in(SP_ENV_SYMS);
    if (!in) {
      errs() << "missing environment symbol list " << SP_ENV_SYMS << "\n";
      std::exit(1);
    }
    for (std::string line; std::getline(in, line);)
      if (!line.empty() && line[0] != '#')
        s.insert(line);
    return s;
  }();
  return syms.count(name) != 0;
}

bool nativeResidue(const Module &M, const std::string &name) {
  const NamedMDNode *MD = M.getNamedMetadata("sp.native");
  if (!MD)
    return false;
  for (const MDNode *N : MD->operands()) {
    if (!N || N->getNumOperands() == 0)
      continue;
    if (const auto *S = dyn_cast<MDString>(N->getOperand(0)))
      if (S->getString() == name)
        return true;
  }
  return false;
}

namespace {

// The stored word is the symbol's address plus the addend. A PC-relative slot
// or a TLS slot is not reconstructed; the object that holds one stays open.
bool absolutePointer(unsigned machine, uint32_t type) {
  return (machine == ELF::EM_X86_64 && type == ELF::R_X86_64_64) ||
         (machine == ELF::EM_AARCH64 && type == ELF::R_AARCH64_ABS64);
}

std::vector<std::string> installedObjects(const fs::path &dir) {
  std::ifstream in(dir / "surfaces.json");
  std::string text((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
  std::vector<std::string> out;
  std::set<std::string> seen;
  for (size_t k = text.find("\"so\""); k != std::string::npos; k = text.find("\"so\"", k + 1)) {
    auto c = text.find(':', k);
    auto q = text.find('"', c);
    auto e = text.find('"', q + 1);
    if (q == std::string::npos || e == std::string::npos)
      continue;
    std::string so = caseFile(dir, text.substr(q + 1, e - q - 1)).string();
    std::error_code ec;
    fs::path real = fs::weakly_canonical(so, ec);
    std::string key = ec ? so : real.string();
    if (!so.empty() && seen.insert(key).second && fs::is_regular_file(so))
      out.push_back(so);
  }
  return out;
}

fs::path remap(const fs::path &caseDir, StringRef recorded) { return caseFile(caseDir, recorded.str()); }

std::set<std::string> definedIn(const fs::path &bc, LLVMContext &ctx) {
  std::set<std::string> out;
  ErrorOr<std::unique_ptr<MemoryBuffer>> buf = MemoryBuffer::getFile(bc.string());
  if (!buf)
    return out;
  Expected<std::unique_ptr<SymbolicFile>> sym =
      SymbolicFile::createSymbolicFile((*buf)->getMemBufferRef(), file_magic::unknown, &ctx);
  if (!sym) {
    consumeError(sym.takeError());
    return out;
  }
  for (auto S : (*sym)->symbols()) {
    auto flags = S.getFlags();
    if (!flags) {
      consumeError(flags.takeError());
      continue;
    }
    std::string raw;
    raw_string_ostream os(raw);
    if (Error e = S.printName(os)) {
      consumeError(std::move(e));
      continue;
    }
    os.flush();
    if ((*flags & SymbolRef::SF_Undefined) || !(*flags & (SymbolRef::SF_Global | SymbolRef::SF_Weak)))
      continue;
    out.insert(stripVersion(raw));
  }
  return out;
}

std::set<std::string> unresolved(Module &M) {
  std::set<std::string> out;
  for (Function &F : M)
    if (F.isDeclaration() && !F.isIntrinsic() && !F.getName().starts_with("llvm."))
      out.insert(F.getName().str());
  for (GlobalVariable &G : M.globals())
    if (G.isDeclaration() && !G.getName().starts_with("llvm."))
      out.insert(G.getName().str());
  return out;
}

// One bitcode unit. A path is a file in the case. Raw is a .llvm_bc section
// that is bitcode itself rather than a list of paths.
struct Cand {
  fs::path path;
  std::string raw;
};

// The external definition `have` holds under name n: a function, a variable,
// or an alias. A local symbol is private to its unit and never shared.
bool definesExternal(Module &have, StringRef n) {
  GlobalValue *V = have.getNamedValue(n);
  if (!V || V->hasLocalLinkage())
    return false;
  if (isa<GlobalAlias>(V))
    return true;
  return !V->isDeclaration();
}

// An external definition `have` already holds becomes a declaration in mod.
// The program then has one body under each name: the one in `have`.
unsigned demote(Module &mod, Module &have) {
  unsigned n = 0;
  for (Function &F : mod) {
    if (F.isDeclaration() || F.hasLocalLinkage() || !definesExternal(have, F.getName()))
      continue;
    F.setComdat(nullptr);
    F.deleteBody();
    F.setLinkage(GlobalValue::ExternalLinkage);
    ++n;
  }
  for (GlobalVariable &G : mod.globals()) {
    if (G.isDeclaration() || G.hasLocalLinkage() || !definesExternal(have, G.getName()))
      continue;
    G.setComdat(nullptr);
    G.setInitializer(nullptr);
    G.setLinkage(GlobalValue::ExternalLinkage);
    ++n;
  }
  std::vector<GlobalAlias *> aliases;
  for (GlobalAlias &A : mod.aliases())
    if (!A.hasLocalLinkage() && definesExternal(have, A.getName()))
      aliases.push_back(&A);
  for (GlobalAlias *A : aliases) {
    std::string name = A->getName().str();
    GlobalValue *decl;
    if (auto *FT = dyn_cast<FunctionType>(A->getValueType()))
      decl = Function::Create(FT, GlobalValue::ExternalLinkage, "", &mod);
    else
      decl = new GlobalVariable(mod, A->getValueType(), false, GlobalValue::ExternalLinkage, nullptr, "");
    A->replaceAllUsesWith(decl);
    A->eraseFromParent();
    decl->setName(name);
    ++n;
  }
  return n;
}

// Symbols mod only declares and the other library does not define: the ones
// the program D ∪ U still lacks.
std::set<std::string> openIn(Module &mod, Module &other) {
  std::set<std::string> out;
  for (const std::string &s : unresolved(mod))
    if (!definesExternal(other, s))
      out.insert(s);
  return out;
}

std::set<std::string> definedInCand(const Cand &c, LLVMContext &ctx) {
  if (!c.path.empty())
    return definedIn(c.path, ctx);
  std::set<std::string> out;
  SMDiagnostic err;
  auto mod = parseIR(MemoryBufferRef(c.raw, "llvm_bc"), err, ctx);
  if (!mod)
    return out;
  for (Function &F : *mod)
    if (!F.isDeclaration())
      out.insert(F.getName().str());
  for (GlobalVariable &G : mod->globals())
    if (!G.isDeclaration())
      out.insert(G.getName().str());
  return out;
}

bool linkCand(Module &dest, Module *have, const Cand &c) {
  SMDiagnostic err;
  std::unique_ptr<Module> mod = c.path.empty()
                                    ? parseIR(MemoryBufferRef(c.raw, "llvm_bc"), err, dest.getContext())
                                    : parseIRFile(c.path.string(), err, dest.getContext());
  if (!mod)
    return false;
  // A unit enters whole, as a linker pulls an archive member: its local
  // state exists once for all its functions. A name already defined keeps
  // the definition that came first.
  demote(*mod, dest);
  if (have)
    demote(*mod, *have);
  Linker L(dest);
  if (L.linkInModule(std::move(mod))) {
    errs() << "close: link failed " << (c.path.empty() ? std::string("llvm_bc") : c.path.string()) << "\n";
    return false;
  }
  return true;
}

bool hits(const std::set<std::string> &defs, const std::set<std::string> &open) {
  for (const std::string &d : defs)
    if (open.count(d) && !environmentSymbol(d))
      return true;
  return false;
}

// Bitcode the case still has, including the list an installed library stores
// in its .llvm_bc section. The two input files are not read again.
std::vector<Cand> collectBitcode(LLVMContext &ctx, const fs::path &caseDir, const std::vector<std::string> &objects) {
  (void)ctx;
  std::set<std::string> skip = {(caseDir / "upstream.bc").string(), (caseDir / "upstream.pre.bc").string(),
                                (caseDir / "se_lib" / "downstream.closure.bc").string()};
  std::vector<Cand> cands;
  std::set<std::string> seen;
  std::error_code ec;
  for (fs::recursive_directory_iterator it(caseDir, fs::directory_options::skip_permission_denied, ec), end; it != end;
       it.increment(ec)) {
    if (!it->is_regular_file(ec) || it->path().extension() != ".bc")
      continue;
    if (!skip.count(it->path().string()) && seen.insert(it->path().string()).second)
      cands.push_back({it->path(), {}});
  }
  auto takeSection = [&](StringRef bytes) {
    if (bytes.size() >= 4 && bytes[0] == 'B' && bytes[1] == 'C' && (unsigned char)bytes[2] == 0xc0 &&
        (unsigned char)bytes[3] == 0xde) {
      cands.push_back({{}, bytes.str()});
      return;
    }
    StringRef rest = bytes;
    while (!rest.empty()) {
      auto nl = rest.find('\n');
      StringRef line = rest.substr(0, nl).trim();
      rest = nl == StringRef::npos ? StringRef() : rest.substr(nl + 1);
      if (line.empty())
        continue;
      fs::path mapped = remap(caseDir, line);
      if (!mapped.empty() && seen.insert(mapped.string()).second)
        cands.push_back({mapped, {}});
    }
  };
  for (const std::string &so : objects) {
    auto bin = ObjectFile::createObjectFile(so);
    if (!bin) {
      consumeError(bin.takeError());
      continue;
    }
    for (const SectionRef &S : (*bin).getBinary()->sections()) {
      auto name = S.getName();
      if (!name || *name != ".llvm_bc") {
        if (!name)
          consumeError(name.takeError());
        continue;
      }
      auto bytes = S.getContents();
      if (!bytes) {
        consumeError(bytes.takeError());
        continue;
      }
      takeSection(*bytes);
    }
  }
  return cands;
}

unsigned linkRecordedBitcode(Module &M, const fs::path &caseDir, const std::vector<std::string> &objects) {
  std::vector<Cand> cands = collectBitcode(M.getContext(), caseDir, objects);
  std::vector<char> used(cands.size(), 0);
  unsigned linked = 0;
  bool progress = true;
  while (progress) {
    progress = false;
    std::set<std::string> open = unresolved(M);
    for (size_t i = 0; i < cands.size(); ++i) {
      if (used[i])
        continue;
      std::set<std::string> defs = definedInCand(cands[i], M.getContext());
      if (!hits(defs, open))
        continue;
      used[i] = 1;
      if (linkCand(M, nullptr, cands[i]))
        ++linked;
      progress = true;
    }
  }
  return linked;
}

// The two input libraries, closed before analysis. A unit that defines a symbol
// declared in upstream is linked there; one that defines a symbol declared only
// in downstream is linked there. A symbol both declare is defined once, in upstream.
unsigned closeModulesBitcode(Module &down, Module &up, const fs::path &caseDir, const std::vector<std::string> &objects) {
  // The client loads D, then U as D's dependency. A name both define
  // resolves to D's definition for every caller, U's own included.
  demote(up, down);
  std::vector<Cand> cands = collectBitcode(up.getContext(), caseDir, objects);
  std::vector<char> used(cands.size(), 0);
  unsigned linked = 0;
  bool progress = true;
  while (progress) {
    progress = false;
    std::set<std::string> openD = openIn(down, up);
    std::set<std::string> openU = openIn(up, down);
    for (size_t i = 0; i < cands.size(); ++i) {
      if (used[i])
        continue;
      std::set<std::string> defs = definedInCand(cands[i], up.getContext());
      bool inU = hits(defs, openU);
      bool inD = hits(defs, openD);
      if (!inU && !inD)
        continue;
      used[i] = 1;
      bool ok = false;
      if (inU)
        ok = linkCand(up, &down, cands[i]) || ok;
      if (inD)
        ok = linkCand(down, &up, cands[i]) || ok;
      if (ok)
        ++linked;
      progress = true;
    }
  }
  return linked;
}

template <class ELFT>
void readImage(ELFObjectFile<ELFT> &obj, Image &im, std::map<std::string, Sym> &table, int index) {
  const ELFFile<ELFT> &ef = obj.getELFFile();
  im.machine = ef.getHeader().e_machine;
  auto sections = ef.sections();
  if (!sections) {
    consumeError(sections.takeError());
    return;
  }
  for (const auto &s : *sections) {
    Sec sec;
    sec.addr = s.sh_addr;
    sec.size = s.sh_size;
    sec.flags = s.sh_flags;
    sec.bss = s.sh_type == ELF::SHT_NOBITS;
    if (!sec.bss && (s.sh_flags & ELF::SHF_ALLOC)) {
      auto bytes = ef.getSectionContents(s);
      if (bytes)
        sec.bytes = *bytes;
      else
        consumeError(bytes.takeError());
    }
    im.secs.push_back(sec);
    if (s.sh_type != ELF::SHT_RELA && s.sh_type != ELF::SHT_REL)
      continue;
    auto symtab = ef.getSection(s.sh_link);
    if (!symtab) {
      consumeError(symtab.takeError());
      continue;
    }
    auto strtab = ef.getStringTableForSymtab(**symtab);
    if (!strtab) {
      consumeError(strtab.takeError());
      continue;
    }
    auto add = [&](uint64_t off, uint32_t type, int64_t addend, uint32_t symi) {
      Rel r;
      r.addr = off;
      r.type = type;
      r.addend = addend;
      if (symi != 0) {
        auto sym = ef.template getEntry<typename ELFT::Sym>(**symtab, symi);
        if (!sym) {
          consumeError(sym.takeError());
          return;
        }
        if ((*sym)->st_name)
          r.symbol = stripVersion((*strtab).drop_front((*sym)->st_name).split('\0').first);
      }
      im.rels.push_back(std::move(r));
    };
    if (s.sh_type == ELF::SHT_RELA) {
      auto rels = ef.relas(s);
      if (!rels) {
        consumeError(rels.takeError());
        continue;
      }
      for (const auto &r : *rels)
        add(r.r_offset, r.getType(false), r.r_addend, r.getSymbol(false));
    } else {
      auto rels = ef.rels(s);
      if (!rels) {
        consumeError(rels.takeError());
        continue;
      }
      for (const auto &r : *rels)
        add(r.r_offset, r.getType(false), 0, r.getSymbol(false));
    }
  }
  auto takeSymtab = [&](const typename ELFT::Shdr &s) {
    auto syms = ef.symbols(&s);
    auto strtab = ef.getStringTableForSymtab(s);
    if (!syms || !strtab) {
      if (!syms)
        consumeError(syms.takeError());
      if (!strtab)
        consumeError(strtab.takeError());
      return;
    }
    for (const auto &sym : *syms) {
      if (sym.st_name == 0 || sym.st_shndx == ELF::SHN_UNDEF || sym.st_shndx == ELF::SHN_ABS ||
          sym.st_shndx == ELF::SHN_XINDEX || sym.st_shndx == ELF::SHN_COMMON)
        continue;
      unsigned type = sym.getType();
      if (type == ELF::STT_FILE || type == ELF::STT_SECTION || type == ELF::STT_TLS)
        continue;
      if (sym.st_shndx >= im.secs.size())
        continue;
      const Sec &sec = im.secs[sym.st_shndx];
      if (sec.flags & ELF::SHF_TLS)
        continue;
      std::string name = stripVersion((*strtab).drop_front(sym.st_name).split('\0').first);
      if (name.empty())
        continue;
      bool exec = sec.flags & ELF::SHF_EXECINSTR;
      Sym got;
      got.addr = sym.st_value;
      got.size = sym.st_size;
      got.image = index;
      got.sec = (int)sym.st_shndx;
      got.func = type == ELF::STT_FUNC || (type == ELF::STT_NOTYPE && exec);
      got.data = type == ELF::STT_OBJECT || (type == ELF::STT_NOTYPE && !exec);
      auto it = table.find(name);
      // The first image that defines a symbol keeps it. A later image fills
      // only a name that is still absent or was seen with no size.
      if (it != table.end() && it->second.size >= got.size)
        continue;
      table[name] = got;
    }
  };
  for (const auto &s : *sections)
    if (s.sh_type == ELF::SHT_DYNSYM || s.sh_type == ELF::SHT_SYMTAB)
      takeSymtab(s);
  std::sort(im.rels.begin(), im.rels.end(), [](const Rel &a, const Rel &b) { return a.addr < b.addr; });
}

bool openImage(const std::string &path, std::vector<Image> &images, std::map<std::string, Sym> &table) {
  auto bin = ObjectFile::createObjectFile(path);
  if (!bin) {
    consumeError(bin.takeError());
    return false;
  }
  Image im;
  im.owner = std::move(*bin);
  int index = (int)images.size();
  if (auto *elf = dyn_cast<ELF64LEObjectFile>(im.owner.getBinary()))
    readImage(*elf, im, table, index);
  else if (auto *elf = dyn_cast<ELF64BEObjectFile>(im.owner.getBinary()))
    readImage(*elf, im, table, index);
  else
    return false;
  images.push_back(std::move(im));
  return true;
}

bool ranged(const Image &im, uint64_t lo, uint64_t hi, Rel *first = nullptr) {
  auto it = std::lower_bound(im.rels.begin(), im.rels.end(), lo, [](const Rel &r, uint64_t a) { return r.addr < a; });
  if (it == im.rels.end() || it->addr >= hi)
    return false;
  if (first)
    *first = *it;
  return true;
}

Align alignOf(uint64_t addr) {
  unsigned z = 0;
  while (z < 4 && addr && ((addr >> z) & 1) == 0)
    ++z;
  return Align(1u << z);
}

// A declared global the engine would have to allocate before main.
bool openGlobal(const GlobalVariable &G, const DataLayout &dl) {
  return G.isDeclaration() && G.getName() != "__dso_handle" && !G.getName().starts_with("llvm.") &&
         dl.getTypeAllocSize(G.getValueType()) > 0;
}

void redirect(GlobalVariable *old, Constant *to) {
  old->replaceAllUsesWith(to);
  old->eraseFromParent();
}

Constant *symbolAddress(Module &M, const std::map<std::string, Sym> &table, const std::map<std::string, Constant *> &addr,
                        StringRef name) {
  auto it = addr.find(name.str());
  if (it != addr.end())
    return it->second;
  if (Function *F = M.getFunction(name))
    return F;
  if (GlobalVariable *G = M.getGlobalVariable(name))
    return G;
  auto known = table.find(name.str());
  if (known != table.end() && known->second.func)
    return Function::Create(FunctionType::get(Type::getVoidTy(M.getContext()), false), GlobalValue::ExternalLinkage, name, M);
  // A data symbol the image does not carry (a C++ ABI object in a system
  // library that is not installed with the case) still needs an address.
  // A declaration with no size is not allocated, so the engine can start;
  // a use of the address as data ends that path.
  if (M.getNamedValue(name))
    return M.getNamedValue(name);
  return Function::Create(FunctionType::get(Type::getVoidTy(M.getContext()), false), GlobalValue::ExternalLinkage, name, M);
}

std::vector<Rel> relsOf(const Image &im, uint64_t lo, uint64_t hi) {
  std::vector<Rel> out;
  auto it = std::lower_bound(im.rels.begin(), im.rels.end(), lo, [](const Rel &r, uint64_t a) { return r.addr < a; });
  for (; it != im.rels.end() && it->addr < hi; ++it)
    out.push_back(*it);
  return out;
}

Constant *bytesOf(LLVMContext &ctx, const Sec &sec, uint64_t lo, uint64_t n) {
  if (sec.bss)
    return ConstantAggregateZero::get(ArrayType::get(Type::getInt8Ty(ctx), n));
  uint64_t off = lo - sec.addr;
  if (off + n > sec.bytes.size())
    return nullptr;
  return ConstantDataArray::get(ctx, ArrayRef<uint8_t>(sec.bytes.data() + off, n));
}

// Labels of one section become one object, so a pointer difference is the
// distance the image stores. A sized object is its own global. A relocated
// word becomes a pointer to the symbol it names; any other relocation leaves
// the object open, because the file bytes are not the value the loader writes.
unsigned materialize(Module &M, const std::vector<Image> &images, const std::map<std::string, Sym> &table) {
  const DataLayout &dl = M.getDataLayout();
  LLVMContext &ctx = M.getContext();
  unsigned made = 0;
  std::map<std::string, Constant *> addr;
  if (dl.getPointerSize() != 8)
    return 0;

  struct Group {
    int image = -1, sec = -1;
    std::vector<std::string> names;
  };
  std::map<std::pair<int, int>, Group> groups;
  for (GlobalVariable &G : M.globals()) {
    if (!openGlobal(G, dl))
      continue;
    auto it = table.find(G.getName().str());
    if (it == table.end() || !it->second.data || it->second.size != 0 || it->second.sec < 0)
      continue;
    Group &g = groups[{it->second.image, it->second.sec}];
    g.image = it->second.image;
    g.sec = it->second.sec;
    g.names.push_back(G.getName().str());
  }
  for (auto &kv : groups) {
    Group &g = kv.second;
    const Image &im = images[g.image];
    const Sec &sec = im.secs[g.sec];
    uint64_t lo = ~0ull, hi = 0;
    bool constant = true;
    for (const std::string &n : g.names) {
      lo = std::min(lo, table.at(n).addr);
      hi = std::max(hi, table.at(n).addr);
      if (GlobalVariable *G = M.getGlobalVariable(n))
        constant = constant && G->isConstant();
    }
    bool past = hi >= sec.addr + sec.size;
    uint64_t n = past ? hi - lo : hi - lo + 1;
    if (n == 0 || n > kByteCap || lo < sec.addr || ranged(im, lo, lo + n))
      continue;
    Constant *init = bytesOf(ctx, sec, lo, n);
    if (!init)
      continue;
    auto *blob = new GlobalVariable(M, init->getType(), constant, GlobalValue::PrivateLinkage, init, "client.image");
    blob->setAlignment(alignOf(lo));
    for (const std::string &name : g.names) {
      uint64_t at = table.at(name).addr - lo;
      Constant *gep = ConstantExpr::getInBoundsGetElementPtr(Type::getInt8Ty(ctx), blob, ConstantInt::get(Type::getInt64Ty(ctx), at));
      addr[name] = gep;
      if (GlobalVariable *old = M.getGlobalVariable(name))
        redirect(old, gep);
      ++made;
    }
  }

  std::set<std::string> want;
  for (GlobalVariable &G : M.globals()) {
    if (!openGlobal(G, dl))
      continue;
    auto it = table.find(G.getName().str());
    if (it != table.end() && it->second.data && it->second.size > 0)
      want.insert(G.getName().str());
  }
  bool grew = true;
  while (grew) {
    grew = false;
    for (const std::string &name : std::vector<std::string>(want.begin(), want.end())) {
      const Sym &s = table.at(name);
      for (const Rel &r : relsOf(images[s.image], s.addr, s.addr + s.size)) {
        auto t = table.find(r.symbol);
        if (t != table.end() && t->second.data && t->second.size > 0 && want.insert(r.symbol).second)
          grew = true;
      }
    }
  }
  std::set<std::string> bad;
  bool changed = true;
  while (changed) {
    changed = false;
    for (const std::string &name : want) {
      if (bad.count(name))
        continue;
      const Sym &s = table.at(name);
      const Image &im = images[s.image];
      const Sec &sec = im.secs[s.sec];
      bool fail = s.size > kByteCap || s.addr < sec.addr || s.addr + s.size > sec.addr + sec.size ||
                  (!sec.bss && s.addr - sec.addr + s.size > sec.bytes.size());
      std::vector<Rel> rs = relsOf(im, s.addr, s.addr + s.size);
      uint64_t prev = 0;
      bool any = false;
      for (const Rel &r : rs) {
        uint64_t o = r.addr - s.addr;
        if (!absolutePointer(im.machine, r.type) || r.symbol.empty() || o + 8 > s.size || (any && o < prev + 8))
          fail = true;
        any = true;
        prev = o;
        auto t = table.find(r.symbol);
        if (t != table.end() && t->second.data && t->second.size > 0 && bad.count(r.symbol))
          fail = true;
        if (t != table.end() && t->second.data && t->second.size == 0 && !addr.count(r.symbol))
          fail = true;
      }
      if (fail && bad.insert(name).second)
        changed = true;
    }
  }

  struct Item {
    Sym sym;
    bool constant = false;
    Type *type = nullptr;
    std::vector<Rel> rels;
  };
  std::map<std::string, Item> items;
  for (const std::string &name : want) {
    if (bad.count(name))
      continue;
    const Sym &s = table.at(name);
    Item item;
    item.sym = s;
    item.rels = relsOf(images[s.image], s.addr, s.addr + s.size);
    GlobalVariable *old = M.getGlobalVariable(name);
    item.constant = old ? old->isConstant() : !(images[s.image].secs[s.sec].flags & ELF::SHF_WRITE);
    if (item.rels.empty())
      item.type = ArrayType::get(Type::getInt8Ty(ctx), s.size);
    else {
      std::vector<Type *> parts;
      uint64_t pos = 0;
      for (const Rel &r : item.rels) {
        uint64_t o = r.addr - s.addr;
        if (o > pos)
          parts.push_back(ArrayType::get(Type::getInt8Ty(ctx), o - pos));
        parts.push_back(PointerType::get(ctx, 0));
        pos = o + 8;
      }
      if (pos < s.size)
        parts.push_back(ArrayType::get(Type::getInt8Ty(ctx), s.size - pos));
      item.type = StructType::get(ctx, parts, true);
    }
    items.emplace(name, std::move(item));
  }
  for (auto &kv : items) {
    Item &item = kv.second;
    auto *gv = new GlobalVariable(M, item.type, item.constant, GlobalValue::ExternalLinkage, Constant::getNullValue(item.type),
                                  "client.image");
    gv->setAlignment(alignOf(item.sym.addr));
    addr[kv.first] = gv;
    if (GlobalVariable *old = M.getGlobalVariable(kv.first))
      redirect(old, gv);
    gv->setName(kv.first);
  }
  for (auto &kv : items) {
    Item &item = kv.second;
    const Sym &s = item.sym;
    const Sec &sec = images[s.image].secs[s.sec];
    Constant *init = nullptr;
    if (item.rels.empty()) {
      init = bytesOf(ctx, sec, s.addr, s.size);
    } else {
      std::vector<Constant *> parts;
      uint64_t pos = 0;
      bool ok = true;
      for (const Rel &r : item.rels) {
        uint64_t o = r.addr - s.addr;
        if (o > pos) {
          Constant *raw = bytesOf(ctx, sec, s.addr + pos, o - pos);
          if (!raw) {
            ok = false;
            break;
          }
          parts.push_back(raw);
        }
        Constant *base = symbolAddress(M, table, addr, r.symbol);
        Constant *slot = r.addend ? ConstantExpr::getGetElementPtr(
                                        Type::getInt8Ty(ctx), base, ConstantInt::get(ctx, APInt(64, (uint64_t)r.addend, true)))
                                  : base;
        parts.push_back(slot);
        pos = o + 8;
      }
      if (ok && pos < s.size) {
        Constant *raw = bytesOf(ctx, sec, s.addr + pos, s.size - pos);
        if (!raw)
          ok = false;
        else
          parts.push_back(raw);
      }
      if (ok)
        init = ConstantStruct::get(cast<StructType>(item.type), parts);
    }
    if (!init)
      continue;
    cast<GlobalVariable>(addr[kv.first])->setInitializer(init);
    ++made;
  }
  return made;
}

template <class ELFT>
void readDynamic(ELFObjectFile<ELFT> &obj, std::vector<std::string> &needed, std::string &runpath) {
  const ELFFile<ELFT> &ef = obj.getELFFile();
  auto sections = ef.sections();
  if (!sections) {
    consumeError(sections.takeError());
    return;
  }
  const typename ELFT::Shdr *dynstr = nullptr;
  const typename ELFT::Shdr *dynamic = nullptr;
  for (const auto &s : *sections) {
    auto name = ef.getSectionName(s);
    if (!name) {
      consumeError(name.takeError());
      continue;
    }
    if (*name == ".dynstr")
      dynstr = &s;
    else if (*name == ".dynamic")
      dynamic = &s;
  }
  if (!dynstr || !dynamic)
    return;
  auto str = ef.getStringTable(*dynstr);
  auto bytes = ef.getSectionContents(*dynamic);
  if (!str || !bytes) {
    if (!str)
      consumeError(str.takeError());
    if (!bytes)
      consumeError(bytes.takeError());
    return;
  }
  size_t n = bytes->size() / sizeof(typename ELFT::Dyn);
  auto *ents = reinterpret_cast<const typename ELFT::Dyn *>(bytes->data());
  for (size_t i = 0; i < n; ++i) {
    if (ents[i].getTag() == ELF::DT_NULL)
      break;
    if (ents[i].d_un.d_val > str->size())
      continue;
    std::string value = str->drop_front(ents[i].d_un.d_val).split('\0').first.str();
    if (ents[i].getTag() == ELF::DT_NEEDED)
      needed.push_back(value);
    else if (ents[i].getTag() == ELF::DT_RUNPATH || (runpath.empty() && ents[i].getTag() == ELF::DT_RPATH))
      runpath = value;
  }
}

bool readDynamic(const std::string &path, std::vector<std::string> &needed, std::string &runpath) {
  auto bin = ObjectFile::createObjectFile(path);
  if (!bin) {
    consumeError(bin.takeError());
    return false;
  }
  if (auto *elf = dyn_cast<ELF64LEObjectFile>(bin->getBinary()))
    readDynamic(*elf, needed, runpath);
  else if (auto *elf = dyn_cast<ELF64BEObjectFile>(bin->getBinary()))
    readDynamic(*elf, needed, runpath);
  return true;
}

// Sonames in the build tree that holds an installed library. The walk starts a
// few directories above that library and stays inside the project, so a
// dependency built beside the install tree is visible and a system directory
// is not.
std::map<std::string, std::string> sonamesUnder(const fs::path &root) {
  std::map<std::string, std::string> out;
  std::vector<std::pair<fs::path, int>> work{{root, 4}};
  while (!work.empty()) {
    auto [dir, depth] = work.back();
    work.pop_back();
    std::error_code ec;
    for (fs::directory_iterator it(dir, ec), end; it != end && !ec; it.increment(ec)) {
      std::error_code sec;
      bool link = it->is_symlink(sec);
      if (it->is_regular_file(sec)) {
        std::string name = it->path().filename().string();
        if (name.find(".so") != std::string::npos)
          out.emplace(name, it->path().string());
      } else if (!link && it->is_directory(sec) && depth > 0) {
        work.push_back({it->path(), depth - 1});
      }
    }
  }
  return out;
}

fs::path findDependency(const fs::path &from, const std::string &soname, const std::string &runpath, const fs::path &caseDir) {
  auto present = [](const fs::path &p) {
    std::error_code ec;
    return fs::is_regular_file(p, ec) ? p : fs::path();
  };
  std::error_code oec;
  fs::path origin = fs::weakly_canonical(from, oec).parent_path();
  if (oec)
    origin = from.parent_path();
  std::string rest = runpath;
  while (!rest.empty()) {
    auto cut = rest.find(':');
    std::string ent = rest.substr(0, cut);
    rest = cut == std::string::npos ? "" : rest.substr(cut + 1);
    if (ent.empty())
      continue;
    for (std::string token = "$ORIGIN"; ent.find(token) != std::string::npos;) {
      auto at = ent.find(token);
      ent.replace(at, token.size(), origin.string());
    }
    fs::path dir(ent);
    std::error_code dec;
    if (!fs::is_directory(dir, dec)) {
      std::string marker = "/" + caseDir.filename().string() + "/";
      auto pos = ent.find(marker);
      if (pos != std::string::npos)
        dir = caseDir / ent.substr(pos + marker.size());
    }
    if (fs::path hit = present(dir / soname); !hit.empty())
      return hit;
  }
  if (fs::path hit = present(origin / soname); !hit.empty())
    return hit;
  fs::path project = caseDir.parent_path().parent_path();
  fs::path anc = origin;
  for (int i = 0; i < 3; ++i) {
    fs::path up = anc.parent_path();
    if (up == anc)
      break;
    std::string us = up.string(), ps = project.string();
    if (us.size() < ps.size() || us.compare(0, ps.size(), ps) != 0)
      break;
    anc = up;
  }
  static std::map<std::string, std::map<std::string, std::string>> cache;
  auto it = cache.find(anc.string());
  if (it == cache.end())
    it = cache.emplace(anc.string(), sonamesUnder(anc)).first;
  auto found = it->second.find(soname);
  return found == it->second.end() ? fs::path() : fs::path(found->second);
}

// Installed libraries, then every DT_NEEDED they can name inside the case or
// the build tree that holds them. The same image is opened once.
std::vector<std::string> closureObjects(const fs::path &caseDir) {
  std::vector<std::string> objects = installedObjects(caseDir);
  std::set<std::string> seen;
  for (const std::string &so : objects) {
    std::error_code ec;
    fs::path real = fs::weakly_canonical(so, ec);
    seen.insert(ec ? so : real.string());
  }
  for (size_t i = 0; i < objects.size(); ++i) {
    std::vector<std::string> needed;
    std::string runpath;
    if (!readDynamic(objects[i], needed, runpath))
      continue;
    for (const std::string &soname : needed) {
      fs::path hit = findDependency(objects[i], soname, runpath, caseDir);
      if (hit.empty())
        continue;
      std::error_code ec;
      fs::path real = fs::weakly_canonical(hit, ec);
      std::string key = ec ? hit.string() : real.string();
      if (seen.insert(key).second)
        objects.push_back(hit.string());
    }
  }
  return objects;
}

} // namespace

unsigned closeModules(Module &down, Module &up, const fs::path &caseDir) {
  std::vector<std::string> objects = closureObjects(caseDir);
  unsigned linked = closeModulesBitcode(down, up, caseDir, objects);
  errs() << "modules " << caseDir.filename().string() << " bitcode " << linked << "\n";
  return linked;
}

void closeLibrary(Module &M, const fs::path &caseDir) {
  std::vector<std::string> objects = closureObjects(caseDir);
  unsigned linked = linkRecordedBitcode(M, caseDir, objects);
  std::vector<Image> images;
  std::map<std::string, Sym> table;
  for (const std::string &so : objects)
    openImage(so, images, table);
  unsigned imaged = materialize(M, images, table);
  // A function still declared after every bitcode unit was linked, yet defined
  // in an installed image, is native residue (DESIGN-D §0). Record it; do not
  // invent a body.
  if (NamedMDNode *old = M.getNamedMetadata("sp.native"))
    M.eraseNamedMetadata(old);
  NamedMDNode *native = M.getOrInsertNamedMetadata("sp.native");
  unsigned natives = 0;
  for (Function &F : M) {
    if (!F.isDeclaration() || F.isIntrinsic() || F.getName().starts_with("llvm."))
      continue;
    auto it = table.find(F.getName().str());
    if (it == table.end() || !it->second.func)
      continue;
    native->addOperand(MDNode::get(M.getContext(), {MDString::get(M.getContext(), F.getName())}));
    ++natives;
  }
  unsigned open = 0;
  for (GlobalVariable &G : M.globals())
    if (openGlobal(G, M.getDataLayout()))
      ++open;
  errs() << "close " << caseDir.filename().string() << " bitcode " << linked << " image " << imaged << " libraries " << objects.size()
         << " native " << natives << " open-globals " << open << "\n";
}
