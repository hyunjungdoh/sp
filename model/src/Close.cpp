#include "Close.h"

#include "llvm/BinaryFormat/ELF.h"
#include "llvm/IR/Constants.h"
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

bool environmentSymbol(const std::string &name) {
  static void *libs[4];
  static bool ready = false;
  if (!ready) {
    ready = true;
    const char *ns[] = {"libc.so.6", "libm.so.6", "libstdc++.so.6", "libgcc_s.so.1"};
    for (int i = 0; i < 4; ++i)
      libs[i] = dlopen(ns[i], RTLD_LAZY);
  }
  for (void *h : libs)
    if (h && dlsym(h, name.c_str()))
      return true;
  return false;
}

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
    std::string so = text.substr(q + 1, e - q - 1);
    std::error_code ec;
    fs::path real = fs::weakly_canonical(so, ec);
    std::string key = ec ? so : real.string();
    if (!so.empty() && seen.insert(key).second && fs::is_regular_file(so))
      out.push_back(so);
  }
  return out;
}

// A path recorded on the build machine names the same file here when the case
// directory moved: the suffix after "/<case>/" is the path inside this case.
fs::path remap(const fs::path &caseDir, StringRef recorded) {
  fs::path asIs(recorded.str());
  std::error_code ec;
  if (fs::is_regular_file(asIs, ec))
    return asIs;
  std::string marker = "/" + caseDir.filename().string() + "/";
  auto pos = recorded.find(marker);
  if (pos == StringRef::npos)
    return {};
  fs::path mapped = caseDir / recorded.substr(pos + marker.size()).str();
  return fs::is_regular_file(mapped, ec) ? mapped : fs::path();
}

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

// Bitcode the case still has, including the list an installed library stores
// in its .llvm_bc section. The two modules already linked are not read again.
unsigned linkRecordedBitcode(Module &M, const fs::path &caseDir, const std::vector<std::string> &objects) {
  std::set<std::string> skip = {(caseDir / "upstream.bc").string(), (caseDir / "upstream.pre.bc").string(),
                                (caseDir / "se_lib" / "downstream.closure.bc").string()};
  std::vector<fs::path> cands;
  std::set<std::string> seen;
  std::error_code ec;
  for (fs::recursive_directory_iterator it(caseDir, fs::directory_options::skip_permission_denied, ec), end; it != end;
       it.increment(ec)) {
    if (!it->is_regular_file(ec) || it->path().extension() != ".bc")
      continue;
    if (!skip.count(it->path().string()) && seen.insert(it->path().string()).second)
      cands.push_back(it->path());
  }
  unsigned linked = 0;
  auto takeSection = [&](StringRef bytes) {
    if (bytes.size() >= 4 && bytes[0] == 'B' && bytes[1] == 'C' && (unsigned char)bytes[2] == 0xc0 &&
        (unsigned char)bytes[3] == 0xde) {
      SMDiagnostic err;
      auto mod = parseIR(MemoryBufferRef(bytes, "llvm_bc"), err, M.getContext());
      if (!mod)
        return;
      Linker L(M);
      if (!L.linkInModule(std::move(mod), Linker::Flags::LinkOnlyNeeded))
        ++linked;
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
        cands.push_back(mapped);
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
  Linker L(M);
  std::vector<char> used(cands.size(), 0);
  bool progress = true;
  while (progress) {
    progress = false;
    std::set<std::string> open = unresolved(M);
    for (size_t i = 0; i < cands.size(); ++i) {
      if (used[i])
        continue;
      std::set<std::string> defs = definedIn(cands[i], M.getContext());
      bool useful = false;
      for (const std::string &d : defs)
        if (open.count(d) && !environmentSymbol(d))
          useful = true;
      if (!useful)
        continue;
      SMDiagnostic err;
      auto mod = parseIRFile(cands[i].string(), err, M.getContext());
      if (!mod)
        continue;
      if (L.linkInModule(std::move(mod), Linker::Flags::LinkOnlyNeeded))
        errs() << "close: link failed " << cands[i].string() << "\n";
      else
        ++linked;
      used[i] = 1;
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

void closeLibrary(Module &M, const fs::path &caseDir) {
  std::vector<std::string> objects = closureObjects(caseDir);
  unsigned linked = linkRecordedBitcode(M, caseDir, objects);
  std::vector<Image> images;
  std::map<std::string, Sym> table;
  for (const std::string &so : objects)
    openImage(so, images, table);
  unsigned imaged = materialize(M, images, table);
  unsigned open = 0;
  for (GlobalVariable &G : M.globals())
    if (openGlobal(G, M.getDataLayout()))
      ++open;
  errs() << "close " << caseDir.filename().string() << " bitcode " << linked << " image " << imaged << " libraries " << objects.size()
         << " open-globals " << open << "\n";
}
