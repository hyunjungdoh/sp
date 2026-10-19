#include "gen/Emit.hpp"

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Demangle/Demangle.h"

#include <filesystem>
#include <limits>
#include <unordered_set>

namespace gen {

namespace {

std::string shown(const llvm::Function &F) {
  std::string n = F.getName().str();
  std::string d = llvm::demangle(n);
  if (d.empty() || d == n)
    return n;
  return d;
}

bool covers(const llvm::Function &F, int arg) {
  if (arg < 0)
    return false;
  if (static_cast<unsigned>(arg) < F.arg_size())
    return true;
  return F.isVarArg();
}

const llvm::Function *lookup(llvm::Module &library, const Placed &placed) {
  int need = -1;
  for (const PlacedArg &a : placed.args)
    if (a.index > need)
      need = a.index;
  const llvm::Function *best = nullptr;
  for (llvm::Function &F : library) {
    if (!F.hasName() || shown(F) != placed.func || !covers(F, need))
      continue;
    if (!best) {
      best = &F;
      continue;
    }
    bool body = !F.isDeclaration();
    bool bestBody = !best->isDeclaration();
    if (body != bestBody) {
      if (body)
        best = &F;
      continue;
    }
    if (F.getName() < best->getName())
      best = &F;
  }
  return best;
}

llvm::GlobalVariable *nameOf(llvm::Module &m, llvm::LLVMContext &ctx, const std::string &text) {
  std::string bytes = text;
  bytes.push_back('\0');
  auto *ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(ctx), bytes.size());
  auto *init = llvm::ConstantDataArray::getString(ctx, text, true);
  return new llvm::GlobalVariable(m, ty, true, llvm::GlobalValue::PrivateLinkage, init);
}

} // namespace

Emitted emitDriver(const Placed &placed, llvm::Module &library, const std::string &outDir,
                   llvm::Module *upstream) {
  Emitted out;
  const llvm::Function *src = lookup(library, placed);
  if (!src)
    return out;
  out.irName = src->getName().str();
  llvm::LLVMContext &ctx = library.getContext();
  llvm::Module m(out.irName, ctx);
  m.setDataLayout(library.getDataLayout());
  m.setTargetTriple(library.getTargetTriple());

  auto *i8 = llvm::Type::getInt8Ty(ctx);
  auto *i32 = llvm::Type::getInt32Ty(ctx);
  auto *i64 = llvm::Type::getInt64Ty(ctx);
  auto *ptr = llvm::PointerType::get(ctx, 0);
  auto *kleeTy = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), {ptr, i64, ptr}, false);
  auto *klee = llvm::Function::Create(kleeTy, llvm::GlobalValue::ExternalLinkage, "klee_make_symbolic", m);
  auto *decl = llvm::Function::Create(src->getFunctionType(), llvm::GlobalValue::ExternalLinkage, src->getName(), m);
  auto *mainTy = llvm::FunctionType::get(i32, false);
  auto *main = llvm::Function::Create(mainTy, llvm::GlobalValue::ExternalLinkage, "main", m);
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", main);
  llvm::IRBuilder<> b(entry);
  std::vector<llvm::Value *> intSym;

  // KLEE accepts klee_make_symbolic only when the size is the whole object.
  // A field is a separate object of that size, copied into the struct.
  auto symbolic = [&](llvm::Value *addr, int64_t nbytes, const std::string &label) {
    if (nbytes <= 0)
      return;
    auto *nm = nameOf(m, ctx, label);
    auto *tmp = b.CreateAlloca(i8, llvm::ConstantInt::get(i64, nbytes), "sym");
    tmp->setAlignment(llvm::Align(1));
    b.CreateCall(klee, {tmp, llvm::ConstantInt::get(i64, nbytes), nm});
    b.CreateMemCpy(addr, llvm::Align(1), tmp, llvm::Align(1),
                   static_cast<uint64_t>(nbytes));
  };
  auto buildShape = [&](const Shape &shape, int argIndex, int shapeIndex) -> llvm::Value * {
    std::vector<llvm::Value *> objs;
    objs.reserve(shape.objects.size());
    for (size_t oi = 0; oi < shape.objects.size(); ++oi) {
      const Object &o = shape.objects[oi];
      auto *buf = b.CreateAlloca(i8, llvm::ConstantInt::get(i64, o.size),
                                 "a" + std::to_string(argIndex) + "s" + std::to_string(shapeIndex) + "o" +
                                     std::to_string(oi));
      buf->setAlignment(llvm::Align(o.align == 0 ? 1 : o.align));
      b.CreateMemSet(buf, llvm::ConstantInt::get(i8, 0), o.size, llvm::Align(o.align == 0 ? 1 : o.align));
      objs.push_back(buf);
    }
    auto storeEdge = [&](size_t oi, const Edge &e) {
      llvm::Value *slot = objs[oi];
      if (e.at != 0)
        slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, e.at));
      b.CreateStore(objs[e.child], slot);
    };
    for (size_t oi = 0; oi < shape.objects.size(); ++oi) {
      const Object &o = shape.objects[oi];
      bool fileName = placed.fileBytes > 0 && o.type == "char";
      if (fileName && !objs.empty()) {
        b.CreateStore(llvm::ConstantInt::get(i8, 'A'), objs[oi]);
        if (o.size > 1) {
          auto *z = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, 1));
          b.CreateStore(llvm::ConstantInt::get(i8, 0), z);
        }
      }
      for (const Range &r : o.ranges) {
        if (fileName || r.len <= 0)
          continue;
        llvm::Value *at = objs[oi];
        if (r.off != 0)
          at = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, r.off));
        symbolic(at, r.len,
                 placed.func + ".arg" + std::to_string(argIndex) + "." + o.type + "+" +
                     std::to_string(r.off));
      }
      unsigned bits = m.getDataLayout().getPointerSizeInBits(0);
      auto *ity = llvm::Type::getIntNTy(ctx, bits == 0 ? 64 : bits);
      bool fileStr = placed.fileBytes > 0 &&
                     (o.type.find("basic_string") != std::string::npos || o.type.find("string_view") != std::string::npos);
      for (const auto &w : o.words) {
        llvm::Value *slot = objs[oi];
        if (w.first != 0)
          slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, w.first));
        uint64_t val = fileStr ? 1 : w.second;
        auto *st = b.CreateStore(llvm::ConstantInt::get(ity, val), slot);
        st->setAlignment(llvm::Align(bits == 0 ? 8 : bits / 8));
      }
      auto integer = [&](uint64_t bytes, const std::string &dec) -> llvm::ConstantInt * {
        if (bytes == 0 || bytes > std::numeric_limits<unsigned>::max() / 8)
          return nullptr;
        unsigned bits = (unsigned)bytes * 8;
        return llvm::ConstantInt::get(ctx, llvm::APInt(bits, dec, 10));
      };
      for (const Object::Pin &p : o.pins) {
        llvm::ConstantInt *c = integer(p.bytes, p.val);
        if (!c)
          continue;
        llvm::Value *slot = objs[oi];
        if (p.off != 0)
          slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, p.off));
        auto *st = b.CreateStore(c, slot);
        st->setAlignment(llvm::Align(1));
      }
      if (!o.assumes.empty()) {
        auto assumeTy = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), {llvm::Type::getInt1Ty(ctx)}, false);
        llvm::FunctionCallee assume = m.getOrInsertFunction("klee_assume", assumeTy);
        for (const Object::Assume &a : o.assumes) {
          if (a.vals.empty() && a.otherAlloc < 0 && a.otherArg < 0)
            continue;
          if (a.bytes == 0 || a.bytes > std::numeric_limits<unsigned>::max() / 8)
            continue;
          llvm::Value *slot = objs[oi];
          if (a.off != 0)
            slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, a.off));
          auto *ty = llvm::Type::getIntNTy(ctx, (unsigned)a.bytes * 8);
          auto *ld = b.CreateLoad(ty, slot);
          ld->setAlignment(llvm::Align(1));
          llvm::Value *tested = ld;
          if (!a.mask.empty()) {
            llvm::ConstantInt *m = integer(a.bytes, a.mask);
            if (!m)
              continue;
            tested = b.CreateAnd(ld, m);
          }
          llvm::Value *cond = nullptr;
          if (a.otherArg >= 0 && a.otherArg < (int)intSym.size() && intSym[(size_t)a.otherArg] &&
              intSym[(size_t)a.otherArg]->getType() == ty) {
            cond = b.CreateICmp(static_cast<llvm::CmpInst::Predicate>(a.pred), tested,
                                intSym[(size_t)a.otherArg]);
          } else if (a.otherAlloc >= 0 && a.otherOff >= 0 && a.otherAlloc < (int)objs.size()) {
            llvm::Value *other = objs[(size_t)a.otherAlloc];
            if (a.otherOff != 0)
              other = b.CreateGEP(i8, other, llvm::ConstantInt::get(i64, a.otherOff));
            auto *rd = b.CreateLoad(ty, other);
            rd->setAlignment(llvm::Align(1));
            cond = b.CreateICmp(static_cast<llvm::CmpInst::Predicate>(a.pred), tested, rd);
          } else if (a.pred == llvm::ICmpInst::ICMP_EQ && a.vals.size() > 1) {
            cond = llvm::ConstantInt::getFalse(ctx);
            for (const std::string &v : a.vals) {
              llvm::ConstantInt *c = integer(a.bytes, v);
              if (!c)
                continue;
              cond = b.CreateOr(cond, b.CreateICmpEQ(tested, c));
            }
          } else if (!a.vals.empty()) {
            llvm::ConstantInt *c = integer(a.bytes, a.vals[0]);
            if (!c)
              continue;
            cond = b.CreateICmp(static_cast<llvm::CmpInst::Predicate>(a.pred), tested, c);
          }
          if (cond)
            b.CreateCall(assume, cond);
        }
      }
    }
    for (size_t oi = 0; oi < shape.objects.size(); ++oi)
      for (const Edge &e : shape.objects[oi].edges)
        if (!e.choice)
          storeEdge(oi, e);
    for (size_t oi = 0; oi < shape.objects.size(); ++oi) {
      for (const Edge &e : shape.objects[oi].edges) {
        if (!e.choice)
          continue;
        auto *bitA = b.CreateAlloca(llvm::Type::getInt1Ty(ctx));
        symbolic(bitA, 1, placed.func + ".arg" + std::to_string(argIndex) + ".bound" + std::to_string(e.at));
        auto *bit = b.CreateLoad(llvm::Type::getInt1Ty(ctx), bitA);
        auto *neuBB = llvm::BasicBlock::Create(ctx, "neu", main);
        auto *joinBB = llvm::BasicBlock::Create(ctx, "join", main);
        b.CreateCondBr(bit, neuBB, joinBB);
        b.SetInsertPoint(neuBB);
        storeEdge(oi, e);
        b.CreateBr(joinBB);
        b.SetInsertPoint(joinBB);
      }
    }
    for (size_t oi = 0; oi < shape.objects.size(); ++oi) {
      for (const Object::FnPtr &fn : shape.objects[oi].fns) {
        auto findBody = [&](llvm::Module *M) -> const llvm::Function * {
          if (!M)
            return nullptr;
          const llvm::Function *decl = nullptr;
          for (llvm::Function &F : *M) {
            if (!F.hasName() || (F.getName() != fn.name && shown(F) != fn.name))
              continue;
            if (!F.isDeclaration())
              return &F;
            if (!decl)
              decl = &F;
          }
          return decl;
        };
        const llvm::Function *lib = findBody(&library);
        if (!lib)
          lib = findBody(upstream);
        if (!lib)
          continue;
        llvm::Function *decl = m.getFunction(lib->getName());
        if (!decl)
          decl = llvm::Function::Create(lib->getFunctionType(), llvm::GlobalValue::ExternalLinkage, lib->getName(), m);
        else if (decl->getFunctionType() != lib->getFunctionType())
          continue;
        llvm::Value *slot = objs[oi];
        if (fn.at != 0)
          slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, fn.at));
        auto *st = b.CreateStore(decl, slot);
        st->setAlignment(llvm::Align(8));
      }
      for (int64_t at : shape.objects[oi].backs) {
        llvm::Value *slot = objs[oi];
        if (at != 0)
          slot = b.CreateGEP(i8, objs[oi], llvm::ConstantInt::get(i64, at));
        auto *st = b.CreateStore(objs[shape.root], slot);
        st->setAlignment(llvm::Align(8));
      }
    }
    return objs[shape.root];
  };

  unsigned nSym = src->arg_size();
  intSym.assign(nSym, nullptr);
  {
    std::vector<char> need(nSym, 0);
    for (const PlacedArg &a : placed.args)
      for (const Shape &sh : a.shapes)
        for (const Object &o : sh.objects)
          for (const Object::Assume &as : o.assumes)
            if (as.otherArg >= 0 && as.otherArg < (int)nSym)
              need[(size_t)as.otherArg] = 1;
    for (unsigned i = 0; i < nSym; ++i) {
      if (!need[i])
        continue;
      llvm::Type *ty = decl->getArg(i)->getType();
      if (!ty->isIntegerTy() || !ty->isSized())
        continue;
      uint64_t bytes = m.getDataLayout().getTypeStoreSize(ty).getFixedValue();
      auto *slot = b.CreateAlloca(ty, nullptr, "iarg" + std::to_string(i));
      symbolic(slot, static_cast<int64_t>(bytes), placed.func + ".arg" + std::to_string(i));
      intSym[i] = b.CreateLoad(ty, slot);
    }
  }

  std::vector<llvm::Value *> args;
  unsigned n = src->arg_size();
  args.reserve(n);
  for (unsigned i = 0; i < n; ++i) {
    llvm::Type *ty = decl->getArg(i)->getType();
    const PlacedArg *slot = nullptr;
    for (const PlacedArg &a : placed.args)
      if (a.index == static_cast<int>(i))
        slot = &a;
    if (!slot) {
      if (src->hasParamAttribute(i, llvm::Attribute::StructRet) ||
          src->hasParamAttribute(i, llvm::Attribute::ByVal)) {
        llvm::Type *memTy = nullptr;
        if (src->hasParamAttribute(i, llvm::Attribute::StructRet))
          memTy = src->getParamAttribute(i, llvm::Attribute::StructRet).getValueAsType();
        else
          memTy = src->getParamAttribute(i, llvm::Attribute::ByVal).getValueAsType();
        uint64_t bytes = memTy ? m.getDataLayout().getTypeAllocSize(memTy) : m.getDataLayout().getPointerSize(0);
        if (bytes == 0)
          bytes = 1;
        auto *slotp = b.CreateAlloca(i8, llvm::ConstantInt::get(i64, bytes), "arg" + std::to_string(i));
        llvm::Align al(8);
        if (memTy)
          al = m.getDataLayout().getABITypeAlign(memTy);
        slotp->setAlignment(al);
        b.CreateMemSet(slotp, llvm::ConstantInt::get(i8, 0), bytes, al);
        args.push_back(slotp);
      } else if (ty->isPointerTy()) {
        uint64_t bytes = m.getDataLayout().getPointerSize(0);
        if (bytes == 0)
          bytes = 8;
        const llvm::Argument *A = src->getArg(i);
        std::vector<const llvm::Value *> q{A};
        std::unordered_set<const llvm::Value *> seen;
        for (size_t vi = 0; vi < q.size(); ++vi) {
          if (!seen.insert(q[vi]).second)
            continue;
          for (const llvm::User *U : q[vi]->users()) {
            if (const auto *C = llvm::dyn_cast<llvm::CastInst>(U))
              q.push_back(C);
            else if (const auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
              q.push_back(G);
              llvm::APInt ap(m.getDataLayout().getIndexSizeInBits(0), 0);
              if (G->accumulateConstantOffset(m.getDataLayout(), ap) && !ap.isNegative()) {
                uint64_t end = ap.getZExtValue();
                llvm::Type *rt = G->getResultElementType();
                if (rt && rt->isSized())
                  end += m.getDataLayout().getTypeStoreSize(rt).getFixedValue();
                if (end > bytes)
                  bytes = end;
              }
            }
          }
        }
        auto *slotp = b.CreateAlloca(i8, llvm::ConstantInt::get(i64, bytes), "arg" + std::to_string(i));
        slotp->setAlignment(llvm::Align(8));
        b.CreateMemSet(slotp, llvm::ConstantInt::get(i8, 0), bytes, llvm::Align(8));
        args.push_back(slotp);
      } else if (i < intSym.size() && intSym[i]) {
        args.push_back(intSym[i]);
      } else {
        args.push_back(llvm::Constant::getNullValue(ty));
      }
      continue;
    }
    if (ty->isPointerTy()) {
      if (slot->shapes.empty()) {
        bool path = placed.file && placed.fileArg == static_cast<int>(i);
        uint64_t bytes = path ? 2 : m.getDataLayout().getPointerSize(0);
        if (bytes == 0)
          bytes = 8;
        auto *slotp = b.CreateAlloca(i8, llvm::ConstantInt::get(i64, bytes), "arg" + std::to_string(i));
        slotp->setAlignment(llvm::Align(8));
        if (path) {
          b.CreateStore(llvm::ConstantInt::get(i8, 'A'), slotp);
          auto *z = b.CreateGEP(i8, slotp, llvm::ConstantInt::get(i64, 1));
          b.CreateStore(llvm::ConstantInt::get(i8, 0), z);
        } else {
          b.CreateMemSet(slotp, llvm::ConstantInt::get(i8, 0), bytes, llvm::Align(8));
        }
        args.push_back(slotp);
      } else if (slot->shapes.size() == 1) {
        args.push_back(buildShape(slot->shapes[0], static_cast<int>(i), 0));
      } else {
        // One concrete object per path. A select of those pointers is one
        // symbolic address, and the solver then indexes every object.
        auto *choice = b.CreateAlloca(i32, nullptr, "arg" + std::to_string(i) + ".which");
        symbolic(choice, m.getDataLayout().getTypeAllocSize(i32),
                 placed.func + ".arg" + std::to_string(i) + ".which");
        llvm::Value *which = b.CreateLoad(i32, choice);
        auto *join = llvm::BasicBlock::Create(ctx, "shapes", main);
        auto *defBB = llvm::BasicBlock::Create(ctx, "shape0", main);
        auto *sw = b.CreateSwitch(which, defBB, slot->shapes.size());
        std::vector<std::pair<llvm::BasicBlock *, llvm::Value *>> incoming;
        for (size_t s = 0; s < slot->shapes.size(); ++s) {
          llvm::BasicBlock *bb =
              s == 0 ? defBB : llvm::BasicBlock::Create(ctx, "shape" + std::to_string(s), main);
          if (s != 0)
            sw->addCase(llvm::ConstantInt::get(i32, s), bb);
          b.SetInsertPoint(bb);
          llvm::Value *obj = buildShape(slot->shapes[s], static_cast<int>(i), static_cast<int>(s));
          llvm::BasicBlock *from = b.GetInsertBlock();
          b.CreateBr(join);
          incoming.emplace_back(from, obj);
        }
        b.SetInsertPoint(join);
        auto *phi = b.CreatePHI(ptr, incoming.size());
        for (const auto &in : incoming)
          phi->addIncoming(in.second, in.first);
        args.push_back(phi);
      }
    } else {
      auto *slotv = b.CreateAlloca(ty, nullptr, "arg" + std::to_string(i));
      uint64_t bytes = m.getDataLayout().getTypeAllocSize(ty);
      symbolic(slotv, static_cast<int64_t>(bytes), placed.func + ".arg" + std::to_string(i));
      args.push_back(b.CreateLoad(ty, slotv));
    }
  }
  b.CreateCall(decl, args);
  b.CreateRet(llvm::ConstantInt::get(i32, 0));

  std::string err;
  llvm::raw_string_ostream os(err);
  if (llvm::verifyModule(m, &os))
    return Emitted{};

  std::filesystem::create_directories(outDir);
  std::string file = out.irName + ".bc";
  for (char &c : file)
    if (c == '/' || c == ' ')
      c = '_';
  out.file = file;
  std::error_code ec;
  llvm::raw_fd_ostream dest((std::filesystem::path(outDir) / file).string(), ec);
  if (ec)
    return Emitted{};
  llvm::WriteBitcodeToFile(m, dest);
  return out;
}

} // namespace gen
