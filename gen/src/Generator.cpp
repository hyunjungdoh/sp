#include "gen/Generator.hpp"

#include "gen/Driver.hpp"
#include "gen/Loader.hpp"
#include "gen/Place.hpp"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Support/SourceMgr.h"

#include <algorithm>
#include <filesystem>
#include <fstream>

namespace gen {

namespace {

// An inbounds index into an array of n elements, n >= 2, is an integer in
// 0 .. n-1. The bound is the array type in the instruction.
void boundInboundsArrays(llvm::Module &m) {
  llvm::LLVMContext &ctx = m.getContext();
  llvm::FunctionCallee assume = m.getOrInsertFunction(
      "klee_assume", llvm::FunctionType::get(llvm::Type::getVoidTy(ctx),
                                             {llvm::Type::getInt1Ty(ctx)}, false));
  std::vector<llvm::GetElementPtrInst *> geps;
  for (llvm::Function &F : m) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F))
      if (auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I))
        if (G->isInBounds())
          geps.push_back(G);
  }
  for (llvm::GetElementPtrInst *G : geps) {
    llvm::Type *cur = G->getSourceElementType();
    bool first = true;
    for (llvm::Value *idx : G->indices()) {
      if (first) {
        first = false;
        continue;
      }
      if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(cur)) {
        uint64_t n = AT->getNumElements();
        unsigned bits = idx->getType()->getIntegerBitWidth();
        if (n >= 2 && bits > 0 && n < (1ULL << std::min(bits, 63u)) &&
            !llvm::isa<llvm::Constant>(idx)) {
          llvm::IRBuilder<> b(G);
          llvm::Value *ge = b.CreateICmpSGE(idx, llvm::ConstantInt::get(idx->getType(), 0));
          llvm::Value *lt = b.CreateICmpSLT(idx, llvm::ConstantInt::get(idx->getType(), n));
          b.CreateCall(assume, {ge});
          b.CreateCall(assume, {lt});
        }
        cur = AT->getElementType();
      } else if (auto *ST = llvm::dyn_cast<llvm::StructType>(cur)) {
        auto *C = llvm::dyn_cast<llvm::ConstantInt>(idx);
        if (!C || C->getZExtValue() >= ST->getNumElements())
          break;
        cur = ST->getElementType(C->getZExtValue());
      } else {
        break;
      }
    }
  }
}

} // namespace

std::vector<Generated> generate(const std::string &reportPath, const std::string &bitcodePath,
                                const std::string &outDir, const std::string &upstreamPath) {
  Report report = loadReport(reportPath);
  std::vector<Driver> drivers = driversOf(report);

  llvm::LLVMContext ctx;
  llvm::SMDiagnostic err;
  std::unique_ptr<llvm::Module> library = llvm::parseIRFile(bitcodePath, err, ctx);
  std::vector<Generated> written;
  if (!library)
    return written;
  std::unique_ptr<llvm::Module> upstream;
  if (!upstreamPath.empty())
    upstream = llvm::parseIRFile(upstreamPath, err, ctx);
  std::vector<Placed> placed = placeAll(drivers, *library, upstream.get());

  std::filesystem::create_directories(outDir);
  std::ofstream manifest(std::filesystem::path(outDir) / "manifest.txt");
  if (!report.kept.empty())
    manifest << "kept " << report.kept << "\n";
  for (const Placed &p : placed) {
    Emitted e = emitDriver(p, *library, outDir, upstream.get());
    Generated g;
    g.func = p.func;
    g.irName = e.irName;
    g.file = e.file;
    g.ranges = 0;
    manifest << g.func << "\n";
    manifest << "ir " << g.irName << "\n";
    manifest << "file " << g.file << "\n";
    for (const PlacedArg &a : p.args) {
      g.args.push_back(a.index);
      manifest << "arg " << a.index << " dropped " << a.dropped << " shapes " << a.shapes.size() << "\n";
      for (const Shape &s : a.shapes) {
        const Object &root = s.objects[s.root];
        manifest << "shape " << root.type << " size " << root.size << "\n";
        for (size_t oi = 0; oi < s.objects.size(); ++oi) {
          const Object &o = s.objects[oi];
          for (const auto &edge : o.edges)
            manifest << "edge " << oi << " " << edge.at << (edge.choice ? " choice" : "") << " -> " << edge.child
                     << " " << s.objects[edge.child].type << "\n";
          for (const auto &w : o.words)
            manifest << "word " << oi << " " << w.first << " " << w.second << "\n";
          for (const Object::Pin &pin : o.pins)
            manifest << "pin " << oi << " " << pin.off << " " << pin.val << " " << pin.bytes << "\n";
          for (const Object::FnPtr &fn : o.fns)
            manifest << "fn " << oi << " " << fn.at << " " << fn.name << "\n";
          for (const Object::Assume &a : o.assumes) {
            manifest << "assume " << oi << " " << a.off << " " << a.pred << " " << a.bytes;
            for (const std::string &v : a.vals)
              manifest << " " << v;
            manifest << "\n";
          }
          for (const Range &r : o.ranges) {
            manifest << "sym " << oi << " " << o.type << " " << r.off << "+" << r.len << "\n";
            ++g.ranges;
          }
        }
      }
    }
    if (p.file)
      manifest << "klee-file 1 " << p.fileBytes << "\n";
    if (!e.file.empty() && !upstreamPath.empty()) {
      llvm::LLVMContext lctx;
      llvm::SMDiagnostic lerr;
      std::string harnessPath = (std::filesystem::path(outDir) / e.file).string();
      std::unique_ptr<llvm::Module> harness = llvm::parseIRFile(harnessPath, lerr, lctx);
      std::unique_ptr<llvm::Module> down = llvm::parseIRFile(bitcodePath, lerr, lctx);
      std::unique_ptr<llvm::Module> up = llvm::parseIRFile(upstreamPath, lerr, lctx);
      if (!harness || !down || !up) {
        llvm::errs() << "link parse failed " << p.func << "\n";
      } else {
        llvm::Linker linker(*harness);
        std::unique_ptr<llvm::Module> fileRt =
            llvm::parseIRFile("/home/guswjd/sp/gen/runtime/file.bc", lerr, lctx);
        bool linked = !linker.linkInModule(std::move(down)) && !linker.linkInModule(std::move(up));
        if (linked && fileRt)
          linked = !linker.linkInModule(std::move(fileRt));
        if (!linked) {
          llvm::errs() << "link failed " << p.func << "\n";
        } else {
          // An internal definition keeps its name by taking a numeric suffix
          // when the harness already declared that name. The store must be
          // the definition.
          std::vector<llvm::Function *> decls;
          for (llvm::Function &F : *harness)
            if (F.isDeclaration() && F.hasName() && !F.use_empty())
              decls.push_back(&F);
          for (llvm::Function *D : decls) {
            llvm::Function *body = nullptr;
            bool many = false;
            std::string prefix = D->getName().str() + ".";
            for (llvm::Function &F : *harness) {
              if (&F == D || F.isDeclaration() || F.getFunctionType() != D->getFunctionType())
                continue;
              llvm::StringRef n = F.getName();
              if (!n.starts_with(prefix) || n.size() == prefix.size())
                continue;
              bool digits = true;
              for (size_t i = prefix.size(); i < n.size(); ++i)
                if (n[i] < '0' || n[i] > '9')
                  digits = false;
              if (!digits)
                continue;
              if (body)
                many = true;
              else
                body = &F;
            }
            if (body && !many) {
              D->replaceAllUsesWith(body);
              D->eraseFromParent();
            }
          }
          // A sized global with no definition is the zero object of its type.
          // The process streams stay the host streams.
          for (llvm::GlobalVariable &G : harness->globals()) {
            if (!G.isDeclaration() || !G.hasName())
              continue;
            llvm::StringRef n = G.getName();
            if (n == "stdout" || n == "stderr" || n == "stdin")
              continue;
            llvm::Type *ty = G.getValueType();
            if (!ty || !ty->isSized())
              continue;
            G.setInitializer(llvm::Constant::getNullValue(ty));
          }
          boundInboundsArrays(*harness);
          std::filesystem::path linked = std::filesystem::path(outDir) / e.file;
          linked.replace_extension(".linked.bc");
          std::error_code ec;
          llvm::raw_fd_ostream dest(linked.string(), ec);
          if (!ec) {
            llvm::WriteBitcodeToFile(*harness, dest);
            manifest << "linked " << linked.string() << "\n";
            g.file = linked.string();
          }
        }
      }
    }
    written.push_back(std::move(g));
  }
  return written;
}

} // namespace gen
