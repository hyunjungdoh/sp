#pragma once

#include <filesystem>

#include <string>

namespace llvm {
class Module;
}

// A path recorded on the build machine (surfaces.json, .llvm_bc) names the
// same file here when the case directory moved: the suffix after "/<case>/"
// is the path inside this case. Empty when neither names a file.
std::filesystem::path caseFile(const std::filesystem::path &caseDir, const std::string &recorded);

// upstream.bc is the upstream library that contains the sink. downstream.closure.bc
// is the downstream library the client calls. Before either is analyzed, every
// case closes those two the same way: bitcode the case still has, including
// the lists installed libraries store, is linked for a symbol either library
// only declares. The unit goes to the library that declares the symbol, and to
// upstream when both do, so the body exists once. A function with no bitcode
// in the case stays a declaration. Nothing is rebuilt and no body is invented.
unsigned closeModules(llvm::Module &down, llvm::Module &up, const std::filesystem::path &caseDir);

// The linked client still names data the two libraries left undefined. Every
// case fills that the same way: a data object the installed image defines is
// given that image's bytes. Bitcode still missing is linked by the same rule
// as closeModules. A function with no bitcode stays a declaration.
void closeLibrary(llvm::Module &M, const std::filesystem::path &caseDir);
