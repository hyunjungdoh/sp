#pragma once

#include <filesystem>

namespace llvm {
class Module;
}

// The linked client still names library objects and functions that neither
// upstream nor downstream bitcode defines. Every case, present and later,
// closes that set the same way before the module is what an engine runs:
// bitcode the installed libraries point at is linked for the symbols still
// missing, and a data object the installed image defines is given that
// image's bytes. A function with no bitcode stays a declaration. The engine
// stops at the call, and no body is invented for it.
void closeLibrary(llvm::Module &M, const std::filesystem::path &caseDir);
