#pragma once

#include "llvm/IR/Module.h"

#include <filesystem>
#include <map>
#include <string>
#include <vector>

// §3.10 The call relation of D and U: per defined function, the targets the
// may layer resolves for each of its indirect call sites, in the order the
// sites appear. It is written to calls.txt and carried in the bitcode as the
// marks klee/Support/CallTargets.h reads.
namespace calls {

// A function: its module ('D' or 'U') and name.
using Fn = std::pair<char, std::string>;
using Table = std::map<Fn, std::vector<std::vector<Fn>>>;

void write(const Table &t, const std::filesystem::path &p);
bool read(Table &t, const std::filesystem::path &p);
// Marks D and U. Fails, saying where, when a function's indirect call sites
// are not the ones the table lists.
bool annotate(llvm::Module &D, llvm::Module &U, const Table &t);

} // namespace calls
