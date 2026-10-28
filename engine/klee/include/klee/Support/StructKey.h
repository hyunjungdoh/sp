//===-- StructKey.h ---------------------------------------------*- C++ -*-===//
//
// The tag identifying a struct type across translation units: a literal type
// is printed, a named type keeps its tag without the linker's .N suffix. A
// tagless declaration is a distinct type (C11 6.7.2.3p5; clang names it
// "anon"), so it keeps its full IR name: only the linker's own unification of
// one declaration seen in several units makes two of them one.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_STRUCTKEY_H
#define KLEE_STRUCTKEY_H

#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

namespace klee {

inline std::string structKey(llvm::StructType *ST) {
  if (ST->isLiteral() || !ST->hasName()) {
    std::string s;
    llvm::raw_string_ostream os(s);
    ST->print(os);
    return os.str();
  }
  llvm::StringRef n = ST->getName();
  while (true) {
    size_t dot = n.rfind('.');
    if (dot == llvm::StringRef::npos || dot + 1 == n.size())
      break;
    llvm::StringRef tail = n.substr(dot + 1);
    if (!llvm::all_of(tail, [](char c) { return c >= '0' && c <= '9'; }))
      break;
    n = n.substr(0, dot);
  }
  if (n.ends_with(".anon") || n.ends_with("::anon"))
    return ST->getName().str();
  return n.str();
}

} // namespace klee

#endif
