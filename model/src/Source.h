#pragma once

// The source identity of struct fields.
//
// Linking uniques isomorphic named structs: the IR mover maps a struct onto
// any structurally equal one the destination already has. After linking an
// IR struct name therefore denotes a class of source types. libjpeg's color
// converter, color deconverter, coefficient controller and upsampler are
// all {ptr, ptr} and end up under one name, so a field identity built from
// IR names joins function pointers of unrelated components.
//
// DWARF keeps the source types. The type of the object a pointer value
// addresses, pi(v), follows from the declarations its derivation passes:
//   pi(parameter)   = pointee of the declared parameter type
//   pi(alloca)      = the type of the variable dbg.declare binds to it
//   pi(global)      = the type of the global's variable
//   pi(gep b, i..)  = the member of pi(b) the indices select
//   pi(load p)      = pointee of pi(p)
//   pi(call f)      = pointee of f's declared return type
//   pi(cast x)      = pi(x), and a phi or select whose known inputs agree.
// A struct level is named by its source type when pi reaches it and the
// source layout is the IR struct's layout, the condition under which the
// linker merges the two. A level pi does not reach, or one accessed through
// a cast to a struct of another layout, is named by the IR struct. Either
// name is spelled struct.N / class.ns::N without the numeric suffix that
// uniquing within one LLVMContext appends: the suffix is not a type.

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Operator.h"

#include <string>
#include <utility>
#include <vector>

namespace llvm {
class DIType;
class GlobalVariable;
class Module;
class StructType;
} // namespace llvm

namespace source {

// Record the composite definitions of M, so a declaration resolves to its
// definition in another compile unit. reset forgets every module.
void index(llvm::Module &M);
void reset();

// The source type of the object V addresses, or null.
const llvm::DIType *pointee(const llvm::Value *V);

// The source type of a global's object, or null.
const llvm::DIType *ofGlobal(const llvm::GlobalVariable &G);

// The member of D at byte offset off whose size is size bytes, or null.
const llvm::DIType *member(const llvm::DIType *D, uint64_t off, uint64_t size);

// The element type of an array D, or null.
const llvm::DIType *element(const llvm::DIType *D);

// The IR spelling of the record D denotes (struct.N, class.ns::N), or "".
std::string name(const llvm::DIType *D);

// The name of IR struct S when it holds an object of source type D.
std::string key(const llvm::DIType *D, llvm::StructType *S, const llvm::DataLayout &dl);

// The name of the struct a GEP indexes, "" when its source is not a named
// struct.
std::string container(const llvm::GEPOperator *G, const llvm::DataLayout &dl);

// The struct levels a constant GEP passes, outermost first, each with the
// byte offset of the addressed location inside it.
std::vector<std::pair<std::string, int64_t>> levels(const llvm::GEPOperator *G, const llvm::DataLayout &dl);

// An IR struct observed under a name, for its layout.
llvm::StructType *irType(const std::string &name);

// How many struct levels were named by source type, by IR name, and by a
// source name that differs from the IR name.
struct Stats {
  unsigned source = 0, ir = 0, renamed = 0;
};
const Stats &stats();

} // namespace source
