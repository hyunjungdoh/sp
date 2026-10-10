#pragma once

#include <string>
#include <vector>

namespace llvm {
class Function;
class Module;
}

namespace chain {

struct ChopResult {
  std::string sinkFile;
  unsigned sinkLine = 0;
  std::vector<std::string> sinkFns;
  unsigned reach = 0;
  unsigned called = 0;
  std::vector<std::string> chops;
};

// Module-entry functions of a call-graph chop to the sink.
// An indirect call targets a function when inclusion-based points-to
// (Andersen; flow-insensitive, context-insensitive, field-sensitive by
// constant byte offset) puts that function in the callee value.
// Objects are globals, allocas, and a fresh heap at each call of a
// noalias pointer-returning declaration. A function that only returns such
// a heap — including a call through an allocator function pointer, and a
// null check of that pointer — is an allocation site at each of its calls.
// A heap is the struct it is accessed as. A first member is that struct,
// either way. A heap that already has a struct type does not take fields of
// a proved-different struct through a merged pointer, or a heap that has
// no type yet: that access is the
// external object of the struct being accessed. It is not every offset of
// the other heap, and it is not an empty points-to.
// An object that is returned, or stored through a parameter, and was
// accessed as struct T, shares its fields with the external object of T.
// Constant field offsets along a GEP chain are added. A variable index into
// an array of pointers or aggregates is every element. A constant step
// through a pointer stays inside one array of pointers of the object's
// type. A type repeated on the layout path is not that array. A step that
// is not inside it is every offset of that object. An offset
// before the object, past its end, or into an object that has no size yet
// is every offset of that object. A zero index with no field is
// the same address. A procedure list is a parameter or one constant field
// of a parameter, holding an array of function pointers. Storing the
// integer 0 at offset 0 empties it only when the walk compares a load of
// that integer. A walk that does not compare it is not emptied. A walk loads its callee
// from a variable element of that array, or from a pointer that this
// function steps by one pointer and feeds back through a phi. A constant
// index is a fixed slot, and a load from a constant struct field is not a
// walk. The call is an edge of the caller that holds the path. It calls the
// procedures stored on a path that reaches the walk with no such store. A
// procedure is a constant function or a parameter. The parameter is replaced
// by the actual at the call. A parameter that remains contributes the
// functions in its points-to set. If the summary equations do not settle,
// that path's callees are every procedure stored into a list.
// Two paths whose pointees meet are one path.
// A parameter that no object reaches, used as a struct, denotes one
// external object of that struct. Outside the module a direct call is that
// callee. An indirect call whose target does not reduce has the functions
// that reach that callee operand. A load of a constant field of a struct
// that has a non-pointer field reaches the functions stored at that field.
// An all-pointer layout is not a field. The LLVM function type is not that
// set. A function reached through a load of such a field reaches that call
// only when every dereferenceable size the call and the function both state
// is the same size. A missing size leaves the function in the set. LLVM
// merges every std::function instantiation into one struct; that size is
// the instantiation. Two specializations of one class template share an
// instruction-stored function only when they are that same specialization.
// An initializer reaches every load of the field. A store or a load that
// is not inside that class template shares the field. The LLVM struct type
// is not the specialization. A parameter is the union of what reaches each actual, and one
// callsite does not erase another. A walk whose list is
// not one argument calls every procedure stored into a list.
ChopResult findChops(llvm::Module &upstream, llvm::Module &downstream, const std::string &file,
                     unsigned line);

std::string formatChops(const ChopResult &r);

// The class-template specialization that contains this function, written
// the way the demangler spells the class. Empty when the function is not
// inside a class template. Two methods of one specialization share it.
std::string classSpec(const llvm::Function *F);

// An initializer reaches every load. A store or a load that is not inside a
// class template shares the field. Two specializations of one class template
// share a stored function only when they are that same specialization.
bool fieldSpecVisible(const std::string &storeSpec, bool init, const std::string &loadSpec);

} // namespace chain
