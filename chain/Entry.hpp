#pragma once

#include "Chop.hpp"

#include <string>
#include <vector>

namespace llvm {
class Module;
}

namespace chain {

// One chop, and the downstream strong exports that reach a call to it.
// A strong export is defined, named, not local, and not hidden. A hidden
// plugin hook is not an entry.
//
// The call graph is may-reachability. A direct call or invoke names its
// callee. An indirect call has an edge only in the two cases below.
//
// A load of a constant byte offset of struct type T may be any function
// stored at that offset of T whose type is the type of the call. The offset
// is taken modulo the size of T, so the elements of an array of T share the
// field. A variable index is not a field. A function may return any function
// it returns. Distinct objects of T share this field. A function is recorded
// on T only when the store or the initializer names T, and only when T has a
// field that is not a pointer.
// An all-pointer struct is not a source type: LLVM merges every struct of
// that layout into one type, so a lock table and an allocator would be one
// field. A load of any field of an all-pointer struct is the one buffer of
// the object that contains it, so the first and one-past-the-end pointers
// of an array are the same buffer. That struct is not a field name. A load
// that names an object has the functions copied onto that object, and no
// others: a copy whose destination named no object is not that object.
// A global, an alloca, an argument, and a noalias allocation are named
// objects. A load of such an object has the functions copied onto it. A
// function left unresolved at another object is not a callee: the same LLVM
// function type is not the same object. The merged layout is not the load.
// A function reached through a load of a struct field, or copied onto the
// called value, reaches that call only when every dereferenceable size the
// call and the function both state is the same size. A missing size leaves
// the function in the set. LLVM merges every std::function instantiation
// into one struct; that size is the instantiation. Two specializations of
// one class template share an instruction-stored function only when they
// are that same specialization. An initializer reaches every load of the
// field. A store or a load that is not inside that class template shares
// the field. The LLVM struct type is not the specialization. A vtable slot
// stays the function at that slot.
// A function constant stored by an instruction is also recorded on that
// object. A load/store copy carries it. A phi or a select may be any of its
// inputs, so those objects stay distinct and the function is copied to each.
// At a direct call, a parameter in the copy is replaced by the actual
// argument, and two calls stay two objects. One callsite does not erase
// the copies of another. Passing that parameter back at
// the same address adds no object. A different offset is that field. If an
// actual does not reduce to an object, the functions that reach that actual
// stay on the parameter. A function that does not reach it is not carried.
// The LLVM type is not that set. A function that was never stored by an
// instruction stays with a struct that has a non-pointer field. When
// every such copy reduces, an instruction-stored function is a target only
// if the copies put it at the loaded address. The pointer may cross a cast.
// __dynamic_cast with a non-negative src2dst offset returns the source
// pointer moved back by that offset: that is the offset of the source
// subobject in the destination. A negative offset is not a known
// adjustment. A load/store copy puts the same pointer in two cells. If
// those cells meet a global or a noalias allocation, a load of either cell
// is that object. A callee that is handed the object may be what copies the
// pointer; the copy is still the same pointer, and a field of the pointee
// is that field of the source. A noalias allocation stored into a cell is
// that cell's pointee: a function at an offset of the allocation is at
// that offset of the pointee. A function held in an object is also copied by the
// callees that object is passed to. The formal is not that location: the
// actual at the call is. If one of those destinations does not reduce to an
// object, the function stays on the named end of that copy. A walk that reaches a
// function again at the same offset adds no object. A walk that reaches it
// again at a different offset does not name a field, so that destination
// does not reduce. When the load itself reduces to a global or a noalias
// allocation, an instruction-stored function is absent from that load only
// when every copy of it reduced and none of those objects is the loaded
// one. A function whose copy did not reduce stays on the parameter of that
// copy. It does not stay on the struct type, and it remains a target of the
// load that reads that parameter.
// A direct call may return the address of a field of an argument. A load of
// an alloca may be any function stored into that alloca.
//
// A load of a pointer followed by a constant index into an array of
// pointers may be the function at that byte of a global table of function
// pointers, when that function's type is the type of the call. The tables considered are those stored at offset zero of an
// object that reaches the loaded pointer. An object is the pointer returned
// by a noalias call, or the address of an alloca. It reaches the load along
// casts, phi nodes, selects, freezes, a zero-offset getelementptr, alloca
// copies, and the arguments and returns of direct calls. A getelementptr of
// nonzero offset does not keep that object. A constant-index field of an
// allocation is a separate object. A field of that object keeps the object:
// the virtual table loaded from it is the object's table. A constant-index
// field is also a
// slot of its parent: the address of the field may be copied by the same
// operations, except a nonzero getelementptr, including when that address
// is passed to a function that stores through it. A store through the
// address is read by a load of the same field of the same parent. A
// variable index is not a field and does not select an entry of the table.
// Objects are not merged by struct type.
//
// A vtable call passes its receiver to the parameter of each function at
// that slot. The receiver is the argument that is the object the table was
// loaded from. That object then reaches a later load of the same pointer
// through casts, phi nodes, selects, freezes, a zero-offset getelementptr,
// a store to and load from an alloca, the matching argument of a direct
// call, and a returned pointer. A load through the pointer is not a copy.
// A function-pointer field does not pass a receiver: the field is shared
// by every object of the struct type, and the edge is only the function.
// The call does return the objects those functions return, when the object
// holds a table. A direct call already does this. An indirect factory
// would otherwise drop the allocated object at the call.
// That pointer may be stored at a byte offset of one object and loaded back
// by a function that returns the pointer at that offset of its argument.
// The load is the pointer stored into that same object. The struct type is
// not the slot: LLVM gives every one-pointer struct one name. Only the
// receiver of that virtual call is filled.
// A function stays on the named load unless every copy of it reduced to
// some other object. A summary that was not built is not that proof, so the
// function stays. The named entries are what the harness calls. A function
// left unresolved at another object is not a callee of this load: the same
// LLVM function type is not the same object. Residual is empty unless a
// callee remains after that distinction. The distinction is kept.
struct EntryGroup {
  std::string chop;
  std::vector<std::string> entries;
  std::vector<std::string> residual;
};

std::vector<EntryGroup> findEntries(llvm::Module &downstream, const std::vector<std::string> &chops);

std::string formatEntries(const ChopResult &chop, const std::vector<EntryGroup> &groups);

} // namespace chain
