// libstdc++'s exception-raising entry points (functexcept.cc), for an
// engine that does not unwind, and its allocation functions.
#include <bits/functexcept.h>
#include <cstdlib>
#include <new>
#include <regex>
#include <string>

// The engine does not unwind: a thrown exception ends the program as an
// uncaught one does, by std::terminate.
namespace std {
void __throw_bad_exception() { abort(); }
void __throw_bad_alloc() { abort(); }
void __throw_bad_array_new_length() { abort(); }
void __throw_bad_cast() { abort(); }
void __throw_bad_typeid() { abort(); }
void __throw_logic_error(const char *) { abort(); }
void __throw_domain_error(const char *) { abort(); }
void __throw_invalid_argument(const char *) { abort(); }
void __throw_length_error(const char *) { abort(); }
void __throw_out_of_range(const char *) { abort(); }
void __throw_out_of_range_fmt(const char *, ...) { abort(); }
void __throw_runtime_error(const char *) { abort(); }
void __throw_range_error(const char *) { abort(); }
void __throw_overflow_error(const char *) { abort(); }
void __throw_underflow_error(const char *) { abort(); }
void __throw_ios_failure(const char *) { abort(); }
void __throw_ios_failure(const char *, int) { abort(); }
void __throw_system_error(int) { abort(); }
void __throw_future_error(int) { abort(); }
void __throw_bad_function_call() { abort(); }
void __throw_regex_error(regex_constants::error_type) { abort(); }
} // namespace std

// The replaceable allocation functions ([new.delete]) the engine does not
// handle itself; it handles operator new/new[](size_t) and the plain and
// sized deletes. An allocation returns a distinct object even for size 0.
extern "C" void *memalign(size_t, size_t);

static void *allocate(std::size_t n, std::size_t a) {
  if (n == 0)
    n = 1;
  void *p = a ? memalign(a, n) : malloc(n);
  if (!p)
    std::__throw_bad_alloc();
  return p;
}

void *operator new(std::size_t n, std::align_val_t a) { return allocate(n, static_cast<std::size_t>(a)); }
void *operator new[](std::size_t n, std::align_val_t a) { return allocate(n, static_cast<std::size_t>(a)); }
void *operator new(std::size_t n, const std::nothrow_t &) noexcept { return malloc(n ? n : 1); }
void *operator new[](std::size_t n, const std::nothrow_t &) noexcept { return malloc(n ? n : 1); }
void *operator new(std::size_t n, std::align_val_t a, const std::nothrow_t &) noexcept {
  return memalign(static_cast<std::size_t>(a), n ? n : 1);
}
void *operator new[](std::size_t n, std::align_val_t a, const std::nothrow_t &) noexcept {
  return memalign(static_cast<std::size_t>(a), n ? n : 1);
}
void operator delete(void *p, std::align_val_t) noexcept { free(p); }
void operator delete[](void *p, std::align_val_t) noexcept { free(p); }
void operator delete(void *p, std::size_t, std::align_val_t) noexcept { free(p); }
void operator delete[](void *p, std::size_t, std::align_val_t) noexcept { free(p); }
void operator delete(void *p, const std::nothrow_t &) noexcept { free(p); }
void operator delete[](void *p, const std::nothrow_t &) noexcept { free(p); }
void operator delete(void *p, std::align_val_t, const std::nothrow_t &) noexcept { free(p); }
void operator delete[](void *p, std::align_val_t, const std::nothrow_t &) noexcept { free(p); }
