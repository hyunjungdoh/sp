// Bitcode stand-ins for the libstdc++ pieces the harness calls on the way
// to a sink. A native definition of any of these runs against host memory
// while its arguments are KLEE objects, which is an out-of-bounds access.
//
// The locale is "C". ctype<char>::tolower is ASCII case folding, dispatched
// through the same vtable slots libstdc++ uses. A path is one filename
// component; the only file in the environment is "f".
#include <filesystem>
#include <locale>
#include <sstream>
#include <string>
#include <utility>

namespace {

// Same primary vtable as libstdc++ ctype<char>, and the same 576-byte
// object so widen/narrow read their cache inside this object.
struct CType {
  virtual ~CType() {}
  virtual char do_toupper(char c) const {
    return (c >= 'a' && c <= 'z') ? char(c - 32) : c;
  }
  virtual const char *do_toupper(char *lo, const char *hi) const {
    for (; lo != hi; ++lo)
      *lo = do_toupper(*lo);
    return hi;
  }
  virtual char do_tolower(char c) const {
    return (c >= 'A' && c <= 'Z') ? char(c + 32) : c;
  }
  virtual const char *do_tolower(char *lo, const char *hi) const {
    for (; lo != hi; ++lo)
      *lo = do_tolower(*lo);
    return hi;
  }
  virtual char do_widen(char c) const { return c; }
  virtual const char *do_widen(const char *lo, const char *hi, char *to) const {
    for (; lo != hi; ++lo, ++to)
      *to = *lo;
    return hi;
  }
  virtual char do_narrow(char c, char) const { return c; }
  virtual const char *do_narrow(const char *lo, const char *hi, char, char *to) const {
    for (; lo != hi; ++lo, ++to)
      *to = *lo;
    return hi;
  }
  unsigned char storage[568];
};
static_assert(sizeof(CType) == 576, "ctype<char> layout");

CType facet;
unsigned short ctype_table[256];

struct Impl {
  int refcount;
  int pad;
  const void **facets;
  size_t facets_size;
  const void **caches;
  char **names;
};

const void *facet_slots[64];
const void *cache_slots[64];
char c_name[] = "C";
char *name_slots[6] = {c_name, c_name, c_name, c_name, c_name, c_name};
Impl impl;
alignas(std::locale) unsigned char classic_bytes[sizeof(std::locale)];
int classic_ready;

void init_classic() {
  if (classic_ready)
    return;
  classic_ready = 1;
  unsigned char *raw = reinterpret_cast<unsigned char *>(&facet);
  for (int c = 0; c < 256; ++c) {
    unsigned short m = 0;
    if (c >= 'A' && c <= 'Z')
      m = std::ctype_base::upper | std::ctype_base::alpha | std::ctype_base::alnum |
          std::ctype_base::graph | std::ctype_base::print |
          (c <= 'F' ? std::ctype_base::xdigit : 0);
    else if (c >= 'a' && c <= 'z')
      m = std::ctype_base::lower | std::ctype_base::alpha | std::ctype_base::alnum |
          std::ctype_base::graph | std::ctype_base::print |
          ((c <= 'f') ? std::ctype_base::xdigit : 0);
    else if (c >= '0' && c <= '9')
      m = std::ctype_base::digit | std::ctype_base::alnum | std::ctype_base::graph |
          std::ctype_base::print | std::ctype_base::xdigit;
    else if (c == ' ' || c == '\t')
      m = std::ctype_base::space | std::ctype_base::blank | std::ctype_base::print;
    else if (c == '\n' || c == '\r' || c == '\f' || c == '\v')
      m = std::ctype_base::space | std::ctype_base::cntrl;
    else if (c < 32 || c == 127)
      m = std::ctype_base::cntrl;
    else
      m = std::ctype_base::graph | std::ctype_base::print | std::ctype_base::punct;
    ctype_table[c] = m;
    raw[57 + c] = static_cast<unsigned char>(c); // _M_widen
    raw[313 + c] = static_cast<unsigned char>(c); // _M_narrow
  }
  raw[56] = 1;  // _M_widen_ok
  raw[569] = 1; // _M_narrow_ok
  *reinterpret_cast<const unsigned short **>(raw + 48) = ctype_table;
  size_t i = std::ctype<char>::id._M_id();
  if (i < 64)
    facet_slots[i] = &facet;
  impl.refcount = 1;
  impl.facets = facet_slots;
  impl.facets_size = 64;
  impl.caches = cache_slots;
  impl.names = name_slots;
  *reinterpret_cast<Impl **>(classic_bytes) = &impl;
}

} // namespace

namespace std {

locale::id ctype<char>::id;

const locale &locale::classic() {
  init_classic();
  return *reinterpret_cast<const locale *>(classic_bytes);
}

locale::locale() throw() {
  init_classic();
  _M_impl = reinterpret_cast<locale *>(classic_bytes)->_M_impl;
  if (_M_impl)
    _M_impl->_M_refcount++;
}

locale::locale(const locale &other) throw() : _M_impl(other._M_impl) {
  if (_M_impl)
    _M_impl->_M_refcount++;
}

locale::~locale() throw() {}

const locale &locale::operator=(const locale &other) throw() {
  if (this != &other) {
    if (other._M_impl)
      other._M_impl->_M_refcount++;
    _M_impl = other._M_impl;
  }
  return *this;
}

ios_base::ios_base() throw()
    : _M_precision(), _M_width(), _M_flags(), _M_exception(), _M_streambuf_state(),
      _M_callbacks(0), _M_word_zero(), _M_word_size(_S_local_word_size),
      _M_word(_M_local_word), _M_ios_locale() {}

ios_base::~ios_base() {
  _M_callbacks = 0;
}

void ios_base::_M_init() throw() {
  _M_precision = 6;
  _M_width = 0;
  _M_flags = skipws | dec;
  _M_exception = goodbit;
  _M_streambuf_state = badbit;
  _M_ios_locale = locale();
}

void ios_base::_M_call_callbacks(event) throw() {}

void ios_base::_M_dispose_callbacks() throw() { _M_callbacks = 0; }

locale ios_base::imbue(const locale &loc) throw() {
  locale old = _M_ios_locale;
  _M_ios_locale = loc;
  return old;
}

size_t locale::id::_M_id() const throw() {
  static size_t next;
  if (!_M_index)
    _M_index = ++next;
  return _M_index - 1;
}

} // namespace std

// std::use_facet<std::ctype<char>>(const std::locale&)
// The explicit instantiation in libstdc++ is what tolower(c, loc) calls.
extern "C" void *_ZSt9use_facetISt5ctypeIcEERKT_RKSt6locale(const void *) {
  init_classic();
  return &facet;
}

extern "C" bool _ZSt9has_facetISt5ctypeIcEEbRKSt6locale(const void *) {
  init_classic();
  return true;
}

// regex::use_facet<const ctype<char>> is a different symbol. The header
// body dynamic_casts to libstdc++'s ctype typeinfo, which is not in this
// address space.
extern "C" void *_ZSt9use_facetIKSt5ctypeIcEERKT_RKSt6locale(const void *) {
  init_classic();
  return &facet;
}

// Numeric facets are not part of this model. _M_cache_locale stores null
// and the string insertion path never dereferences them.
extern "C" bool
_ZSt9has_facetISt7num_putIcSt19ostreambuf_iteratorIcSt11char_traitsIcEEEEbRKSt6locale(
    const void *) {
  return false;
}

extern "C" bool
_ZSt9has_facetISt7num_getIcSt19istreambuf_iteratorIcSt11char_traitsIcEEEEbRKSt6locale(
    const void *) {
  return false;
}

namespace std::filesystem {

path::_List::_List()
    : _M_impl(reinterpret_cast<_Impl *>(static_cast<uintptr_t>(_Type::_Filename))) {}

void path::_List::_Impl_deleter::operator()(_Impl *p) const noexcept {
  // A type tag occupies the low bits and is not an allocation. This
  // environment never builds a multi-component list.
  (void)p;
}

void path::_List::clear() {}

void path::_List::type(_Type t) noexcept {
  auto val = reinterpret_cast<uintptr_t>(_M_impl.release());
  val &= ~uintptr_t{3};
  _M_impl.reset(reinterpret_cast<_Impl *>(val | static_cast<unsigned char>(t)));
}

void path::_M_split_cmpts() {
  _M_cmpts.clear();
  bool slash = false;
  bool other = false;
  for (char c : _M_pathname) {
    if (c == '/')
      slash = true;
    else
      other = true;
  }
  if (!other)
    _M_cmpts.type(slash ? _Type::_Root_dir : _Type::_Filename);
  else
    _M_cmpts.type(_Type::_Filename);
}

std::pair<const path::string_type *, std::size_t> path::_M_find_extension() const noexcept {
  const string_type *s = nullptr;
  if (_M_type() == _Type::_Filename)
    s = &_M_pathname;
  if (s && s->size()) {
    if (s->size() <= 2 && (*s)[0] == '.')
      return {s, string_type::npos};
    if (auto pos = s->rfind('.'))
      return {s, pos};
    return {s, string_type::npos};
  }
  return {};
}

namespace {
bool is_input(const path &p) {
  const auto &s = p.native();
  return s == "f" || s == "./f" || s == "/f" ||
         (s.size() >= 2 && s[s.size() - 1] == 'f' && s[s.size() - 2] == '/');
}
} // namespace

file_status status(const path &p, std::error_code &ec) noexcept {
  ec.clear();
  if (is_input(p))
    return file_status(file_type::regular, perms::owner_read | perms::owner_write);
  return file_status(file_type::not_found);
}

} // namespace std::filesystem

// Explicit instantiation definitions override the headers' extern template
// declarations, so the vtables and the iostream methods the harness calls
// are emitted here instead of taken from the host libstdc++.
template class std::basic_streambuf<char>;
template class std::basic_ios<char>;
template class std::basic_ostream<char>;
template class std::basic_stringbuf<char>;
template std::ostream &std::operator<<(std::ostream &, const std::string &);
template std::ostream &std::operator<<(std::ostream &, const char *);
template std::ostream &std::__ostream_insert(std::ostream &, const char *, std::streamsize);

template class std::basic_ostringstream<char>;
