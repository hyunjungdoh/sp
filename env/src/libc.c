// The rest of the C library for the closed program, under the same fixed
// environment as env.c. Each function follows its specification; where the
// environment decides the outcome (no network, no other process, no
// dynamic loading, a fixed clock) it returns one of the results the
// specification allows.
#define _GNU_SOURCE
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <locale.h>
#include <pwd.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/times.h>
#include <time.h>
#include <unistd.h>

void klee_silent_exit(int status);
long long klee_get_value_i64(long long expr);

// ---------------------------------------------------------------------------
// Standard streams: objects the stream functions do not own, so input is
// empty and output is discarded.

static char standard[3][16];
FILE *stdin = (FILE *)standard[0];
FILE *stdout = (FILE *)standard[1];
FILE *stderr = (FILE *)standard[2];
char *empty_environ[] = {NULL};
char **environ = empty_environ;
char __libc_single_threaded = 1;

int puts(const char *s) {
  (void)s;
  return 1;
}
void perror(const char *s) { (void)s; }

// ---------------------------------------------------------------------------
// Character classes of the "C" locale, in glibc's table layout: indexable
// from -128 to 255.

static unsigned short ctypeB[384];
static int32_t ctypeLower[384], ctypeUpper[384];
static const unsigned short *ctypeBp;
static const int32_t *ctypeLowerP, *ctypeUpperP;
static void ctypeInit(void) {
  if (ctypeBp)
    return;
  for (int c = -128; c < 256; ++c) {
    unsigned short m = 0;
    int u = c >= 'A' && c <= 'Z', l = c >= 'a' && c <= 'z', d = c >= '0' && c <= '9';
    int sp = c == ' ' || (c >= '\t' && c <= '\r');
    int pr = c >= 0x20 && c < 0x7f;
    int cn = (c >= 0 && c < 0x20) || c == 0x7f;
    if (u)
      m |= _ISupper;
    if (l)
      m |= _ISlower;
    if (u || l)
      m |= _ISalpha;
    if (d)
      m |= _ISdigit;
    if (d || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))
      m |= _ISxdigit;
    if (sp)
      m |= _ISspace;
    if (pr)
      m |= _ISprint;
    if (pr && c != ' ')
      m |= _ISgraph;
    if (c == ' ' || c == '\t')
      m |= _ISblank;
    if (cn)
      m |= _IScntrl;
    if (pr && c != ' ' && !u && !l && !d)
      m |= _ISpunct;
    if (u || l || d)
      m |= _ISalnum;
    ctypeB[c + 128] = m;
    ctypeLower[c + 128] = u ? c + 32 : c;
    ctypeUpper[c + 128] = l ? c - 32 : c;
  }
  ctypeBp = ctypeB + 128;
  ctypeLowerP = ctypeLower + 128;
  ctypeUpperP = ctypeUpper + 128;
}
const unsigned short **__ctype_b_loc(void) {
  ctypeInit();
  return &ctypeBp;
}
const int32_t **__ctype_tolower_loc(void) {
  ctypeInit();
  return &ctypeLowerP;
}
const int32_t **__ctype_toupper_loc(void) {
  ctypeInit();
  return &ctypeUpperP;
}

// ---------------------------------------------------------------------------
// Strings.

size_t strnlen(const char *s, size_t n) {
  size_t i = 0;
  while (i < n && s[i])
    ++i;
  return i;
}
char *strncat(char *d, const char *s, size_t n) {
  char *p = d + strlen(d);
  size_t i = 0;
  for (; i < n && s[i]; ++i)
    p[i] = s[i];
  p[i] = 0;
  return d;
}
// Case folding and case-insensitive comparison as values of the characters
// (§7): the first position where they differ or a ends decides the result,
// selected without branching on them. The scan stops at a concrete NUL of
// either string, and forks only where both characters are symbolic and
// whether it goes on is undecided.
unsigned klee_is_symbolic(unsigned long n);
static int fold(int c) { return c + 32 * ((unsigned)(c - 'A') < 26u); }
static int casecmp(const char *a, const char *b, size_t n) {
  const unsigned char *p = (const unsigned char *)a, *q = (const unsigned char *)b;
  int r = 0, live = 1;
  for (; n; --n, ++p, ++q) {
    unsigned char cx = *p, cy = *q;
    int x = fold(cx), y = fold(cy);
    int d = x - y;
    int stop = live & ((d != 0) | (x == 0));
    int m = -stop;
    r = (d & m) | (r & ~m);
    live = live & (stop == 0);
    if (!klee_is_symbolic(cx) && cx == 0)
      break;
    if (!klee_is_symbolic(cy) && cy == 0)
      break;
    if (!klee_is_symbolic(live) && !live)
      break;
    if (klee_is_symbolic(cx) && klee_is_symbolic(cy) && !live)
      break;
  }
  return r;
}
int strcasecmp(const char *a, const char *b) { return casecmp(a, b, (size_t)-1); }
int strncasecmp(const char *a, const char *b, size_t n) { return casecmp(a, b, n); }
char *strstr(const char *h, const char *n) {
  size_t m = strlen(n);
  for (; *h; ++h)
    if (!strncmp(h, n, m))
      return (char *)h;
  return m ? NULL : (char *)h;
}
char *strcasestr(const char *h, const char *n) {
  size_t m = strlen(n);
  for (; *h; ++h)
    if (!strncasecmp(h, n, m))
      return (char *)h;
  return m ? NULL : (char *)h;
}
size_t strspn(const char *s, const char *a) {
  size_t i = 0;
  while (s[i] && strchr(a, s[i]))
    ++i;
  return i;
}
size_t strcspn(const char *s, const char *r) {
  size_t i = 0;
  while (s[i] && !strchr(r, s[i]))
    ++i;
  return i;
}
char *strpbrk(const char *s, const char *a) {
  s += strcspn(s, a);
  return *s ? (char *)s : NULL;
}
char *strdup(const char *s) {
  size_t n = strlen(s) + 1;
  char *p = malloc(n);
  if (p)
    memcpy(p, s, n);
  return p;
}
char *strndup(const char *s, size_t n) {
  size_t m = strnlen(s, n);
  char *p = malloc(m + 1);
  if (p) {
    memcpy(p, s, m);
    p[m] = 0;
  }
  return p;
}
char *strtok_r(char *s, const char *d, char **save) {
  if (!s)
    s = *save;
  s += strspn(s, d);
  if (!*s) {
    *save = s;
    return NULL;
  }
  char *e = s + strcspn(s, d);
  if (*e)
    *e++ = 0;
  *save = e;
  return s;
}
static char *tokSave;
char *strtok(char *s, const char *d) { return strtok_r(s, d, &tokSave); }
char *strsep(char **sp, const char *d) {
  char *s = *sp;
  if (!s)
    return NULL;
  char *e = s + strcspn(s, d);
  if (*e) {
    *e = 0;
    *sp = e + 1;
  } else
    *sp = NULL;
  return s;
}
void *memrchr(const void *s, int c, size_t n) {
  const unsigned char *p = s;
  while (n--)
    if (p[n] == (unsigned char)c)
      return (void *)(p + n);
  return NULL;
}
char *strerror(int e) {
  (void)e;
  return "error";
}
char *strerror_r(int e, char *buf, size_t n) {
  (void)e, (void)buf, (void)n;
  return "error";
}
int __xpg_strerror_r(int e, char *buf, size_t n) {
  (void)e;
  if (n)
    strncpy(buf, "error", n - 1), buf[n - 1] = 0;
  return 0;
}

// ---------------------------------------------------------------------------
// Numbers.

int abs(int x) { return x < 0 ? -x : x; }
long labs(long x) { return x < 0 ? -x : x; }
long long llabs(long long x) { return x < 0 ? -x : x; }
div_t div(int a, int b) { return (div_t){a / b, a % b}; }
ldiv_t ldiv(long a, long b) { return (ldiv_t){a / b, a % b}; }

static int digitOf(int c) {
  if (c >= '0' && c <= '9')
    return c - '0';
  if (c >= 'a' && c <= 'z')
    return c - 'a' + 10;
  if (c >= 'A' && c <= 'Z')
    return c - 'A' + 10;
  return 99;
}
static unsigned long long scanUnsigned(const char *s, char **end, int base, int *neg, int *any) {
  const char *p = s;
  while (*p == ' ' || (*p >= '\t' && *p <= '\r'))
    ++p;
  *neg = 0;
  if (*p == '+' || *p == '-')
    *neg = *p++ == '-';
  if ((base == 0 || base == 16) && p[0] == '0' && (p[1] == 'x' || p[1] == 'X') && digitOf(p[2]) < 16) {
    p += 2;
    base = 16;
  } else if (base == 0)
    base = p[0] == '0' ? 8 : 10;
  unsigned long long v = 0;
  *any = 0;
  for (int d; (d = digitOf((unsigned char)*p)) < base; ++p) {
    v = v * base + d;
    *any = 1;
  }
  if (end)
    *end = (char *)(*any ? p : s);
  return v;
}
long long strtoll(const char *s, char **end, int base) {
  int neg, any;
  unsigned long long v = scanUnsigned(s, end, base, &neg, &any);
  return neg ? -(long long)v : (long long)v;
}
unsigned long long strtoull(const char *s, char **end, int base) {
  int neg, any;
  unsigned long long v = scanUnsigned(s, end, base, &neg, &any);
  return neg ? -v : v;
}
long long atoll(const char *s) { return strtoll(s, NULL, 10); }
long atol(const char *s) { return (long)strtoll(s, NULL, 10); }
intmax_t strtoimax(const char *s, char **end, int base) { return strtoll(s, end, base); }
uintmax_t strtoumax(const char *s, char **end, int base) { return strtoull(s, end, base); }

long double strtold(const char *s, char **end) {
  const char *p = s;
  while (*p == ' ' || (*p >= '\t' && *p <= '\r'))
    ++p;
  int neg = 0;
  if (*p == '+' || *p == '-')
    neg = *p++ == '-';
  if (!strncasecmp(p, "inf", 3)) {
    p += strncasecmp(p, "infinity", 8) ? 3 : 8;
    if (end)
      *end = (char *)p;
    return neg ? -__builtin_infl() : __builtin_infl();
  }
  if (!strncasecmp(p, "nan", 3)) {
    if (end)
      *end = (char *)(p + 3);
    return __builtin_nanl("");
  }
  long double v = 0;
  int any = 0, exp10 = 0;
  if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X') && (digitOf((unsigned char)p[2]) < 16 || p[2] == '.')) {
    const char *q = p + 2;
    int exp2 = 0;
    for (; digitOf((unsigned char)*q) < 16; ++q, any = 1)
      v = v * 16 + digitOf((unsigned char)*q);
    if (*q == '.')
      for (++q; digitOf((unsigned char)*q) < 16; ++q, any = 1) {
        v = v * 16 + digitOf((unsigned char)*q);
        exp2 -= 4;
      }
    if (!any) {
      if (end)
        *end = (char *)(p + 1);
      return 0;
    }
    if (*q == 'p' || *q == 'P') {
      const char *r = q + 1;
      int en = 0;
      if (*r == '+' || *r == '-')
        en = *r++ == '-';
      if (*r >= '0' && *r <= '9') {
        int e = 0;
        for (; *r >= '0' && *r <= '9'; ++r)
          if (e < 100000)
            e = e * 10 + (*r - '0');
        exp2 += en ? -e : e;
        q = r;
      }
    }
    for (; exp2 > 0 && v != 0; --exp2)
      v *= 2;
    for (; exp2 < 0 && v != 0; ++exp2)
      v /= 2;
    if (end)
      *end = (char *)q;
    return neg ? -v : v;
  }
  for (; *p >= '0' && *p <= '9'; ++p, any = 1)
    v = v * 10 + (*p - '0');
  if (*p == '.')
    for (++p; *p >= '0' && *p <= '9'; ++p, any = 1) {
      v = v * 10 + (*p - '0');
      --exp10;
    }
  if (!any) {
    if (end)
      *end = (char *)s;
    return 0;
  }
  if (*p == 'e' || *p == 'E') {
    const char *q = p + 1;
    int en = 0;
    if (*q == '+' || *q == '-')
      en = *q++ == '-';
    if (*q >= '0' && *q <= '9') {
      int e = 0;
      for (; *q >= '0' && *q <= '9'; ++q)
        if (e < 100000)
          e = e * 10 + (*q - '0');
      exp10 += en ? -e : e;
      p = q;
    }
  }
  for (; exp10 > 0 && v != 0; --exp10) {
    v *= 10;
    if (v > 1e4900L) {
      v = __builtin_infl();
      errno = ERANGE;
      break;
    }
  }
  for (; exp10 < 0 && v != 0; ++exp10)
    v /= 10;
  if (end)
    *end = (char *)p;
  return neg ? -v : v;
}
double strtod(const char *s, char **end) { return (double)strtold(s, end); }
float strtof(const char *s, char **end) { return (float)strtold(s, end); }
double atof(const char *s) { return strtod(s, NULL); }

static unsigned long randState = 1;
int rand(void) {
  randState = randState * 1103515245 + 12345;
  return (int)((randState / 65536) % 32768);
}
void srand(unsigned s) { randState = s; }
int rand_r(unsigned *s) {
  *s = *s * 1103515245 + 12345;
  return (int)((*s / 65536) % 32768);
}
long random(void) { return rand(); }
void srandom(unsigned s) { srand(s); }

// ---------------------------------------------------------------------------
// Formatted output.

struct sink {
  char *buf;
  size_t cap, len;
};
static void put(struct sink *o, char c) {
  if (o->len + 1 < o->cap)
    o->buf[o->len] = c;
  ++o->len;
}
static void pad(struct sink *o, char c, int n) {
  while (n-- > 0)
    put(o, c);
}
static void emit(struct sink *o, const char *pre, const char *body, size_t n, int width, int left, int zero) {
  size_t pl = strlen(pre);
  int fill = width - (int)(pl + n);
  if (!left && !zero)
    pad(o, ' ', fill);
  for (size_t i = 0; i < pl; ++i)
    put(o, pre[i]);
  if (!left && zero)
    pad(o, '0', fill);
  for (size_t i = 0; i < n; ++i)
    put(o, body[i]);
  if (left)
    pad(o, ' ', fill);
}
// The digits are output only: they are written for one value v can take, and
// the path is not narrowed to it.
static int digits(char *out, unsigned long long v, int base, int upper) {
  const char *d = upper ? "0123456789ABCDEF" : "0123456789abcdef";
  char t[72];
  int n = 0;
  v = (unsigned long long)klee_get_value_i64((long long)v);
  do
    t[n++] = d[v % base];
  while (v /= base);
  for (int i = 0; i < n; ++i)
    out[i] = t[n - 1 - i];
  return n;
}
// The decimal digits of v >= 0 with prec digits after the point, rounded.
static int fixed(char *out, long double v, int prec, int dot) {
  if (prec > 30)
    prec = 30;
  long double scale = 1;
  for (int i = 0; i < prec; ++i)
    scale *= 10;
  int n = 0;
  if (v >= 1e18L) {
    int e = 0;
    while (v >= 1e18L) {
      v /= 10;
      ++e;
    }
    unsigned long long ip = (unsigned long long)(v + 0.5L);
    n = digits(out, ip, 10, 0);
    for (int i = 0; i < e; ++i)
      out[n++] = '0';
    if (prec || dot)
      out[n++] = '.';
    for (int i = 0; i < prec; ++i)
      out[n++] = '0';
    return n;
  }
  unsigned long long ip = (unsigned long long)v;
  long double fp = (v - (long double)ip) * scale;
  unsigned long long f = (unsigned long long)fp;
  long double rem = fp - (long double)f;
  // Round to nearest, ties to even.
  unsigned long long last = prec ? f : ip;
  if (rem > 0.5L || (rem == 0.5L && (last & 1)))
    ++f;
  if ((long double)f >= scale) {
    f -= (unsigned long long)scale;
    ++ip;
  }
  n = digits(out, ip, 10, 0);
  if (prec || dot) {
    out[n++] = '.';
    char t[40];
    int m = digits(t, f, 10, 0);
    for (int i = m; i < prec; ++i)
      out[n++] = '0';
    for (int i = 0; i < m && prec; ++i)
      out[n++] = t[i];
  }
  return n;
}
// v > 0 normalized to [1, 10) and its decimal exponent.
static long double normal(long double v, int *e) {
  *e = 0;
  while (v >= 10) {
    v /= 10;
    ++*e;
  }
  while (v > 0 && v < 1) {
    v *= 10;
    --*e;
  }
  return v;
}
static int expo(char *out, long double v, int prec, int dot, int upper) {
  int e = 0;
  long double m = v > 0 ? normal(v, &e) : 0;
  int n = fixed(out, m, prec, dot);
  if (out[0] == '1' && out[1] == '0' && (n == 2 || out[2] == '.')) {
    m /= 10;
    ++e;
    n = fixed(out, m, prec, dot);
  }
  out[n++] = upper ? 'E' : 'e';
  out[n++] = e < 0 ? '-' : '+';
  if (e < 0)
    e = -e;
  if (e < 10)
    out[n++] = '0';
  n += digits(out + n, (unsigned)e, 10, 0);
  return n;
}
static int general(char *out, long double v, int prec, int alt, int upper) {
  int P = prec == 0 ? 1 : prec, X = 0;
  if (v > 0)
    normal(v, &X);
  char t[128];
  int n;
  if (P > X && X >= -4) {
    n = fixed(t, v, P - 1 - X, alt);
  } else
    n = expo(t, v, P - 1, alt, upper);
  if (!alt) {
    char *ep = memchr(t, upper ? 'E' : 'e', n);
    int mant = ep ? (int)(ep - t) : n;
    if (memchr(t, '.', mant)) {
      int k = mant;
      while (k > 0 && t[k - 1] == '0')
        --k;
      if (k > 0 && t[k - 1] == '.')
        --k;
      memmove(t + k, t + mant, n - mant);
      n -= mant - k;
    }
  }
  memcpy(out, t, n);
  return n;
}

int vsnprintf(char *buf, size_t cap, const char *f, va_list ap) {
  struct sink o = {buf, cap, 0};
  for (; *f; ++f) {
    if (*f != '%') {
      put(&o, *f);
      continue;
    }
    ++f;
    int left = 0, plus = 0, space = 0, alt = 0, zero = 0;
    for (;; ++f) {
      if (*f == '-')
        left = 1;
      else if (*f == '+')
        plus = 1;
      else if (*f == ' ')
        space = 1;
      else if (*f == '#')
        alt = 1;
      else if (*f == '0')
        zero = 1;
      else
        break;
    }
    int width = 0, prec = -1;
    if (*f == '*') {
      width = va_arg(ap, int);
      if (width < 0)
        left = 1, width = -width;
      ++f;
    } else
      while (*f >= '0' && *f <= '9')
        width = width * 10 + (*f++ - '0');
    if (*f == '.') {
      ++f;
      prec = 0;
      if (*f == '*') {
        prec = va_arg(ap, int);
        ++f;
      } else
        while (*f >= '0' && *f <= '9')
          prec = prec * 10 + (*f++ - '0');
    }
    int len = 0;
    for (;; ++f) {
      if (*f == 'h')
        len = len == -1 ? -2 : -1;
      else if (*f == 'l')
        len = len == 1 ? 2 : 1;
      else if (*f == 'q' || *f == 'j' || *f == 'z' || *f == 't')
        len = 2;
      else if (*f == 'L')
        len = 3;
      else
        break;
    }
    char body[512];
    int n = 0;
    char pre[4] = "";
    char c = *f;
    if (!c)
      break;
    switch (c) {
    case 'd':
    case 'i': {
      long long v = len >= 2 ? va_arg(ap, long long) : len == 1 ? va_arg(ap, long) : va_arg(ap, int);
      if (len == -1)
        v = (short)v;
      else if (len == -2)
        v = (signed char)v;
      unsigned long long u = v < 0 ? -(unsigned long long)v : (unsigned long long)v;
      strcpy(pre, v < 0 ? "-" : plus ? "+" : space ? " " : "");
      n = prec == 0 && u == 0 ? 0 : digits(body, u, 10, 0);
      if (prec > n) {
        memmove(body + (prec - n), body, n);
        memset(body, '0', prec - n);
        n = prec;
      }
      emit(&o, pre, body, n, width, left, zero && prec < 0);
      break;
    }
    case 'u':
    case 'x':
    case 'X':
    case 'o': {
      unsigned long long u = len >= 2   ? va_arg(ap, unsigned long long)
                             : len == 1 ? va_arg(ap, unsigned long)
                                        : va_arg(ap, unsigned);
      if (len == -1)
        u = (unsigned short)u;
      else if (len == -2)
        u = (unsigned char)u;
      int base = c == 'o' ? 8 : c == 'u' ? 10 : 16;
      n = prec == 0 && u == 0 ? 0 : digits(body, u, base, c == 'X');
      if (prec > n) {
        memmove(body + (prec - n), body, n);
        memset(body, '0', prec - n);
        n = prec;
      }
      if (alt && u && base == 16)
        strcpy(pre, c == 'X' ? "0X" : "0x");
      else if (alt && base == 8 && (n == 0 || body[0] != '0'))
        strcpy(pre, "0");
      emit(&o, pre, body, n, width, left, zero && prec < 0);
      break;
    }
    case 'p': {
      void *p = va_arg(ap, void *);
      strcpy(pre, "0x");
      n = digits(body, (uintptr_t)p, 16, 0);
      emit(&o, pre, body, n, width, left, 0);
      break;
    }
    case 'c':
      body[0] = (char)va_arg(ap, int);
      emit(&o, "", body, 1, width, left, 0);
      break;
    case 's': {
      const char *s = va_arg(ap, const char *);
      if (!s)
        s = "(null)";
      size_t m = prec >= 0 ? strnlen(s, (size_t)prec) : strlen(s);
      emit(&o, "", s, m, width, left, 0);
      break;
    }
    case 'f':
    case 'F':
    case 'e':
    case 'E':
    case 'g':
    case 'G':
    case 'a':
    case 'A': {
      long double v = len == 3 ? va_arg(ap, long double) : va_arg(ap, double);
      int neg = __builtin_signbit(v);
      if (neg)
        v = -v;
      strcpy(pre, neg ? "-" : plus ? "+" : space ? " " : "");
      int upper = c == 'F' || c == 'E' || c == 'G' || c == 'A';
      if (v != v || v - v != 0) {
        const char *w = v != v ? (upper ? "NAN" : "nan") : (upper ? "INF" : "inf");
        emit(&o, pre, w, 3, width, left, 0);
        break;
      }
      if (prec < 0)
        prec = 6;
      if (c == 'f' || c == 'F')
        n = fixed(body, v, prec, alt);
      else if (c == 'g' || c == 'G')
        n = general(body, v, prec, alt, upper);
      else
        n = expo(body, v, prec, alt, upper);
      emit(&o, pre, body, n, width, left, zero);
      break;
    }
    case 'n': {
      int *p = va_arg(ap, int *);
      *p = (int)o.len;
      break;
    }
    case '%':
      put(&o, '%');
      break;
    default:
      put(&o, '%');
      put(&o, c);
    }
  }
  if (cap)
    buf[o.len < cap ? o.len : cap - 1] = 0;
  return (int)o.len;
}
int snprintf(char *buf, size_t cap, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vsnprintf(buf, cap, f, ap);
  va_end(ap);
  return n;
}
int vsprintf(char *buf, const char *f, va_list ap) { return vsnprintf(buf, (size_t)INT_MAX, f, ap); }
int sprintf(char *buf, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vsprintf(buf, f, ap);
  va_end(ap);
  return n;
}
int vasprintf(char **out, const char *f, va_list ap) {
  va_list aq;
  va_copy(aq, ap);
  int n = vsnprintf(NULL, 0, f, aq);
  va_end(aq);
  *out = malloc((size_t)n + 1);
  if (!*out)
    return -1;
  return vsnprintf(*out, (size_t)n + 1, f, ap);
}
int asprintf(char **out, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vasprintf(out, f, ap);
  va_end(ap);
  return n;
}
int vprintf(const char *f, va_list ap) { return vsnprintf(NULL, 0, f, ap); }
int printf(const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vprintf(f, ap);
  va_end(ap);
  return n;
}
int vdprintf(int fd, const char *f, va_list ap) {
  char buf[1024];
  int n = vsnprintf(buf, sizeof buf, f, ap);
  if (n > 0)
    write(fd, buf, (size_t)n < sizeof buf ? (size_t)n : sizeof buf - 1);
  return n;
}
int dprintf(int fd, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vdprintf(fd, f, ap);
  va_end(ap);
  return n;
}
int __vsnprintf_chk(char *b, size_t c, int fl, size_t bl, const char *f, va_list ap) {
  (void)fl, (void)bl;
  return vsnprintf(b, c, f, ap);
}
int __snprintf_chk(char *b, size_t c, int fl, size_t bl, const char *f, ...) {
  (void)fl, (void)bl;
  va_list ap;
  va_start(ap, f);
  int n = vsnprintf(b, c, f, ap);
  va_end(ap);
  return n;
}
int __vsprintf_chk(char *b, int fl, size_t bl, const char *f, va_list ap) {
  (void)fl;
  return vsnprintf(b, bl, f, ap);
}
int __sprintf_chk(char *b, int fl, size_t bl, const char *f, ...) {
  (void)fl;
  va_list ap;
  va_start(ap, f);
  int n = vsnprintf(b, bl, f, ap);
  va_end(ap);
  return n;
}
int __printf_chk(int fl, const char *f, ...) {
  (void)fl;
  va_list ap;
  va_start(ap, f);
  int n = vprintf(f, ap);
  va_end(ap);
  return n;
}
int __vfprintf_chk(FILE *fp, int fl, const char *f, va_list ap) {
  (void)fl;
  return vfprintf(fp, f, ap);
}
int __fprintf_chk(FILE *fp, int fl, const char *f, ...) {
  (void)fl;
  va_list ap;
  va_start(ap, f);
  int n = vfprintf(fp, f, ap);
  va_end(ap);
  return n;
}

// ---------------------------------------------------------------------------
// Formatted input from a string.

int vsscanf(const char *s, const char *f, va_list ap) {
  const char *p = s;
  int count = 0, any = 0;
  for (; *f; ++f) {
    if (*f == ' ' || (*f >= '\t' && *f <= '\r')) {
      while (*p == ' ' || (*p >= '\t' && *p <= '\r'))
        ++p;
      continue;
    }
    if (*f != '%' || f[1] == '%') {
      if (*f == '%')
        ++f;
      if (*p != *f)
        break;
      ++p;
      continue;
    }
    ++f;
    int skip = 0, width = 0, len = 0;
    if (*f == '*')
      skip = 1, ++f;
    while (*f >= '0' && *f <= '9')
      width = width * 10 + (*f++ - '0');
    for (;; ++f) {
      if (*f == 'h')
        len = len == -1 ? -2 : -1;
      else if (*f == 'l')
        len = len == 1 ? 2 : 1;
      else if (*f == 'L' || *f == 'q' || *f == 'j' || *f == 'z' || *f == 't')
        len = *f == 'L' ? 3 : 2;
      else
        break;
    }
    char c = *f;
    if (c == 'n') {
      if (!skip)
        *va_arg(ap, int *) = (int)(p - s);
      continue;
    }
    if (c != 'c' && c != '[')
      while (*p == ' ' || (*p >= '\t' && *p <= '\r'))
        ++p;
    if (!*p)
      return any ? count : EOF;
    char tmp[128];
    size_t lim = width ? (size_t)width : sizeof tmp - 1;
    if (lim > sizeof tmp - 1)
      lim = sizeof tmp - 1;
    if (c == 'd' || c == 'i' || c == 'u' || c == 'x' || c == 'X' || c == 'o') {
      size_t m = 0;
      while (p[m] && m < lim && !(p[m] == ' ' || (p[m] >= '\t' && p[m] <= '\r')))
        tmp[m] = p[m], ++m;
      tmp[m] = 0;
      char *e;
      int base = c == 'd' || c == 'u' ? 10 : c == 'i' ? 0 : c == 'o' ? 8 : 16;
      long long v = c == 'd' || c == 'i' ? strtoll(tmp, &e, base) : (long long)strtoull(tmp, &e, base);
      if (e == tmp)
        break;
      p += e - tmp;
      any = 1;
      if (skip)
        continue;
      void *dst = va_arg(ap, void *);
      if (len >= 2)
        *(long long *)dst = v;
      else if (len == 1)
        *(long *)dst = (long)v;
      else if (len == -1)
        *(short *)dst = (short)v;
      else if (len == -2)
        *(char *)dst = (char)v;
      else
        *(int *)dst = (int)v;
      ++count;
    } else if (c == 'f' || c == 'e' || c == 'g' || c == 'E' || c == 'G' || c == 'a') {
      size_t m = 0;
      while (p[m] && m < lim && !(p[m] == ' ' || (p[m] >= '\t' && p[m] <= '\r')))
        tmp[m] = p[m], ++m;
      tmp[m] = 0;
      char *e;
      long double v = strtold(tmp, &e);
      if (e == tmp)
        break;
      p += e - tmp;
      any = 1;
      if (skip)
        continue;
      void *dst = va_arg(ap, void *);
      if (len == 3)
        *(long double *)dst = v;
      else if (len == 1)
        *(double *)dst = (double)v;
      else
        *(float *)dst = (float)v;
      ++count;
    } else if (c == 's') {
      char *dst = skip ? NULL : va_arg(ap, char *);
      size_t m = 0, w = width ? (size_t)width : (size_t)-1;
      while (p[m] && m < w && !(p[m] == ' ' || (p[m] >= '\t' && p[m] <= '\r'))) {
        if (dst)
          dst[m] = p[m];
        ++m;
      }
      if (dst)
        dst[m] = 0;
      p += m;
      any = 1;
      if (dst)
        ++count;
    } else if (c == 'c') {
      char *dst = skip ? NULL : va_arg(ap, char *);
      size_t w = width ? (size_t)width : 1;
      for (size_t m = 0; m < w; ++m) {
        if (!p[m])
          return any ? count : EOF;
        if (dst)
          dst[m] = p[m];
      }
      p += w;
      any = 1;
      if (dst)
        ++count;
    } else if (c == '[') {
      ++f;
      int neg = *f == '^';
      if (neg)
        ++f;
      const char *set = f;
      if (*f == ']')
        ++f;
      while (*f && *f != ']')
        ++f;
      size_t setLen = (size_t)(f - set);
      char *dst = skip ? NULL : va_arg(ap, char *);
      size_t m = 0, w = width ? (size_t)width : (size_t)-1;
      while (p[m] && m < w) {
        int in = memchr(set, p[m], setLen) != NULL;
        if (in == neg)
          break;
        if (dst)
          dst[m] = p[m];
        ++m;
      }
      if (!m)
        break;
      if (dst)
        dst[m] = 0;
      p += m;
      any = 1;
      if (dst)
        ++count;
    } else
      break;
  }
  return count;
}
// The headers name these __isoc99_vsscanf and __isoc99_sscanf; programs
// built otherwise call the plain names.
int sscanf(const char *s, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vsscanf(s, f, ap);
  va_end(ap);
  return n;
}
int plainVsscanf(const char *s, const char *f, va_list ap) __asm__("vsscanf");
int plainVsscanf(const char *s, const char *f, va_list ap) { return vsscanf(s, f, ap); }
int plainSscanf(const char *s, const char *f, ...) __asm__("sscanf");
int plainSscanf(const char *s, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int n = vsscanf(s, f, ap);
  va_end(ap);
  return n;
}

// ---------------------------------------------------------------------------
// Math with an out-parameter.

double frexp(double x, int *e) {
  *e = 0;
  if (x == 0 || x != x || x - x != 0)
    return x;
  double a = x < 0 ? -x : x;
  while (a >= 1) {
    a /= 2;
    ++*e;
  }
  while (a < 0.5) {
    a *= 2;
    --*e;
  }
  return x < 0 ? -a : a;
}
float frexpf(float x, int *e) { return (float)frexp(x, e); }
double modf(double x, double *ip) {
  double i = (double)(long long)x;
  if (x >= 9.2e18 || x <= -9.2e18)
    i = x;
  *ip = i;
  return x - i;
}
float modff(float x, float *ip) {
  double i;
  double r = modf(x, &i);
  *ip = (float)i;
  return (float)r;
}

// ---------------------------------------------------------------------------
// Time: the clock stands at a fixed instant, the epoch, in UTC.

time_t time(time_t *t) {
  if (t)
    *t = 0;
  return 0;
}
int clock_gettime(clockid_t c, struct timespec *ts) {
  (void)c;
  ts->tv_sec = 0;
  ts->tv_nsec = 0;
  return 0;
}
int gettimeofday(struct timeval *tv, void *tz) {
  (void)tz;
  if (tv)
    tv->tv_sec = 0, tv->tv_usec = 0;
  return 0;
}
clock_t clock(void) { return 0; }
clock_t times(struct tms *t) {
  if (t)
    memset(t, 0, sizeof *t);
  return 0;
}
int getrusage(int who, struct rusage *u) {
  (void)who;
  memset(u, 0, sizeof *u);
  return 0;
}
int nanosleep(const struct timespec *a, struct timespec *b) {
  (void)a;
  if (b)
    b->tv_sec = 0, b->tv_nsec = 0;
  return 0;
}
unsigned sleep(unsigned s) {
  (void)s;
  return 0;
}
int usleep(unsigned u) {
  (void)u;
  return 0;
}

static int leap(long y) { return (y % 4 == 0 && y % 100 != 0) || y % 400 == 0; }
struct tm *gmtime_r(const time_t *t, struct tm *r) {
  long long s = *t, days = s / 86400, rem = s % 86400;
  if (rem < 0)
    rem += 86400, --days;
  memset(r, 0, sizeof *r);
  r->tm_hour = (int)(rem / 3600);
  r->tm_min = (int)(rem % 3600 / 60);
  r->tm_sec = (int)(rem % 60);
  r->tm_wday = (int)((4 + days % 7 + 7) % 7);
  long y = 1970;
  for (;;) {
    long n = leap(y) ? 366 : 365;
    if (days >= n)
      days -= n, ++y;
    else if (days < 0)
      --y, days += leap(y) ? 366 : 365;
    else
      break;
  }
  r->tm_year = (int)(y - 1900);
  r->tm_yday = (int)days;
  static const int md[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
  int m = 0;
  while (m < 12) {
    int n = md[m] + (m == 1 && leap(y));
    if (days < n)
      break;
    days -= n;
    ++m;
  }
  r->tm_mon = m;
  r->tm_mday = (int)days + 1;
  return r;
}
struct tm *localtime_r(const time_t *t, struct tm *r) { return gmtime_r(t, r); }
static struct tm tmStatic;
struct tm *gmtime(const time_t *t) { return gmtime_r(t, &tmStatic); }
struct tm *localtime(const time_t *t) { return gmtime_r(t, &tmStatic); }
time_t timegm(struct tm *tm) {
  long y = tm->tm_year + 1900L;
  long long days = 0;
  for (long k = 1970; k < y; ++k)
    days += leap(k) ? 366 : 365;
  for (long k = y; k < 1970; ++k)
    days -= leap(k) ? 366 : 365;
  static const int md[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
  for (int m = 0; m < tm->tm_mon && m < 12; ++m)
    days += md[m] + (m == 1 && leap(y));
  days += tm->tm_mday - 1;
  return (time_t)(days * 86400 + tm->tm_hour * 3600L + tm->tm_min * 60L + tm->tm_sec);
}
time_t mktime(struct tm *tm) { return timegm(tm); }
size_t strftime(char *s, size_t max, const char *f, const struct tm *tm) {
  size_t n = 0;
  char t[64];
  for (; *f; ++f) {
    const char *add = t;
    t[0] = 0;
    if (*f != '%') {
      t[0] = *f, t[1] = 0;
    } else {
      switch (*++f) {
      case 'Y':
        snprintf(t, sizeof t, "%d", tm->tm_year + 1900);
        break;
      case 'm':
        snprintf(t, sizeof t, "%02d", tm->tm_mon + 1);
        break;
      case 'd':
        snprintf(t, sizeof t, "%02d", tm->tm_mday);
        break;
      case 'H':
        snprintf(t, sizeof t, "%02d", tm->tm_hour);
        break;
      case 'M':
        snprintf(t, sizeof t, "%02d", tm->tm_min);
        break;
      case 'S':
        snprintf(t, sizeof t, "%02d", tm->tm_sec);
        break;
      case 'z':
        add = "+0000";
        break;
      case 'Z':
        add = "UTC";
        break;
      case '%':
        add = "%";
        break;
      case 0:
        --f;
        break;
      default:
        snprintf(t, sizeof t, "%%%c", *f);
      }
    }
    size_t m = strlen(add);
    if (n + m >= max)
      return 0;
    memcpy(s + n, add, m);
    n += m;
  }
  if (n < max)
    s[n] = 0;
  return n;
}
char *ctime(const time_t *t) {
  static char buf[32];
  struct tm r;
  gmtime_r(t, &r);
  strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S\n", &r);
  return buf;
}

// ---------------------------------------------------------------------------
// The process: no signal arrives, no other process or library can be
// started, no network is reachable, one thread runs.

typedef void (*handler)(int);
handler signal(int s, handler h) {
  (void)s, (void)h;
  return NULL;
}
int sigaction(int s, const void *a, void *o) {
  (void)s, (void)a;
  if (o)
    memset(o, 0, 152);
  return 0;
}
int sigemptyset(void *set) {
  memset(set, 0, 128);
  return 0;
}
int sigfillset(void *set) {
  memset(set, 0xff, 128);
  return 0;
}
int sigaddset(void *set, int s) {
  (void)set, (void)s;
  return 0;
}
int sigdelset(void *set, int s) {
  (void)set, (void)s;
  return 0;
}
int sigprocmask(int how, const void *set, void *old) {
  (void)how, (void)set;
  if (old)
    memset(old, 0, 128);
  return 0;
}
int pthread_sigmask(int how, const void *set, void *old) { return sigprocmask(how, set, old); }
int raise(int s) {
  (void)s;
  klee_silent_exit(0);
  return 0;
}
pid_t getpid(void) { return 1; }
pid_t getppid(void) { return 0; }
uid_t getuid(void) { return 1000; }
uid_t geteuid(void) { return 1000; }
gid_t getgid(void) { return 1000; }
gid_t getegid(void) { return 1000; }
// No user database: the file system holds only the input file. A lookup
// that finds no entry returns 0 and stores NULL in *result.
int getpwnam_r(const char *name, struct passwd *pwd, char *buf, size_t len, struct passwd **result) {
  (void)name, (void)pwd, (void)buf, (void)len;
  *result = NULL;
  return 0;
}
int getpwuid_r(uid_t uid, struct passwd *pwd, char *buf, size_t len, struct passwd **result) {
  (void)uid, (void)pwd, (void)buf, (void)len;
  *result = NULL;
  return 0;
}
struct passwd *getpwnam(const char *name) {
  (void)name;
  return NULL;
}
struct passwd *getpwuid(uid_t uid) {
  (void)uid;
  return NULL;
}

void *memalign(size_t align, size_t size);
int posix_memalign(void **p, size_t align, size_t size) {
  if (align < sizeof(void *) || (align & (align - 1)))
    return EINVAL;
  void *m = memalign(align, size);
  if (!m)
    return ENOMEM;
  *p = m;
  return 0;
}

// The only locale is "C": the _l variants are the plain conversions.
long strtol_l(const char *s, char **end, int base, locale_t l) {
  (void)l;
  return strtol(s, end, base);
}
unsigned long strtoul_l(const char *s, char **end, int base, locale_t l) {
  (void)l;
  return strtoul(s, end, base);
}
long long strtoll_l(const char *s, char **end, int base, locale_t l) {
  (void)l;
  return strtoll(s, end, base);
}
unsigned long long strtoull_l(const char *s, char **end, int base, locale_t l) {
  (void)l;
  return strtoull(s, end, base);
}
int getrlimit(__rlimit_resource_t r, struct rlimit *l) {
  (void)r;
  l->rlim_cur = l->rlim_max = RLIM_INFINITY;
  return 0;
}
int setrlimit(__rlimit_resource_t r, const struct rlimit *l) {
  (void)r, (void)l;
  return 0;
}
int getdtablesize(void) { return 1024; }
int getloadavg(double *a, int n) {
  for (int i = 0; i < n; ++i)
    a[i] = 0;
  return n;
}
int getentropy(void *b, size_t n) {
  memset(b, 0, n);
  return 0;
}
pid_t fork(void) {
  errno = EAGAIN;
  return -1;
}
int execvp(const char *f, char *const argv[]) {
  (void)f, (void)argv;
  errno = ENOENT;
  return -1;
}
int execv(const char *f, char *const argv[]) { return execvp(f, argv); }
pid_t waitpid(pid_t p, int *st, int o) {
  (void)p, (void)st, (void)o;
  errno = ECHILD;
  return -1;
}
void *dlopen(const char *f, int m) {
  (void)f, (void)m;
  return NULL;
}
void *dlsym(void *h, const char *s) {
  (void)h, (void)s;
  return NULL;
}
int dlclose(void *h) {
  (void)h;
  return 0;
}
char *dlerror(void) { return "dynamic loading is unavailable"; }
int socket(int d, int t, int p) {
  (void)d, (void)t, (void)p;
  errno = EACCES;
  return -1;
}
int connect(int s, const void *a, unsigned l) {
  (void)s, (void)a, (void)l;
  errno = ENETUNREACH;
  return -1;
}
int bind(int s, const void *a, unsigned l) {
  (void)s, (void)a, (void)l;
  errno = EACCES;
  return -1;
}
int listen(int s, int b) {
  (void)s, (void)b;
  errno = EBADF;
  return -1;
}
int accept(int s, void *a, void *l) {
  (void)s, (void)a, (void)l;
  errno = EBADF;
  return -1;
}
ssize_t send(int s, const void *b, size_t n, int f) {
  (void)s, (void)b, (void)n, (void)f;
  errno = EBADF;
  return -1;
}
ssize_t recv(int s, void *b, size_t n, int f) {
  (void)s, (void)b, (void)n, (void)f;
  errno = EBADF;
  return -1;
}
int setsockopt(int s, int l, int o, const void *v, unsigned n) {
  (void)s, (void)l, (void)o, (void)v, (void)n;
  errno = EBADF;
  return -1;
}
int getaddrinfo(const char *n, const char *s, const void *h, void **r) {
  (void)n, (void)s, (void)h;
  *r = NULL;
  return -2;
}
void freeaddrinfo(void *r) { (void)r; }
const char *gai_strerror(int e) {
  (void)e;
  return "name resolution is unavailable";
}

// Thread-specific data of the one thread.
#define ENV_KEYS 64
static void *keyValue[ENV_KEYS];
static int keyUsed[ENV_KEYS];
int pthread_key_create(unsigned *k, void (*d)(void *)) {
  (void)d;
  for (unsigned i = 0; i < ENV_KEYS; ++i)
    if (!keyUsed[i]) {
      keyUsed[i] = 1;
      keyValue[i] = NULL;
      *k = i;
      return 0;
    }
  return EAGAIN;
}
int pthread_key_delete(unsigned k) {
  if (k < ENV_KEYS)
    keyUsed[k] = 0;
  return 0;
}
void *pthread_getspecific(unsigned k) { return k < ENV_KEYS ? keyValue[k] : NULL; }
int pthread_setspecific(unsigned k, const void *v) {
  if (k >= ENV_KEYS)
    return EINVAL;
  keyValue[k] = (void *)v;
  return 0;
}
// With one thread, a wait for a condition no one else can signal never
// returns.
int pthread_cond_wait(void *c, void *m) {
  (void)c, (void)m;
  klee_silent_exit(0);
  return 0;
}

// A non-local jump: setjmp returns 0 when called. A longjmp would resume
// at that call, which this environment cannot do, so the execution ends
// there.
int _setjmp(void *env) {
  (void)env;
  return 0;
}
int setjmp(void *env) {
  (void)env;
  return 0;
}
int __sigsetjmp(void *env, int save) {
  (void)env, (void)save;
  return 0;
}
void longjmp(void *env, int v) {
  (void)env, (void)v;
  klee_silent_exit(0);
}
void _longjmp(void *env, int v) { longjmp(env, v); }
void siglongjmp(void *env, int v) { longjmp(env, v); }

// File system operations env.c does not model.
int remove(const char *p) { return unlink(p); }
int rename(const char *a, const char *b) {
  (void)a, (void)b;
  errno = EACCES;
  return -1;
}
int mkdir(const char *p, unsigned m) {
  (void)p, (void)m;
  errno = EACCES;
  return -1;
}
ssize_t readlink(const char *p, char *b, size_t n) {
  (void)p, (void)b, (void)n;
  errno = EINVAL;
  return -1;
}
int symlink(const char *a, const char *b) {
  (void)a, (void)b;
  errno = EACCES;
  return -1;
}
int fchmod(int fd, unsigned m) {
  (void)fd, (void)m;
  return 0;
}
int chmod(const char *p, unsigned m) {
  (void)p, (void)m;
  return 0;
}
int posix_fallocate(int fd, long o, long n) {
  (void)fd, (void)o, (void)n;
  return 0;
}
ssize_t sendfile(int o, int i, long *off, size_t n) {
  (void)o, (void)i, (void)off, (void)n;
  errno = EINVAL;
  return -1;
}
