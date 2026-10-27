// Environment model for the closed program. A library function outside the
// program returns one of the results its specification allows, so every
// execution of the harness is an execution against some real environment.
//
// The environment is fixed, not input: the attacker controls only what the
// client passes through D's interface. It is the one any user can reproduce:
//   env -i ./client f </dev/null >/dev/null 2>/dev/null
// The process is single-threaded and no environment variable is set. The
// file system holds one regular file, the client's input "f", whose bytes
// are the client's choice, and the files the program itself creates; no
// directory can be listed and no other program can be run. Standard input
// is empty and standard output and error discard what is written.
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

void klee_make_symbolic(void *addr, size_t nbytes, const char *name);
void klee_assume(unsigned long cond);

char *getenv(const char *name) {
  (void)name;
  return NULL;
}

char *secure_getenv(const char *name) { return getenv(name); }

// No new thread can be created; the caller runs its work itself.
typedef unsigned long pthread_t;
int pthread_create(pthread_t *t, const void *attr, void *(*fn)(void *), void *arg) {
  (void)t, (void)attr, (void)fn, (void)arg;
  return EAGAIN;
}
pthread_t pthread_self(void) { return 1; }
int pthread_join(pthread_t t, void **ret) {
  (void)t, (void)ret;
  return ESRCH;
}
int pthread_detach(pthread_t t) {
  (void)t;
  return ESRCH;
}

// With one thread every lock is free and no wait is ever woken by another
// thread, so these operations succeed without effect.
int pthread_mutex_init(void *m, const void *a) { (void)m, (void)a; return 0; }
int pthread_mutex_destroy(void *m) { (void)m; return 0; }
int pthread_mutex_lock(void *m) { (void)m; return 0; }
int pthread_mutex_trylock(void *m) { (void)m; return 0; }
int pthread_mutex_unlock(void *m) { (void)m; return 0; }
int pthread_mutexattr_init(void *a) { (void)a; return 0; }
int pthread_mutexattr_destroy(void *a) { (void)a; return 0; }
int pthread_mutexattr_settype(void *a, int t) { (void)a, (void)t; return 0; }
int pthread_cond_init(void *c, const void *a) { (void)c, (void)a; return 0; }
int pthread_cond_destroy(void *c) { (void)c; return 0; }
int pthread_cond_signal(void *c) { (void)c; return 0; }
int pthread_cond_broadcast(void *c) { (void)c; return 0; }
int pthread_once(int *once, void (*fn)(void)) {
  if (!*once) {
    *once = 1;
    fn();
  }
  return 0;
}

// C++ ABI guards of function-local statics, single-threaded: the first byte
// of the guard records that the initialization completed.
int __cxa_guard_acquire(long long *g) { return *(char *)g == 0; }
void __cxa_guard_release(long long *g) { *(char *)g = 1; }
void __cxa_guard_abort(long long *g) { (void)g; }

int pthread_attr_init(void *a) { (void)a; return 0; }
int pthread_attr_destroy(void *a) { (void)a; return 0; }
int pthread_attr_setdetachstate(void *a, int s) { (void)a, (void)s; return 0; }
int pthread_attr_setstacksize(void *a, size_t s) { (void)a, (void)s; return 0; }

// The only locale is "C". Selecting it, or querying, succeeds; any other
// locale is unavailable.
static char c_locale[] = "C";
static int c_locale_obj;
static int is_c(const char *name) {
  return !name[0] || (name[0] == 'C' && !name[1]) ||
         (name[0] == 'P' && name[1] == 'O' && name[2] == 'S' && name[3] == 'I' && name[4] == 'X' && !name[5]);
}
char *setlocale(int category, const char *name) {
  (void)category;
  return !name || is_c(name) ? c_locale : NULL;
}
void *newlocale(int mask, const char *name, void *base) {
  (void)mask, (void)base;
  if (!is_c(name)) {
    errno = ENOENT;
    return NULL;
  }
  return &c_locale_obj;
}
void *uselocale(void *loc) {
  (void)loc;
  return &c_locale_obj;
}
void freelocale(void *loc) { (void)loc; }
void *bsearch(const void *key, const void *base, size_t n, size_t size,
              int (*cmp)(const void *, const void *)) {
  const char *lo = (const char *)base;
  while (n) {
    const char *mid = lo + (n / 2) * size;
    int c = cmp(key, mid);
    if (!c)
      return (void *)mid;
    if (c > 0) {
      lo = mid + size;
      n = n - n / 2 - 1;
    } else {
      n /= 2;
    }
  }
  return NULL;
}

void qsort(void *base, size_t n, size_t size, int (*cmp)(const void *, const void *)) {
  char *a = (char *)base;
  for (size_t i = 1; i < n; ++i)
    for (size_t j = i; j > 0 && cmp(a + (j - 1) * size, a + j * size) > 0; --j)
      for (size_t k = 0; k < size; ++k) {
        char t = a[(j - 1) * size + k];
        a[(j - 1) * size + k] = a[j * size + k];
        a[j * size + k] = t;
      }
}

// Every locale object is "C", so the _l conversions are the plain ones.
double strtod(const char *s, char **end);
float strtof(const char *s, char **end);
long double strtold(const char *s, char **end);
double strtod_l(const char *s, char **end, void *loc) { (void)loc; return strtod(s, end); }
float strtof_l(const char *s, char **end, void *loc) { (void)loc; return strtof(s, end); }
long double strtold_l(const char *s, char **end, void *loc) { (void)loc; return strtold(s, end); }

// No directory can be opened.
void *opendir(const char *path) {
  (void)path;
  errno = ENOENT;
  return NULL;
}
void *fdopendir(int fd) {
  (void)fd;
  errno = ENOENT;
  return NULL;
}
void *readdir(void *d) { (void)d; return NULL; }
int closedir(void *d) { (void)d; return 0; }

// ---------------------------------------------------------------------------
// File system. The working directory is the root, so "f", "./f" and "/f"
// name the same file. A file is a byte array; the input's bytes are
// symbolic and its length is fixed.

#define ENV_FILE_LEN 256
#define ENV_NAME 64
#define ENV_NODES 8
#define ENV_FDS 16

struct node {
  int used;
  char name[ENV_NAME];
  unsigned char *data;
  size_t size, cap;
};
struct ofd {
  int used, node, flags;
  size_t off;
};
static struct node nodes[ENV_NODES];
static struct ofd fds[ENV_FDS];
static int fs_ready;

static void fs_init(void) {
  if (fs_ready)
    return;
  fs_ready = 1;
  nodes[0].used = 1;
  nodes[0].name[0] = 'f';
  nodes[0].data = malloc(ENV_FILE_LEN);
  klee_make_symbolic(nodes[0].data, ENV_FILE_LEN, "file");
  nodes[0].size = nodes[0].cap = ENV_FILE_LEN;
}

// The path relative to the root, compared byte by byte so that a symbolic
// path the client chose forks only on the comparison.
static const char *rel(const char *p) {
  for (;;) {
    if (p[0] == '/')
      p += 1;
    else if (p[0] == '.' && p[1] == '/')
      p += 2;
    else
      return p;
  }
}
static int same(const char *a, const char *b) {
  for (size_t i = 0; i < ENV_NAME; ++i) {
    if (a[i] != b[i])
      return 0;
    if (!a[i])
      return 1;
  }
  return 0;
}
static int lookup(const char *path) {
  fs_init();
  if (!path)
    return -1;
  const char *p = rel(path);
  for (int i = 0; i < ENV_NODES; ++i)
    if (nodes[i].used && same(nodes[i].name, p))
      return i;
  return -1;
}
static int create(const char *path) {
  const char *p = rel(path);
  for (int i = 0; i < ENV_NODES; ++i)
    if (!nodes[i].used) {
      size_t k = 0;
      for (; k + 1 < ENV_NAME && p[k]; ++k)
        nodes[i].name[k] = p[k];
      nodes[i].name[k] = 0;
      nodes[i].used = 1;
      nodes[i].data = NULL;
      nodes[i].size = nodes[i].cap = 0;
      return i;
    }
  return -1;
}
static int grow(struct node *n, size_t want) {
  if (want <= n->cap)
    return 0;
  size_t cap = n->cap ? n->cap : 64;
  while (cap < want)
    cap *= 2;
  unsigned char *d = malloc(cap);
  if (!d)
    return -1;
  if (n->size)
    memcpy(d, n->data, n->size);
  n->data = d;
  n->cap = cap;
  return 0;
}
static struct ofd *fdp(int fd) {
  return fd >= 3 && fd < ENV_FDS && fds[fd].used ? &fds[fd] : NULL;
}

int open(const char *path, int flags, ...) {
  int n = lookup(path);
  if (n < 0) {
    if (!(flags & O_CREAT) || (n = create(path)) < 0) {
      errno = ENOENT;
      return -1;
    }
  } else if ((flags & O_CREAT) && (flags & O_EXCL)) {
    errno = EEXIST;
    return -1;
  }
  if ((flags & O_TRUNC) && (flags & O_ACCMODE) != O_RDONLY)
    nodes[n].size = 0;
  for (int fd = 3; fd < ENV_FDS; ++fd)
    if (!fds[fd].used) {
      fds[fd].used = 1;
      fds[fd].node = n;
      fds[fd].flags = flags;
      fds[fd].off = (flags & O_APPEND) ? nodes[n].size : 0;
      return fd;
    }
  errno = EMFILE;
  return -1;
}
int open64(const char *path, int flags, ...) { return open(path, flags, 0644); }
int openat(int dir, const char *path, int flags, ...) {
  (void)dir;
  return open(path, flags, 0644);
}
int creat(const char *path, mode_t mode) { return open(path, O_WRONLY | O_CREAT | O_TRUNC, mode); }
int close(int fd) {
  struct ofd *o = fdp(fd);
  if (o)
    o->used = 0;
  else if (fd < 0 || fd > 2) {
    errno = EBADF;
    return -1;
  }
  return 0;
}

static ssize_t readAt(struct ofd *o, void *buf, size_t n, size_t at) {
  struct node *nd = &nodes[o->node];
  if (at >= nd->size)
    return 0;
  if (n > nd->size - at)
    n = nd->size - at;
  memcpy(buf, nd->data + at, n);
  return (ssize_t)n;
}
static ssize_t writeAt(struct ofd *o, const void *buf, size_t n, size_t at) {
  struct node *nd = &nodes[o->node];
  if (grow(nd, at + n) < 0) {
    errno = ENOSPC;
    return -1;
  }
  if (at > nd->size)
    memset(nd->data + nd->size, 0, at - nd->size);
  memcpy(nd->data + at, buf, n);
  if (at + n > nd->size)
    nd->size = at + n;
  return (ssize_t)n;
}
ssize_t read(int fd, void *buf, size_t n) {
  struct ofd *o = fdp(fd);
  if (!o) {
    if (fd == 0)
      return 0;
    errno = EBADF;
    return -1;
  }
  ssize_t r = readAt(o, buf, n, o->off);
  if (r > 0)
    o->off += (size_t)r;
  return r;
}
ssize_t write(int fd, const void *buf, size_t n) {
  struct ofd *o = fdp(fd);
  if (!o) {
    if (fd == 1 || fd == 2)
      return (ssize_t)n;
    errno = EBADF;
    return -1;
  }
  if (o->flags & O_APPEND)
    o->off = nodes[o->node].size;
  ssize_t r = writeAt(o, buf, n, o->off);
  if (r > 0)
    o->off += (size_t)r;
  return r;
}
ssize_t pread(int fd, void *buf, size_t n, off_t at) {
  struct ofd *o = fdp(fd);
  if (!o || at < 0) {
    errno = o ? EINVAL : EBADF;
    return -1;
  }
  return readAt(o, buf, n, (size_t)at);
}
ssize_t pread64(int fd, void *buf, size_t n, off_t at) { return pread(fd, buf, n, at); }
ssize_t pwrite(int fd, const void *buf, size_t n, off_t at) {
  struct ofd *o = fdp(fd);
  if (!o || at < 0) {
    errno = o ? EINVAL : EBADF;
    return -1;
  }
  return writeAt(o, buf, n, (size_t)at);
}
ssize_t pwrite64(int fd, const void *buf, size_t n, off_t at) { return pwrite(fd, buf, n, at); }
off_t lseek(int fd, off_t off, int whence) {
  struct ofd *o = fdp(fd);
  if (!o) {
    errno = fd >= 0 && fd <= 2 ? ESPIPE : EBADF;
    return -1;
  }
  off_t base = whence == SEEK_SET ? 0 : whence == SEEK_CUR ? (off_t)o->off : (off_t)nodes[o->node].size;
  if (whence != SEEK_SET && whence != SEEK_CUR && whence != SEEK_END) {
    errno = EINVAL;
    return -1;
  }
  if (base + off < 0) {
    errno = EINVAL;
    return -1;
  }
  o->off = (size_t)(base + off);
  return (off_t)o->off;
}
off_t lseek64(int fd, off_t off, int whence) { return lseek(fd, off, whence); }
int ftruncate(int fd, off_t len) {
  struct ofd *o = fdp(fd);
  if (!o || len < 0) {
    errno = o ? EINVAL : EBADF;
    return -1;
  }
  struct node *nd = &nodes[o->node];
  if ((size_t)len > nd->size) {
    if (grow(nd, (size_t)len) < 0)
      return -1;
    memset(nd->data + nd->size, 0, (size_t)len - nd->size);
  }
  nd->size = (size_t)len;
  return 0;
}
int ftruncate64(int fd, off_t len) { return ftruncate(fd, len); }
int fsync(int fd) { return fdp(fd) ? 0 : (errno = EBADF, -1); }
int fcntl(int fd, int cmd, ...) {
  (void)cmd;
  return fdp(fd) || (fd >= 0 && fd <= 2) ? 0 : (errno = EBADF, -1);
}

static void fill(struct stat *st, int n) {
  memset(st, 0, sizeof *st);
  st->st_mode = S_IFREG | 0644;
  st->st_nlink = 1;
  st->st_ino = (ino_t)(n + 1);
  st->st_size = (off_t)nodes[n].size;
  st->st_blksize = 4096;
  st->st_blocks = (blkcnt_t)((nodes[n].size + 511) / 512);
}
int fstat(int fd, struct stat *st) {
  struct ofd *o = fdp(fd);
  if (!o) {
    errno = EBADF;
    return -1;
  }
  fill(st, o->node);
  return 0;
}
int fstat64(int fd, struct stat *st) { return fstat(fd, st); }
int stat(const char *path, struct stat *st) {
  int n = lookup(path);
  if (n < 0) {
    errno = ENOENT;
    return -1;
  }
  fill(st, n);
  return 0;
}
int stat64(const char *path, struct stat *st) { return stat(path, st); }
int lstat(const char *path, struct stat *st) { return stat(path, st); }
int lstat64(const char *path, struct stat *st) { return stat(path, st); }
int access(const char *path, int mode) {
  (void)mode;
  return lookup(path) < 0 ? (errno = ENOENT, -1) : 0;
}
int unlink(const char *path) {
  int n = lookup(path);
  if (n < 0) {
    errno = ENOENT;
    return -1;
  }
  nodes[n].used = 0;
  return 0;
}
int mkstemp(char *tmpl) {
  size_t len = 0;
  while (tmpl[len])
    ++len;
  for (size_t i = len >= 6 ? len - 6 : 0; i < len; ++i)
    if (tmpl[i] == 'X')
      tmpl[i] = '0';
  return open(tmpl, O_RDWR | O_CREAT | O_EXCL, 0600);
}
char *getcwd(char *buf, size_t size) {
  if (!buf) {
    buf = malloc(2);
    size = 2;
  }
  if (size < 2) {
    errno = ERANGE;
    return NULL;
  }
  buf[0] = '/';
  buf[1] = 0;
  return buf;
}
char *realpath(const char *path, char *out) {
  int n = lookup(path);
  if (n < 0) {
    errno = ENOENT;
    return NULL;
  }
  if (!out)
    out = malloc(ENV_NAME + 1);
  out[0] = '/';
  size_t k = 0;
  for (; k < ENV_NAME - 1 && nodes[n].name[k]; ++k)
    out[k + 1] = nodes[n].name[k];
  out[k + 1] = 0;
  return out;
}

// A file mapping is a private copy of the file's bytes; an anonymous one is
// zeroed memory.
void *mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off) {
  (void)addr, (void)prot;
  if (!len) {
    errno = EINVAL;
    return MAP_FAILED;
  }
  unsigned char *m = malloc(len);
  if (!m) {
    errno = ENOMEM;
    return MAP_FAILED;
  }
  memset(m, 0, len);
  if (flags & MAP_ANONYMOUS)
    return m;
  struct ofd *o = fdp(fd);
  if (!o || off < 0) {
    errno = EBADF;
    return MAP_FAILED;
  }
  readAt(o, m, len, (size_t)off);
  return m;
}
void *mmap64(void *addr, size_t len, int prot, int flags, int fd, off_t off) {
  return mmap(addr, len, prot, flags, fd, off);
}
int munmap(void *addr, size_t len) {
  (void)addr, (void)len;
  return 0;
}

// No other program can be run.
FILE *popen(const char *cmd, const char *mode) {
  (void)cmd, (void)mode;
  errno = ENOSYS;
  return NULL;
}
int pclose(FILE *p) {
  (void)p;
  errno = ECHILD;
  return -1;
}
int system(const char *cmd) { return cmd ? -1 : 0; }

// ---------------------------------------------------------------------------
// Streams over the file system. A stream the program did not open here is a
// standard stream: input is empty and output is discarded.

#define ENV_STREAMS 16
struct stream {
  int used, fd, eof, err, back;
};
static struct stream streams[ENV_STREAMS];
static struct stream *ours(FILE *fp) {
  struct stream *s = (struct stream *)fp;
  return s >= streams && s < streams + ENV_STREAMS && s->used ? s : NULL;
}
static int modeFlags(const char *m) {
  int plus = 0;
  for (const char *c = m; *c; ++c)
    plus |= *c == '+';
  if (m[0] == 'r')
    return plus ? O_RDWR : O_RDONLY;
  if (m[0] == 'w')
    return (plus ? O_RDWR : O_WRONLY) | O_CREAT | O_TRUNC;
  if (m[0] == 'a')
    return (plus ? O_RDWR : O_WRONLY) | O_CREAT | O_APPEND;
  return -1;
}
static FILE *wrap(int fd) {
  for (int i = 0; i < ENV_STREAMS; ++i)
    if (!streams[i].used) {
      streams[i] = (struct stream){1, fd, 0, 0, EOF};
      return (FILE *)&streams[i];
    }
  close(fd);
  errno = EMFILE;
  return NULL;
}
FILE *fopen(const char *path, const char *mode) {
  int fl = modeFlags(mode);
  if (fl < 0) {
    errno = EINVAL;
    return NULL;
  }
  int fd = open(path, fl, 0644);
  return fd < 0 ? NULL : wrap(fd);
}
FILE *fopen64(const char *path, const char *mode) { return fopen(path, mode); }
FILE *fdopen(int fd, const char *mode) {
  (void)mode;
  if (!fdp(fd) && (fd < 0 || fd > 2)) {
    errno = EBADF;
    return NULL;
  }
  return wrap(fd);
}
int fclose(FILE *fp) {
  struct stream *s = ours(fp);
  if (!s)
    return 0;
  s->used = 0;
  return close(s->fd);
}
size_t fread(void *buf, size_t size, size_t n, FILE *fp) {
  struct stream *s = ours(fp);
  size_t want = size * n, got = 0;
  if (!s || !want)
    return 0;
  unsigned char *b = buf;
  if (s->back != EOF) {
    b[got++] = (unsigned char)s->back;
    s->back = EOF;
  }
  while (got < want) {
    ssize_t r = read(s->fd, b + got, want - got);
    if (r < 0) {
      s->err = 1;
      break;
    }
    if (r == 0) {
      s->eof = 1;
      break;
    }
    got += (size_t)r;
  }
  return got / size;
}
size_t fwrite(const void *buf, size_t size, size_t n, FILE *fp) {
  struct stream *s = ours(fp);
  if (!s)
    return n;
  if (!size || !n)
    return 0;
  ssize_t r = write(s->fd, buf, size * n);
  if (r < 0) {
    s->err = 1;
    return 0;
  }
  return (size_t)r / size;
}
int fgetc(FILE *fp) {
  unsigned char c;
  return fread(&c, 1, 1, fp) == 1 ? c : EOF;
}
int getc(FILE *fp) { return fgetc(fp); }
int getc_unlocked(FILE *fp) { return fgetc(fp); }
int _IO_getc(FILE *fp) { return fgetc(fp); }
int ungetc(int c, FILE *fp) {
  struct stream *s = ours(fp);
  if (!s || c == EOF)
    return EOF;
  s->back = (unsigned char)c;
  s->eof = 0;
  return (unsigned char)c;
}
char *fgets(char *buf, int n, FILE *fp) {
  int i = 0;
  while (i + 1 < n) {
    int c = fgetc(fp);
    if (c == EOF)
      break;
    buf[i++] = (char)c;
    if (c == '\n')
      break;
  }
  if (!i)
    return NULL;
  buf[i] = 0;
  return buf;
}
int fputc(int c, FILE *fp) {
  unsigned char b = (unsigned char)c;
  return fwrite(&b, 1, 1, fp) == 1 ? b : EOF;
}
int putc(int c, FILE *fp) { return fputc(c, fp); }
int fputs(const char *str, FILE *fp) {
  size_t len = 0;
  while (str[len])
    ++len;
  return fwrite(str, 1, len, fp) == len ? 1 : EOF;
}
int vfprintf(FILE *fp, const char *fmt, va_list ap) {
  struct stream *s = ours(fp);
  if (!s)
    return 0;
  char buf[1024];
  int n = vsnprintf(buf, sizeof buf, fmt, ap);
  if (n < 0)
    return n;
  size_t len = (size_t)n < sizeof buf ? (size_t)n : sizeof buf - 1;
  return fwrite(buf, 1, len, fp) == len ? n : -1;
}
int fprintf(FILE *fp, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vfprintf(fp, fmt, ap);
  va_end(ap);
  return n;
}
int fseeko(FILE *fp, off_t off, int whence) {
  struct stream *s = ours(fp);
  if (!s) {
    errno = ESPIPE;
    return -1;
  }
  if (whence == SEEK_CUR && s->back != EOF)
    off -= 1;
  if (lseek(s->fd, off, whence) < 0)
    return -1;
  s->back = EOF;
  s->eof = 0;
  return 0;
}
int fseek(FILE *fp, long off, int whence) { return fseeko(fp, (off_t)off, whence); }
int fseeko64(FILE *fp, off_t off, int whence) { return fseeko(fp, off, whence); }
off_t ftello(FILE *fp) {
  struct stream *s = ours(fp);
  if (!s) {
    errno = ESPIPE;
    return -1;
  }
  off_t at = lseek(s->fd, 0, SEEK_CUR);
  return at < 0 ? at : at - (s->back != EOF);
}
long ftell(FILE *fp) { return (long)ftello(fp); }
off_t ftello64(FILE *fp) { return ftello(fp); }
void rewind(FILE *fp) {
  struct stream *s = ours(fp);
  if (s) {
    fseeko(fp, 0, SEEK_SET);
    s->err = 0;
  }
}
int feof(FILE *fp) {
  struct stream *s = ours(fp);
  return s ? s->eof : 1;
}
int ferror(FILE *fp) {
  struct stream *s = ours(fp);
  return s ? s->err : 0;
}
void clearerr(FILE *fp) {
  struct stream *s = ours(fp);
  if (s)
    s->eof = s->err = 0;
}
int fileno(FILE *fp) {
  struct stream *s = ours(fp);
  return s ? s->fd : 2;
}
int fflush(FILE *fp) {
  (void)fp;
  return 0;
}
int setvbuf(FILE *fp, char *buf, int mode, size_t size) {
  (void)fp, (void)buf, (void)mode, (void)size;
  return 0;
}
void setbuf(FILE *fp, char *buf) { (void)fp, (void)buf; }

// ---------------------------------------------------------------------------
// The C++ runtime's dynamic_cast (Itanium C++ ABI 2.9.7). An object's vtable
// holds at -16 the offset to the most-derived object and at -8 its
// type_info. A class's type_info is a __class_type_info (no bases), a
// __si_class_type_info (one public non-virtual base at offset 0, at +16), or
// a __vmi_class_type_info (flags at +16, base count at +20, then pairs of
// base type_info and offset_flags: offset in the high bits, virtual 0x1,
// public 0x2). Two type_infos are the same type when their names are.

extern char _ZTVN10__cxxabiv120__si_class_type_infoE[] __attribute__((weak));
extern char _ZTVN10__cxxabiv121__vmi_class_type_infoE[] __attribute__((weak));

static const char *tiName(const void *ti) {
  const char *n = ((const char *const *)ti)[1];
  return n[0] == '*' ? n + 1 : n;
}
static int sameType(const void *a, const void *b) {
  if (a == b)
    return 1;
  const char *x = tiName(a), *y = tiName(b);
  for (size_t i = 0;; ++i) {
    if (x[i] != y[i])
      return 0;
    if (!x[i])
      return 1;
  }
}
static int kind(const void *ti) {
  const void *vt = *(const void *const *)ti;
  if (vt == _ZTVN10__cxxabiv120__si_class_type_infoE + 16)
    return 1;
  if (vt == _ZTVN10__cxxabiv121__vmi_class_type_infoE + 16)
    return 2;
  return 0;
}
// The address of the public base subobject of type 'want' inside the
// object at 'obj' whose dynamic type is 'ti', or NULL.
static void *findBase(char *obj, const void *ti, const void *want) {
  if (sameType(ti, want))
    return obj;
  switch (kind(ti)) {
  case 1:
    return findBase(obj, ((const void *const *)ti)[2], want);
  case 2: {
    unsigned count = ((const unsigned *)ti)[5];
    const char *base = (const char *)ti + 24;
    for (unsigned i = 0; i < count; ++i) {
      const void *bt = *(const void *const *)(base + 16 * i);
      long of = *(const long *)(base + 16 * i + 8);
      if (!(of & 2))
        continue;
      long off = of >> 8;
      char *sub = (of & 1) ? obj + *(const long *)(*(char **)obj + off) : obj + off;
      void *r = findBase(sub, bt, want);
      if (r)
        return r;
    }
    return NULL;
  }
  default:
    return NULL;
  }
}
void *__dynamic_cast(const void *src, const void *srcType, const void *dstType, long src2dst) {
  (void)srcType, (void)src2dst;
  if (!src)
    return NULL;
  const char *vt = *(const char *const *)src;
  long top = *(const long *)(vt - 16);
  const void *whole = *(const void *const *)(vt - 8);
  return findBase((char *)src + top, whole, dstType);
}

/* The C++ runtime's non-template pieces the libraries call, by the
 * Itanium C++ ABI and libstdc++'s layouts. The standard streams need no
 * setup (output is discarded, input is empty), and std::allocator<char>
 * has no state. */
void _ZNSt8ios_base4InitC1Ev(void *self) { (void)self; }
void _ZNSt8ios_base4InitD1Ev(void *self) { (void)self; }
void _ZNSaIcEC1Ev(void *self) { (void)self; }
void _ZNSaIcEC2Ev(void *self) { (void)self; }
void _ZNSaIcED1Ev(void *self) { (void)self; }
void _ZNSaIcED2Ev(void *self) { (void)self; }
void _ZNSaIcEC1ERKS_(void *self, const void *other) { (void)self, (void)other; }
void _ZNSaIcEC2ERKS_(void *self, const void *other) { (void)self, (void)other; }

/* std::_Rb_tree_node_base: color (red 0, black 1), parent, left, right.
 * The header's parent is the root, its left the leftmost node, its right
 * the rightmost. */
typedef struct rb {
  int color;
  struct rb *parent, *left, *right;
} rb;
enum { RED = 0, BLACK = 1 };

rb *_ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base(rb *x) {
  if (x->right) {
    x = x->right;
    while (x->left)
      x = x->left;
  } else {
    rb *y = x->parent;
    while (x == y->right) {
      x = y;
      y = y->parent;
    }
    if (x->right != y)
      x = y;
  }
  return x;
}
const rb *_ZSt18_Rb_tree_incrementPKSt18_Rb_tree_node_base(const rb *x) {
  return _ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base((rb *)x);
}
rb *_ZSt18_Rb_tree_decrementPSt18_Rb_tree_node_base(rb *x) {
  if (x->color == RED && x->parent->parent == x)
    x = x->right;
  else if (x->left) {
    rb *y = x->left;
    while (y->right)
      y = y->right;
    x = y;
  } else {
    rb *y = x->parent;
    while (x == y->left) {
      x = y;
      y = y->parent;
    }
    x = y;
  }
  return x;
}
const rb *_ZSt18_Rb_tree_decrementPKSt18_Rb_tree_node_base(const rb *x) {
  return _ZSt18_Rb_tree_decrementPSt18_Rb_tree_node_base((rb *)x);
}

static void rotateLeft(rb *x, rb **root) {
  rb *y = x->right;
  x->right = y->left;
  if (y->left)
    y->left->parent = x;
  y->parent = x->parent;
  if (x == *root)
    *root = y;
  else if (x == x->parent->left)
    x->parent->left = y;
  else
    x->parent->right = y;
  y->left = x;
  x->parent = y;
}
static void rotateRight(rb *x, rb **root) {
  rb *y = x->left;
  x->left = y->right;
  if (y->right)
    y->right->parent = x;
  y->parent = x->parent;
  if (x == *root)
    *root = y;
  else if (x == x->parent->right)
    x->parent->right = y;
  else
    x->parent->left = y;
  y->right = x;
  x->parent = y;
}

void _ZSt29_Rb_tree_insert_and_rebalancebPSt18_Rb_tree_node_baseS0_RS_(_Bool left, rb *x, rb *p, rb *header) {
  rb **root = &header->parent;
  x->parent = p;
  x->left = x->right = NULL;
  x->color = RED;
  if (left) {
    p->left = x;
    if (p == header) {
      header->parent = x;
      header->right = x;
    } else if (p == header->left)
      header->left = x;
  } else {
    p->right = x;
    if (p == header->right)
      header->right = x;
  }
  while (x != *root && x->parent->color == RED) {
    rb *xpp = x->parent->parent;
    if (x->parent == xpp->left) {
      rb *y = xpp->right;
      if (y && y->color == RED) {
        x->parent->color = BLACK;
        y->color = BLACK;
        xpp->color = RED;
        x = xpp;
      } else {
        if (x == x->parent->right) {
          x = x->parent;
          rotateLeft(x, root);
        }
        x->parent->color = BLACK;
        xpp->color = RED;
        rotateRight(xpp, root);
      }
    } else {
      rb *y = xpp->left;
      if (y && y->color == RED) {
        x->parent->color = BLACK;
        y->color = BLACK;
        xpp->color = RED;
        x = xpp;
      } else {
        if (x == x->parent->left) {
          x = x->parent;
          rotateRight(x, root);
        }
        x->parent->color = BLACK;
        xpp->color = RED;
        rotateLeft(xpp, root);
      }
    }
  }
  (*root)->color = BLACK;
}

rb *_ZSt28_Rb_tree_rebalance_for_erasePSt18_Rb_tree_node_baseRS_(rb *z, rb *header) {
  rb **root = &header->parent, **leftmost = &header->left, **rightmost = &header->right;
  rb *y = z, *x = NULL, *xp = NULL;
  if (!y->left)
    x = y->right;
  else if (!y->right)
    x = y->left;
  else {
    y = y->right;
    while (y->left)
      y = y->left;
    x = y->right;
  }
  if (y != z) {
    z->left->parent = y;
    y->left = z->left;
    if (y != z->right) {
      xp = y->parent;
      if (x)
        x->parent = y->parent;
      y->parent->left = x;
      y->right = z->right;
      z->right->parent = y;
    } else
      xp = y;
    if (*root == z)
      *root = y;
    else if (z->parent->left == z)
      z->parent->left = y;
    else
      z->parent->right = y;
    y->parent = z->parent;
    int c = y->color;
    y->color = z->color;
    z->color = c;
    y = z;
  } else {
    xp = y->parent;
    if (x)
      x->parent = y->parent;
    if (*root == z)
      *root = x;
    else if (z->parent->left == z)
      z->parent->left = x;
    else
      z->parent->right = x;
    if (*leftmost == z) {
      if (!z->right)
        *leftmost = z->parent;
      else {
        rb *m = x;
        while (m->left)
          m = m->left;
        *leftmost = m;
      }
    }
    if (*rightmost == z) {
      if (!z->left)
        *rightmost = z->parent;
      else {
        rb *m = x;
        while (m->right)
          m = m->right;
        *rightmost = m;
      }
    }
  }
  if (y->color != RED) {
    while (x != *root && (!x || x->color == BLACK)) {
      if (x == xp->left) {
        rb *w = xp->right;
        if (w->color == RED) {
          w->color = BLACK;
          xp->color = RED;
          rotateLeft(xp, root);
          w = xp->right;
        }
        if ((!w->left || w->left->color == BLACK) && (!w->right || w->right->color == BLACK)) {
          w->color = RED;
          x = xp;
          xp = xp->parent;
        } else {
          if (!w->right || w->right->color == BLACK) {
            w->left->color = BLACK;
            w->color = RED;
            rotateRight(w, root);
            w = xp->right;
          }
          w->color = xp->color;
          xp->color = BLACK;
          if (w->right)
            w->right->color = BLACK;
          rotateLeft(xp, root);
          break;
        }
      } else {
        rb *w = xp->left;
        if (w->color == RED) {
          w->color = BLACK;
          xp->color = RED;
          rotateRight(xp, root);
          w = xp->left;
        }
        if ((!w->right || w->right->color == BLACK) && (!w->left || w->left->color == BLACK)) {
          w->color = RED;
          x = xp;
          xp = xp->parent;
        } else {
          if (!w->left || w->left->color == BLACK) {
            w->right->color = BLACK;
            w->color = RED;
            rotateLeft(w, root);
            w = xp->left;
          }
          w->color = xp->color;
          xp->color = BLACK;
          if (w->left)
            w->left->color = BLACK;
          rotateRight(xp, root);
          break;
        }
      }
    }
    if (x)
      x->color = BLACK;
  }
  return y;
}
