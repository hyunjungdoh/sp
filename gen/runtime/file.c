/* A file is a total function from a concrete offset to one byte.
   Each byte is its own symbolic object, allocated when a read first asks
   for that offset, and reused when a later read asks again.
   A transfer has a concrete byte count: that count is the size of the
   transfer, and the call returns that many bytes. There is no chosen
   length of the file. */
typedef unsigned long size_t;
typedef long ssize_t;
typedef struct Stream Stream;

void klee_make_symbolic(void *addr, size_t nbytes, const char *name);
unsigned klee_is_symbolic(unsigned long n);
void *malloc(size_t n);
void *memcpy(void *dst, const void *src, size_t n);

struct Seg {
  size_t off;
  size_t len;
  char *data;
  struct Seg *next;
};

struct Stream {
  size_t pos;
  struct Seg *head;
};

struct Fd {
  int fd;
  struct Stream *s;
  struct Fd *next;
};

static struct Fd *fds;
static int nextfd = 3;

static struct Seg *find_seg(struct Stream *s, size_t off) {
  struct Seg *g;
  for (g = s->head; g; g = g->next)
    if (off >= g->off && off - g->off < g->len)
      return g;
  return 0;
}

static void fill(struct Stream *s, char *dst, size_t n) {
  size_t i = 0;
  while (i < n) {
    size_t off = s->pos + i;
    struct Seg *hit = find_seg(s, off);
    if (hit) {
      size_t k = hit->len - (off - hit->off);
      if (k > n - i)
        k = n - i;
      memcpy(dst + i, hit->data + (off - hit->off), k);
      i += k;
      continue;
    }
    size_t k = 1;
    while (i + k < n && !find_seg(s, off + k))
      k++;
    struct Seg *g = (struct Seg *)malloc(sizeof(struct Seg));
    g->off = off;
    g->len = k;
    g->data = (char *)malloc(k);
    klee_make_symbolic(g->data, k, "file");
    g->next = s->head;
    s->head = g;
    memcpy(dst + i, g->data, k);
    i += k;
  }
  s->pos += n;
}

static struct Stream *new_stream(void) {
  struct Stream *s = (struct Stream *)malloc(sizeof(struct Stream));
  s->pos = 0;
  s->head = 0;
  return s;
}

static struct Stream *stream_of(int fd) {
  struct Fd *f;
  for (f = fds; f; f = f->next)
    if (f->fd == fd)
      return f->s;
  return 0;
}

Stream *fopen(const char *path, const char *mode) {
  (void)path;
  (void)mode;
  return new_stream();
}

Stream *fopen64(const char *path, const char *mode) { return fopen(path, mode); }

int open(const char *path, int flags, ...) {
  struct Fd *f;
  (void)path;
  (void)flags;
  f = (struct Fd *)malloc(sizeof(struct Fd));
  f->fd = nextfd++;
  f->s = new_stream();
  f->next = fds;
  fds = f;
  return f->fd;
}

int open64(const char *path, int flags, ...) { return open(path, flags); }

size_t fread(void *ptr, size_t size, size_t nmemb, Stream *stream) {
  size_t n;
  if (!ptr || !stream || size == 0 || nmemb == 0)
    return 0;
  if (klee_is_symbolic((unsigned long)size) || klee_is_symbolic((unsigned long)nmemb))
    return 0;
  if (nmemb > ((size_t)-1) / size)
    return 0;
  n = size * nmemb;
  fill(stream, (char *)ptr, n);
  return nmemb;
}

ssize_t read(int fd, void *buf, size_t n) {
  struct Stream *s = stream_of(fd);
  if (!s || !buf)
    return -1;
  if (klee_is_symbolic((unsigned long)n))
    return -1;
  fill(s, (char *)buf, n);
  return (ssize_t)n;
}

ssize_t pread(int fd, void *buf, size_t n, long off) {
  struct Stream *s = stream_of(fd);
  size_t saved;
  ssize_t r;
  if (!s || !buf || klee_is_symbolic((unsigned long)off))
    return -1;
  saved = s->pos;
  s->pos = (size_t)off;
  r = read(fd, buf, n);
  s->pos = saved;
  return r;
}

ssize_t pread64(int fd, void *buf, size_t n, long off) { return pread(fd, buf, n, off); }

/* The end of a file is not a chosen length. A concrete offset moves
   the stream. An unknown offset, and SEEK_END, transfer nothing. */
long lseek(int fd, long off, int whence) {
  struct Stream *s = stream_of(fd);
  if (!s || klee_is_symbolic((unsigned long)off))
    return -1;
  if (whence == 0)
    s->pos = (size_t)off;
  else if (whence == 1)
    s->pos += (size_t)off;
  else
    return -1;
  return (long)s->pos;
}

long lseek64(int fd, long off, int whence) { return lseek(fd, off, whence); }

/* A concrete map is an object of that many bytes from the file.
   The address is a KLEE object. A host mapping is not. */
void *mmap(void *addr, size_t length, int prot, int flags, int fd, long offset) {
  struct Stream *s;
  void *p;
  size_t saved;
  (void)addr;
  (void)prot;
  (void)flags;
  if (length == 0 || klee_is_symbolic((unsigned long)length) || klee_is_symbolic((unsigned long)offset))
    return (void *)-1;
  p = malloc(length);
  if (!p)
    return (void *)-1;
  s = stream_of(fd);
  if (!s)
    s = new_stream();
  saved = s->pos;
  s->pos = (size_t)offset;
  fill(s, (char *)p, length);
  s->pos = saved;
  return p;
}

void *mmap64(void *addr, size_t length, int prot, int flags, int fd, long offset) {
  return mmap(addr, length, prot, flags, fd, offset);
}

int munmap(void *addr, size_t length) {
  (void)addr;
  (void)length;
  return 0;
}

int fseek(Stream *stream, long off, int whence) {
  if (!stream || klee_is_symbolic((unsigned long)off))
    return -1;
  if (whence == 0)
    stream->pos = (size_t)off;
  else if (whence == 1)
    stream->pos += (size_t)off;
  else
    return -1;
  return 0;
}

int fseeko(Stream *stream, long off, int whence) { return fseek(stream, off, whence); }
int fseeko64(Stream *stream, long off, int whence) { return fseek(stream, off, whence); }

long ftell(Stream *stream) {
  if (!stream)
    return -1;
  return (long)stream->pos;
}

long ftello(Stream *stream) { return ftell(stream); }
long ftello64(Stream *stream) { return ftell(stream); }

int fclose(Stream *stream) {
  (void)stream;
  return 0;
}

int feof(Stream *stream) {
  (void)stream;
  return 0;
}

int ferror(Stream *stream) {
  (void)stream;
  return 0;
}

int fflush(Stream *stream) {
  (void)stream;
  return 0;
}

size_t fwrite(const void *ptr, size_t size, size_t nmemb, Stream *stream) {
  (void)ptr;
  (void)stream;
  if (size == 0 || nmemb == 0)
    return 0;
  if (klee_is_symbolic((unsigned long)size) || klee_is_symbolic((unsigned long)nmemb))
    return 0;
  return nmemb;
}

char *fgets(char *s, int n, Stream *stream) {
  size_t k;
  if (!s || !stream || n <= 1)
    return 0;
  if (klee_is_symbolic((unsigned long)n))
    return 0;
  k = (size_t)n - 1;
  fill(stream, s, k);
  s[k] = 0;
  return s;
}

struct Gz {
  void *file;
  struct Stream *s;
  struct Gz *next;
};

static struct Gz *gzs;

int gzread(void *file, void *buf, unsigned n) {
  struct Gz *g;
  if (!file || !buf || klee_is_symbolic((unsigned long)n))
    return -1;
  for (g = gzs; g; g = g->next)
    if (g->file == file)
      break;
  if (!g) {
    g = (struct Gz *)malloc(sizeof(struct Gz));
    g->file = file;
    g->s = new_stream();
    g->next = gzs;
    gzs = g;
  }
  fill(g->s, (char *)buf, n);
  return (int)n;
}

/* The direct call returns 0. A later longjmp is a different return,
   and this runtime has no second return. */
/* An aligned allocation is a KLEE object. A host allocator returns an
   address the memory checker does not own. */
/* The harness has no environment. A host getenv returns a pointer
   the memory checker does not own. */
char *setlocale(int category, const char *locale) {
  (void)category;
  (void)locale;
  return 0;
}

/* A locale object from the host is an address the memory checker does not own. */
void *newlocale(int category, const char *locale, void *base) {
  (void)category;
  (void)locale;
  (void)base;
  return 0;
}

void *uselocale(void *locale) {
  (void)locale;
  return 0;
}

/* The C classification table is 384 entries, indexed from -128.
   A host __ctype_b_loc pointer is not a KLEE object. */
static unsigned short ctype_b[384];
static const unsigned short *ctype_bp;
static int ctype_lower[384];
static int ctype_upper[384];
static const int *ctype_lp;
static const int *ctype_up;
static int ctype_ready;

static void ctype_init(void) {
  int c;
  if (ctype_ready)
    return;
  for (c = 0; c < 384; ++c) {
    int ch = c - 128;
    unsigned short b = 0;
    int lo = ch;
    int up = ch;
    /* Little-endian _ISbit: bits 0..7 live in the high byte. */
    if (ch >= 'A' && ch <= 'Z') {
      b = (unsigned short)(0x0100 | 0x0400 | 0x4000 | 0x8000 | 0x0008);
      lo = ch - 'A' + 'a';
    } else if (ch >= 'a' && ch <= 'z') {
      b = (unsigned short)(0x0200 | 0x0400 | 0x4000 | 0x8000 | 0x0008);
      up = ch - 'a' + 'A';
    } else if (ch >= '0' && ch <= '9') {
      b = (unsigned short)(0x0800 | 0x1000 | 0x4000 | 0x8000 | 0x0008);
    } else if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == '\f' || ch == '\v') {
      b = (unsigned short)0x2000;
      if (ch == ' ' || ch == '\t')
        b = (unsigned short)(b | 0x0001);
    }
    ctype_b[c] = b;
    ctype_lower[c] = lo;
    ctype_upper[c] = up;
  }
  ctype_bp = ctype_b;
  ctype_lp = ctype_lower;
  ctype_up = ctype_upper;
  ctype_ready = 1;
}

const unsigned short **__ctype_b_loc(void) {
  ctype_init();
  return &ctype_bp;
}

const int **__ctype_tolower_loc(void) {
  ctype_init();
  return &ctype_lp;
}

const int **__ctype_toupper_loc(void) {
  ctype_init();
  return &ctype_up;
}

char *getenv(const char *name) {
  (void)name;
  return 0;
}
char *secure_getenv(const char *name) { return getenv(name); }

int posix_memalign(void **memptr, size_t alignment, size_t size) {
  unsigned char *raw;
  unsigned long base;
  unsigned long aligned;
  if (!memptr)
    return 22;
  if (klee_is_symbolic((unsigned long)alignment) || klee_is_symbolic((unsigned long)size))
    return 12;
  if (alignment < sizeof(void *) || (alignment & (alignment - 1)) != 0 || size == 0)
    return 22;
  raw = (unsigned char *)malloc(size + alignment);
  if (!raw)
    return 12;
  base = (unsigned long)raw;
  aligned = (base + (alignment - 1)) & ~(alignment - 1);
  *memptr = (void *)aligned;
  return 0;
}

void *aligned_alloc(size_t alignment, size_t size) {
  void *p = 0;
  if (posix_memalign(&p, alignment, size) != 0)
    return 0;
  return p;
}

void *memalign(size_t alignment, size_t size) { return aligned_alloc(alignment, size); }

int setjmp(void *env) { (void)env; return 0; }
int _setjmp(void *env) { (void)env; return 0; }
int sigsetjmp(void *env, int savesigs) { (void)env; (void)savesigs; return 0; }
int __sigsetjmp(void *env, int savesigs) { (void)env; (void)savesigs; return 0; }
