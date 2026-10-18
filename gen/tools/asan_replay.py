#!/usr/bin/env python3
"""Replay one KLEE witness on the ASan allocator.

Harness objects are mallocs of the sizes already in the module. The concrete
bytes of one .ktest fill those objects. AddressSanitizer's malloc and memcpy
then report a copy or call that leaves an object.
"""
import os
import re
import struct
import subprocess
import sys

LLVM = "/home/guswjd/project/tools/llvm-18/bin"
HERE = os.path.dirname(os.path.abspath(__file__))

# Symbols the host C library, libm, or zlib already define.
LIBC = {
    "__assert_fail", "__ctype_b_loc", "__errno_location", "__isoc99_sscanf",
    "atan2", "atoi", "bsearch", "calloc", "close", "deflate", "deflateEnd",
    "deflateInit_", "deflateParams", "deflateReset", "exit", "exp", "fprintf",
    "fputc", "fputs", "free", "fstat64", "inflate", "inflateEnd", "inflateInit_",
    "inflateReset", "log", "log2", "longjmp", "lseek64", "malloc", "memcmp",
    "mmap64", "munmap", "pow", "qsort", "realloc", "snprintf", "sprintf", "sqrt",
    "stderr", "strchr", "strcmp", "strcpy", "strerror", "strlen", "time",
    "vfprintf", "write",
}


def read_u32(f):
    b = f.read(4)
    if len(b) != 4:
        raise SystemExit("truncated ktest")
    return struct.unpack(">I", b)[0]


def read_str(f):
    n = read_u32(f)
    b = f.read(n)
    if len(b) != n:
        raise SystemExit("truncated ktest string")
    return b


def load_ktest(path):
    with open(path, "rb") as f:
        magic = f.read(5)
        if magic not in (b"KTEST", b"BOUT\n"):
            raise SystemExit("not a ktest")
        version = read_u32(f)
        nargs = read_u32(f)
        for _ in range(nargs):
            read_str(f)
        if version >= 2:
            read_u32(f)
            read_u32(f)
        nobj = read_u32(f)
        objs = []
        for _ in range(nobj):
            name = read_str(f).split(b"\x00", 1)[0].decode("latin1")
            size = read_u32(f)
            data = f.read(size)
            if len(data) != size:
                raise SystemExit("truncated ktest object")
            objs.append((name, data))
    return objs


def emit_concrete(objs, path):
    lines = [
        "#include <string.h>",
        "#include <stdint.h>",
        "struct Obj { const char *name; unsigned size; const unsigned char *bytes; };",
        "static unsigned char B[] = {",
    ]
    blobs = []
    off = 0
    parts = []
    for name, data in objs:
        blobs.append((name, off, len(data)))
        parts.append(",".join(str(c) for c in data))
        off += len(data)
    lines.append(",".join(parts) if parts else "0")
    lines.append("};")
    lines.append("static struct Obj O[] = {")
    for name, o, n in blobs:
        lines.append('  {"%s", %u, B + %u},' % (name.replace("\\", "\\\\").replace('"', '\\"'), n, o))
    lines.append("};")
    lines.append(
        """
void klee_make_symbolic(void *addr, size_t nbytes, const char *name) {
  static unsigned pos = 0;
  if (!addr) return;
  if (pos >= sizeof O / sizeof O[0]) {
    memset(addr, 0, nbytes);
    return;
  }
  size_t n = O[pos].size < nbytes ? O[pos].size : nbytes;
  memcpy(addr, O[pos].bytes, n);
  if (n < nbytes)
    memset((char *)addr + n, 0, nbytes - n);
  pos++;
  (void)name;
}
void klee_assume(int cond) { (void)cond; }
int klee_is_symbolic(const void *addr, size_t nbytes) {
  (void)addr; (void)nbytes;
  return 0;
}
"""
    )
    with open(path, "w") as f:
        f.write("\n".join(lines))


def stub_undefined(bc, path):
    nm = subprocess.check_output([os.path.join(LLVM, "llvm-nm"), "-u", bc], text=True)
    names = sorted({ln.split()[-1] for ln in nm.splitlines() if ln.strip()})
    lines = ["/* A declaration with no body in the linked module returns zero. */"]
    extra = 0
    for n in names:
        if n in LIBC or n.startswith("klee_") or n.startswith("llvm.") or n.startswith("__asan"):
            continue
        if n in ("stdin", "stdout", "stderr"):
            continue
        # x86-64: integer and pointer results come back in rax.
        if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", n):
            lines.append("long %s() { return 0; }" % n)
        else:
            lines.append('long stub_%d() __asm__("%s");' % (extra, n))
            lines.append("long stub_%d() { return 0; }" % extra)
            extra += 1
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def run(cmd, **kw):
    print("+", " ".join(cmd), flush=True)
    subprocess.check_call(cmd, **kw)


def main():
    if len(sys.argv) != 4:
        raise SystemExit("usage: asan_replay.py <linked.bc> <ktest> <outdir>")
    bc, ktest, out = sys.argv[1:]
    os.makedirs(out, exist_ok=True)
    heap = os.path.join(out, "heap.bc")
    obj = os.path.join(out, "mod.o")
    concrete = os.path.join(out, "concrete.c")
    stubs = os.path.join(out, "stubs.c")
    exe = os.path.join(out, "replay")
    log = os.path.join(out, "asan.log")
    tool = os.path.join(out, "asan_heap")

    def llvm_flags(args):
        return subprocess.check_output([os.path.join(LLVM, "llvm-config")] + args).decode().split()

    run(["c++", "-fno-rtti", "-O2", "-std=c++17", *llvm_flags(["--cxxflags"]),
         os.path.join(HERE, "asan_heap.cpp"), "-o", tool,
         *llvm_flags(["--ldflags", "--libs", "core", "irreader", "bitwriter", "support"]),
         *llvm_flags(["--system-libs"])])
    run([tool, bc, heap])
    run([os.path.join(LLVM, "llc"), "-relocation-model=pic", "-filetype=obj", "-o", obj, heap])
    emit_concrete(load_ktest(ktest), concrete)
    stub_undefined(heap, stubs)
    run(["clang-14", "-fsanitize=address", "-O0", "-g", "-o", exe, obj, concrete, stubs, "-lz", "-lm"])
    env = os.environ.copy()
    env["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1:abort_on_error=1:symbolize=1"
    print("+ replay", flush=True)
    with open(log, "w") as f:
        p = subprocess.run([exe], stdout=f, stderr=subprocess.STDOUT, env=env, timeout=60)
    print("exit", p.returncode, "log", log)
    text = open(log, errors="replace").read()
    sys.stdout.write(text[-8000:])


if __name__ == "__main__":
    main()
