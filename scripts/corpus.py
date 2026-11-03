#!/usr/bin/env python3
# First-generation seeds for --concolic.
#
# The harness data object `input` is seeded from dataset/<CVE>/poc/ only —
# the byte sequences known to reach the sink. US/DS source trees, fuzz
# corpora, and test fixtures are not seeds (they drowned the PoC and never
# drove the sink path).
#
# Usage: corpus.py <dataset-case-dir> <N>
# Replaces any previous concolic_seed/ contents. Dedup by content; size ≤ N.
import hashlib, os, shutil, struct, sys

case, N = sys.argv[1], int(sys.argv[2])
out = os.path.join(case, "concolic_seed")
poc = os.path.join(case, "poc")

_SKIP_DIR = {".git", ".svn", ".hg", "mac-asan", "build", "CMakeFiles",
             "dSYM", "prefix", "install", "__pycache__"}
_SKIP_EXT = (".sh", ".c", ".cc", ".cpp", ".h", ".hpp", ".py", ".pyc",
             ".md", ".txt", ".log", ".yml", ".yaml", ".json", ".a", ".o",
             ".so", ".dylib", ".exe", ".cmake", ".plist", ".ktest", ".zip",
             ".options", ".in")
_BIN_MAGIC = (
    b"\x7fELF",
    b"\xcf\xfa\xed\xfe",
    b"\xfe\xed\xfa\xce",
    b"\xca\xfe\xba\xbe",
)

def keep(rel, path):
    parts = rel.split(os.sep)
    if any(p in _SKIP_DIR or p.endswith(".dSYM") for p in parts):
        return False
    base = parts[-1]
    if base.endswith(_SKIP_EXT):
        return False
    if not (0 < os.path.getsize(path) <= N):
        return False
    head = open(path, "rb").read(4)
    if head in _BIN_MAGIC:
        return False
    return True

files = {}
if os.path.isdir(poc):
    for root, sub, names in os.walk(poc):
        sub[:] = sorted(
            x for x in sub
            if x not in _SKIP_DIR and not x.endswith(".dSYM"))
        for f in sorted(names):
            p = os.path.join(root, f)
            if os.path.islink(p) or not os.path.isfile(p):
                continue
            rel = os.path.relpath(p, case)
            if not keep(rel, p):
                continue
            body = open(p, "rb").read()
            files.setdefault(hashlib.sha1(body).digest(), (p, body))

if os.path.isdir(out):
    shutil.rmtree(out)
os.makedirs(out)
with open(os.path.join(out, "index.txt"), "w") as idx:
    for k, (p, body) in enumerate(sorted(files.values()), 1):
        name = b"input"
        blob = [b"KTEST", struct.pack(">III", 3, 0, 0), struct.pack(">I", 0),
                struct.pack(">I", 1), struct.pack(">I", len(name)), name,
                struct.pack(">I", len(body)), body]
        open(os.path.join(out, f"seed{k:05d}.ktest"), "wb").write(b"".join(blob))
        idx.write(f"seed{k:05d} {os.path.relpath(p, case)}\n")
print(f"{case}: poc/ -> {len(files)} seeds -> {out}")
