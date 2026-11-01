#!/usr/bin/env python3
# First-generation seeds for --concolic. From the US and DS trees named in
# pins.yaml, keep a regular file only when it sits under test/images or
# fuzzing (poc/ and VCS metadata stay out), at most N bytes so a seed is the
# file itself within the input bound, deduplicated by content. The file goes
# to the harness data object `input`.
# Usage: corpus.py <dataset-case-dir> <N>
# Writes dataset/<CVE>/concolic_seed/ (replaces any previous contents).
import hashlib, os, re, shutil, struct, sys

case, N = sys.argv[1], int(sys.argv[2])
out = os.path.join(case, "concolic_seed")
dirs, role = [], None
for line in open(os.path.join(case, "pins.yaml")):
    m = re.match(r"\s*-\s*role:\s*(\S+)", line)
    if m:
        role = m.group(1)
    m = re.match(r"\s*dir:\s*(\S+)", line)
    if m and role in ("US", "DS"):
        dirs.append(m.group(1))

def sample(rel):
    parts = rel.split(os.sep)
    if "poc" in parts or ".git" in parts:
        return False
    if "fuzzing" in parts:
        return True
    return any(parts[i] == "images" and i > 0 and parts[i - 1] == "test" for i in range(len(parts)))

files = {}
for d in dirs:
    for root, sub, names in os.walk(os.path.join(case, d)):
        sub[:] = sorted(x for x in sub if x not in (".git", ".svn", ".hg"))
        for f in sorted(names):
            p = os.path.join(root, f)
            if os.path.islink(p) or not os.path.isfile(p):
                continue
            rel = os.path.relpath(p, case)
            if not sample(rel) or not (0 < os.path.getsize(p) <= N):
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
print(f"{case}: {' '.join(dirs)} -> {len(files)} seeds -> {out}")
