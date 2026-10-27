#!/usr/bin/env python3
# First-generation seeds for --concolic (DESIGN-D §6 시드): every regular file
# of the US and DS source trees named in pins.yaml (VCS metadata excluded,
# the case's poc/ is outside them), at most N bytes so a seed is the file
# itself within the H2 input bound, deduplicated by content. The file goes to
# the harness data object `input`; every other symbolic object is absent and
# the engine binds it to zero.
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

files = {}
for d in dirs:
    for root, sub, names in os.walk(os.path.join(case, d)):
        sub[:] = sorted(x for x in sub if x not in (".git", ".svn", ".hg"))
        for f in sorted(names):
            p = os.path.join(root, f)
            if os.path.islink(p) or not os.path.isfile(p):
                continue
            if 0 < os.path.getsize(p) <= N:
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
