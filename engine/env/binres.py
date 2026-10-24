#!/usr/bin/env python3
"""Data the program links from files, as GNU ld's binary input does.

`ld -r -b binary path` defines _binary_<p>_start, _end and _size, where <p>
is the path with every character outside [A-Za-z0-9] replaced by '_'. The
closed program needs these objects with the file's bytes; this emits them
as an LLVM module for the symbols a program leaves undefined, finding each
file under the source tree by that naming.

usage: binres.py PROGRAM.bc SOURCE_ROOT OUT.bc
"""
import os
import re
import subprocess
import sys

LLVM = "/home/guswjd/project/tools/llvm-18/bin"


def mangle(path):
    return re.sub(r"[^A-Za-z0-9]", "_", path)


def main():
    prog, root, out = sys.argv[1:4]
    nm = subprocess.run([f"{LLVM}/llvm-nm", "-u", prog], capture_output=True, text=True, check=True).stdout
    wanted = set()
    for line in nm.split():
        m = re.fullmatch(r"_binary_(.+)_(start|end|size)", line)
        if m:
            wanted.add(m.group(1))
    found = {}
    if wanted:
        for d, subdirs, files in os.walk(root):
            subdirs[:] = [s for s in subdirs if not s.startswith(("build", ".git"))]
            for f in files:
                parts = os.path.relpath(os.path.join(d, f), root).split(os.sep)
                for i in range(len(parts)):
                    key = mangle("/".join(parts[i:]))
                    if key in wanted and key not in found:
                        found[key] = os.path.join(d, f)
    lines = []
    for key, path in sorted(found.items()):
        data = open(path, "rb").read()
        n = len(data)
        body = "".join(chr(b) if 32 <= b < 127 and b not in (34, 92) else "\\%02X" % b for b in data)
        lines.append(f'@_binary_{key}_start = constant [{n} x i8] c"{body}", align 1')
        lines.append(f"@_binary_{key}_end = alias i8, getelementptr (i8, ptr @_binary_{key}_start, i64 {n})")
    ll = out + ".ll"
    with open(ll, "w") as fp:
        fp.write("\n".join(lines) + "\n")
    subprocess.run([f"{LLVM}/llvm-as", ll, "-o", out], check=True)
    os.remove(ll)
    print(f"binres: {len(found)}/{len(wanted)} files")


if __name__ == "__main__":
    main()
