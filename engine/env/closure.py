#!/usr/bin/env python3
"""The link units the program runs with, as the dynamic linker loads them.

surfaces.json lists the shared objects of D's link-unit closure. The
analysis bitcode may hold only some of them; the closed program needs the
code of all, as the process that loads D would. Each unit built by wllvm
carries its bitcode; this extracts it, and prints one path per line for
klee --link-llvm-lib, which links a library only for the symbols the
program leaves undefined, the dynamic linker's rule.

The units those need in turn (DT_NEEDED, transitively, as ldd resolves
them) that carry no bitcode are loaded natively: printed as "native:PATH"
for klee --load-native. The C and C++ runtimes are not among them: KLEE's
own and the environment model (env.bc) provide them, since native runtime
code would allocate and free outside the engine's memory model.

A symbol defined by several units binds to the first definition in load
order, the program's own before any library's (ELF interposition). A unit
is linked with the definitions an earlier module already provides turned
into declarations; PROGRAM_BC lists those earlier modules.

usage: closure.py CASE_DIR OUT_DIR PRUNED_DIR [PROGRAM_BC...]
"""
import json
import os
import re
import subprocess
import sys

EXTRACT = os.path.expanduser("~/.local/bin/extract-bc")
LLVM = "/home/guswjd/project/tools/llvm-18/bin"
INTERPOSE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "interpose")
RUNTIME = re.compile(r"^(libc|libm|libdl|libpthread|librt|ld-linux[-\w]*|linux-vdso"
                     r"|libstdc\+\+|libgcc_s)\.so")


def needed(so):
    r = subprocess.run(["ldd", so], capture_output=True, text=True)
    out = []
    for line in r.stdout.splitlines():
        m = re.match(r"\s*(\S+)\s+=>\s+(\S+)", line)
        if m and os.path.exists(m.group(2)):
            out.append(os.path.realpath(m.group(2)))
    return out


def defined(bc):
    """Defined external symbols: name -> whether a function."""
    r = subprocess.run([os.path.join(LLVM, "llvm-nm"), "--defined-only", "--extern-only", bc],
                       capture_output=True, text=True)
    out = {}
    for line in r.stdout.splitlines():
        p = line.split()
        if len(p) >= 2:
            out[p[-1]] = p[-2] in ("T", "W")
    return out


def interpose(bc, prior, pruned):
    """bc with the symbols prior defines turned into declarations."""
    mine = defined(bc)
    dup = sorted(n for n in mine if n in prior)
    prior.update(mine)
    if not dup:
        return bc
    os.makedirs(pruned, exist_ok=True)
    dst = os.path.join(pruned, os.path.basename(bc))
    names = dst + ".names"
    with open(names, "w") as f:
        f.write("\n".join(dup) + "\n")
    r = subprocess.run([INTERPOSE, bc, dst, names], capture_output=True, text=True)
    if r.returncode != 0:
        print(f"closure: interposing {bc}: {r.stderr.strip()}", file=sys.stderr)
        return bc
    return dst


def main():
    case, out, pruned = sys.argv[1:4]
    prior = {}
    for p in sys.argv[4:]:
        prior.update(defined(p))
    os.makedirs(out, exist_ok=True)
    s = json.load(open(os.path.join(case, "surfaces.json")))
    sos = [u["so"] for u in s.get("ds_closure", [])]
    us = s.get("us", {}).get("so")
    seen = {os.path.realpath(p) for p in sos + ([us] if us else []) if os.path.exists(p)}
    native = []
    for so in sos:
        if not os.path.exists(so):
            continue
        for dep in needed(so):
            if dep in seen or RUNTIME.match(os.path.basename(dep)):
                continue
            seen.add(dep)
            native.append(dep)
        bc = os.path.join(out, os.path.basename(so) + ".bc")
        if not os.path.exists(bc):
            r = subprocess.run([EXTRACT, "-o", bc, so], capture_output=True, text=True,
                               env=dict(os.environ, LLVM_COMPILER_PATH=LLVM))
            if r.returncode != 0 or not os.path.exists(bc):
                print(f"closure: no bitcode in {so}", file=sys.stderr)
                continue
        print(interpose(bc, prior, pruned))
    for dep in native:
        print("native:" + dep)


if __name__ == "__main__":
    main()
