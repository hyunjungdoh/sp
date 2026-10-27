#!/usr/bin/env python3
# Compares the base and gen runs of batch.sh per case: reach, wall/solver time,
# covered instructions, concolic counters, and the deepest function of the
# static sink path (client.reach.txt cfg-path) that the run executed.
# Usage: summary.py <N> [harness name, default n<N>]
import os, re, sqlite3, sys

N = sys.argv[1]
H = sys.argv[2] if len(sys.argv) > 2 else f"n{N}"
ROOT = os.path.join(os.path.dirname(__file__), "..")


def stats(d):
    try:
        c = sqlite3.connect(os.path.join(d, "run.stats"))
        r = c.execute("SELECT WallTime,Instructions,CoveredInstructions,SolverTime,States "
                      "FROM stats ORDER BY rowid DESC LIMIT 1").fetchone()
        return r
    except Exception:
        return None


def fncov(d):
    cov, fn, skip = {}, None, False
    p = os.path.join(d, "run.istats")
    if not os.path.exists(p):
        return cov
    for line in open(p, errors="replace"):
        if line.startswith("fn="):
            fn = line[3:].strip(); continue
        if line.startswith("calls="):
            skip = True; continue
        if fn and line[:1].isdigit():
            if skip:
                skip = False; continue
            c = line.split()
            if len(c) > 2:
                cov[fn] = cov.get(fn, 0) + int(c[2])
    return cov


def ledger(d):
    p = os.path.join(d, "concolic.txt")
    if not os.path.exists(p):
        return {}
    return dict(l.split(None, 1) for l in open(p) if l.strip())


# REACHED: an input hit the marker. UNREACHABLE(K): the search ended with
# nothing open (every candidate explored or proven not to reach the sink)
# within flip bound K. UNKNOWN: otherwise; the open counts are the gap.
def verdict(tag, c, d):
    if reach(tag, c).startswith("yes"):
        return "REACHED"
    led = ledger(d)
    if led.get("exhaustive", "0").strip() == "1":
        # H3: the harness is the program only when it has no open obligation.
        p = os.path.join(ROOT, f"out/harness/{H}/{c}/client.open.txt")
        n = sum(1 for l in open(p) if l.strip()) if os.path.exists(p) else 0
        if n:
            return f"UNKNOWN(H3: {n} open obligations)"
        return f"UNREACHABLE(K={led['flip-bound'].strip()})"
    return "UNKNOWN"


def reach(tag, c):
    try:
        for line in open(os.path.join(ROOT, f"out/{tag}/{H}/result.txt")):
            if line.startswith(c + " "):
                m = re.search(r"reach=(\S*) t=(\S+)", line)
                return ("yes " + m.group(2)) if m.group(1) else "no"
    except FileNotFoundError:
        pass
    return "?"


print(f"{'case':16} {'run':4} {'reach':9} {'wall':>5} {'solver':>6} {'cov':>6} {'path depth':>10}  notes")
harness = os.path.join(ROOT, f"out/harness/{H}")
for c in sorted(x for x in os.listdir(harness) if x.startswith("CVE")):
    path = [l.split()[1].lstrip("*") for l in open(os.path.join(harness, c, "client.reach.txt"))
            if l.startswith("cfg-path")]
    for tag in ("base", "gen"):
        d = os.path.join(ROOT, f"out/{tag}/{H}/{c}")
        s = stats(d)
        cov = fncov(d)
        depth = max([i + 1 for i, f in enumerate(path) if cov.get(f, 0)] or [0])
        logp = d + ".log"
        log = open(logp, errors="replace").read() if os.path.exists(logp) else ""
        notes = []
        if tag == "gen":
            notes.append(verdict(tag, c, d))
            led = ledger(d)
            opens = {k[5:]: v.strip() for k, v in led.items() if k.startswith("open:")}
            if led:
                notes.append(f"flips={led['flips'].strip()} bounded={led['bounded'].strip()} "
                             f"respawned={led['respawned'].strip()} open={led['open'].strip()}")
            if opens:
                notes.append("open[" + ",".join(f"{k}={v}" for k, v in sorted(opens.items())) + "]")
        m = re.search(r"using (\d+) seeds", log)
        if m:
            notes.append(f"seeds={m.group(1)}")
        errs = len(re.findall(r"^KLEE: ERROR:", log, re.M))
        if errs:
            notes.append(f"errors={errs}")
        for fatal in ("LLVM ERROR", "Assertion", "Segmentation", "klee: ", "Killed"):
            if fatal in log:
                notes.append("FATAL:" + fatal.strip())
        if s:
            print(f"{c:16} {tag:4} {reach(tag, c):9} {s[0]/1e6:5.0f} {s[3]/1e6:6.0f} {s[2]:6} "
                  f"{depth:>4}/{len(path):<5}  {' '.join(notes)}")
        else:
            print(f"{c:16} {tag:4} {reach(tag, c):9} (no stats) {' '.join(notes)}")
    print("  path:", " > ".join(path))
