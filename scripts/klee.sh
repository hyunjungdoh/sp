#!/bin/bash
# Runs inside the klee-sink image with the repo root mounted at /w.
# Usage: klee.sh <N> <budget-seconds> <CVE>...
# Reach = KLEE prints the harness marker "SINK-REACHED"; the elapsed second is recorded.
# H = harness name under out/harness (default n$N). TAG = base|gen.
N=$1; T=$2; shift 2
H=${H:-n$N}
TAG=${TAG:-base}
cd /w
for c in "$@"; do
  out=out/$TAG/$H/$c
  # The host mount can be briefly unreadable when containers start together.
  seeds=$(echo "$KOPTS" | sed -n 's/.*--seed-dir=\([^ ]*\).*/\1/p')
  for i in $(seq 30); do [ -z "$seeds" ] || ls "$seeds" >/dev/null 2>&1 && break; sleep 1; done
  rm -rf "$out"
  mkdir -p "out/$TAG/$H"
  start=$SECONDS
  # Skip assembly.ll: dumping the full linked module as text dominates
  # startup on large D∪U harnesses and is unused by measurement.
  stdbuf -oL -eL timeout $((T + 300)) /home/klee/klee_build/bin/klee \
    --libc=klee --link-llvm-lib=/w/env/env.bc --external-calls=${EXTCALLS:-over-approx} \
    --kdalloc=false --search=nurs:sink --use-batching-search --sym-alloc-cap=${CAP:-65536} $KOPTS \
    --output-source=false \
    --max-time=${T}s --watchdog --max-memory=${MEM:-2500} \
    --only-output-states-covering-new \
    --output-dir="$out" out/harness/$H/$c/client.bc > "$out.log" 2>&1 &
  pid=$!
  hit=
  while kill -0 $pid 2>/dev/null; do
    # Require the executed warning form; the nurs setup line "found no
    # SINK-REACHED marker" must not count as a hit. Prefer klee_warning
    # (always prints); klee_warning_once can be suppressed by an earlier once.
    if grep -qE 'WARNING( ONCE)?:.*: SINK-REACHED' "$out.log"; then hit=$((SECONDS - start)); kill $pid; break; fi
    sleep 2
  done
  wait $pid
  # A run that neither reached nor finished (killed from outside) is no measurement.
  if [ -n "$hit" ] || grep -q "^KLEE: done:" "$out.log"; then
    echo "$c n$N reach=${hit:+yes} t=${hit:--}" >> out/$TAG/$H/result.txt
  fi
done
