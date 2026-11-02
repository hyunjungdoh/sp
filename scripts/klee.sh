#!/bin/bash
# Runs inside the klee-sink image with the repo root mounted at /w.
# Usage: klee.sh <N> <budget-seconds> <CVE>...
# Trigger = KLEE raises a program memory error at the sink's source line
# (File:Line in dataset/<CVE>/sink.yaml). The sink is an ASan crash site, so
# reaching the line ("SINK-REACHED") is not the verdict; faulting at it is.
# Hit = "KLEE: ERROR: <file>:<line>: memory error". Elapsed second is recorded.
# H = harness name under out/harness (default n$N). TAG = base|gen.
N=$1; T=$2; shift 2
H=${H:-n$N}
TAG=${TAG:-base}
cd /w
for c in "$@"; do
  out=out/$TAG/$H/$c
  # Sink source location (File:Line) that the trigger verdict keys on.
  sf=$(sed -n 's/^[[:space:]]*File:[[:space:]]*//p' dataset/$c/sink.yaml | head -1)
  sl=$(sed -n 's/^[[:space:]]*Line:[[:space:]]*//p' dataset/$c/sink.yaml | head -1)
  trig="KLEE: ERROR: .*${sf}:${sl}: memory error"
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
    # Stop on the first program memory error at the sink line (the trigger).
    if grep -qE "$trig" "$out.log"; then hit=$((SECONDS - start)); kill $pid; break; fi
    sleep 2
  done
  wait $pid
  # A run that neither triggered nor finished (killed from outside) is no measurement.
  if [ -n "$hit" ] || grep -q "^KLEE: done:" "$out.log"; then
    echo "$c n$N trigger=${hit:+yes} t=${hit:--}" >> out/$TAG/$H/result.txt
  fi
done
