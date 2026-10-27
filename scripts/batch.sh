#!/bin/bash
# Runs every case twice under the same budget: stock symbolic search (TAG=base)
# and --concolic with dataset/<CVE>/concolic_seed (TAG=gen).
# Usage: [H=<harness name>] batch.sh <N> <T> <P> [tags, default "base gen"]
N=$1; T=$2; P=$3; TAGS=${4:-base gen}
export H=${H:-n$N}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
jobs=()
for c in $(ls out/harness/$H | grep CVE); do
  for t in $TAGS; do jobs+=("$t $c"); done
done
printf '%s\n' "${jobs[@]}" | xargs -P "$P" -L 1 bash -c '
  tag=$0; c=$1
  grep -q "^$c " out/$tag/$H/result.txt 2>/dev/null && exit 0
  docker ps --format "{{.Names}}" | grep -qx "$tag-$c" && exit 0
  if [ $tag = gen ]; then
    k="--concolic --concolic-data=input,bytes --max-solver-time=10s --seed-dir=/w/dataset/$c/concolic_seed --named-seed-matching --allow-seed-extension --allow-seed-truncation --always-output-seeds=false"
  else k=""; fi
  docker run --rm --name "$tag-$c" -v "'"$ROOT"'":/w -e TAG=$tag -e H=$H -e MEM=1600 -e KOPTS="$k" \
    klee-sink bash /w/scripts/klee.sh '"$N $T"' "$c" >/dev/null 2>&1
  echo "$(date +%T) done $tag $c"
'
