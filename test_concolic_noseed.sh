#!/bin/bash
# --only-replay-seeds 없이 일반 concolic 실행 테스트

cd /Users/hyunjung/Desktop/sp

# Docker 환경에서 KLEE 실행
docker run --rm \
  -v "$(pwd):/w" \
  -w /w \
  klee/klee:latest \
  /home/klee/klee_build/bin/klee \
    --libc=klee \
    --link-llvm-lib=/w/env/env.bc \
    --external-calls=over-approx \
    --kdalloc=false \
    --search=nurs:sink \
    --sym-alloc-cap=65536 \
    --concolic \
    --concolic-data=input,bytes \
    --max-solver-time=10s \
    --max-time=180s \
    --watchdog \
    --max-memory=4000 \
    --output-dir=/w/out/test_concolic_explore \
    /w/.mac/runs/r13phi/CVE-2023-1729/client.bc

echo ""
echo "=== 결과 확인 ==="
echo "explored paths:"
grep "explored paths" out/test_concolic_explore/info || echo "N/A"

echo ""
echo "sink 도달 여부:"
grep -i "sink\|error\|ASSERTION" out/test_concolic_explore/warnings.txt | head -5 || echo "없음"

echo ""
echo "생성된 테스트:"
ls -lh out/test_concolic_explore/*.ktest 2>/dev/null | wc -l
