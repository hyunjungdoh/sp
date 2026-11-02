# D→U 하네스 Concolic 실행 문제 분석

## 문제 요약
- **하네스**: 567개 entry + sink 조건 포함 (witnesses.txt)
- **Seed**: `input` (65KB PoC 파일)만 포함
- **Concolic**: `--concolic-data=input,bytes` → input만 flip
- **결과**: `entry`, `write`, `arg` 변수들이 기본값 → sink 미도달

## 근본 원인
```
--only-replay-seeds:
  if (var_name in seed):
    use seed_value  # input → ✅ PoC 내용
  else:
    use default     # entry, write, arg → ❌ 0 또는 임의값
```

## 해결책 비교

### 옵션 1: Witness → Seed 자동 변환 ⭐
- **장점**: 기존 코드 수정 없음, 범용 적용 가능
- **방법**: witnesses.txt 파싱 → ktest 생성
- **적용**: 모든 CVE에 자동화 가능

### 옵션 2: Concolic 대상 확장
- **장점**: 순수 concolic 접근
- **단점**: entry/write/arg 조합 폭발 → 큐 스케줄링 문제

### 옵션 3: Witness-Guided Search 🎯
- **장점**: 근본 해결 + 연구 기여
- **단점**: KLEE 수정 필요
- **기여**: "D→U Harness-Aware Witness-Guided Concolic"

## 다음 단계
1. witness_to_seed.py 스크립트 구현
2. CVE-2023-1729 검증
3. 다른 CVE들에 자동 적용
4. (선택) KLEE witness-guided search 구현

## 연구 정당성
- ❌ "버그 조건 사전 지식 필요" → 틀림
- ✅ "하네스 witness 활용" → 맞음
- ✅ "D→U 특화 자동화" → 기여
