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

---

# 2026-11-05 추가 분석 (CVE-2023-1729)

D→U: **downstream = OpenImageIO(RawInput)**, **upstream = LibRaw**, **sink = `raw2image.cpp:492`(업스트림)**.
네이티브 PoC(`poc/crash_dcraw_half`, 39891B)는 `dcraw_half`로 **LibRaw 단독**에서 재현됨 — CVE는 순수 업스트림 버그.

## A. 확정된 일반 교정 — `demote()`의 `llvm.global_ctors` 파괴
- **증상**: 업스트림(LibRaw) 정적 테이블 `tagtype_dataunit_bytes`(class `libraw_static_table_t`)가 0으로 남아
  `tiff_get`의 외부 `fseek`(`utils_dcraw.cpp:329`)가 안 일어나고 차원이 오파싱됨.
- **근본 원인**: `model/src/Close.cpp`의 `demote(mod, have)`가 D/U 양쪽에 정의된 심볼을 선언으로 강등할 때,
  **appending-linkage 전역 `llvm.global_ctors`의 initializer까지 비움** → 그 배열이 유일하게 참조하던
  내부 C++ 동적초기화 함수(`_GLOBAL__sub_I_wblists.cpp` → `tagtype_dataunit_bytes` 생성)가 링커에서 드롭됨.
- **교정**: `demote()`에서 `hasAppendingLinkage()` 전역은 강등하지 않음 (`Close.cpp:211-231`).
- **일반성**: CVE 한정 아님 — **D/U 양쪽에 `global_ctors`/`global_dtors`/`llvm.used`가 있는 모든 페어링**에 적용.
- **검증(교정 후)**: `_GLOBAL__sub_I_wblists` 복원(3 refs)·ctor 정의됨, 정적 테이블 초기화,
  `tiff_get` 외부 seek 실행(L329=5968), 가짜 IOSPACE throw(`utils_dcraw.cpp:322`) 소멸.

## B. 남은 sink 미도달 = KLEE **해석 벽**(모델 버그 아님)
- **증상**: seed-only(`--concolic-data-concrete`) 재생이 **~27.5M instr에서 동결**, `apply_tiff`(차원)·sink 도달 전에 멈춤.
- **증거**:
  - 세 실행(`--max-time=1800s` / `3600s` / `--kdalloc=true --max-memory=14000`) **모두 동일 ~27.5M에서 멈춤** → 시간·메모리 무관.
  - `run.stats`: `SolverTime=0`, `SolverQueries=0` → solver 무관(경로 사실상 concrete).
  - 14GB 실행에서 Instructions가 90초 완전 동결. 비용 프런티어:
    `exif_parser_cb → pvt::exif_tagmap_ref → TagMap 생성자 → tsl::robin_map 삽입 + ustring::ustring(≈4.2M)`.
- **해석**: 업스트림(LibRaw) TIFF/EXIF 파싱이 per-IFD-entry로 **downstream 콜백 `exif_parser_cb`(OIIO, U→D 콜백)** 호출 →
  첫 호출이 OIIO EXIF `TagMap`(수백 태그 이름 ustring interning + robin_map)을 **일회성 생성**.
  이 계산은 **입력-비의존**인데 KLEE가 명령어 단위로 해석하다 동결.
  로그의 `unsupported intrinsic llvm.x86.sse2.psad.bw/pmadd.wd/movmsk.ps`가 robin_map/ustring 해싱 경로에 있어,
  미지원 intrinsic의 undef가 탐침 루프를 비정상화했을 가능성(단순 "느림"이 아니라 "동결"인 이유).
- **soundness**: `exif_parser_cb`는 메타데이터 전용(`spec->attribute`)이라 업스트림 차원/디코드 경로·sink와 무관.
  생략은 가능하나 OIIO 특정 **밴드에이드**라 일반화 아님.

## C. `--optimize`는 탈락
- **KLEE 크래시**: `SelectInst::init: "Invalid operands for select"` 어서션(optimize 패스 중), seeding 전 사망.
- 설령 안 죽어도 optimize는 비트코드를 변형 → `surfaces.json`/`reach/`/`pins.yaml` 등 **원본 모듈 기준 정적 산출물과 1:1 대응이 깨짐**.
  런타임 바인딩(sink 마커 `raw2image.cpp:492`, named 시드 `"input"`)은 live라 보존되지만, **권위 측정 파이프라인으론 부적합**.

## D. 일반 해법 방향 (artifact 보존, 향후)
- **원리**: 심볼릭 입력에서 유래하지 않은 계산은 심볼릭 해석에서 제외(concretize / 모델 / 초기화 상태 주입).
  **모델·env 레이어**에 두어 비트코드·정적 산출물 대응을 유지.
- **후보**:
  1. 테인트 기반 concretize — 입력 테인트 없는 호출을 native 브리지로(KLEE external-call은 concrete 메모리 쓰기 왕복 가능).
  2. 정적 init 사전 concrete 실행 후 **post-init 스냅샷**에서 시드 경로 시작.
  3. 미지원 SSE intrinsic의 올바른 lowering(동결 원인이 intrinsic undef면 직접 해소).
- 현재셋에서 이 벽에 걸리는 건 **1729(유일 OIIO)**뿐; hidden OIIO/무거운 downstream 케이스엔 공통 적용될 일반 문제.
