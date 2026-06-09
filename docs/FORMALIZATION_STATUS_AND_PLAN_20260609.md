# 형식화 상태 점검 + 계획 (2026-06-09)

> **갱신 (2026-06-09, audit 후)**: 논문 수치 전수 audit 완료 —
> `PAPER_NUMERIC_AUDIT_20260609.md`. 값 불일치 1건(D7 stage 3 shifted pair) 수정
> 완료, 게이트 green 유지. 1단계(H1a)의 세부 작업 순서는 audit 문서 §7의 확정판
> (hdesc → active-set → recurrence 인스턴스 → full-carrier rank → 조립)을 따른다.

방법: `scripts/check_evenv11_progress.sh` 실행(풀빌드 포함) + Main/구조 모듈 직접
판독 + git 상태 확인으로 **검증된 사실**만 기록하고, 그 위에 닫힘 계획을 세운다.

## 1. 검증된 현재 상태 (2026-06-09 실행)

- **게이트: passed.** `lake build EvenV11` green (8407 jobs), axiom/admit 없음,
  structural native_decide 없음.
- **열린 홀 = 정확히 4개** (`Main.lean`의 `assume_* := sorry`):

  | 홀 | Main 위치 | 내용 |
  |---|---|---|
  | H1a | `Main.lean:57` | `TerminalA2CarrierCyclicityFamily` (모든 짝수 m≥4, F_i 단일 m²-cycle) |
  | H1b | `Main.lean:66` | `Nonempty TerminalA2RootFlatRealizationFamily` (root-flat realization, 명시적 `sectionEquiv`) |
  | H5 | `Main.lean:424` | `FinalOddHighModulusTargetPromotion` (anchors + high-even growth) |
  | H6 | `Main.lean:427` | `FinalOddEndpointPhaseProductTargetPromotion` (endpoint successor b↦2b+1) |

- H2/H3/H4는 finite witness(native_decide: `LowD5M4Finite`(Fin 256)·
  `LowD7M4Finite`(Fin 4096)·`LowD7M6Finite`(Fin 46656))로 **닫힌 상태 유지**.
  인벤토리 검사 통과.
- H1a 배관은 `CURRENT_STATE_GROUND_TRUTH_20260608.md`의 2026-06-09 항목까지
  코드와 일치함을 확인: no-collision은 `Even m ∧ 6 ≤ m`에서 완료
  (`endpointPoint_injective_of_even_six_le`), recurrence는 paper-faithful bridge
  form으로 수정됐고, `terminalCompressedEndpointReturn_endpointDescSucc`가 닫혀
  남은 rank-step 의무는 descriptor table equality 하나로 축소됨.
- **미커밋 작업 多**: 수정 17파일(+1160/−280) + 신규 8파일
  (`LowD7M6Finite.lean` 32MB, `LowD7M4Finite.lean` 1.5MB,
  `TerminalA2EndpointRank.lean` 144KB 포함). 현재 브랜치
  `route-e-v3-6-20260506`.

## 2. 계획 (우선순위 순)

### 0단계 — 체크포인트 커밋 (즉시, 위험 관리)

게이트 green인 지금 상태를 커밋한다. 6/8–6/9 작업(endpoint no-collision 완료,
descriptor successor handoff, recurrence interface 수정, finite witness 복원)이
전부 working tree에만 있다. 32MB/1.5MB witness 파일은 이미 같은 성격의 파일이
저장소에 있던 전례(복원물)이므로 그대로 커밋하되, clean-빌드 비용(M6 ~10분,
RSS ~4GB)은 CI 노트로 남긴다.

### 1단계 — H1a 닫기 (현재 최단 닫힘 단위)

남은 의무는 정확히 두 개로 축소돼 있다.

1. **Descriptor table equality** (rank-step):
   `endpointDescSucc c (endpointDesc m c n) = endpointDesc m c (endpointRankSucc m n)`
   — color c∈{0,1,2} × rank n∈Fin(2m) closed-form case 분석. 전부 산술/parity
   계산이므로 `omega`/`Fin` 보조정리 수준. 닫히면
   `compressedEndpoint_rank_step_of_desc_rank_step` →
   `compressedEndpointImageMap_singleCycle_of_even_six_le_desc_rank_step` 경유로
   `Even m ∧ 6 ≤ m`의 active endpoint image 단일순환이 자동.
2. **Interval-splice 승격**: active endpoint image 위 단일순환(`h_i = n_i ∘ η_i`)을
   전체 carrier `F_i`의 m²-cycle로 올리는 lemma (논문 `lem:terminal-cyclicity`의
   splice 부분). `Shared/MasterReturn`·`SwitchCalculus`의 packet/flag-splice
   판정기를 재사용할 수 있는지 먼저 감사하고, 안 되면 active interval 전용
   splice lemma를 신설.
3. **조립**: m=4 finite base(`terminalA2M4FiniteCyclicity`) + m≥6 generic(1+2)을
   합쳐 `TerminalA2CarrierCyclicityFamily` 구성 → `Main.lean:57` sorry 제거.
   sorry 4→3.

### 2단계 — H1b 닫기 (H1a와 배관 공유)

`TerminalA2RootFlatRealizationFamily`: 모든 짝수 m≥4에 대한 explicit
`sectionEquiv : TerminalQ m ≃ RootState m` + color translation. pointwise
interface(`TerminalA2RootFlatRealizationAt`)와 m=4 bridge
(`D3TerminalA2M4Bridge`, `terminalA2M4RealizationAt_of_physical`)는 준비돼 있으므로,
common section 구성을 m-parametric으로 일반화하는 것이 핵심
(요청 A-realization). 닫히면 closed adapter
`cycleDataFamily_of_carrierCyclicity_and_realization`이 H1 전체를 종결. sorry 3→2.

### 3단계 — H5 닫기 (요청 C + D, 섹션 단위 작업)

1. **C (finite anchors, `thm:finite-anchors`)**: D5·D7 coforest-splice anchor의
   marked 분해 + endpoint reserve. closing-primitivity 표(`D5D7SeedTables`)·
   reserve는 포팅 완료이므로, 이들로부터 anchor 분해 단일순환을 구성.
2. **D (high-even growth)**: anchor → 모든 high-even target (d, odd m>d)으로의
   2좌표 성장 사슬(7→9→…). C 완료 후 착수.
3. 엔진 `run` 구성에 연결 → `Main.lean:424` 제거. sorry 2→1.

### 4단계 — H6 닫기 (요청 E)

`prop:endpoint-successor`: marked `RHD(b,·)` → `RHD(2b+1,·)` endpoint 확장
(phase-product). promotion 타입·bridge는 sorry-free로 준비됨. 구성만 남음 →
`Main.lean:427` 제거. **sorry 0 도달.**

### 5단계 — 선택적 장기 목표 (sorry 0 이후)

- **요청 B(ribbon realization)** 부활: H2/H3/H4를 native_decide-free structural
  증명으로 교체해 axiom 위생을 `[propext, Classical.choice, Quot.sound]`로 회복.
- V28Hard 계층의 `TwoRailRelayRealization`/`TerminalA2ParametricSolution`/
  `HardPromotionEngines` 구성(현재 main 경로에는 불필요).

## 3. 순서 근거

H1a는 closed-form equality 한 개 + splice lemma까지 축소된 **현재 최단 닫힘
단위**이고, H1b는 H1a와 같은 A2 배관을 공유한다. H5/H6은 논문 섹션 전체를
parametric하게 옮기는 큰 작업이라 뒤에 둔다. 각 단계 종료마다
`scripts/check_evenv11_progress.sh` green을 게이트로 유지하고 체크포인트 커밋한다.
