# 논문 table·검증근거 → Lean 충실 포팅: 진행 (2026-06-07)

목표: 논문의 table / `verify_rootflat_certificates.py`로 검증된 근거를 Lean에
충실히 구현, pseudocode 포팅.

## ✅ 완료: D2 anti-diagonal (`EvenV11/D2AntiDiagonal.lean`)

검증된 pseudocode(`verify_rootflat [E]`, `d2_antidiagonal_dir`)를 **완전 sorry-free**
Lean으로 포팅.

- `dir` (n=1, Fin 2): 색0 = 높이-0 layer에서 좌표 증가(dir 0)·그 외 no-op(dir 1);
  색1 = 상보 Latin. 논문 `root_flat_first_returns.tex` Prop D2-antidiagonal 충실 구현.
- RF1(`rowLatin`): row가 Equiv라 자동.
- RF2(`layerBijective`): dir이 w-무관 → `rootStep`이 translation이라 bijective.
- RF3(`returnsSingleCycle`): returnMap을 prefixMap 귀납으로 `+1`/`+(m-1)`로 계산,
  `Shared.zmod_add_single_cycle_of_unit`(단위 carry ⟹ 단일순환)로 마무리.
- 산출: `d2Certificate : FinalRootFlatTorusCertificate 2 m` (모든 m≥1).
- **축 검증**: `[propext, Classical.choice, Quot.sound]` — sorryAx·ofReduceBool 없음.

### 의의
**`RootFlatCycle.RootFlatCycleData` 인터페이스가 실제 `dir`로부터 sorry-free
certificate를 만든다는 것을 end-to-end 입증.** 즉 H1/H3/H4의 핸드오프
(`dir + RF1/RF2/RF3`)가 건전하고, 같은 RF1/RF2/RF3 증명 패턴으로 닫힌다는 것이
확인됨. (D2 base 자체는 `Shared.D2Seed`로 이미 닫혀 있어 hole은 아니며, 이 포팅은
인터페이스 검증·패턴 확립용.)

### 재사용 패턴 (홀에 그대로 적용)
1. `dir`을 t-의존 row-equiv로 정의(RF1 자동).
2. RF2: layer map = `rootStep (dir t w c)`; w-의존이면 bijection 증명, 아니면 translation.
3. RF3: returnMap을 prefixMap 귀납으로 계산 → unit-carry 또는 ribbon 켤레.

## 포팅 로드맵 — 무엇이 지금 포팅 가능한가

| 대상 | 검증근거 | 포팅 난이도 |
|---|---|---|
| D2 base | `[E]` ✅ | **완료** |
| 논문 finite table (D5/D7 forest, closing `\|det\|=1`, support rank, W4/W6) | `verify_finite_checks.py` ✅ | 중 (유한, plain `decide`) — 다음 후보 |
| H1 terminal F_i 유한순환 (m=4..12) | `[B]` ✅ | 일부 Seed에 있음 |
| H1/H2/H3/H4 의 **dir 실현**(run-collapse/ribbon/two-rail) | 추상 return은 검증됨 | **하드 (run-collapse 수학)** |

→ **지금 sorry-free 포팅 가능한 것**: 위 "유한 table" (논문 부록 표를 `decide`-검증
데이터로) — 다음 포팅 대상. **dir 실현**은 hard 수학(협업상 사용자 영역).

## ✅ 완료: D5/D7 부록 table 포팅 (`EvenV11/D5D7SeedTables.lean`)

`verify_finite_checks.py`의 D5/D7 검증 데이터를 **완전 sorry-free·native_decide-free**
Lean으로 포팅:

- **closing-column primitivity** (`check_closing_signs`): 각 색의 forest+closing 행렬
  `M`(isolate basis)과 명시 정수 역행렬 `N`을 포팅, `M*N=1`을 entrywise 증명 →
  `IsUnit M.det`(unimodular = `|det|=1` = unit-carry/RF3 basis). D5 5색 + D7 7색 전부.
  - `d5_closing_primitive`, `d7_closing_primitive`. 축: `[propext, Classical.choice, Quot.sound]`.
- **support-row ranks** (`check_support_rows`): `|support| = d-stage-1`, `active ⊆ support`.
  `d5_support_valid`, `d7_support_valid` (by `decide`). 축: `[propext, Quot.sound]`.
- **reserve-point plane equations** (`check_reserve_points`): D5(mod 6) `x₃=2`, `x₁+x₂+x₄=5`;
  D7(mod 8) `x₁=1,x₄=5,x₂+x₆=6,x₃+x₅=5`. `d5_reserve_valid`, `d7_reserve_valid`
  (`fin_cases` + `decide`).

논문 원본 스크립트도 독립 재실행 통과(`verify_finite_checks.py` → "All finite arithmetic
checks passed"). 즉 **논문 부록 D5/D7 table = 올바른 검증 데이터**임이 Lean kernel과
Python 양쪽에서 확인됨. umbrella 통합, 전체 빌드 green.

## ✅ 완료: H2 direct-row ribbon handoff (`EvenV11/LowD5M4RibbonInterface.lean`)

`V28Hard/D5M4H2Skeleton`에서 필요했던 archive 의존 없는 핵심을 active spine으로
승격하고, archive-dependent skeleton 자체는 `archive/EvenV11/V28Hard/`로 분리:

- `PhysicalLayerRows`: 논문 §11의 네 physical layer row를 직접 받는 row-equiv 인터페이스.
- `PhysicalRowsRibbonCollapseInput`: RF2 + wild `e` + pointwise `returnRealization`이면
  `ResetPortH2RowEquivRibbonRealizationData`를 즉시 생성.
- `PhysicalRowsMapConjRibbonCollapseInput`: 더 자연스러운 map-level 등식
  `returnMap = e ∘ fullReturn ∘ e.symm`에서 H2 handoff로 변환.
- `PhysicalSingletonSwitchLayerData`: Table D54-reset-ports의 local two-entry exchange가
  RF2를 주는 singleton-switch helper.

추가로 `LowD5M4Structural.returnRealization_of_returnMap_conj`를 추가해 map-level
conjugacy와 현재 H2 필드 방향을 연결했다. `lake build EvenV11.LowD5M4RibbonInterface`
및 `lake build EvenV11.V28Hard` 통과.

추가 cleanup: `LowD5M4TameObstruction`을 추가해 tame `seedRootEquiv`로
`paperReturn`을 직접 네 layer root-step schedule로 실현하는 경로가 불가능함을 Lean에서
닫았다. 따라서 H2의 남은 입력은 반드시 wild `e`를 포함한
`PhysicalRowsSingletonSwitchMapConjInput`이어야 한다.

## 남은 것
- (선택) terminal folded words W4/W6 m²-cycle 포팅(터미널 appendix, decide).
- 홀의 **dir 실현**(run-collapse/ribbon/two-rail)은 hard 수학(협업상 사용자);
  포팅된 table이 그 RF3 unit-carry 근거를 Lean에 고정해 둠. verify_rootflat로 후보 즉시 검증.
