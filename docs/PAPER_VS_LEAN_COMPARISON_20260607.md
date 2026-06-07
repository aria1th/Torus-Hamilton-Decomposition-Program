# 논문 수학 vs 현재 Lean 구현 — 정밀 비교 (2026-06-07)

v28 논문(`even_modulus_directed_tori.tex`)의 증명 구조와 현재 Lean(`EvenV11`)을
1:1 대조. 결론 먼저: **논문의 induction 골격과 두 cyclicity 엔진은 Lean에서
sorry-free로 증명돼 있고, 남은 6홀은 정확히 induction의 per-range 수학 입력이다.**

## 0. 최상위 구조

논문 `thm:simultaneous-induction` (= `thm:even-main`): 차원 `d`에 대한 강귀납.
`HD(d,m)`(d≥2, 짝수 m≥4) + 표식 `RHD(d,m)`(d≥4, 4≤m≤2d+1).

Lean: `EvenV11.Main.evenModulusToriAllDimensions`가 `evenCertificateChecklist`
(6 입력)을 `finalTargetCayley_from_d3AndLowRootFlatChecklist`로 조립. **이 조립
+ 아래 엔진 전부 sorry-free** (gate: sorry는 Main의 6 `assume_*` 뿐).

## 1. Lean에서 이미 증명된 것 = 논문의 "기계"

| 논문 | 명제 | Lean | 상태 |
|---|---|---|---|
| root-flat 환원 | `prop:RF-criterion` (Latin schedule ⟺ first-return 단일순환) | `Shared/RootFlat.lean` | ✅ |
| cut-splice/ribbon | `switching_ribbons.tex` (partial-exchange, cut-splice, ribbon) | `Shared/SwitchCalculus.lean`, `MasterReturn.lean` | ✅ |
| unit-carry lift | `lem:unit-carry` (carry가 unit ⟺ skew 단일순환) | `Shared/UnitCarry.lean`, `WordSkew.lean` (Bundle B) | ✅ |
| phase-doubling | `thm:phase-doubling` (짝수차원 d=2a) | `PhaseDoubling.lean` + bridge | ✅ |
| **D2 base** | `prop:D2-antidiagonal` | `Shared/D2Seed.lean` + **`D2AntiDiagonal.lean`**(검증 포팅) | ✅ |
| simultaneous induction | `thm:simultaneous-induction` 골격 | `FinalInductionBridge` 외 Final*Bridge 조립 | ✅ |
| D5(4) 5색 단일순환 | `lem:D54-active-core`, `prop:D54-reset`(순환부) | `LowD5M4Seed.lean` | ✅ |
| D5/D7 부록 표 | `check_closing_signs`/`support`/`reserve` | `D5D7SeedTables.lean`(검증 포팅) | ✅ |

→ 논문이 개발하는 **두 cyclicity 원리(coforest splice = cut-splice, unit carry)와
차원 결합(phase-doubling)·전체 귀납**이 Lean에 다 있다. 즉 "골격과 연장(engine)"은
완성.

## 2. 6홀 = 논문의 per-range 핵심 구성 (남은 수학)

각 홀은 §1 엔진으로 환원돼 있고, 남은 것은 논문의 특정 cyclicity/realization 증명.

| 홀 | 논문 명제 | 논문이 하는 것 | Lean 현재 | 남은 수학 |
|---|---|---|---|---|
| **H1** D3 | `prop:D3-base` ← `lem:terminal-cyclicity` | 터미널 A₂ `F₀,F₁,F₂`가 모든 짝수 m에서 m²-cycle (endpoint-recurrence `Aʳ/Bʳ`) | `TerminalA2LowMod`(carrier 정의); m∈{4..12} Python 검증 | **parametric terminal-cyclicity** (Lean 증명) |
| **H2** D5(4) | `prop:D54-reset` (= `RHD(5,4)`) | 5색 reset return 단일순환 + layer-row 실현 | 단일순환 **완료**(Seed); ribbon 인터페이스 준비 | **t-의존 dir 실현**(run-collapse `e`, RF2) |
| **H3/H4** D7(4),(6) | `prop:rank-three-endpoint-bases` (`RHD(7,4)`,`RHD(7,6)`) | folded rank-3 endpoint; 재사용 plus-lane word `F₁F₀²`/`F₁²F₀³` 순환 + 7-site 실현 | 표 데이터 **완료**(D5D7SeedTables: forest/primitivity/support/reserve) | **folded-port 실현** + 재사용 word 순환 |
| **H5** high-even | `cor:odd-high-even-closure` ← finite anchors(`thm:finite-anchors`) + growth(§high-even-growth) | D5/D7 coforest-splice anchor + 7→9 chain + 2좌표 growth | promotion 타입 + consumer + input bridge(sorry-free) | **anchor 구성 + growth** (입력 전체) |
| **H6** endpoint | `prop:endpoint-successor` (`b↦2b+1`) | endpoint 확장 단계 | promotion 타입 + bridge(sorry-free) | **endpoint successor 구성** |

## 3. Granularity 비대칭 (중요)

- **H1**: 단일 lemma (terminal-cyclicity). 가장 작고 가장 "Lean 친화적"(clean parametric).
- **H2/H3/H4**: 특정 유한 base. 단일순환/표는 끝, **realization**만 남음.
- **H5/H6**: **논문 한 섹션 전체**(high_even_growth 28KB + seed_realization 33KB;
  endpoint_successor 17KB). 가장 크고 parametric. Lean엔 promotion 타입·bridge만 있고
  실제 구성(입력)은 통째로 sorry.

## 4. 충실성 평가

- 현재 Lean 구조는 논문 architecture를 **충실히 미러링**: RF criterion 인터페이스 =
  논문 환원; 6홀 = 논문 base/step에 1:1; 엔진 = 논문 두 cyclicity 원리.
- pivot 이후 **죽은/중첩 경로(Route E, blob, tame paperReturn)는 archive**됨 →
  남은 spine은 논문 충실 + native_decide-free(축 `[propext, choice, Quot.sound]`).
- 검증으로 de-risk됨: D5(4) 단일순환(Seed)·terminal cyclicity 유한(m≤12)·D5/D7 표·
  D2 전체 — 모두 Lean kernel 또는 Python으로 확인.

## 5. 한 줄 결론

> 논문의 **귀납 골격 + 두 cyclicity 엔진 + phase-doubling + D2**는 Lean에서 완증.
> 남은 6홀은 논문의 **per-range cyclicity 구성**이며, 난도 순서는 대략
> H2(realization) ≈ H1(parametric terminal) < H3/H4(folded rank-3) < H5/H6(전체
> 고차 branch). H1–H4는 유한/구조 자산이 갖춰져 다음 표적으로 가장 적합.
