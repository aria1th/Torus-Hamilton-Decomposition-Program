# P3 (cut-splice) 종이검증 결과

작성일: 2026-06-03. 대상: 논문 §3(switching ribbons) + §6(tree splicing in type A,
`high_even_seed_realization.tex`). 목적: cut-splice가 H2·H3·H4·H6를 닫기에 충분한지,
§6 coforest flag-splicing(P6)까지 필요한지, 체인이 건전한지 확정.

## 1. 단일순환 생성 체인 (P3 → P6 → P1)

finite anchor(H3·H4)·high-modulus(H5)의 단일순환은 다음으로 환원된다:

| 단계 | 논문 보조정리 | 역할 |
|---|---|---|
| **P3-atomic** | Lemma 3.5 `lem:cut-splice` | 순열을 cut tail에서 잘라 π로 재연결 → 순환구조 = π |
| **P3-core** | Lemma 6.13 `lem:one-step-packet-splice` | **유한 abelian 군에서 q개 coset-cycle을 하나로 병합** |
| **P6** | Lemma 6.16 `lem:flag-splicing-criterion` | flag `H_0≤…≤H_r`를 따라 one-step을 귀납 적용 |
| — | Lemma 6.17 `lem:forest-return-cyclicity` | `H_0=0`(싱글톤)에서 시작 → forest quotient에서 단일순환 |
| **P1** | Lemma 2.4 `lem:unit-carry` + 6.21 `lem:seed-unit-carry-lift` | forest-quotient cycle을 full root-flat Hamilton return으로 lift (carry ±1) |

## 2. 핵심 보조정리 = `one-step-packet-splice` (P3-core)

> **(Lemma 6.13)** 유한 abelian 군 `G`, `H ≤ G`, `v`의 `H` mod 위수 `q`. return
> 순열 `R`이 각 `H`-coset에서 단일순환. 고정 `H+⟨v⟩`-coset 안에서
> `C_j = g+jv+H` (`j∈Z/q`), cut tail `a_j∈C_j`, old head `h_j=R(a_j)∈C_j`.
> simultaneous cut-splice가 각 `a_j`의 나가는 변을 `a_j→h_{j+1}`로 바꾸면,
> 수정된 return은 `g+H+⟨v⟩`에서 단일순환. 모든 `H+⟨v⟩`-coset에서 독립적으로 성립.

**이것이 형식화의 본체다.** 이유:
- **구성-무관(construction-agnostic)**: 트리·coforest·anchor 표를 일절 언급하지 않음.
  순수하게 유한 abelian 군 + 순열 cycle 조합론. → `Shared/SwitchCalculus.lean`에
  anchor 데이터와 독립적으로 형식화 가능.
- **증명 건전성(검증 완료)**: 각 `C_j`는 단일 `R`-cycle(가정). `a_j`의 나가는 변
  `a_j→h_j`를 자르면 `C_j`-cycle이 head `h_j`…tail `a_j`의 구간으로 열림. 새 변
  `a_j→h_{j+1}=R(a_{j+1})`은 다음 구간의 head로 연결. `C_0→C_1→…→C_{q-1}→C_0`로
  q개 구간이 하나의 cycle로 이어짐. ✔ (Lemma 3.5의 coset 특수화.)

## 3. P6 = `flag-splicing-criterion` — one-step 위의 값싼 귀납

> **(Lemma 6.16)** laminar flag `0=H_0≤…≤H_r≤G`. 초기 return이 각 `H_0`-coset에서
> 단일순환. flag 순서로 국소 스위치 적용 → step `s` 후 각 `H_s`-coset에서 단일순환.
> 특히 전체 후 각 `H_r`-coset에서 단일순환.

증명 = `s`에 대한 귀납, 각 step이 `one-step-packet-splice` 1회 (triple row는 2회,
Lemma 6.14). laminarity는 support 분리(중첩/비교차)로 step들이 가환임을 보장.
**별도의 어려운 정리가 아니라 짧은 귀납.** P3-core만 있으면 거의 따라온다.

## 4. 판정

1. **P3 (cut-splice / one-step-packet-splice)가 핵심 레버다.** §3 intro가 명시하듯
   cut-splice는 "terminal block, high-even anchors, endpoint construction" 모두가 사용
   → **H2·H3·H4·H6 공통 도구.**
2. **P6 (flag induction)는 H3·H4·H5(다단계 two-rail anchor + growth)에 추가로 필요**,
   단 P3-core 위의 값싼 귀납.
3. **체인은 건전하다(gap 없음).** one-step 병합 논증과 flag 귀납을 직접 검증.
   unit-carry lift도 `closed-one-isolate-tree`(det=±1) → carry `mA±1` → unit, 건전.
4. **추상층(P3/P6)은 anchor 데이터와 완전 분리** → 더러운 표와 무관하게 먼저 형식화
   가능. anchor-specific 작업(D5/D7 표가 가정을 만족함)은 `rooted-coforest-completions`
   + `FiniteAudit`의 decide층(부분 완료)으로 분리됨.

## 5. 형식화 타깃 (다음 단계: P3 형식화)

신규 `Shared/SwitchCalculus.lean`. mathlib `Equiv.Perm.IsCycleOn s`(부분집합 위
단일순환)가 정확한 도구.

```lean
-- P3-atomic: Lemma 3.5 (선택적; one-step을 직접 증명하면 생략 가능)
-- P3-core: Lemma 6.13
theorem oneStepPacketSplice
    {α : Type*} [Fintype α] [DecidableEq α]
    {q : ℕ} (R R' : Equiv.Perm α)
    (C : Fin q → Set α)                       -- q개 이전 coset (서로소)
    (a h : Fin q → α)
    (hCell  : ∀ j, a j ∈ C j ∧ h j ∈ C j)
    (hHead  : ∀ j, R (a j) = h j)
    (hCyc   : ∀ j, R.IsCycleOn (C j))         -- 각 coset 단일순환
    (hSplice: ∀ j, R' (a j) = h (j + 1))      -- 재연결
    (hRest  : ∀ x, (∀ j, x ≠ a j) → R' x = R x) -- a_j 외 불변
    : R'.IsCycleOn (⋃ j, C j)

-- P6: Lemma 6.16 — 위 step의 flag 귀납
theorem flagSplicingCriterion
    {α : Type*} [Fintype α] [DecidableEq α]
    (steps : List (…))                        -- 각 step의 cut 데이터
    (hInit : R₀.IsCycleOn (각 H_0-coset))
    … : Rfinal.IsCycleOn (각 H_r-coset)
```

이미 존재하는 자산과 결합:
- **P1** `UnitCarry.rankUnitCarrySingleCycle` (carry 합 unit → skew 단일순환) — 보유.
- **det=±1** `lem:closed-one-isolate-tree` — type-A 트리 + closing edge가 Z-basis.
  `EvenV11/FiniteAudit`의 Bareiss `primitiveDetBool`이 이미 구체 표를 decide로 확인.
- **`IsCycleOn` → `IsSingleCycleMap`** 다리 (set = 전체일 때) 한 줄.

## 6. 형식화 순서 (P3 → 첫 hole)
1. `SwitchCalculus.oneStepPacketSplice` (본체) → `flagSplicingCriterion` (귀납).
2. `forestReturnCyclicity`: `H_0=0`에서 시작하는 wrapper.
3. 가장 단순한 anchor부터 인스턴스화 — **D7(4)=H3** 권장(two-rail, 4096; D7(6)보다
   modulus 작아 표 검증 가벼움). `rooted-coforest-completions` 가정을 D7 표로 충족 →
   forest cycle → P1 lift → `FinalRootFlatTorusModel 7 4` → `assume_lowD7M4` 교체.
4. 같은 틀로 H4(D7(6)), H5(high-modulus). H2(D5(4))·H6(endpoint)는 cut-splice를
   공유하되 folded/endpoint 경로 → 별도 인스턴스화.

**다음 작업: `Shared/SwitchCalculus.lean`에 `oneStepPacketSplice` 형식화 착수.**
