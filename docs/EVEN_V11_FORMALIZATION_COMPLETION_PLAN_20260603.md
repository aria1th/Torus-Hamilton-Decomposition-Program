# EvenV11 형식화 완성 계획 + 증명 가치가 높은 보조정리 목록

작성일: 2026-06-03
대상 원고: `even_modulus_directed_tori_v28_finite_audit` (SangHyun Park,
"Hamilton decompositions of positive-basis directed tori for even moduli")
대상 형식화: `Torus-Hamilton-Decomposition-Program/EvenV11/`

업데이트(2026-06-04): 이 문서는 초기 완성 계획이다. 현재 H3 `D7(4)`는 generated
finite root-flat certificate로 닫혔다. H2 `D5(4)`와 H4 `D7(6)`의 generated
witnesses(`lake build EvenV11.LowD5M4Finite`, `lake build EvenV11.LowD7M6Finite`)는
kernel 검증 가능한 archive/명시 target으로 보존하지만, 논문 §11 및 Appendix A/B
구조 포팅으로 대체하기 위해 기본 `EvenV11/Main.lean` proof spine에서는 open
input으로 두었다. 따라서 기본 spine의 실제 `sorry`는 H1/H2/H4/H5/H6 다섯 개다.

---

## 0. 현재 형식화 상태 (감사 요약)

- 초기 `Status.lean` 경로는 `sorry`/`axiom`/`native_decide` 없이 **빌드되는 환원
  골격(reduction skeleton)**처럼 보였다. (olean 61개 존재, closure 게이트 통과.)
- 그러나 그 경로의 최종 정리
  `finalTargetCayley_from_d3AndLowRootFlatChecklist_closed` 는 **조건부**다:
  가정 `checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat` 을
  요구하며, 이 구조를 **구성하는 항(term)이 코드 전체에 없다**.
- 현재 authoritative spine은 `EvenV11/Main.lean`이며, 남은 수학적 입력을
  `assume_* := sorry`로 노출한다. H3만 닫혔고 H1/H2/H4/H5/H6는 open input이다.
- 즉 논문 §2 환원(Prop 2.1 = `finalRootFlatCayley_of_certificate`)과 유한 산술
  audit(`FiniteAudit`)은 실증되었으나, **논문의 구성(§5–§11) 전부가
  certificate 가정으로 남아 미증명**이다.
- 미해소 leaf 가정:

  | Lean leaf | 논문 | root-flat 크기 |
  |---|---|---|
  | `FinalRootFlatTorusCertificate 2 m` (D2 base) | Prop 2.5 | `m` |
  | `FinalD3EvenRootFlatCertificateFamily` | §5 + D3 seed | `m²` |
  | `FinalLowD5M4RootFlatCertificateFamily` | §11 D5(4) | `4⁴=256` |
  | `FinalLowD7M4RootFlatCertificateFamily` | App. A/B | `4⁶=4096` |
  | `FinalLowD7M6RootFlatCertificateFamily` | App. A/B | `6⁶=46656` |
  | `FinalOddHighModulusTargetPromotion` | §6–8 | 일반 |
  | `FinalOddEndpointPhaseProductTargetPromotion` | §9–10 | 일반 |

- 모든 leaf의 공통 의무는 `Shared.RootFlatSchedule` 데이터 +
  `FinalRootFlatTorusModel`의 4필드:
  `rowLatin`, `layerBijective`, `returnsSingleCycle`, `stepConjugacy`.
  이 중 **`returnsSingleCycle`(단일순환)가 유일한 병목**이다.

---

## 1. 완성 계획 (Phase 0–4)

### Phase 0 — 환경 (0.5일, 위험 낮음)
mathlib/deps olean 7940개가 이미 존재 → `cache get` 불필요. toolchain만 설치:
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source ~/.elan/env
elan toolchain install leanprover/lean4:v4.30.0-rc2
lake build EvenV11 && bash scripts/check_evenv11_progress.sh
```

### Phase 1 — 인벤토리 + D2 수직 슬라이스 (1–2일, 위험 낮음, 가장 중요)
1. 각 `EvenV11/*.lean`을 (R) 실질 변환·단일순환 보조정리 / (B) 가정 통과 bridge
   로 분류 → 남은 작업량 확정.
2. D2 base를 끝까지 구성(Prop 2.5). 파이프라인 전체(데이터→3속성→stepConjugacy
   →bridge 연결) 검증. 이후 모든 leaf의 템플릿.

### Phase 2 — 유한 예외 (1–3주, 위험 높음)
D5(4), D7(4), D7(6). 단일순환은 **브루트포스 `decide` 금지**(46656개 + native_decide
불가) → §2.4의 구조적 word/rank certificate(`FiniteCertificate.lean`)로 도출.
`FiniteAuditBridge.v28FiniteInputBridgeAudit`가 이미 folded word 단일순환을
`decide`로 확보 → 이를 `returnMap`에 잇는 것이 간극.

### Phase 3 — 귀납 단계 (3–6주, 위험 매우 높음, 논문 본체)
D3 even 패밀리(§5), type-A coforest splice(§6), high-even growth(§8),
endpoint successor(§9–10), phase doubling. 각 항목 = "schedule 변환 + 3속성
보존 정리".

### Phase 4 — 조립 + 게이트 해제 (2–4일, 위험 낮음)
checklist를 항으로 구성 → 무가정 `evenModulusDirectedToriHamiltonDecomposition`
서술. closure 게이트의 `deferred_decl_pattern`(메인 정리 이름 금지)을 해제.
`#print axioms`로 커스텀 axiom 0 확인.

---

## 2. 추가로 증명하면 가치가 큰 보조정리 (제안)

아래는 **Lean 형식화 상태와 무관하게, 논문 + 진술만으로 착수 가능한** 문제들이다.
정렬 기준: 깔끔함(self-contained) × 재사용성 × 리뷰 대응력.

리뷰 `paper-reviews/C.md`의 1순위 반론은
*"local switches가 실제로 layer bijectivity(RF2)를 보존하는가?"* 였다.
Tier 1은 정확히 그 반론을 정리(theorem) 형태로 닫는다.

---

### Tier 1 — 일반 비교-스위치 산술 (지금 바로 가능, 최고 레버리지)

이 다섯은 구성 데이터와 무관한 순수 유한 조합론이며, 합치면 README가 원하던
"재사용 certificate-calculus"가 된다. 권장 위치: `Shared/SwitchCalculus.lean`(신규).

**P1. 단위-carry skew product (Lemma 2.4, iff 형)**
> `B`가 유한집합 `X`의 단일순환, `γ : X → ZMod m`, `T(x,r)=(Bx, r+γ(x))`.
> 그러면 `T`가 `X × ZMod m`에서 단일순환 ⟺ `∑_{x∈X} γ(x)`가 `m`의 가역원.
```lean
theorem skewProduct_singleCycle_iff
    {X : Type*} [Fintype X] {m : ℕ} [NeZero m]
    {B : X → X} (hB : IsSingleCycleMap B) (γ : X → ZMod m) :
    IsSingleCycleMap (fun p : X × ZMod m => (B p.1, p.2 + γ p.1))
      ↔ IsUnit (∑ x, γ x)
```
- 가치: 논문의 carry 불변량 전체(terminal determinant carry / one-point carry /
  completion carry)를 하나로 통일. `Shared.RootFlat`에 `⟸` 방향은 이미 있음
  (`fullStep_singleCycle_of_return`) → **iff·일반형으로 승격**이 핵심.
- 난이도: 낮음. (orbit 길이 = `N · ord(Γ)` 계산.)
- Lean 상태(2026-06-03): rank-coordinate 형식은 완료.
  `Shared.skewProduct_zmod_additive_rank_single_cycle_iff_unit_sum` 및
  `EvenV11.UnitCarry.rankUnitCarrySingleCycle_iff`.

**P2. 부분 교환 판정 (Lemma 3.2) — RF2의 핵심**
> `T,R`가 유한집합 `X`의 순열, `U⊆X`.
> `T_U := (x∈U ? R x : T x)`, `R_U := (x∈U ? T x : R x)`.
> 그러면 `T_U,R_U`가 순열 ⟺ `T⁻¹R(U)=U`.
```lean
theorem partialExchange_bijective_iff
    {X : Type*} [Fintype X] [DecidableEq X]
    {T R : X → X} (hT : Function.Bijective T) (hR : Function.Bijective R)
    (U : Finset X) :
    Function.Bijective (fun x => if x ∈ U then R x else T x)
      ↔ U.image (fun x => (Equiv.ofBijective T hT).symm (R x)) = U
```
- 가치: **C.md 1순위 반론을 직접 닫는 정리.** 이후 모든 local substitution은
  "이것은 P2의 `T⁻¹R(U)=U`를 만족한다"만 보이면 RF2가 자동. 리뷰가 요구한
  4줄 표(`U, f,g, g⁻¹f(U)=U, ∴ bijective`)의 형식적 근거.
- 난이도: 낮음~중간. (`image(T_U)=T((X∖U)∪T⁻¹R(U))` 계산.)

**P3. Cut-splice 공식 (Lemma 3.5)**
> `P` 단일순환, `B`가 cut tail 집합, `H=P(B)`, `τ(h)`=`h`에서 `P` 반복해 처음
> 만나는 `B`의 점, `π(h)=P'(τ(h))`. 그러면 touched part의 `P'` 순환분해 =
> `π`의 순환분해. 특히 `π`가 `H`에서 단일순환 ⟹ `P'`이 touched part에서 단일순환.
- 가치: §6 coforest splice, §7 finite anchor의 단일순환 도출 엔진. 순열의
  cut-and-reconnect를 일반 명제로.
- 난이도: 중간. (interval cut 일대일 대응.)
- Lean 상태(2026-06-03): coset packet 특수형(P3-core) 완료.
  `Shared.SwitchCalculus.oneStepPacketSplice`,
  `Shared.SwitchCalculus.oneStepPacketSplice_singleCycleMap`.

**P4. Interlacing selector (Cor 3.7)**
> `C={c_j}_{j∈Z/L}` 가 한 `σ`-cycle, `s_{G,C}(c_j)=c_{j+a}`, `s_{H,C}(c_j)=c_{j+b}`.
> `gcd(a−1,L)=gcd(b+1,L)=1` ⟹ 스위치 후 두 return 모두 단일순환.
> 추가로 `L`이 `m`의 가역원이면 `C`는 unit selector.
- 가치: terminal A2·endpoint의 selector 조건을 한 줄 coprimality로. P3의 따름.
- 난이도: 중간. (splice map = 평행이동 `j↦j+a−1`.)

**P5. Ribbon 합성 (Lemma 3.9)**
> support-분리된 switching ribbon 유한족은 RF1/RF2를 보존하고, first-return에
> 대한 효과는 cut-splice 공식들의 순서곱이며, ribbon과 분리된 marked selector는
> 합성 후에도 marked.
- 가치: 모든 construction이 "이것은 P5의 ribbon이다"로 환원되는 합성 법칙.
  P2(RF2 보존) + P3(splice 효과) + 분리성(가환)으로 조립.
- 난이도: 중간. (분리성 → 가환 → 순서곱.)

> Tier 1의 P1–P5를 `Shared/SwitchCalculus.lean`로 독립 형식화하면, 그 자체로
> C.md가 요구한 구조정리화의 절반을 달성하고, Phase 2–3의 단일순환 증명이 전부
> 이 5개의 적용으로 환원된다.

---

### Tier 2 — 구조 spine 정리 (중간 난이도, 논문의 척추)

**P6. Type-A rooted coforest splice 정리 (§6)**
> type `A_{d−1}` rooted coforest splice flag는 비교-스위치 열을 결정하며, 그
> return-level 효과는 laminar quotient flag를 따라 coset cycle을 병합한다.
- 가치: README가 "standalone certificate-calculus로 분리하라"고 명시한 항목.
  `terminal fan`, `two-rail relay`를 이 정리의 작은 certificate로 격하.
- 의존: P3, P5 + descendant-cut의 laminar 성질.

**P7. 유한 anchor certificate 정리 (§7, Thm 7.1) — 리뷰가 요구한 형태**
> 다음으로 이루어진 표가 조건 C1–C5를 만족하면 marked high-even datum을 산출:
> (i) one-isolate color forest `F_c`, (ii) primitive closing edge `β_c` (sign ±1),
> (iii) splice row마다 rooted contracted support tree `T_{r,P,c}`.
- 가치: Appendix A/B의 표를 "어떤 certificate theorem의 입력"으로 정제(C.md
  핵심 권고). `FiniteAudit`의 `decide`-검증(primitive det, support row, reserve
  plane)이 정확히 C1–C5의 입력이 되도록 연결.
- 의존: P1(carry), P6(splice).

**P8. Terminal A2 six-turn 유일성 (§5) — 부정형→양의 특성화**
> 세 punctured line string의 국소 완성 중, (i) 각 `ℓ_i`-fiber가 정확히 두 active
> endpoint, (ii) `η_i(S_i)=S_i`, (iii) 유도 endpoint map이 index shift ±1로 두
> string을 교대 — 를 만족하는 것은 **여섯 boundary turn이 유일**하다.
- 가치: C.md가 지적한 "실패표 방어"를 양의 정리로. 구성의 심장(§5)을 정리화.
- 의존: P4(interlacing).

---

### Tier 3 — 구성별 certificate (구체 데이터, leaf 직접 대응)

각 항목은 `FinalRootFlatTorusModel` 인스턴스 1개. 위 Tier 1–2의 적용으로 단일순환
의무가 해소되면 나머지는 좌표 계산.

- **P9. D2 anti-diagonal base** (Prop 2.5) → `FinalRootFlatTorusCertificate 2 m`.
  P1 직접 적용(carry ±1). Phase 1 슬라이스.
- **P10. D5(4)/D7(4)/D7(6) 유한 anchor** → 세 `FinalLow…Family`.
  P7 + `FiniteAudit` 표. 단일순환은 P3/word-certificate.
- **P11. D5(4) parity reset** (§11, Lemma 11.1–11.3) → odd terminal reset
  `W=F₁F₂F₀`의 common-image 방정식 `R_a(c̃)=R_b(c̃)=I` 명시(C.md 필수수정).
- **P12. High-even growth 불변량 G_D** (§8) → `FinalOddHighModulusTargetPromotion`.
  > 모든 four-point 확장에서 inactive flag `H⁻`는, 공통 phase translate 후
  > boundary set `B_s`를 피하는 guide center의 incidence line으로 생성된다.
  이 귀납 불변량 + "생성집합이 `H⁻`를 span ⟹ `Θ(H⁻)=0`" (C.md 권고).
- **P13. Endpoint successor** (§10, Lemma 10.2–10.5) →
  `FinalOddEndpointPhaseProductTargetPromotion`. product exponent `1`, `m²−1≡−1`
  계산 + reset row common-image.

---

## 3. 의존 그래프 & 권장 순서

```
P2 (partial exchange, RF2)  ─┐
P1 (unit carry, iff)        ─┼─→ P5 (ribbon 합성) ─→ P6 (coforest splice) ─┐
P3 (cut-splice)             ─┘            │                                ├─→ P7 (anchor cert) ─→ P10
P3 ─→ P4 (interlacing) ─────────────────→ P8 (six-turn)                   │
P1 ─→ P9 (D2 base, 슬라이스)                                              P12,P13 (growth/endpoint)
```

권장: 완료된 **P1 rank-iff + P3-core** 위에서 **P2/P4/P5**와
**P6 flag-splicing**을 닫고, 그다음 P7+P10(유한), 마지막 P8/P12/P13.

## 4. 한 줄 결론
지금 가장 가치 있는 추가 증명은 **Tier 1(P1–P5)의 비교-스위치 산술을 독립
라이브러리로 형식화**하는 것이다. 이는 (a) C.md 1순위 반론을 정리로 닫고,
(b) Phase 2–3의 모든 단일순환 의무를 5개 일반정리의 적용으로 환원하며,
(c) 논문 자체의 구조정리화에도 직접 기여한다.

---

## 5. `decide` vs `native_decide` 경계 분석

closure 게이트는 `native_decide`를 **금지**한다(커널 외부 컴파일러 신뢰 = TCB 확대).
따라서 "어떤 유한 의무가 커널 `decide`로 닫히고, 어떤 것이 `native_decide`를
강제하는가"가 결정적이다. v28 "finite audit" 재구성은 정확히 이 경계를 의식해
이뤄진 것으로 보인다.

### 5.1 측정 결과: 모든 `decide`가 m²-fiber 이하
EvenV11의 `decide`/계산 `rfl`을 전수 census한 결과, **전체 root flat(`m^{d-1}`)을
점별로 도는 `decide`는 하나도 없다.** 단일순환은 항상 작은 terminal fiber
`TerminalQ m = ZMod m × ZMod m`(m=4→16, m=6→36) 위에서 **명시적 orbit + 국소
successor `decide`**로 증명되고, 나머지 차원은 구조적 lift로 올라간다.

| 계산 의무 | 대상 크기 | 기법 | 위치 |
|---|---|---|---|
| terminal orbit 전단사 | `Fin 16`/`Fin 36` | `decide` | `TerminalA2LowMod` |
| 국소 successor `orbit(i+1)=wordEval(orbit i)` | 16/36 검사 | `decide` | `TerminalA2LowMod` |
| D5(4) reset orbit (동일 기법) | `Fin 16` | `decide` | `D54Reset` |
| folded role nodup / code 리스트 | 7-원소 | `decide`/`rfl` | `FoldedSiteTrace` |
| forest closing 행렬식 primitive(±1) | `D×D` (≤7×7) | Bareiss + `decide` | `FiniteAudit` |
| support/reserve projection 분리 | `ZMod m` 투영 | `decide` | `FoldedReserveSeparation` |

핵심: **단일순환은 `IndexedOrbitCertificate` 패턴으로 증명된다** — orbit 순서를
손으로 제공(`terminalOrbit4 : Fin 16 → TerminalQ 4`)하고, "i번째에 word를 적용하면
i+1번째"라는 국소 관계만 `decide`(16/36회)로 확인한 뒤, `Fin N ≃ Q` 켤레로
`IsSingleCycleMap`을 구조적으로 도출. **orbit 폐포를 추상적으로 열거하지 않는다.**

### 5.2 세 가지 분류

**(K) 커널 `decide`로 닫힘 (게이트 준수, 그대로 유지)**
m² ≤ 36 fiber 검사, D×D ≤ 49 행렬식, 짧은 word(길이 ≤ 5), 작은 리스트/투영.
→ 커널 부담 미미(수백 회 환원). v28의 모든 유한 audit이 여기 속한다.

**(S) 반드시 구조적 (크기와 무관하게 `decide` 금지)**
전체 root flat(`m^{d-1}`)·전체 정점(`m^d`)을 점별로 건드리는 4대 의무:
- `returnsSingleCycle` → word/skew certificate(`FiniteCertificate`) + P1 unit-carry lift.
  **절대 orbit 열거 금지.** D7(6)의 46656을 커널 `decide`하려 들면 안 됨.
- `layerBijective` → P2(부분 교환) / `step∘dir` 구조적 단사. 열거(`m^{d-1}·m·d`) 금지.
- `rowLatin` → 각 색 = 서로 다른 generator라는 구조적 사실. 열거 금지.
- `stepConjugacy` → torusEquiv와의 정의적 동치(`simp`/`rfl`). `m^d` 점별 검사 금지.

**(N) `native_decide` 위험 지대 (구조적 lift에 구멍이 나면 강제됨)**
- **D7(6) (root flat 46656, 정점 279936)** — 최대 위험. (S)의 어느 의무라도
  구조적으로 닫지 못하고 전체 집합 점별 검사로 떨어지면, 커널 `decide`는
  timeout/OOM → `native_decide`가 유일한 기계적 수단이 됨.
- D7(4) (root flat 4096) — 경계선. 커널 `decide`가 *원리상* 가능하나 매우 느림.
- D5(4) (root flat 256) — 최후의 fallback으로 커널 `decide` 가능.

### 5.3 판정 및 규칙
- **현재 EvenV11은 native_decide가 전혀 불필요**하며, 게이트의 금지는 만족된다.
  v28 finite-audit 재구성이 바로 이를 가능케 한 설계다(모든 검사를 m²-fiber로 압축).
- 위험은 미구성 leaf(특히 D7(6))를 **실제로 구성할 때** (S) 의무에 구조적 구멍이
  생겨 native_decide의 유혹에 빠지는 것이다. 이는 native_decide 필요 신호가 아니라
  **누락된 구조 보조정리(P1/P2/P3/word-skew certificate) 신호**로 해석해야 한다.
- **실무 규칙:** 모든 `decide`는 대상 크기 ≲ m²(≤36) 또는 D²(≤49)로 제한한다.
  10³를 넘는 `decide`가 등장하면 즉시 멈추고, 그 의무를 작은 fiber로 환원하는
  구조 보조정리를 먼저 증명한다. 이 규칙을 closure 게이트에 추가하는 것을 권장
  (예: `decide` 라인의 도메인 상한 정적 검사).

**결론:** "native_decide로만 닫히는 부분"은 *설계상 존재하지 않아야 하며*, 현재도
없다. 단 D7(6)의 (S) 의무를 구조적으로 끝까지 닫는 것이 그 무결성을 지키는
핵심 과제다(Phase 2–3, P1·P3 + `IndexedWordSkewOrbitCertificate`).

---

## 6. finite certificate 해결가능성 검증 (실측, 2026-06-03)

`/root/.elan` toolchain으로 `lake build EvenV11` 성공(약 4초, olean 재사용).
이후 finite certificate 기계가 D7(6)을 native_decide 없이 닫기에 충분한지 정밀 검증.

### 6.1 존재·증명된 부품 (no sorry, no native_decide, 스케일-free)
| 부품 | 위치 | 성질 |
|---|---|---|
| small-fiber 단일순환 (orbit cert) | `TerminalA2LowMod` (Fin 16/36) | `decide`, m²-제한 |
| 기호적 unit-carry lift P1 | `UnitCarry.rankUnitCarrySingleCycle` | `Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum` 호출, O(1) |
| 기호적 carry 합 닫힌 형 | `UnitCarry.pointCarrySum` (`simp`→`a`) | **Base 크기 무관, 열거 없음** |
| P2 부분교환 전단사 | `Switching.partialExchange{Left,Right,Pair}_bijective` | 기호적 |
| 환원 `RootFlatModel→Cayley` | `FinalTargetRootFlatCertificateBridge` | 증명됨 |
| coforest 행 데이터 audit | `TypeA.AnchorBridge.*_holds` (D5,D7 stage1-2) | `decide`, 작은 표 |

→ **D7(6)의 46656 단일순환을 native_decide 없이 만들 *능력*은 검증됨**:
36-원소 terminal fiber에서 시작해 P1 lift를 기호적으로 연쇄(각 단계 carry 합을
`simp`로 ±1 닫힌 형), 곱집합을 결코 열거하지 않음.

### 6.2 결정적 빈 구멍 — splice→single-cycle 정리 부재
- `IndexedWordSkewOrbitCertificate`는 `orbit : Fin N ≃ Base×Fiber` 전체와
  `stepOrbit : ∀ i:Fin N`를 요구 → **O(N)**. 작은 fiber에만 유효, D7(6) 전체엔
  부적합(쓰면 그게 곧 native_decide 영역). 따라서 스케일하는 경로는 P1 lift뿐.
- 그런데 P1 lift는 "base가 *이미* 단일순환 + rank 좌표 보유"를 가정한다.
  terminal fiber(36)는 orbit cert로 rank를 주지만, **D7 two-rail relay는 여러
  coset cycle을 splice로 병합해 base를 만든다.** 그 병합 결과가 단일순환이고
  깨끗한 `≃ ZMod N` rank를 갖는다는 정리 = 논문 Lemma 3.5(cut-splice) + §6
  flag-splicing criterion.
- **검색 결과 `cutSplice`/`flagSplicing`/`spliceSuccessor`/`firstReturn` 식별자가
  EvenV11·Shared에 전무.** `HighEvenFiniteAnchorInput`는 `Bool=true` 표-정합성만
  전달하고, 그 표가 실제 단일순환을 만든다는 정리는 없다.

### 6.3 판정
- **"native_decide로만 닫히는 부분"은 없다.** 빠진 splice 정리(P3/P6)는 순열의
  cut-and-reconnect = 순수 조합론·기호적이라 native_decide 불요.
- 그러나 **finite certificate는 "완전히 해결 가능한 *상태*"는 맞아도 "해결됨"은
  아니다.** 가장 큰 단일 빈 구멍은 **cut-splice / coforest flag-splicing
  single-cycle 정리(P3+P6)**다. 이것이 없으면 lift 체인을 시작할 two-rail base를
  기호적으로 생산할 수 없다(§2 제안의 P3/P6와 정확히 일치).
- 위험: P3를 증명하는 대신 spliced base를 직접 orbit-cert로 열거하려 하면, 그
  base가 36보다 크므로 거기서 native_decide 유혹이 발생. **P3를 기호적 정리로
  증명하는 것이 유일한 올바른 길이자 최우선 과제.**

### 6.4 다음 작업 (우선순위)
1. **P6 coforest flag-splicing** — splice 열의 return-level 효과 = laminar
   quotient 따라 coset cycle 병합, 결과에 rank 좌표 부여.
2. 필요하면 **P3-atomic 일반 cut-splice** — 현재는 coset packet 특수형
   `oneStepPacketSplice`가 닫혀 있음.
3. 이후 D7 anchor: terminal fiber(orbit cert) → P6 splice로 rank base 생산 →
   P1 lift 연쇄 → `FinalRootFlatTorusModel 7 6`. rowLatin/layerBijective는 P2,
   stepConjugacy는 `simp`.
