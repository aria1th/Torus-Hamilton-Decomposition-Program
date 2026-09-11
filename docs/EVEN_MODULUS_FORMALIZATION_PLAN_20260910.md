# 짝수 법수 확장 형식화 계획 (기존 홀수 Lean 코드 이어받기)

Date: 2026-09-10.

현재 재개 지점은 [collar 진행 문서](COLLAR_PROGRESS_20260911.md), 원고·Lean 대응은
[2026-09-11 준비 문서](LEAN_PREPARATION_20260911.md)를 따른다. E0–E4는 완료되었고
E5 anchored entry가 남았다. 아래 단계별 원안의 환경 부재·coset 기계 부재·E3 예정 문장은
최초 조사 시점의 기록이다. D3의 native leaf는 실제 조회 기준 14개다.

입력 원고: `/local/angel/etc/paper/torus_integrated_proof.zip`
(`even_directed_tori_integrated.tex`, SHA256 `846a1e5f…88e98`; 주정리: 모든 짝수
m>=4, 모든 d>=2에서 D_d(m)의 Hamilton 분해). 번들의 다섯 Python 검사기는 2026-09-10에
이 저장소 옆 환경에서 재실행되어 리포트가 바이트 단위로 재현되었다. 이 문서는 그
원고를 현재 저장소(`0.0.3-allodd`, toolchain `leanprover/lean4:v4.30.0-rc2`)의 Lean
코드 위에 형식화하는 계획이며, 완료 선언이 아니다.

판정 등급은 zip의 `previous_formalization_plan.md`를 그대로 따른다:
**P** 종이 증명, **E** 유한 전수 검사, **C** 정수형 증서, **K** 커널 정리(+ axiom 목록).
`native_decide`는 K 안에서도 `Lean.ofReduceBool` 의존으로 따로 표기한다.

---

## 1. 최종 목표 정리의 형태

```lean
-- 새 라이브러리 TorusEven, 파일 TorusEven/Endpoints.lean
def EvenModulusToriAllDimensionsGoal : Prop :=
  ∀ {d m : Nat}, 2 ≤ d → Even m → 4 ≤ m →
    Shared.CayleyHamiltonDecomposition d m

theorem even_modulus_tori_all_dimensions :
    EvenModulusToriAllDimensionsGoal
```

`Shared.CayleyHamiltonDecomposition d m` (`Shared/TorusCayley.lean:457`)은 홀수
endpoint와 동일한 정의(색→방향 선택자, 정점별 Latin, 색별 단일 순환)이므로 최종
문장은 홀수 정리와 같은 타입 패밀리에 놓인다. 두 정리를 합친 all-m>=3 따름정리는
`RoundComposite.Concrete.odd_modulus_tori_all_dimensions_v75`와 합쳐 한 줄로 끝난다.
그 따름정리는 원고 Corollary(all-moduli)와 같이 별도 이름으로 두고, 짝수 주정리
자체는 홀수 정리에 의존하지 않게 유지한다.

---

## 2. 기존 자산 분류

조사 기준: 2026-09-10 `main` (`0a00a8a`).

### 2a. 홀짝 무관, 그대로 재사용 (녹색)

| 자산 | 위치 | 역할 |
|---|---|---|
| `IsSingleCycleMap`, `single_cycle_of_periodic_return_cover` | `Shared/ReturnLift.lean:5,49` | 첫 귀환이 단일 순환이면 전체 순환 |
| `RootFlatSchedule`, `RootFlatCertificate`, `rootFlatLayeredDecomposition_of_certificate` | `Shared/RootFlat.lean:5,226,268` | 높이층 스케줄 → Cayley 분해. `[NeZero m]`만 요구 |
| `sectionReturn`, `single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum` | `Shared/Monodromy.lean:376,688` | unit carry lift = 원고 Lemma(lift) |
| `zmodVectorLowerTriangularUnitCycleCoordinate` | `Shared/Monodromy.lean:777` | odometer형 lift, 홀짝 가정 없음 |
| `single_cycle_of_zmod_rank`, `zmod_add_single_cycle_of_unit` | `Shared/RankCycle.lean:21,108` | rank 증서 → 단일 순환 |
| `cayleyHamiltonDecomposition_product_of_left_coordinatized` | `Shared/CayleyProduct.lean:335` | D_a(m) ⊗ D_b(m^a) ⇒ D_{ab}(m). 홀짝 무관 |
| `standard_cayley_pointwise_composite_expansion` | `RoundComposite.lean:342` | 위 곱의 `Solved` 추상화. `Odd` 없음 |
| `Shared.D2.cayleyHamiltonDecomposition` | `Shared/D2Seed.lean:242` | D_2(m) 모든 m>=1. 이미 K |
| `D5EvenRouteEM4FiniteTarget_unconditional` | `D5Odd/EvenRouteEM4.lean:206` | D_5(4) 완료(K, `native_decide`) |
| `D7Odd.rootFlatCertificate_to_hamiltonDecomposition` | `D7Odd/Torus.lean:239` | root-flat 증서 → D_7 |

### 2b. 짝수에서 막히는 것 (적색)

| 자산 | 막히는 지점 |
|---|---|
| `TorusD3Odd.lambda = -(2⁻¹)` (`TorusD3Odd/ReturnMaps.lean:26`) | 세 번째 색 return map이 `k ↦ k-2`. 짝수 m에서 비추이적 |
| `RoundComposite` 고법수 core (`PrefixCount.lean:487,1222,1516,2566`, `ActiveHall.lean:1452`) | carry 알파벳 `{±1,±2}`가 unit이어야 함. 2가 unit이 아님 |
| `SeedSemigroup.odd_coprime_m_sub_two` | 같은 이유 |
| D5/D7 홀수 seed | 스케줄 자체가 홀수 전용 |

결론: **곱 dispatcher와 lift 엔진은 재사용하고, 고법수 core는 재사용하지 않는다.**
짝수 쪽의 일반 엔진은 원고의 relative collar closure(thm:closure)이며, 이는
저장소에 전혀 없다(coset/`AddSubgroup` 관련 정리 0건).

### 2c. 이미 격리 대상인 시도

- `D5Odd/Even.lean`, `D5Odd/EvenRouteE.lean`(2124줄, 조건부 target만 있음),
  `D7Odd/Even.lean`(내용 없는 adapter), 원격 브랜치 `route-e-v3-6-20260506`,
  `certs/d5_routeE_*`, `scripts/*routeE*`, `docs/D5_EVEN_ROUTE_E_*`.
- 이 중 살릴 것: `EvenRouteEM4.lean`(D_5(4) K 결과)와 `Even.lean`의
  `D5_even_cayley_from_orbit_certificate`(홀짝 무관 seam 프레임). 나머지 Route E는
  §4의 Attic으로 이동한다.

---

## 3. 아키텍처: 두 엔진과 커널 마일스톤 순서

원고의 증명 구조(짝수 d: 빈 palette closure / d=3: anchored core / d=5: ordinary /
홀수 d>=7: entry + closure)를 그대로 옮기면 collar closure를 먼저 끝내야 어떤
차원도 닫히지 않는다. 대신 저장소의 홀짝 무관 곱 dispatcher를 앞세워 **collar
closure 없이 닫히는 차원을 먼저 K로 만든다.**

```text
E0 환경 고정 ─ E1 dispatcher 일반화 ─┬─ (즉시) d = 2^k
                                     │
E2 D_3(짝수) ───────────────────────┼─ d ∈ {2,3}-smooth 합성수 (6, 9, 12, 18, …)
E3 D_5(짝수): m=4 leaf + m>=6 chronological ─┴─ d ∈ {2,3,5}-smooth (10, 15, 20, 25, …)

E4 F1–F5 relative collar closure (원고 §3–4)   ← 새 수학 엔진, 가장 큰 작업
E5 F6 entry: near core, shell, anchored 일치, p=2 / p=3 / p>=4
      └─ d = 7 (p=2), 소수 d >= 11, 그리고 원고 방식의 짝수 d 재증명(교차검증)
E6 최종 조립 + axiom ledger
```

d=7은 소수라 곱으로 얻을 수 없다. 따라서 **E4–E5는 d=7에서 처음 불가피해진다.**
E2–E3만 끝나도 부분 정리(`∀ d ∈ ⟨2,3,5⟩-smooth`)가 커널 정리로 남고, 이는
collar 형식화에서 원고의 gap이 드러나더라도 무효화되지 않는다.

---

## 4. 격리 규칙 (실패 시도 분리)

### 4a. 라이브러리 구조

```toml
# lakefile.toml 추가
[[lean_lib]] name = "TorusEven"        # 주 경로만. 루트 TorusEven.lean이 import 목록
[[lean_lib]] name = "TorusEvenAttic"   # 보류/실패 시도. defaultTargets에 넣지 않음
[[lean_lib]] name = "TorusEvenEvidence" # E/C 등급 유한 검사(native_decide 회귀). 주 경로가 import 금지
```

- `TorusEven/`은 `Shared`, `RoundComposite`(dispatcher 부분만), `D5Odd.EvenRouteEM4`
  외에 아무것도 import하지 않는다. 특히 `RoundComposite.OddCore`, `PrefixCount`,
  `D5Odd.EvenRouteE`는 import 금지.
- `TorusEvenAttic/`으로 이동: `D5Odd/EvenRouteE.lean`, `D7Odd/Even.lean`.
  `D5Odd.lean`, `D7Odd.lean` 루트에서 해당 import를 제거한다(홀수 endpoint의
  의존 그래프에 없음을 조사로 확인함). 이동한 파일은 첫 줄에
  `-- STATUS: attic (Route E, superseded 2026-09-10; see docs/EVEN_ATTIC_LEDGER.md)`.
- 모든 `TorusEven/*.lean` 첫 줄에 `-- STATUS: main-path | conditional | evidence`
  를 둔다. `conditional`은 `def *Goal : Prop`만 있고 증명이 없는 파일이며,
  주 endpoint는 `conditional` 파일의 `Goal`을 가정으로 받는 정리로 시작해도 되지만
  최종 릴리스 전에 모두 `main-path`로 바뀌어야 한다.
- 검사 스크립트 `scripts/check_even_isolation.py`: (1) `TorusEven/`가 Attic/Evidence/
  OddCore를 import하지 않음, (2) STATUS 헤더 존재, (3) `sorry/admit/axiom` 0건,
  (4) `native_decide` 사용 파일이 `Evidence`이거나 leaf 목록(§5 E3-a)에 등록됨.
  CI(`lean_action_ci.yml`)에 이 스크립트 단계를 추가한다.

### 4b. Git 운용

- 작업 브랜치 `even-modulus`. 실험은 `even-attic/<주제>-<날짜>` 브랜치에서 하고
  실패하면 병합하지 않는다. 성공한 것만 `even-modulus`로 cherry-pick.
- 마일스톤 태그: `0.1.0-even-smooth`(E3 후), `0.2.0-even-collar`(E4 후),
  `0.3.0-alleven`(E6 후). 각 태그에 `#print axioms` 출력과 `lake build` 로그를
  `docs/EVEN_AXIOM_LEDGER.md`에 기록.
- `docs/EVEN_ATTIC_LEDGER.md`: 각 attic 항목마다 "무엇을 시도했고, 어떤 가정이
  실패했고, 재사용 가능한 정리 이름"을 세 줄로. Route E 브랜치 발산 이력
  (`AI_research_observations.md` §1)의 재발을 막기 위해, 하나의 목표에 대해
  attic 항목이 셋을 넘으면 접근 자체를 재검토한다.

---

## 5. 단계별 모듈 명세

### E0. 환경 고정 (K의 전제)

이 머신에는 `elan`/`lake`/`.lake`가 없어 현재 아무것도 타입체크할 수 없다.
- `elan` 설치, `lake exe cache get`으로 mathlib `v4.30.0-rc2` 캐시, `lake build Shared RoundComposite` 기준선 확인.
- `docs/EVEN_LOCK.md`: toolchain, mathlib rev(`5450b53e…`), 저장소 commit, 원고 SHA256,
  `certificates/*.json` SHA256(`d5_m4_tours.json` = `6dc36c0d…`).

수락 기준: 기준선 빌드 로그와 `#print axioms odd_modulus_tori_all_dimensions_v75`가 재현됨.

### E1. 홀짝 무관 dispatcher (`TorusEven/Dispatch.lean`)

`RoundComposite/ConcreteEndpoints.lean:114`의
`odd_modulus_tori_all_dimensions_uniform_of_357_and_successor`를 법수 술어
`P : Nat → Prop`로 일반화한다.

```lean
structure ModulusClass where
  P : Nat → Prop
  pow_closed : ∀ {m a}, 0 < a → P m → P (m ^ a)
  three_le   : ∀ {m}, P m → 3 ≤ m

theorem all_dimensions_of_seeds_and_successor (C : ModulusClass)
    (h2 : ∀ {m}, C.P m → StandardCayleySolved 2 m)
    (h3 : ∀ {m}, C.P m → StandardCayleySolved 3 m)
    (h5 : ∀ {m}, C.P m → StandardCayleySolved 5 m)
    (h7 : ∀ {m}, C.P m → StandardCayleySolved 7 m)
    (hSucc : ∀ {b m}, 5 ≤ b → C.P m → StandardCayleySolved b m →
                       StandardCayleySolved (2*b+1) m)
    {d m} (hd2 : 2 ≤ d) (hm : C.P m) : StandardCayleySolved d m
```

- 홀수 인스턴스는 기존 정리를 그대로 재유도해 회귀를 확인한다(정리 이름 변경 없음).
- 짝수 인스턴스 `C.P m := Even m ∧ 4 ≤ m`. `h2`는 `Shared.D2.cayleyHamiltonDecomposition`.
- 부분 산출물 `even_smooth_dimensions`: `h3,h5`만으로 `{2,3,5}`-smooth d를 닫는 변형.

수락 기준: `Odd` 문자열이 파일에 없음. 기존 홀수 endpoint의 의미가 바뀌지 않음.

### E2. D_3(짝수) (`TorusEven/D3/`) — **완료 2026-09-10** (아래 원안 대신 Park3 Route E Lean 코드를 vendoring; docs/EVEN_AXIOM_LEDGER.md 참조)

원고 §6 anchored cyclic-star(prop:anchor, lem:star, Appendix A의 `3∤m`/`3|m` 분기).
- `RootFlatSchedule`로 세 색의 높이층 방향표를 정의(높이 = 한 좌표, root = `(ZMod m)^2`).
- `rowLatin`, `layerBijective`는 유한 case split.
- `returnsSingleCycle`: Appendix A의 return 계산. `3∤m`와 `3|m`를 별도 정리로.
  `TorusD3Odd/FullCycles.lean`의 `firstReturn_eq_FMap` 패턴(첫 귀환을 명시적 사상으로
  식별한 뒤 `single_cycle_of_zmod_rank`)을 재사용한다.
- 대안 leaf: Park3(arXiv 2603.24708)의 D3 전 법수 구성이 더 짧으면 그것을 쓰되,
  원고 prop:anchor와의 일치(네 anchor 점의 방향표)는 E5에서 다시 필요하므로 anchored
  버전을 주 경로로 둔다.

수락 기준: `theorem d3_even {m} (hm : Even m) (h4 : 4 ≤ m) : Shared.CayleyHamiltonDecomposition 3 m`,
axiom은 표준 3개만.

### E3. D_5(짝수) (`TorusEven/D5/`) — **완료 2026-09-10** (`TorusEven.d5_even_large : D5EvenLargeGoal`, 표준 axiom만; 파일 대응은 docs/EVEN_AXIOM_LEDGER.md 참조. 아래는 원안)

**E3-a. m=4 leaf.** 기존 `D5EvenRouteEM4FiniteTarget_unconditional`을
`Shared.CayleyHamiltonDecomposition 5 4`로 잇는 adapter가 홀짝 무관인지 확인해 그대로
쓴다(가장 저렴). 원고와의 동기화를 위해 zip의 `d5_m4_tours.json`(다섯 1024-tour)을
`TorusEvenEvidence/D5Four.lean`에 두 번째 leaf로 넣는다: `D5FourTour` 인터페이스대로
`checker_sound : check cert = true → CayleyDecomposition 5 4`를 constructor와 독립으로
증명하고, `check cert = true`는 `decide`가 되면 `decide`, 아니면 `native_decide`로 하고
ledger에 기록한다. 두 leaf 중 어느 쪽이 주 경로인지 `Endpoints.lean`에 명시.

**E3-b. Chronological transversal (`ChronologicalTransversal.lean`).** 저장소에 coset
기계가 없으므로 새로 만든다. 추상 문장:

```lean
-- X : 유한 가환군, H W : AddSubgroup X, IsCompl H W
-- S : Equiv.Perm X,  hS : ∀ x, orbitSet S x = (x +ᵥ (H : Set X))
-- P : Equiv.Perm X,  b,  hP : ∀ x, P x - x - b ∈ H
-- e ∈ W, addOrderOf e = m,  C = z +ᵥ (W : Set X)
-- J := piecewise (· + e) on C, id off C
theorem orbit_eq_coset_of_transversal_splice :
    ∀ x, orbitSet (S * (P⁻¹ * J * P)) x = (x +ᵥ ((H ⊔ AddSubgroup.zmultiples e : AddSubgroup X) : Set X))
```

증명은 원고대로: (i) `A := P⁻¹ '' C`가 각 H-coset을 정확히 한 번 만남, (ii)
source surgery(F1)로 `Ret_A(S r) = r`, (iii) r의 순환이 서로 다른 m개의 H-coset을
지남. **곱 규약(오른쪽부터)을 파일 첫 주석에 고정**하고 `Equiv.Perm`의 `*`와 대조한다.
`check_transversal_lemma.py`의 100개 비선형 prefix 사례와 negative control을
`Evidence`에 `decide` 회귀로 옮긴다(m=3 소형).

**E3-c. F1 source surgery (`SourceSurgery.lean`).** `Shared.Monodromy.sectionReturn`을
marked subtype `U`로 일반화: `Ret_U(S r) = Ret_U(S) * r`, 순환수 공식
`cyc(S r) = h_U(S) + cyc(α r)`. E4에서도 그대로 쓴다.

**E3-d. 정수 증서 (`IntegerComplement.lean`).** 열두 행렬 `Q = [H⁻ W_P]`의 `det = ±1`과
`Q⁻¹ e = (0, v)`를 `Matrix (Fin 4) (Fin 4) ℤ`에서 `decide`/`norm_num`으로, 그 뒤
`ZMod m`으로 환원(`Int.cast`). m=4는 `ZMod 4`에서 별도 증서(det ±1 또는 ±3).
`IsCompl H W`와 `addOrderOf e = m`을 이 증서에서 도출하는 보조정리를 하나로 묶는다.
결정식만으로 끝내지 않고 prefix의 pointwise 합동 `P x = x + b mod H⁻`를 실제
displacement 목록에서 증명하는 것이 E3-b로 가는 다리다.

**E3-e. D5 스케줄 (`Schedule.lean`, `Preterminal.lean`).** root `(ZMod m)^4`, 높이
`ZMod m`, 방향 `Fin 5`; root-height chart `(x,h) ↦ (x, h - Σx)`가 물리 좌표
`Shared.TorusVertex 5 m`로 가는 equiv이고 root-height step이 양의 기저 간선임을
증명. 다섯 cylinder 수정을 순서대로 적용해 Prop(d5-preterminal): 색 0,2는 단일
m^4 순환, 색 1,3,4는 `ker f_c`의 coset. m=4는 `RHO4` 표와 `g_2,g_3,g_4`로 별도 파일.

**E3-f. Terminal endpoint (`PlanarEndpoint.lean`).** `omega_m`, `j_i`, `N_i`, 세 개의
2m-순환 목록(eq:d5-end0..2)을 짝수 m>=4 전체에서 index-range case split로 증명.
m=4의 빈 범위 규약 포함. Python m<=256 루프는 Evidence로만 둔다. 이어 첫 귀환이
정확히 `N_i`(m>=6: 두 점 swap)임을 quotient character 제한 `(a, -b, a+b)`에서 증명,
m=4는 iterate 항등식 (38,59;30,47)을 `decide`로.

**E3-g. 조립.** `RootFlatCertificate` 채우고 `theorem d5_even {m} (hm : Even m) (h4 : 4 ≤ m)`.

수락 기준: m>=6 증명에 유한 m 검사가 인용되지 않음. `native_decide`는 m=4 leaf에만.

### E4. Relative collar closure (`TorusEven/Collar/`) — zip F1–F5

원고 §3–4. 홀수 core를 대체하는 새 엔진. 모듈 순서는 zip 계획을 따르되 각 모듈을
독립 파일과 독립 `Goal`로 두어 실패 시 파일 단위로 Attic 이동이 가능하게 한다.

| 파일 | 내용 | 재사용 |
|---|---|---|
| `Multitorus.lean` | `T_m(a_1..a_n)` 라벨 multitorus, colour–circuit 라벨, 합좌표 chart `(x,t) ↦ (…, x_i - t, t, …)`(lem:physical) | `Shared.CayleyProduct.torusVertexBlockEquiv` 패턴 |
| `BinaryLift.lean` | δ∈{0,1} voltage, row quota가 child multiplicity 보존, unit total ⇒ 단일 lift(lem:lift) | `single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum` |
| `OneGap.lean` (F3) | additive cyclic fibre 정리 먼저; 표시 첫 귀환 보존과 nonzero-fibre 점의 한 gap 귀속(renewal)을 별도 결론으로 | `sectionReturn` |
| `PinnedSelection.lean` (F4) | spanning forest T-join, odd-degree multigraph의 ±1 divergence 방향화, filler 부등식, row 0/1/2 배치, 두 coherence | mathlib `SimpleGraph` Euler는 multigraph에 부적합. 간선 수 귀납으로 "모든 정점에서 `|in - out| ≤ 1`인 방향화 존재"를 직접 증명하는 것을 권장 |
| `IncidenceParity.lean` (F5) | lem:inherit: `a' · #blocks = Σ deg`, 짝수성 재생, untouched 방향 보존, measure `Σ(a_i-1)` 감소 | |
| `Closure.lean` | `thm:closure` 한 정리. 입력: collar state, 출력: 다음 collar state + 모든 필드 | |
| `EvenDegree.lean` | `thm:even-dim`: 빈 palette 특수화로 모든 짝수 d를 닫음. E1의 기존 product 결과와 겹치는 차원에서 교차검증; E1만으로 모든 짝수 d가 닫힌 것은 아님 | |

수락 기준(zip F1–F5와 동일): 우측 합성 규약, unhit orbit 항, `m=2`/`active 2개`
반례가 signature에서 배제됨, closure가 solver/reservoir 가정 없이 닫힘.

### E5. Entry (`TorusEven/Entry/`) — zip F6

near core `(1,1,2)`+Hamilton shell(lem:nearcore, lem:shell), seed incidence
(lem:seed-incidence, lem:small-seed), anchored core와 네 `Q_m` 점 일치(E2의 방향표
직접 대입), `p=2`(lem:entry-seven), `p=3`(lem:entry-nine), `p>=4`(prop:entry).
`check_small_entries.py`의 (4,7),(6,7),(4,9) full endpoint는 Evidence 회귀로.

산출: `d7_even`, 그리고 `hSucc`형 정리
`even_successor : 5 ≤ b → … → StandardCayleySolved b m → StandardCayleySolved (2b+1) m`
가 아니라 원고 방식의 직접 정리 `odd_degree_ge7 : Odd d → 7 ≤ d → …`. E1의 dispatcher
에는 `hSucc` 대신 이 직접 정리를 꽂는 두 번째 조립 경로를 둔다(둘 다 유지).

### E6. 최종 조립과 ledger

- `TorusEven/Endpoints.lean`: `even_modulus_tori_all_dimensions`(E1 경로)와
  `even_modulus_tori_all_dimensions_collar`(원고 경로). 둘의 타입이 같음을 `example`로.
- `all_moduli_tori_all_dimensions : ∀ {d m}, 2 ≤ d → 3 ≤ m → Shared.CayleyHamiltonDecomposition d m`
  는 홀수 v75 + 짝수를 `Nat.even_or_odd`로 합친다.
- `docs/EVEN_AXIOM_LEDGER.md`: 각 endpoint의 `#print axioms`, `native_decide` leaf 목록,
  빌드 로그, 원고 정리 번호 ↔ Lean 이름 대응표.

---

## 6. 리스크와 대응

1. **collar 기계의 종이 증명 gap.** 커널 검증 이력이 없다(archived audit는 E/C 등급).
   E4에서 gap이 나오면 해당 파일만 `conditional`로 두고 E1–E3의 부분 정리는 유지된다.
   특히 `PinnedSelection`의 coherence 논증(row 0/1/2 배치)이 가장 세밀하므로 먼저
   m=4, 작은 block에서 `decide` 반례 탐색을 Evidence로 돌린 뒤 일반 증명에 들어간다.
2. **D5 endpoint 목록의 index-range 증명 비용.** 세 목록 × 홀짝 index 분기. 목록을
   `List`로 정의하고 "목록이 순열의 순환"임을 `List.Nodup` + successor 항등식으로
   환원하면, 각 항등식은 `ZMod m` 산술 `ring`/`omega`(`ZMod.natCast` 처리 후)로 닫힌다.
3. **`Equiv.Perm` 곱 규약 혼동.** `ReturnLift`/`RootFlat`는 함수 합성(`foldl`)이고
   `Equiv.Perm`의 `*`는 `f * g = f ∘ g`. E3-b에서 `Sr`를 `S ∘ r`로 고정하고 lemma 이름에
   `_right`를 붙인다.
4. **native_decide 신뢰 경계.** 현재 등록 파일은 `D5Odd/EvenRouteEM4.lean`,
   `D5Odd/EvenLambdaE.lean`, `TorusD3Even/Color2.lean`이다. D3의 m=6,8 leaf도
   포함한다. 사용 위치 검사는 `scripts/check_even_isolation.py`, 실제 의존성은
   최상위 `#print axioms`로 확인한다.
5. **원격 브랜치 `route-e-v3-6-20260506` 재유입.** Attic ledger에 superseded로 기록하고
   병합하지 않는다.

## 7. Mutation suite (Evidence 등급, 각 항목이 어떤 가정 위반으로 거부되는지 고정)

zip 계획 §5의 12개 항목을 그대로 채택하고 다음을 추가한다.
- E3-b: quotient-translation 가정을 뺀 prefix(negative control, m=3).
- E3-f: m=4 표에 m>=6의 terminal colour `(1,3,4)`를 섞은 경우.
- E3-a: tour 인증서의 short/repeat/non-arc/duplicate-colour 네 손상.
- E1: `pow_closed` 없이 `P m`만 가정한 dispatcher는 `m^a` 단계에서 막혀야 함.

## 8. 완료 기준

1. `lake build TorusEven` 성공, `scripts/check_even_isolation.py` 통과.
2. `even_modulus_tori_all_dimensions`의 `#print axioms`가 표준 3개 + 등록된 leaf의
   `native_decide` axiom만 포함.
3. `docs/EVEN_AXIOM_LEDGER.md`에 원고 정리 ↔ Lean 이름 대응, 빌드 로그, 인증서 해시.
4. Attic ledger가 모든 보류 시도를 설명하고, 주 경로가 Attic을 import하지 않음.
5. 원고 Appendix(app:computation)에 K 등급 결과와 남은 E/C 등급을 구분해 반영.
