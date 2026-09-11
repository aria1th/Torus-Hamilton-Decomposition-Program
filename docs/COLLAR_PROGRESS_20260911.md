# Collar 형식화 진행 — 2026-09-11

E4의 relative lift, physical split, incidence parity 보조정리를 구현했다.
**Pinned coherent selector의 존재 증명과 전체 collar 상태의 조립·귀납은 아직 없다.**
따라서 `thm:closure`, 모든 짝수 차원 specialization, `EvenOddDegreeGoal`의 완료를
선언하지 않는다. E5의 anchored entry도 별도 작업으로 남는다.

진입 import는 `TorusEven.Collar`이며 `TorusEven`의 기본 빌드에 포함된다.
원고와 기존 endpoint의 대응은 [준비 문서](LEAN_PREPARATION_20260911.md)를 따른다.

## 증명된 인터페이스

| 파일 | 주요 결과 |
|---|---|
| [FirstReturn](../TorusEven/Collar/FirstReturn.lean) | 끝점을 제외한 `openGap`, 구간 분할 equiv, return permutation, 귀환 시간의 합, semiconjugacy 아래 귀환 보존 |
| [OneGap](../TorusEven/Collar/OneGap.lean) | `oneGap`: 단일 순환, 모든 marked first return, 정확한 roof, nonzero fibre의 renewal |
| [Circuits](../TorusEven/Collar/Circuits.lean), [SourceSurgery](../TorusEven/Collar/SourceSurgery.lean) | 실제 orbit quotient로 회로를 세며, `patch_circuitCount`에 unmarked 회로 항을 포함 |
| [Lift](../TorusEven/Collar/Lift.lean), [OrbitLift](../TorusEven/Collar/OrbitLift.lean) | 회로별 unit carry에 따른 lift의 회로 대응과 회로 수 보존 |
| [Transport](../TorusEven/Collar/Transport.lean), [RelativeLift](../TorusEven/Collar/RelativeLift.lean) | 여러 old circuit에 대한 `relative_transport`, Hamilton 보존, 회로별 renewal |
| [FibreGap](../TorusEven/Collar/FibreGap.lean) | 기존 fibre gap와 row 0 pinning에서 새 fibre gap를 재생하는 `FibreGap.lift_preserves` |
| [Multitorus](../TorusEven/Collar/Multitorus.lean) | 양의 폭·successor permutation·방향별 quota, 좌표 재색인, 폭 1일 때 기존 `CayleyDecomposition`으로 변환 |
| [BinarySplit](../TorusEven/Collar/BinarySplit.lean) | 실제 양의 좌표 분할, balanced child 폭, active 분리, fibre별 방향·회로 일치, excess의 정확한 감소 |
| [Incidence](../TorusEven/Collar/Incidence.lean), [IncidenceParity](../TorusEven/Collar/IncidenceParity.lean) | full-column component, coherence에서 child parity 도출, complement의 홀수 degree, unsplit block 복제의 component 보존 |

## Relative lift의 정확한 범위

`oneGap`의 입력은 유한 타입 위의 단일 순환 `S`, 비어 있지 않은 `U`, `a ∈ U`,
`δ`의 nonzero support가 `a`의 open gap에 있다는 조건, 그리고 unit total이다.
법수에는 `[NeZero m]`만 필요하다. 결론은

```text
ret_lift(u,0) = (ret_old(u),0)
roof_lift(u,0) = roof_old(u) + if u=a then (m-1)·|X| else 0
t ≠ 0  ⇒  (x,t) ∈ openGap_lift(a,0)
```

일반 gap의 귀환을 먼저 계산한다. 첫 귀환은 유한 집합의 permutation이므로
지정점 밖에서의 일치가 지정점에서의 일치도 강제한다. 구간 분할로 귀환 시간의 합이
전체 정점 수임을 증명하고, 이를 통해 지정 roof와 renewal을 얻는다.

`UnitCarry S δ`는 **각 실제 old orbit**의 합이 unit임을 요구한다.
`GapSupport S U δ`는 U를 만나는 각 old orbit에서 nonzero voltage를 하나의
open gap에 제한한다. 이 두 입력으로 `relative_transport`는 임의의 `r : Equiv.Perm U`에 대해

```text
circuitCount(patch(lift S δ, U×{0}, boundaryLift r))
  = circuitCount(patch(S,U,r))
```

를 증명한다. `patch`의 합성 순서는 `S ∘ r`이다. `boundaryLift`는 U의 zero-section
복사본 하나에서만 r을 적용한다. `patch_lift_at_mark`는 voltage가 U에서 0이면
패치된 head가 원래 head의 zero-section 복사본임을 보인다.

회로 수 공식은 `circuitCount(retPerm) + Nat.card(UnhitCircuit)`이다. U가 모든
회로를 만난다는 추가 가정이 없으며, 빈 U와 고정점 회로도 포함한다. 패치 후 개별
회로 길이가 모두 m배가 된다는 주장은 하지 않는다.

`FibreGap`는 원고 collar 상태의 **조건 (iii)**에 해당한다. 완전한 collar state는
아니다. `FibreGap.lift_preserves`는 row 0 pinning과 unit carry에서 새 조건 (iii)을
증명한다. 다음 gap의 존재를 별도 입력으로 받지 않는다.

## Physical split과 parity의 경계

`MultitorusFactorization.split`은 실제 source 선택 `J x`를 입력받는다.
`J x`가 parent 방향의 사용자 집합에 포함되고 크기가 b일 때, 합좌표 chart
`(x,t) ↦ (…,xᵢ−t,…,t)`에서 두 child 폭은 `aᵢ−b,b`다. 역함수를 가진 successor와
모든 방향별 quota를 함께 구성한다. `balancedSplit`은 b를 `aᵢ/2`로 잡는다.
Active palette에서 방향 함수가 injective라는 조건도 보존한다.

Unit carry가 있으면 `split_circuit_iff`가 old circuit과 physical child circuit의
대응을 증명한다. 따라서 새 fibre를 따라 방향과 실제 회로 label이 모두 일정하다.
폭의 합은 색 수이며 `excess = Σ(aᵢ−1) = |C|−|I|`다.
`split_excess`는 매 split마다 정확히 1 감소함을, `excess_zero_iff`는 0일 때 모든
폭이 1임을 증명한다. **d−n개의 split을 선택할 수 있다는 존재 정리는 아직 아니다.**

Incidence component는 Ω 전체의 quotient이므로 support 밖의 고립 열도 남는다.
`evenComponents_of_coherent_odd_columns`의 입력은 이미 주어진 row 선택 J,
row별 일정한 quota, nonempty/coherent row family, 짝수 row 수, 홀수 column degree다.
Coherence로 한 old block의 모든 row가 같은 component에 속함을 보이고,
ZMod 2에서 incidence를 이중 계수한다. Column degree에 fibre 수를 다시 곱하지 않는다.
`odd_complement_columns`와 `evenComponents_copied`는 각각 다른 child와 unsplit 방향의
보존에 사용할 수 있다. 실제 multitorus의 full colour–circuit Ω와 선택 J를 이 API에
연결하는 작업은 전체 state 조립에 남아 있다.

## 남은 E4 작업

1. **PinnedSelection의 존재 증명.** EvenComponents와 support당 active 열 ≤1에서
   parity join, disjoint local pairs, divergence ±1 방향화, filler, row 0/1/2 배치를
   구성한다. 정확한 quota·unit totals·pinning·두 child의 coherence를 모두 반환해야 한다.
2. **RelativeCollarState 조립.** 실제 factorization, fibre chart, active palette,
   full colour–circuit labels, 표시점 및 incidence 조건을 통합한다. Selector의 출력이
   위 physical/relative/parity 정리의 입력을 만족함을 증명한다.
3. **전체 귀납.** 다음 split의 존재를 추가 가정으로 받지 않고 excess에 대해 귀납한다.
   마지막 recolouring의 quota와 Hamiltonicity를 기존 Cayley endpoint로 내보내고,
   빈 active palette로 모든 짝수 차원을 닫는다.

이미 주어진 J의 성질을 가정하는 보조정리와, J를 구성해야 하는 closure 정리를
구분한다. `ClosedUnderSplit` 같은 가정을 새로 두고 이를 E4 완료로 바꾸지 않았다.

## 검증과 실행 환경

- CPU 노드에서 `lake build TorusEven` 통과. 새 모듈과 해당 의존 경로를 빌드했으며,
  mathlib 전체의 clean rebuild는 아니다. 새 Collar 모듈의 linter 경고는 없다.
- `scripts/check_even_isolation.py` 통과: main-path 43개, attic 4개,
  기존 native 사용 파일 3개. 새 코드에 `sorry`, `admit`, author axiom, `native_decide` 없음.
- 주요 새 선언 19개의 `#print axioms`가 모두 `propext`, `Classical.choice`,
  `Quot.sound`의 부분집합이다. 기존 조건부 even endpoint의 native axiom은 18개로 동일하다.

산출물은 `/fsx/angel/operations/torus-lean-preparation-20260911/`의
[빌드 로그](/fsx/angel/operations/torus-lean-preparation-20260911/collar-full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-preparation-20260911/CollarAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-preparation-20260911/collar-axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-preparation-20260911/collar-verification.json)에 있다.

유지하는 소스는 제어 노드의 `/local/angel/etc/Torus-Hamilton-Decomposition-Program`이다.
CPU 노드 `root@jcssh-hp.mewtant.io:31630`에는 실행용 소스·캐시를
`/local/angel/lean-collar/Torus-Hamilton-Decomposition-Program`에 준비했다.
도구체인은 같은 노드의 `/local/angel/lean-collar/leanprover--lean4---v4.30.0-rc2/bin`이다.
고정 mathlib SHA는 `5450b53e5ddc75d46418fabb605edbf36bd0beb6`이다.
