# Collar 형식화 진행 — 2026-09-11

**E4 relative collar closure와 모든 짝수 차원 specialization을 증명했다.**
`TorusEven.even_degree_collar : EvenDegreeCollarGoal`은 모든 짝수 m≥4, 짝수 d≥2의
Hamilton 분해를 주며 표준 axiom만 사용한다. E5 anchored entry는 남아 있다.
따라서 모든 차원을 다루는 endpoint는 여전히 `EvenOddDegreeGoal`을 가정한다.

진입 import는 `TorusEven.Collar`이고 `lake build TorusEven`에 포함된다.
원고는 `even_directed_tori_integrated.tex`의 `def:collar`, `thm:closure`, `thm:even-dim`이다.
기존 seed와의 대응은 [준비 문서](LEAN_PREPARATION_20260911.md)를 따른다.

## 상태와 closure 인터페이스

| 파일 | 주요 결과 |
|---|---|
| [CircuitBlocks](../TorusEven/Collar/CircuitBlocks.lean) | 전체 colour–circuit 열 `Σ c, Circuit (F.step c)`, fibre별 support, active 열의 분리 |
| [SourceSelection](../TorusEven/Collar/SourceSelection.lean) | row 선택을 실제 source 선택으로 변환하고 정확한 quota·회로별 voltage 합·zero-row pinning 증명 |
| [SplitIncidence](../TorusEven/Collar/SplitIncidence.lean), [IncidenceTransport](../TorusEven/Collar/IncidenceTransport.lean) | 실제 split 전후 회로 label 동치, orbit 대응, incidence component의 재색인 |
| [SelectedSplit](../TorusEven/Collar/SelectedSplit.lean) | 선택된 balanced split의 factorization, 새 fibre consistency, 두 child와 unsplit 방향의 parity |
| [RelativeState](../TorusEven/Collar/RelativeState.lean) | `RelativeCollarState`, selector 존재, 네 상태 조건 보존, active source surgery의 회로 수 보존 |
| [MarkedEquiv](../TorusEven/Collar/MarkedEquiv.lean), [Recolouring](../TorusEven/Collar/Recolouring.lean) | 표시점 동치 아래 patch 전달, 유효한 recolouring의 quota와 head 보존, 모든 색의 회로 수 보존 |
| [Closure](../TorusEven/Collar/Closure.lean) | `exists_split`, 정확한 횟수의 `resolution`, `hamilton_decomposition` |
| [EvenDegree](../TorusEven/Collar/EvenDegree.lean) | 빈 active palette 초기 상태와 `even_degree_collar` |

`RelativeCollarState F frame active U`는 다음 네 조건을 묶는다.

1. `frame : Y × ZMod m ≃ X`의 각 fibre에서 색별 방향과 실제 회로 label이 일정하다.
2. 각 source에서 한 방향을 쓰는 active 색은 최대 하나다.
3. U는 old zero row에 놓이고, U를 만나는 각 active 회로의 nonzero-row 정점들은
   하나의 open U-gap 안에 있다.
4. 폭이 2 이상인 각 방향에서 full-column incidence component의 열 수가 짝수다.

Frame은 정점 집합의 동치이며 원래 물리 좌표 하나일 필요가 없다. 회로는 실제 orbit의
quotient이고, incidence는 support 밖의 고립 열까지 포함한다.

`RelativeCollarState.exists_split`은 m≥4가 짝수일 때 폭이 2 이상인 **어느 방향에나**
balanced selection이 존재함을 증명한다. 결과는 네 상태 조건을 모두 만족하며, 같은
선택이 **모든** 유효한 active recolouring의 색별 회로 수를 보존한다. 다음 split의
존재, coherence, unit carry, 새 gap 또는 parity를 추가 가정으로 받지 않는다.

`SplitResolution F k`는 k번의 balanced physical split 뒤에 모든 폭이 1인 상태에
도달하는 귀납적 증거다. `RelativeCollarState.resolution`의 인덱스는 정확히
`F.excess = Σᵢ(aᵢ−1) = d−|I|`다. `hamilton_decomposition`은 같은 excess 귀납으로
입력 recolouring의 Hamilton성을 전달하고 최종 좌표를 `Fin d`로 재색인하여
`Shared.CayleyDecomposition d m`을 얻는다.

## 선택에서 실제 split까지

앞서 증명한 `Incidence.pinnedSelection_iff`는 짝수 m≥4와 support 크기 ≥2에서
component의 짝수성과 pinned coherent selection의 존재가 동치임을 보인다.
`exists_pinnedSelection`의 구성에는 component parity와 블록당 active 열 ≤1이면
충분하다. 선택은 정확한 절반 quota, 열별 합 ±1, row 0에서 active 제외, 양쪽
nonterminal child의 coherence를 만족한다. 증명의 세부는
[selector audit](/fsx/angel/operations/torus-lean-selector-20260911/verification.json)에 보존했다.

`sourceSelection_orbit_sum`은 **각 실제 old 회로** 위의 voltage 합을 해당 열의 row
선택 횟수와 동일시한다. 이를 unit carry에 연결한다. 새 incidence column degree에
fibre 수를 다시 곱하지 않는다. `splitLabelEquiv`와 `childSupport_mem`으로 selected,
complementary, copied support를 실제 physical split의 full-column support에 옮긴다.

Physical chart는 `(x,t) ↦ (…,xᵢ−t,…,t)`이고 child 폭은
`aᵢ−floor(aᵢ/2), floor(aᵢ/2)`다. 기존 `split_excess`가 정확히 1의 감소를 보장한다.
Old row 0 pinning과 상태의 gap 조건에서 `GapSupport`를 얻고, `relative_renewal`로
새 nonzero fibre가 하나의 enlarged open gap에 놓임을 증명한다.

## Recolouring과 보존량

`Recolouring`은 색별 `boundary : C → Perm U`와 표시점별 `routing : U → Perm C`로
주어진다. Routing은 inactive 색을 고정하며, 다음 head 등식을 만족해야 한다.

```text
F.step c (boundary c u) = F.step (routing u c) u
```

이 조건으로 `Recolouring.factorization`은 표시점에서도 방향별 quota를 유지한다.
선택된 voltage가 active 표시점에서 0이므로 같은 head 등식이 split 뒤에도 성립한다.
`Recolouring.lift_circuitCount`는 active와 inactive를 모두 포함한 각 색에 대해

```text
circuitCount(lifted recolouring) = circuitCount(old recolouring)
```

를 증명한다. 표시점은 `U×{0}` 한 복사본으로 전달한다. Patch의 합성 순서는 `S ∘ r`이다.
U를 만나지 않는 회로도 회로 수 공식에 포함하며, 빈 U도 허용한다. 패치된 각 회로의
길이가 일률적으로 m배가 된다는 주장은 없다. 기존 one-gap 정리는 첫 귀환과 정확한
roof 갱신을 함께 제공한다.

## 짝수 차원 specialization과 남은 작업

`OneDirection.factorization`은 `T_m(d)`에서 각 색에 하나의 positive m-cycle을 준다.
전체 정점 집합이 한 fibre이고, circuit label 집합은 `Fin d`와 동치다. 따라서 유일한
incidence component의 열 수는 짝수 d다. Active palette와 U를 비우고 identity
recolouring을 적용하면 closure로 모든 짝수 d≥2를 얻는다.

`Endpoints.even_modulus_tori_all_dimensions_of_collar`의 짝수 차원 분기도 이 정리를
직접 사용한다. 홀수 차원은 기존 D3/D5와 아직 가정인 `EvenOddDegreeGoal`에 의존한다.
E5의 near-core, 네 anchor에서의 일치와 회로 대표성, active voltage의 unit/gap 조건은
[entry 진행 문서](ENTRY_PROGRESS_20260911.md)의 범위까지 증명되었다. Cyclic-star와
실제 near-core 대체의 Hamilton성도 [모든 짝수 m≥4](STAR_UNIFORM_PROGRESS_20260911.md)에서
닫혔다. [Shell과 합성 seed](SHELL_PROGRESS_20260911.md)도 구성되었고, 남은 작업은
seed incidence parity, matched selection, p=2 / p=3 / p≥4 entry다.
기존 Route E의 D3 Hamilton 분해만으로 anchored agreement를 대체할 수는 없다.

## 검증과 보존

- 지정 CPU 노드에서 `lake build TorusEven` 통과. 새 모듈과 의존 경로를 빌드했으며
  mathlib 전체의 clean rebuild는 아니다. 새 Collar 코드에 linter 경고가 없다.
- Isolation 검사 통과: main-path 59개, attic 4개, 등록된 native 사용 파일 3개.
  새 코드에 `sorry`, `admit`, author axiom, `native_decide`가 없다.
- 이번 주요 선언 24개의 axiom은 모두 `propext`, `Classical.choice`, `Quot.sound`의
  부분집합이다. 기존 전체 차원 조건부 endpoint의 native axiom은 18개로 동일하다.

산출물은 `/fsx/angel/operations/torus-lean-closure-20260911/`에 있다:
[빌드 로그](/fsx/angel/operations/torus-lean-closure-20260911/full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-closure-20260911/ClosureAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-closure-20260911/axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-closure-20260911/verification.json).
Manifest에 CPU와 유지 소스의 SHA256 일치, commit, 복구 bundle을 기록한다.

유지 소스는 제어 노드 `/local/angel/etc/Torus-Hamilton-Decomposition-Program`이다.
CPU `root@jcssh-hp.mewtant.io:31630`의 실행 사본은
`/local/angel/lean-collar/Torus-Hamilton-Decomposition-Program`이다. 이 사본의 Git HEAD는
동기화된 소스의 식별자가 아니므로 파일 hash로 검증한다. 도구체인은 같은 노드의
`/local/angel/lean-collar/leanprover--lean4---v4.30.0-rc2/bin`, mathlib SHA는
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`이다.
