# E5 anchored entry 진행

E5의 near-core 보조정리와 네 anchor의 회로 대표성, active voltage의 unit/gap 조건을
Lean으로 증명했다. E5 전체와 `EvenOddDegreeGoal`은 아직 열려 있다. E4 closure는
완료 상태이며, 전체 차원 endpoint의 가정은 계속 `EvenOddDegreeGoal` 하나다.
후속 cyclic-star 구현과 현재 귀환 증명 경계는 [star 진행 문서](STAR_PROGRESS_20260911.md)에 있다.

## 증명된 원고 대응

| 원고의 주장 | Lean 선언 (`TorusEven.Entry` 아래) |
|---|---|
| Table nearcore의 방향과 유효한 factorization | `NearCore.factorization`, `step_eq` |
| (F_0,F_1) Hamilton | `NearCore.hamilton` |
| (F_2)의 회로 수 2, 전체 회로 열 수 4 | `NearCore.circuitCount`, `circuitLabel_card` |
| ε = w − max(h−2,0) mod 2가 정확히 두 회로를 구별 | `NearCore.orbit_defect_iff` |
| (F_2)의 각 회로 길이 (m^3/2) | `NearCore.orbit_card_two` |
| 고정된 (h,w)에서 x를 바꾼 블록의 방향·회로 일관성 | `xChart_consistent` |
| 네 anchor에서 near-core와 terminal row 일치 | `anchor_agreement`, `anchor_outside` |
| 각 anchor의 지정된 색이 x 방향을 사용 | `anchor_direction`, `anchorLabel_mem` |
| 네 anchor와 실제 전체 회로 열 사이의 전단사 | `anchorEquiv` |
| 각 실제 회로에서 anchor 하나만 선택하는 voltage | `anchorVoltage_single`, `anchorVoltage_unit`, `anchorVoltage_gapSupport` |

Near-core는 높이 증가에 대한 두 번의 additive lift로 구성한다. 첫 번째 lift의
m-step 귀환은 w를 각각 1, 1, −2만큼 옮긴다. `HeightReturn`은 고정 높이 단면의
첫 귀환 시간 m과 귀환 permutation을 증명하고, `EvenTranslation`은 −2 평행이동의
궤도가 짝홀 fibre와 정확히 같음을 증명한다. 두 번째 lift에서 앞의 두 색은 carry −1,
세 번째 색은 각 base 궤도에서 한 점의 carry 1을 받는다.

`NearCore.chart`의 fibre는 y이고, 원고의 entry row는 x다. `xChart`와
`xChart_consistent`가 이 좌표 변환을 처리한다. Defect의 높이는 `ZMod.val`로 취하며,
자연수 뺄셈 `h.val - 2`가 원고의 max와 같다. 높이 wrap도 포함하여 불변성을 증명했다.

## 첫 split과 closure 연결

`Collar.BlockSelection.enters_collar`는 기존 블록의 circuit consistency, full-column
incidence parity, active separation, 유효한 선택과 active `GapSupport`에서 첫 split
뒤의 완전한 `RelativeCollarState`를 만든다. 이때 선택의 reserved palette는 비어 있어
entry에서 active anchor를 선택할 수 있다. 기존 상태가 이미 collar라는 가정은 없다.

`Recolouring.split`은 같은 gap 조건으로 recolouring의 head routing과 모든 색의 회로
수를 보존한다. 기존 `Recolouring.lift` API는 이 일반 정리의 특수화로 유지된다.
`Recolouring.ofReplacement`는 같은 위치 밖에서 일치하는 두 유효한 factorization을
실제 boundary permutation과 recolouring으로 변환한다.

`Collar.hamilton_decomposition_of_entry`가 위 데이터를 E4 closure와 연결한다.
이 정리는 구체적인 selection과 Hamilton replacement를 입력받는 연결 정리다.
현재 증명된 `anchorVoltage`가 전체 shell을 포함한 선택의 active 부분으로 실현된다는
증명은 아래 matched selection 작업에 남아 있다.

## 다음 증명

1. Cyclic-star 대체 core의 일반 Hamilton성: 유효한 factorization과 recolouring,
   실제 2m점 귀환 순열로의 환원, m=4,6의 Hamilton성은 후속 구현에서 증명했다.
   이어 [3∣m인 모든 짝수 법수](STAR_DIVISIBLE_PROGRESS_20260911.md)의 Hamilton성을 닫았다.
   3∤m의 일반 귀환 표와 순환성 연결이 남아 있다.
2. Auxiliary shell 구성·Hamilton성, core와의 superposition, seed incidence parity.
3. 네 mate를 예약한 matched selection: residual component의 parity, 혼합 divergence,
   정확한 quota와 child coherence, active 선택과 `anchorVoltage`의 일치.
4. p=2, p=3의 구체적인 entry 및 p≥4의 일반 entry를 연결해 `EvenOddDegreeGoal` 제거.

기존 Route E의 D3 Hamilton 정리는 이 cyclic-star row와 anchor 일치를 보장하지 않는다.
위의 구체적인 입력을 새 가정으로 포장하는 것으로 E5를 완료 처리하지 않는다.

## 검증과 복구

아래는 near-core 단계의 검증 기록이며, 후속 Star 모듈의 검증은 위 문서에 별도로 기록한다.

지정 CPU 노드에서 `lake build TorusEven` 통과(8432 jobs). 새 Entry와 변경된 Collar
코드에 linter 경고가 없다. Isolation 검사 통과: main-path 74개, attic 4개, 등록된
native 사용 파일 3개. 새 코드에는 `sorry`, `admit`, author axiom, `native_decide`가 없다.

주요 새 선언 39개의 axiom은 모두 `propext`, `Classical.choice`, `Quot.sound`의
부분집합이다. 기존 `even_degree_collar`도 표준 axiom만 사용하며, 전체 차원 조건부
endpoint의 native axiom 18개는 그대로다.

산출물은 `/fsx/angel/operations/torus-lean-entry-20260911/`에 있다:
[빌드 로그](/fsx/angel/operations/torus-lean-entry-20260911/full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-entry-20260911/EntryAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-entry-20260911/axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-entry-20260911/verification.json).
Manifest에 유지 소스 commit, CPU 소스 hash 일치, 복구 bundle을 기록한다.

유지 소스는 제어 노드 `/local/angel/etc/Torus-Hamilton-Decomposition-Program`이다.
CPU 실행 사본은 `root@jcssh-hp.mewtant.io:31630`의
`/local/angel/lean-collar/Torus-Hamilton-Decomposition-Program`이다.
CPU Git HEAD 대신 소스 SHA256으로 빌드 대상을 확인한다. Lean 4.30.0-rc2와 mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`을 사용했다.
