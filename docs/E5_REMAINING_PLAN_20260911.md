# E5 남은 형식화 계획

목표는 원고 `thm:oddconstruction`을 `EvenOddDegreeGoal`로 증명하여 전체 짝수 법수
endpoint의 마지막 가정을 제거하는 것이다. 출발 소스는 `6f16b8d`다. E4 closure,
near-core, 네 anchor와 unit/gap voltage, 모든 짝수 m≥4의 cyclic-star Hamilton성은
완료되었다. 아래 선언명은 새로 구현할 목표 이름이며, 기존 정리와 구분한다.

## 의존관계와 완료 기준

| 순서 | 원고와 구현 범위 | 완료할 결과 | 현재 상태 |
|---|---|---|---|
| 1 | `eq:shell-W`, `tab:shellpairs`, `lem:shell` | `Shell.factorization`, `Shell.hamilton`, `(h,w)` 블록 일관성 | 완료 |
| 2 | `eq:seed-widths`, `eq:seed-columns` | core/shell의 실제 합성 `Seed.factorization`, 회로 열 전단사, anchored replacement Hamilton성 | 완료 |
| 3 | `lem:seed-incidence`, `lem:small-seed` | 각 방향의 전체 orbital incidence가 성분별 짝수; p=2,3의 명시적 분할 포함 | 진행: 실제 support 표와 parity 전달 완료 |
| 4 | `lem:matched` | 지정된 열의 parity join, 혼합 divergence, reserved-slot 선택의 quota·unit·양쪽 coherence | 예정 |
| 5 | `lem:entry-components`, `lem:entry-seven`, `lem:entry-nine` | mate의 자격·단사성, 잔여 성분 계산, 실제 `BlockSelection`과 active voltage 일치 | 예정 |
| 6 | `prop:entry`, `thm:oddconstruction` | entry state와 Hamilton recolouring, `even_odd_degree : EvenOddDegreeGoal`, 무조건부 전체 차원 endpoint | 예정 |

1→2→3과 4는 논리적으로 분리된다. 5에서 2·3·4를 결합하고, 6은 이미 증명한
`Collar.hamilton_decomposition_of_entry`와 closure를 사용한다.

## 구현 선택

Shell의 색은 A₀,…,Aₚ₋₁,B₀,…,Bₚ₋₁의 순서로 표현한다. 원고의 pair 목록과 고정
filler를 그대로 정의한다. `Collar.LocalPairs.row`의 subset·cardinality·sum·coherence를
재사용하고, 각 보조 색이 정확히 한 pair에 속함을 전단사로 증명한다. 첫 번째
lift의 carry는 A에서 −1, B에서 +1이고, 두 번째 lift의 carry도 각 색마다 ±1이다.
두 번의 `lift_singleCycle`과 기존 물리 chart가 shell Hamilton성을 준다.

Seed는 별개 palette를 가진 두 유효한 factorization의 합성으로 만든다. 회로 열은
네 active 회로와 2p개 auxiliary 색으로 명시적으로 식별한다. 이를 실제
`blockSupport xChart`와 연결한 뒤 incidence를 계산한다. 전체 incidence와 mate 삭제
뒤의 incidence를 혼동하지 않는다. 특히 p=4와 m=4에 필요한 연결 행을 포함한다.

Matched selection은 기존 pinned 선택 정리의 가정을 강화하여 호출하는 방식으로
처리할 수 없다. 잔여 그래프에서 nonmate에만 홀수 차수, mate에는 짝수 차수가 필요하다.
`ParityJoin`과 `BalancedOrientation`의 기존 증명을 지정된 홀수 열에 대한 형태로
확장하고 기존 API는 그 특수화로 보존한다. Reserved slot은 active에 실제 합 1,
mate에 m−1을 주며, 나머지 pair/filler 행이 각 quota를 정확히 채우게 한다.
Anchored 행의 사건 rank 0,1,2와 baseline rank 3을 써서 두 child의 coherence를 증명한다.

p=2는 양쪽 child 폭이 1인 직접 선택, p=3은 추가 블록 (h,w)=(0,1)의 B₁/B₂ 선택을
사용한다. p≥4에는 원고의 일반 mate 표와 잔여 성분 정리를 적용한다. 모든 경우에
선택한 active source가 기존 `anchorVoltage`와 같음을 증명하여 `GapSupport`를 전달한다.

## 검증과 기록

각 완료 단계는 지정 CPU 사본에서 Lean을 컴파일하고, 기존 endpoint와 새 주요 정리의
axiom을 검사한다. 새 `sorry`, author axiom, `native_decide`를 도입하지 않는다.
통합 시 `lake build TorusEven`, isolation, 소스 SHA256 일치를 확인한 뒤 focused commit과
FSx bundle을 보존한다. 작업 중 추가 가정으로 미완료 명제를 감춘 정리는 완료로 세지 않는다.

현재 검증된 경계는 [shell과 seed 기록](SHELL_PROGRESS_20260911.md)이다.
이번 shell 작업 산출물은 `/fsx/angel/operations/torus-lean-shell-20260911/`에 보존한다.
