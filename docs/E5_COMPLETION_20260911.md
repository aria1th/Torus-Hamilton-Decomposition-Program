# E5 entry와 전체 차원 정리

`TorusEven.even_odd_degree : EvenOddDegreeGoal`을 증명했다. 모든 홀수 d≥7과 짝수
m≥4에서 구체적인 seed, 첫 split, anchored recolouring, collar closure로 Hamilton
분해를 얻는다. 짝수 전체 차원 endpoint의 추가 입력은 없어졌다.
`TorusAll.all_moduli_tori_all_dimensions`는 기존 홀수 v75 정리를 결합하여 모든
d≥2, m≥3을 다룬다. 짝수 라이브러리는 홀수 core를 import하지 않는다.

| 결과 | 선언 |
|---|---|
| 모든 p≥2의 실제 mate 삭제 후 nonmate parity | `Entry.Seed.residual_even` |
| 정확한 quota·unit carry·coherence와 지정된 active 위치 | `Entry.Seed.exists_matchedSelection` |
| 실제 회로 label 선택과 `anchorVoltage` 일치 | `Entry.Seed.exists_blockSelection` |
| 모든 p≥2, 짝수 m≥4의 D₂ₚ₊₃(m) 분해 | `Entry.Seed.hamilton_decomposition` |
| 모든 홀수 d≥7의 짝수 법수 분해 | `even_odd_degree` |
| 추가 입력 없는 짝수 전체 차원 정리, 두 조립 경로 | `even_modulus_tori_all_dimensions`, `even_modulus_tori_all_dimensions_collar` |
| 모든 d≥2, m≥3 | `TorusAll.all_moduli_tori_all_dimensions` |

## 실제 entry 구성

`MatchAnchors`는 네 block/row 좌표와 실제 anchor를 일치시킨다. `Mates`는 p=3의
작은 mate 표와 그 외 p의 일반 표를 구현하며, 자격·단사성과 전체 support 일치를
증명한다. `residualNat_subset`은 0≤h,w<4의 삭제된 행을 모든 m≥4의 실제
residual support에 전달한다.

Nonmate는 `nonmatePairs`로 완전히 짝지어진다. 짝수 p≥4에서는 A와 B 각각의
양수 인덱스 색들을 연결하며 p=4의 B₂/B₃는 높이 3의 행을 사용한다. 홀수 p≥5에서는
A₀ 이외의 모든 색을 B₀에 연결한다. p=2에는 nonmate가 없고, p=3에는 B₁/B₂만
있으며 (h,w)=(0,1)에 함께 있다. `evenOnComponents_of_pairs`가 모든 경우의 필요한
residual parity를 준다. 원고의 정확한 성분 분류나 고립성 전체를 주장하는 증명은
아니다. 이미 증명한 [일반 matched selection](MATCHED_PROGRESS_20260911.md)을
p=2·3에도 적용하므로 별도의 작은 selector 구현은 필요하지 않다.

`IsPinnedSelection.map`으로 명시적인 색을 실제 회로 quotient label로 옮긴다.
`exists_blockSelection`은 active source가 네 anchor뿐임을 실제 `splitVoltage`의
함수 동치로 증명한다. 기존 `anchorVoltage_gapSupport`를 그대로 적용하여 첫 split이
collar 조건을 만들고 Hamilton replacement를 전달한다.

Closure의 excess 귀납은 임의의 유한 palette로 일반화했다. 마지막 unit-width
factorization에서만 색을 `Fin (Fintype.card C)`로 재색인한다. 기존 `Fin d` closure와
entry API는 보존된다. `EvenOddDegreeGoal`을 가정하는 종전 wrapper도 호환성을 위해
남지만, 새 최종 정리는 이 증명을 직접 사용한다.

## 검증과 복구

CPU `lake build TorusEven TorusAll` 통과(8559 jobs), 새 코드 경고 0개.
`TorusAll`을 포함한 기본 `lake build`도 통과했다(8579 jobs).
Isolation 통과: even main-path 140개, attic 4개, 등록된 native 파일 3개.
추가한 61개 공개 선언과 기존 주요 API를 포함해 68개 선언을 audit했다. 새 선언 중
58개는 `even_odd_degree`를 포함해 표준 axiom만 사용하며, E4 closure도 동일하다.
나머지 세 선언은
최종 조립 정리로, 짝수 두 경로의 native leaf는 기존과 같은 18개이고 모든 법수
정리는 기존 홀수 경로 88개와 합쳐 106개다. 새 native leaf는 없다.

추가 입력 없는 목표 타입 네 개도 Lean으로 확인했다. 유지 소스와 CPU 사본의
Lean 소스·설정 277개가 SHA256으로 일치한다. Lean 4.30.0-rc2,
mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`과 기존 캐시를 사용했다.

산출물은 `/fsx/angel/operations/torus-lean-residual-20260911/`에 있다:
[전체 빌드](/fsx/angel/operations/torus-lean-residual-20260911/full-build.log),
[기본 빌드](/fsx/angel/operations/torus-lean-residual-20260911/default-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-residual-20260911/FinalAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-residual-20260911/axioms.log),
[axiom 목록과 개수](/fsx/angel/operations/torus-lean-residual-20260911/axiom-summary.json),
[검증·복구 manifest](/fsx/angel/operations/torus-lean-residual-20260911/verification.json).
Manifest에 최종 commit과 matched-selection commit `5e63262`에서 이어지는 검증된
복구 bundle을 기록한다. 원격 push나 GitHub release는 수행하지 않았다.
