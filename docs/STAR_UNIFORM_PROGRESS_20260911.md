# E5 cyclic-star: 모든 짝수 법수의 Hamilton성

원고의 anchored cyclic-star와 실제 near-core 대체 recolouring의 세 색이 모두
Hamilton임을 모든 짝수 m≥4에서 증명했다. 이전 3∣m 결과에 3∤m인 경우를 합쳤다.
E5에서 남은 부분은 auxiliary shell, seed incidence, matched selection과 p별 entry
조립이다. 전체 차원 endpoint의 `EvenOddDegreeGoal` 가정은 아직 남아 있다.

## 닫힌 정리

선언은 `TorusEven.Entry.Star` 아래의 `Hamilton.lean`에 있다.

| Lean 선언 | 결론 |
|---|---|
| `return_hamilton` | 색 0의 실제 평면 귀환 trᵥP₀가 단일 순환 |
| `hamilton` | 원고 `terminalRow` factorization의 세 색이 모두 Hamilton |
| `replacement_hamilton` | 실제 near-core 대체 recolouring의 세 색이 모두 Hamilton |

가정은 `[NeZero m]`, `4 ≤ m`, `Even m`이다. 귀환 순환성이나 표 인증서를 추가로
가정하지 않는다. 기존 `anchor_agreement`와 같은 terminal row를 쓰며,
`replacement`가 `replacementSupport` 밖에서 near-core와 일치하므로 E5의 대체 core로
사용할 수 있다. m=4,6은 기존 커널 `decide`, 나머지 법수는 기호적 증명으로 처리했다.

## 3∤m인 실제 귀환 표

m=2k, k≥4에서 `NondivTranslation.lean`은 tr₍₁,₋₂₎의 아홉 첫 교차 공식을 증명한다.
`translation_ret_neg_two_nat`는 음의 두 번째 좌표를 유계 자연수 대표값으로 옮긴다.
그 뒤 축·모서리의 소속 조건과 중간 시각의 비소속을 선형 정수 산술로 확인한다.
`NondivMarked.lean`은 이 결과를 실제 `markedReturn` Φ=νP₀에 연결한다.

`Nondivisible.return_x_table`은 원고 `eq:star-table-nondiv`를 그대로 실현한다.
귀환시간은 물리 간선 수가 아니라 Φ의 적용 횟수다.

| X label s | 첫 귀환 Ψ(s) | 시간 ρ(s) |
|---|---|---|
| 1≤s≤k−2 | s+k+1 | 1 |
| s=k−1 | k | 1 |
| k≤s≤2k−3 | s−k+2 | 3 |
| s=2k−2 | k+1 | 4 |
| s=2k−1 | 1 | 3 |

각 경로의 중간점이 X에 속하지 않음을 증명하여 실제 `retTime`과 `ret`의 등식을
얻었다. `phi_ret_x`는 이 귀환을 `Fin (2*k-1)` 위의 구체적인 순열 `psi`와 연결한다.
`xEmbedding`은 0부터 시작하는 index를 원고의 1부터 시작하는 X label로 옮긴다.

## Ψ의 기호적 순환성

Lean에서는 원고의 gcd·세 점 절단 논증 대신 같은 Ψ를 L={1,…,k−1}로 한 번 더
줄인다. `lower_step`은 다음 χ와 Ψ의 2·3단계 경로를 연결한다.

| L label s | χ(s) | Ψ 적용 횟수 |
|---|---|---|
| 1≤s≤k−4 | s+3 | 2 |
| s=k−3 | 3 | 3 |
| s=k−2 | 1 | 2 |
| s=k−1 | 2 | 2 |

`NondivInner.lean`은 k=3q+r, q≥1, r∈{1,2}를 하나의 명시적 순서 공식으로 처리한다.
물리 label의 순환 순서는 다음과 같다.

- k=3q+1: (1,4,…,3q−2), (3,6,…,3q), (2,5,…,3q−1).
- k=3q+2: (1,4,…,3q+1), (2,5,…,3q−1), (3,6,…,3q).

`order`의 전단사성과 `chi_order`의 순서 보존으로 `chi_hamilton`을 얻는다.
일반 정리 `Surgery.singleCycle_of_cyclic_order`는 이 순서를 ZMod의 +1 순환에 연결한다.
`psi_meets_lower`는 모든 Ψ 궤도가 L을 만남을 보이며,
`singleCycle_of_induced_orbits`가 χ의 순환성을 Ψ로 올린다.

`phi_meets_x`는 Y label의 짝홀과 두 모서리를 계산하여 모든 Φ 궤도가 X를 만남을
증명한다. 같은 일반 정리로 Φ의 Hamilton성을 얻고, `sum_return_times`는 실제
첫 귀환시간의 합이 4k=2m임을 준다. 기존 평면·높이 귀환 정리를 적용하면 세 색의
Hamilton성이 따른다. [3∣m의 증명](STAR_DIVISIBLE_PROGRESS_20260911.md)과 합쳐
`Hamilton.lean`의 uniform 정리를 얻는다.

## 검증과 복구

지정 CPU 노드에서 `lake build TorusEven` 통과(8460 jobs), 새 Star 코드의 linter
경고 0개. Isolation 통과: main-path 102개, attic 4개, 등록된 native 사용 파일 3개.
새 공개 선언 83개 모두 표준 axiom `propext`, `Classical.choice`, `Quot.sound`의
부분집합만 사용한다. 새 `sorry`, `admit`, author axiom, `native_decide`는 없다.
`even_degree_collar`도 표준 axiom만 쓰며, 기존 조건부 전체 차원 endpoint는
native leaf 18개를 포함해 이전 axiom 집합을 그대로 유지한다.

유지 소스와 지정 CPU의 Lean 소스 103개(root 포함)의 SHA256이 모두 일치한다.
실행 사본의 Git HEAD는 오래된 값이므로 빌드 소스는 파일 해시로 식별했다.
Lean 4.30.0-rc2와 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`을 사용했으며,
기존 mathlib 빌드 산출물을 재사용했다. 노드 경로는 [entry 기록](ENTRY_PROGRESS_20260911.md)과 같다.

산출물은 `/fsx/angel/operations/torus-lean-star-nondiv-20260911/`에 있다:
[빌드 로그](/fsx/angel/operations/torus-lean-star-nondiv-20260911/full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-star-nondiv-20260911/NondivAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-star-nondiv-20260911/axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-star-nondiv-20260911/verification.json).
Manifest에 소스 commit, CPU receipt, 이전 divisible 단계에서 이어지는 복구 bundle을 기록한다.

후속 [shell과 seed 기록](SHELL_PROGRESS_20260911.md)에서 auxiliary shell 구성과
Hamilton성, core와의 superposition을 완료했다. 남은 seed incidence parity, 네 mate를
예약한 matched selection, p=2 / p=3 / p≥4 entry는 [E5 계획](E5_REMAINING_PLAN_20260911.md)을
따른다. 이 입력들을 조립해야 `EvenOddDegreeGoal`을 제거할 수 있다.
