# E5 cyclic-star 진행

원고의 anchored cyclic-star 방향표가 실제 factorization과 near-core recolouring을
정의함을 모든 m≥4에서 증명했다. Hamilton성은 실제 2m개 표시점의 귀환 순열로
환원했고, m=4,6은 커널 `decide`로 닫았다. 일반 짝수 m의 cyclic-star Hamilton성과
E5 전체는 아직 열려 있다.

## 원고와 Lean 대응

선언은 `TorusEven.Entry.Star` 아래에 있다. 원고는
`paper/torus_integrated_proof/even_directed_tori_integrated.tex`의
`lem:star`, `prop:anchor`, `app:star`를 따른다.

| 원고의 주장 | Lean 선언 | 증명 범위 |
|---|---|---|
| 세 ray와 색의 회전 대칭 | `row_rotate`, `surgeryMap_rotate` | 모든 m |
| P₀가 Q에서 하나의 2m-순환이고 밖에서는 항등 | `surgery_word`, `surgery_zero_outside`, `zeroPerm_orbit_card` | m≥4 |
| terminal row의 유효한 factorization과 대체 recolouring | `factorization`, `replacement`, `replacement_step` | m≥4 |
| 높이 한 바퀴의 귀환은 trᵥP꜀ | `carry_sum`, `height_return` | m≥4 |
| 색 0의 평면 귀환 Hamilton성에서 전체 세 색의 Hamilton성 | `hamilton_of_return`, `replacement_hamilton_of_return` | m≥4, 명시된 귀환 가정 아래 |
| 모든 translation 회로가 Q를 만남 | `voltage_meets_support` | 짝수 m>0 |
| 평면 귀환과 Φ=νP₀의 회로 수 일치 | `markedReturn_word`, `return_circuitCount` | 짝수 m≥4 |
| 실제 anchored cyclic-star의 Hamilton성 | `hamilton_four`, `hamilton_six` | m=4,6 |
| `eq:small-star-cycle`의 내부 순환 Γ=θ∘(+4) | `InnerReturn.step_order`, `InnerReturn.hamilton` | q≥2, a=2q+1 |

`word : ZMod m × ZMod 2 → Plane m`은
C⁺, X₁,…,Xₘ₋₁, C⁻, Y₁,…,Yₘ₋₁을 나열한다. `wordStep`은 첫 좌표를 1 증가시키고
wrap에서만 두 번째 좌표를 바꾼다. 기존 additive lift 정리로 이 순환을 증명하고,
`word_injective`로 평면에 옮겨 실제 surgery map의 전단사성을 얻었다.

물리 좌표는 `(h,(a,b)) ↦ (h−a−b−3,a,b+3)`이며, 색에는 원고의 `(1 2)` 교환을
적용한다. 따라서 `factorization.direction`은 기존 `terminalRow`와 정확히 같고,
기존 네 anchor의 방향 일치도 이 구성에 적용된다. `replacement`는 같은
`replacementSupport` 밖에서 near-core와 일치하는 실제 recolouring이다.

`OneSpecial.lean`은 한 높이에서만 임의의 permutation을 적용하고 다른 높이에서는
평행이동하는 일반 귀환 정리를 제공한다. 이 정리와 `carry_sum`이 다음 벡터를 준다.

| 조건 | v₀ | v₁ | v₂ |
|---|---|---|---|
| 3∤m | (1,−2) | (1,1) | (−2,1) |
| 3∣m | (1,3) | (−4,1) | (3,−4) |

`Support.lean`은 표시 집합을 단순한 목록과 동일시하는 데서 그치지 않고, 실제
translation의 `retPerm`으로 `markedReturn`을 정의한다. 모든 translation 회로가
Q를 만남을 증명하여 surgery 정리의 unhit 회로 항을 0으로 만든다. 이에 따라
`hamilton_of_markedReturn`의 남은 가정은 이 구체적인 2m점 permutation의 순환성이다.

## 다음 증명 경계

1. `markedReturn`에서 X₁,…,Xₘ₋₁로의 첫 귀환 Ψ와 시간을 증명한다.
   원고 `eq:star-table-nondiv`, `eq:star-divisible-return`의 최소 양의 hitting time과
   중간 X 방문 부재, 귀환 시간 합 2m을 실제 `retPerm`에 연결해야 한다.
2. 3∤m에서는 Ψ=θβ의 순환성을 두 합동류로 나누어 증명한다.
   3∣m에서는 Ψ의 I={1,…,2q+1} 귀환을 `InnerReturn.step`에 연결한다.
   현재 `InnerReturn.hamilton`은 명시적 내부 순환 자체의 정리이며,
   이 연결이나 일반 법수의 `markedReturn` Hamilton성을 가정 없이 주지는 않는다.
3. `markedReturn`의 일반 Hamilton성을 닫고 `replacement_hamilton_of_return`에 넣는다.
   이후 E5의 shell, seed incidence, matched selection, p별 entry 조립을 진행한다.

유한 법수 결과를 일반 법수로 외삽하지 않았고, 기존 Route E의 D3 Hamilton 정리로
anchored 구성의 증명을 대신하지 않았다. `EvenOddDegreeGoal`은 계속 남아 있다.

## 검증과 복구

지정 CPU 노드에서 `lake build TorusEven` 통과(8442 jobs). 새 Star 코드의 linter
경고는 없다. Isolation 검사도 통과했다: main-path 84개, attic 4개, 등록된 native
사용 파일 3개. 새 코드에는 `sorry`, `admit`, author axiom, `native_decide`가 없다.

주요 새 선언 41개의 axiom은 모두 `propext`, `Classical.choice`, `Quot.sound`의
부분집합이다. m=4,6의 증명도 표준 axiom만 사용한다. `even_degree_collar`는 계속
표준 axiom만 사용하며, 조건부 전체 차원 endpoint의 기존 native axiom 18개는 같다.

유지 소스와 CPU 실행 사본, Lean/mathlib 버전은 [entry 기록](ENTRY_PROGRESS_20260911.md)과
같다. CPU에서 검사한 Lean 소스 85개(root 포함)의 SHA256이 유지 소스와 모두 일치한다.
이번 빌드는 기존 mathlib 산출물을 재사용했다.

검증 산출물은 `/fsx/angel/operations/torus-lean-star-20260911/`에 보존한다:
[빌드 로그](/fsx/angel/operations/torus-lean-star-20260911/full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-star-20260911/StarAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-star-20260911/axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-star-20260911/verification.json).
Manifest가 유지 소스 commit, CPU receipt, 복구 bundle과 이전 entry bundle을 연결한다.
