# E5 cyclic-star: 3의 배수인 법수

모든 짝수 m≥4 중 3∣m인 경우, 원고의 anchored cyclic-star와 실제 near-core 대체
recolouring의 세 색이 모두 Hamilton임을 증명했다. 일반 법수 부분은 m=6q, q≥2에서
기호적으로 증명하며, m=6은 앞서 증명한 커널 `decide` 결과를 사용한다.
E5에서 cyclic-star의 남은 경우는 3∤m인 일반 법수다(m=4는 이미 증명됨).

## 닫힌 정리

최종 선언은 `TorusEven.Entry.Star` 아래에 있다.

| Lean 선언 | 결론 |
|---|---|
| `return_hamilton_three_dvd` | 색 0의 실제 평면 귀환 tr₍₁,₃₎P₀가 단일 순환 |
| `hamilton_three_dvd` | 원고 `terminalRow` factorization의 세 색이 모두 Hamilton |
| `replacement_hamilton_three_dvd` | 실제 near-core recolouring의 세 색이 모두 Hamilton |

위 정리들의 가정은 `[NeZero m]`, `4 ≤ m`, `Even m`, `3 ∣ m`이다.
별도의 귀환 순환성이나 표 인증서를 가정하지 않는다. 기존 네 anchor의 일치와
replacement support를 그대로 쓰므로 이 결과를 E5의 anchored 대체에 사용할 수 있다.

## 실제 귀환과 원고 부록의 연결

`Hitting.lean`은 Q의 소속 조건을 두 축과 두 모서리로 분해하고, 유계 자연수 좌표의
ZMod 등식을 네 가능한 대표값으로 바꾼다. `DivTranslation.lean`의 아홉 정리는
tr₍₁,₃₎의 첫 Q 교차점과 그 이전에 Q를 만나지 않음을 증명한다. 이를 P₀ 뒤에 합성한
`DivMarked.lean`은 기존의 실제 `markedReturn`을 그대로 계산한다.

`Divisible.return_x_table`은 이 Φ의 X축 첫 귀환을 다음처럼 증명한다. 시간은
물리 간선 수가 아니라 Φ의 적용 횟수다. 빈 구간에는 입력이 없다.

| X의 label s | 귀환 label Ψ(s) | 첫 귀환 시간 |
|---|---|---|
| 1≤s<4q−1 | s+2q+1 | 1 |
| s=4q−1 | 2q | 1 |
| s=4q | 1 | 5 |
| s=4q+1 | 2q+1 | 4 |
| 4q+2≤s<6q−2 | s−4q | 4 |
| s=6q−2 | 2q−1 | 5 |
| s=6q−1 | 2q−2 | 3 |

각 경로의 중간점이 X에 속하지 않음을 증명하여 실제 `retTime`과 `ret`의 등식을 얻었다.
`Divisible.phi_ret_x`는 이 귀환이 원고의 Ψ=θβ와 같음을 연결한다. Ψ는
`Fin (6*q-1)`의 0부터 시작하는 index로 구현되어 있으며, `xEmbedding`이 원고의
1부터 시작하는 X label로 옮긴다.

`Divisible.psi_inner_return`은 I={1,…,2q+1}에서의 2·3단계 귀환을 기존
`InnerReturn.step` Γ에 연결한다. `psi_meets_inner`는 모든 Ψ 궤도가 I를 만남을
증명하며, `psi_hamilton`은 기존 Γ의 순환성을 이용해 Ψ의 Hamilton성을 닫는다.

`Divisible.phi_meets_x`는 Y label에 대한 감소 귀납과 모서리 계산으로 모든 Φ 궤도가
X를 만남을 증명한다. 따라서 `phi_hamilton`은 실제 Φ의 단일 순환을 주고,
`sum_return_times`는 실제 첫 귀환 시간의 합이 12q=2m임을 준다. 기존 평면·높이 귀환
환원으로 최종 세 색의 Hamilton성을 얻는다. 일반 연결 정리
`Surgery.singleCycle_of_induced_orbits`는 위 두 단계에서 재사용한다.

## 검증과 다음 지점

지정 CPU 노드에서 `lake build TorusEven` 통과(8451 jobs), 새 Star 코드의 linter
경고 0개. Isolation 통과: main-path 93개, attic 4개, 등록된 native 사용 파일 3개.
주요 새 선언 40개는 모두 표준 axiom `propext`, `Classical.choice`, `Quot.sound`만
사용한다. 새 `sorry`, `admit`, author axiom, `native_decide`는 없다.
기존 전체 차원 조건부 endpoint의 axiom 집합도 native leaf 18개를 포함해 그대로다.

검증 산출물은 `/fsx/angel/operations/torus-lean-star-return-20260911/`에 있다:
[빌드 로그](/fsx/angel/operations/torus-lean-star-return-20260911/full-build.log),
[audit 소스](/fsx/angel/operations/torus-lean-star-return-20260911/DivisibleAudit.lean),
[axiom 출력](/fsx/angel/operations/torus-lean-star-return-20260911/axioms.log),
[검증 manifest](/fsx/angel/operations/torus-lean-star-return-20260911/verification.json).
Manifest에 소스 commit, CPU 소스 해시 일치, 이전 단계와 연결한 복구 bundle을 기록한다.
노드 경로와 도구 버전은 [이전 Star 기록](STAR_PROGRESS_20260911.md)과 같다.

다음은 3∤m, m=2k인 경우의 tr₍₁,₋₂₎ 첫 교차점과 `eq:star-table-nondiv`를 증명하고,
k mod 3에 따른 Ψ=θβ의 순환성을 연결하는 작업이다. 이 경우를 닫은 뒤에도 E5의
shell, seed incidence, matched selection, p별 entry 조립과 `EvenOddDegreeGoal`은 남는다.
