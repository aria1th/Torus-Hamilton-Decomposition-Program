# 저자 질문서 — W2: `lem:completion-fiber-bijectivity`의 RF2 (2026-06-10)

대상: `even_modulus_directed_tori.tex` v28, `subtex/endpoint_successor.tex`
(`def:cyclic-completion-rows` :114–123, `def:lifted-completion-fiber` :265–281,
`lem:completion-fiber-bijectivity` :283–298, `lem:endpoint-local-row-realization`
:300–335). 발견 경로: H6 형식화의 displacement 예산 검사
(`E6_DESIGN_20260610.md` §4.2, Wall 2).

## 0. 형식화가 사용하는 정확한 RF2 기준 (검증된 동치)

layer t에서 행이 부분집합 U 위에서 σ, 밖에서 ρ인 2값 layer map
`w ↦ w + e_{σ(c)} (w∈U) / w + e_{ρ(c)} (w∉U)`의 색 c 전단사성은

> **(★)  U + (e_{σ(c)} − e_{ρ(c)}) = U**

와 **동치**다(유한성으로 단사⟺전단사; 교차 충돌 제거가 정확히 (★)).
이는 논문 자신의 two-color 기준 `F⁻¹_{β,t}F_{α,t}(U) = U` (:300–316)와 같은
모양이며, 논문도 X_i·R 행에는 이 기준을 그대로 적용한다.

## 1. 문제: full cyclic row `C_h`는 (★)를 만족하는 진부분 U가 없다

`C_h`는 **모든** 색의 read를 `Ω_k ↦ Ω_{k+h}`로 옮기므로(:115–117), 색들이 만드는
차 벡터 `e_{Ω_{k+h}} − e_{Ω_k}` 전체(영-슬롯 출입의 단위벡터 2개 포함)는
`(ℤ/m)^{2b}` 격자 전체를 생성한다(gcd(h, 2b+1) = 1). 따라서 (★)를 **모든 색에
대해 동시에** 만족하는 U는 ∅ 또는 전체뿐이다.

그런데 `def:lifted-completion-fiber`의 U(lifted fiber)는 부모 좌표 y_ν, 터미널
좌표 q_ν, 기-부가 좌표를 **고정**하는 진부분집합이다. 즉, 정확한 2값 모델에서
`lem:completion-fiber-bijectivity`의 결론(수정된 layer map들이 전단사)은
성립할 수 없다.

증명의 틈이 있는 위치: 증명(:291–298)은 "fiber 밖의 어떤 source도 fiber 안의
source와 같은 parent projection + 같은 fixed successor data를 갖지 않으므로 두
image 집합이 분리"라 주장한다. 그러나 `lem:endpoint-port-room`의 분리는
**사이트들**을 분리하는 반면, 여기서 충돌하는 쌍은 **old-section/기-부가 좌표
방향을 따라** 차이 나는 (fiber 내부, fiber 외부) source 쌍이다 — `C_h`가 그
좌표들의 read도 옮기기 때문이고(":119–120 'All other nonzero changes are in the
old section or in successor coordinates already appended'"), fiber U는 정확히 그
좌표들을 고정하므로 (★)가 그 방향들에서 깨진다. b=4, m=4에서 구체 충돌 쌍을
`decide`로 박제할 수 있다(요청 시 Lean negative theorem으로 제공).

## 2. 질문 (셋 중 어느 것이 의도인가)

**Q1.** `C_h`의 국소화에서, old-section·기-부가 좌표를 read하는 색들에 대해서는
행이 실제로는 **바뀌지 않는다**(즉 fiber 위의 행이 full `C_h`가 아니라 "아직
부가되지 않은 좌표만 옮기는 부분 행")는 독해가 의도인가? 그렇다면 그 부분 행은
Ω의 치환이 아니게 되는데(잘린 cycle), layer 행의 Latin성(RF1)은 어떻게
회복되는가? — 치환이 아닌 행은 같은 layer의 같은 점에서 두 색이 같은 방향을
읽게 만든다.

**Q2.** 아니면 fiber 근방에서 **3값 이상**의 layer(보상 행이 있는 환형 구조)가
의도인가? 그렇다면 그 보상 행과 그 support, 그리고 그들의 (★)-검사가 논문에
기재될 필요가 있다 — 현재 본문은 "Outside the fiber the old row is kept"
(:295)로 2값임을 명시한다.

**Q3.** 아니면 `C_h`-layer는 fiber에 국소화하지 않고 **전 상태 공간에 상수로**
적용하되(이 경우 RF2는 자명 — Lean `EndpointRowSchedule.completionDesc`로 이미
형식화), one-point carry는 별도 메커니즘(예: 인접 layer의 two-color swap 조합)
으로 만드는 구조인가? 상수 `C_h` layer의 carry는 주기당 m·(상수) = 0이 되므로
ledger(:25–40)의 `±1` carry는 다른 곳에서 나와야 한다 — 형식화 측에서는
two-color swap만으로 one-point carry를 만드는 RF2-합법 경로가 존재함을
확인했다(τ₀-read/zero-read 쌍, 단 Wall 3의 부기 필요).

## 3. 형식화 측 현황 (참고)

- 추상 수준(완성 carry의 단일순환성)은 **이미 닫혀 있다**: 1점 carry 인증서와
  tower(`EndpointCompletion`, `CompletionTower.towerMap_singleCycle`). 문제는
  오직 **layer 행 수준의 실현**(RF2)이다.
- 현재 H6 홀은 이 실현을 정확히 포위하는 `EndpointRunCollapseRealization`
  family로 좁혀져 있다(`EndpointRealization.lean`, Main `:447`).
- Q1–Q3의 답에 따라 realization 설계(현재 진행 중인 wild run-collapse 설계)의
  목표 모양이 달라지므로, 답을 주시면 설계에 직접 반영한다.
