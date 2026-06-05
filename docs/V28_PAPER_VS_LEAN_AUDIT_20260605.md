# v28 논문 spine vs Lean 형식화 감사 (2026-06-05)

## 0. 결론

현재 Lean 형식화는 **최종 ordinary Hamilton decomposition 정리의 귀납 분기**는 논문
v28과 대체로 같은 모양이다. 그러나 논문 전체를 형식화했다는 기준으로는 아직 많이
축소되어 있다.

가장 큰 차이는 다음 둘이다.

1. `FinalMarkedTarget d m`이 실제 marked decomposition이 아니라
   `Shared.TorusHamiltonDecomposition d m`의 단순 alias이다
   (`EvenV11/FinalTargetPredicateBridge.lean`). 따라서 논문의 marked selector,
   protected neighborhood, endpoint reserve invariant는 최종 payload에 남아 있지 않다.
   최종 ordinary theorem만 목표라면 허용 가능한 축소지만, 논문 증명 전체의 형식화로는
   큰 drift다.
2. H2에서 확인된 것처럼 논문은 실제 row first-return과 추상 return을 같은 좌표에서
   강제로 동일시하지 않는다. 논문은 switching ribbon / run-collapse reindexing으로
   return-section cycles를 실현한다. 이 점은 H2에서 수정되었고, 같은 주의가 H5/H6에도
   필요하다.

요약하면:

| 항목 | 현재 판단 |
|---|---|
| 최종 induction bookkeeping | 논문과 정합적 |
| ordinary theorem 목표 | 조건부 spine은 타당 |
| marked/reserve invariant | Lean payload에서 소거됨 |
| H2 D5(4) | 잘못된 tame route를 버리고 논문형 open input으로 수정됨 |
| H1 | 부분 자산은 있으나 논문 §5 terminal A2 family 그대로는 아님 |
| H3 | 닫혔지만 generated finite certificate 경로. 논문 경로 형식화와는 별도 |
| H4 | open. generated witness는 archive이고 기본 spine에서는 제외 |
| H5/H6 | 로컬 도구는 많지만 실제 promotion은 아직 `sorry` slot |

## 1. 논문 proof spine

감사한 원문은 다음 tarball에서 추출한 v28 소스다.

`/data/angel/repos/etc/even_modulus_directed_tori_v28_finite_audit_source.tar.gz`

주요 spine:

| 논문 절 | 역할 |
|---|---|
| `root_flat_first_returns.tex` | RF1/RF2/RF3 root-flat criterion, unit-carry |
| `switching_ribbons.tex` | comparison switch, ribbon realization, cut-splice, selector preservation |
| `terminal_A2_block.tex` | D3 base와 terminal carrier |
| `D54_parity_reset.tex` | D5(4) parity reset, five reset returns, ribbon realization |
| `product_phase_doubling.tex` | even dimension phase doubling, marked singleton, reserve line |
| `high_even_seed_realization.tex` | finite high-even relays, Type A coforest, laminar splicing, unit carry |
| `high_even_growth.tex` | odd high-even growth by four-point rows |
| `endpoint_successor.tex` | low-modulus endpoint extension |
| `final_induction_framework.tex` | simultaneous induction |

논문 `final_induction_framework.tex`의 분기는 Lean의
`FinalInductionSchemeBridge.finalInductionScheme`와 잘 맞는다:

- `d=2`, `d=3` base
- even `d=2a`: phase doubling
- odd high-modulus `m>d`: high-even anchors/growth
- odd low-modulus `m≤d`: D5(4), D7(4), D7(6), 또는 endpoint successor

## 2. 전역 drift: marked target 소거

논문은 `HD`와 `RHD`를 동시에 유지한다. `RHD`는 다음 endpoint step에 필요한
comparison cycle과 endpoint reserve를 포함한다.

Lean에서는:

```lean
abbrev FinalOrdinaryTarget (d m : Nat) : Prop :=
  Shared.TorusHamiltonDecomposition d m

abbrev FinalMarkedTarget (d m : Nat) : Prop :=
  Shared.TorusHamiltonDecomposition d m
```

따라서 `FinalMarkedTarget`은 이름과 달리 marker/reserve를 포함하지 않는다.
이 때문에 `phaseDoubling`, `oddHighModulus`, `oddEndpoint`가 모두 `FinalMarkedTarget`을
반환하더라도, 실제로는 ordinary decomposition만 반환한다.

이것은 현재 최종 theorem
`evenModulusToriAllDimensions : EvenModulusToriAllDimensionsGoal`에는 충분할 수 있다.
하지만 논문의 `RHD` invariant를 형식화했다고 보기는 어렵다. 특히 논문에서 reserve
preservation을 따로 증명하는 이유가 Lean 최종 payload에서는 사라진다.

## 3. H1-H6 대조

| Hole | 논문 의무 | 현재 Lean 상태 | drift 판단 |
|---|---|---|---|
| H1 `assume_d3EvenRootFlat` | §5 terminal A2 row word로 모든 even `m≥4`의 D3 base | `D3EvenM4RootFlat`은 `m=4` certificate를 갖고, Route-E bridge가 일반 `m≥6`를 zero-layer bijectivity + return rank package로 줄임 | 중간 drift. 목표 타입은 root-flat certificate family로 적절하지만, proof path는 논문 terminal A2 family 그대로가 아니라 D3 Route-E 자산 중심 |
| H2 `assume_lowD5M4RibbonRealizationData` | §11 D5(4) parity reset. Five abstract reset returns를 실제 root-flat rows/ribbons로 실현 | `LowD5M4Seed`는 abstract `fullReturn` cycles를 닫음. `LowD5M4Structural`은 Latin `row`, RF2, wild `e : Seed ≃ RootState`, return-realization을 open input으로 둠 | 현재 방향은 논문과 정합. 남은 핵심은 실제 ribbon/run-collapse realization |
| H3 `assume_lowD7M4` | rank-three/folded endpoint base `RHD(7,4)` | `LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily`로 닫힘 | theorem은 닫혔지만 논문 proof 구조가 아니라 generated finite root-flat certificate |
| H4 `assume_lowD7M6` | rank-three/folded endpoint base `RHD(7,6)` | 기본 spine에서는 open. `LowD7M6Finite`는 archive/explicit target | open. H3와 같은 generated 경로를 쓸지, 논문 two-rail/folded 구조를 포팅할지 결정 필요 |
| H5 `assume_oddHighModulus` | high-even finite anchors + coforest/laminar splice + four-point growth | Type A coforest audits, projection-kernel, guide-locality, cut-splice tools가 있음. 그러나 `FinalOddHighModulusTargetPromotion` 자체는 open | 큰 open slot. 로컬 lemma는 논문과 꽤 맞지만, finite relay -> root-flat model -> promotion 연결이 없음 |
| H6 `assume_oddEndpoint` | endpoint successor: terminal product cycles, completion unit carry, marked transfer, separated ports | completion carry, phase-product support, marked-transfer audits가 있음. 그러나 `FinalOddEndpointPhaseProductTargetPromotion`은 아직 promotion-shaped open input | 큰 open slot. 로컬 components는 있으나 endpoint row realization -> RF certificate/promotion이 없음 |

## 4. H2에 대한 세부 판단

H2에서 틀어진 핵심은 이전 `LowD5M4Realization` 계열이 암묵적으로 요구하던

```lean
schedule.returnMap = LowD5M4.fullReturn
```

식의 tame coordinate equality다. 논문 `D54_parity_reset.tex` 마지막 구현 문단은 그런
동일성을 주장하지 않는다. 논문은:

- terminal A2 layer word, Y-row, neutral Z-row를 출발점으로 삼고,
- Table D54-reset-ports의 다섯 switching site에서 local two-entry exchange를 넣고,
- switching-ribbons lemma로 return-section 효과를 실현하며,
- protected selector와 reserve가 disjoint임을 보존한다.

즉 필요한 것은 실제 root-flat schedule의 first return이 추상 reset return과 **wild
reindexing/conjugacy**로 연결되는 것이다. 현재 `Main`의 H2 slot은
`ResetPortH2RowEquivRibbonRealizationData`를 받는다. 그래서 RF1은 Latin row
equivalence에서 자동으로 닫히고, 남은 입력은 RF2와 wild reindexing/conjugacy다.

남은 H2 작업은 다음 세 묶음이다.

- `row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5`
- `layerBijective`
- `returnRealization` with `e : Seed ≃ RootState`

여기서 `e`는 tame chart가 아니라 ribbon correspondence가 만들어내는 run-collapse
reindexing이어야 한다.

## 5. H5/H6에서 같은 실수를 피해야 할 지점

논문 high-even과 endpoint도 실제 large row schedule을 직접 계산해서 한 좌표 chart에서
return equality를 밀어붙이는 방식이 아니다.

H5 high-even:

- finite relay data
- rooted coforest completion
- quotient transversal support line
- tail-head identity
- laminar-compatible switching ribbons
- final one-isolate tree determinant / unit carry

이 chain을 거쳐 RF3를 얻는다. Lean에는 `TypeA/AnchorBridge`, `ProjectionKernel`,
`GuideLocality`, `Shared/SwitchCalculus`가 대응 자산으로 있다. 그러나 아직
`FinalOddHighModulusTargetPromotion`은 이 자산을 사용해 실제 `FinalMarkedTarget`을
만드는 정리로 닫혀 있지 않다.

H6 endpoint:

- terminal/auxiliary product-cycle exponent
- completion rows as one-point unit-carry lifts
- localized two-color exchanges with RF2
- marked transfer and port separation

Lean에는 `EndpointCompletion`, `EndpointMarkedTransferBridge`,
`PhaseProductRealizationBridge`, `FinalTargetPhaseProductCertificateBridge`가 대응 자산이다.
하지만 최종 `FinalOddEndpointPhaseProductTargetPromotion`은 아직 promotion-shaped open
input이다.

따라서 H5/H6에서 “실제 row first-return = 추상 return” 같은 강한 목표를 만들면 H2와
같은 blocker가 재발할 가능성이 높다. 목표는 paper lemma 이름과 같은 bridge를 세우고,
return effect는 cut-splice/ribbon/reindexing으로 운반하는 형태여야 한다.

## 6. 권장 수정 경로

1. **목표를 둘로 분리**
   - A: 현재 ordinary theorem을 닫는 최소 spine.
   - B: 논문 `RHD` marked/reserve invariant까지 포함하는 faithful spine.

   A만 목표라면 현재 `FinalMarkedTarget = TorusHamiltonDecomposition` 축소를 명시적으로
   인정하고 H1/H2/H4/H5/H6를 ordinary certificate/promotion으로 닫으면 된다. B가 목표라면
   `FinalMarkedTarget`을 실제 구조체로 바꾸는 큰 재설계가 필요하다.

2. **H2는 현재 방향 유지**
   - `LowD5M4Realization`의 paper-table route는 기본 proof spine에 직접 넣지 않고,
     `LowD5M4H2PaperRow`의 explicit adapter로만 사용한다.
   - H2는 `ResetPortH2RowEquivRibbonRealizationData`를 실제 paper port/ribbon data로
     채운다.

3. **H5/H6는 paper-spine wrapper부터 만든다**
   - `CoforestSpliceAnchorData -> FinalOddHighModulusTargetPromotion`
   - `EndpointSuccessorRowData -> FinalOddEndpointPhaseProductTargetPromotion`
   같은 이름의 중간 구조체를 만들고, 각 필드를 논문 lemma 단위로 맞춘다.

4. **generated finite certificates의 지위를 명확히 유지**
   - H3처럼 generated certificate로 닫은 항목은 theorem closure로는 유효하다.
   - 하지만 논문 경로 형식화로 세지 않으려면 archive/explicit target임을 계속 표시한다.

5. **다음 실작업 우선순위**
   - H2: `row/e/layerBijective/returnRealization` 중 먼저 `row`와 local support
     disjointness를 paper table에서 옮긴다. RF1은 row equivalence로 자동 처리한다.
   - H1: 현재 Route-E path를 끝낼지, 논문 terminal A2 family path로 되돌릴지 결정한다.
   - H6: endpoint promotion을 파일럿으로 삼기 좋다. 이미 completion/phase-product
     로컬 자산이 비교적 잘 정리되어 있고, promotion 하나가 닫히면 H5에서도 같은 패턴을
     재사용할 수 있다.

## 7. 현재 진행 지표

기본 proof spine 기준 open holes:

- H1 `assume_d3EvenRootFlat`
- H2 `assume_lowD5M4RibbonRealizationData`
- H4 `assume_lowD7M6`
- H5 `assume_oddHighModulus`
- H6 `assume_oddEndpoint`

H3 `D7(4)`는 기본 spine에서 닫혀 있다. 단, 논문 구조 형식화 여부와 theorem closure
여부는 별도로 계산해야 한다.

## 8. 2026-06-05 1-3단계 착수 기록

1-3단계의 첫 코딩 패스는 기존 ordinary theorem spine을 깨지 않으면서 paper-faithful
payload 경로를 병행 추가하는 방식으로 진행했다.

- `EvenV11.FinalTargetPredicateBridge`
  - `FinalMarkedEvidence d m`를 추가했다. 이는 논문 RHD의 comparison selector와
    endpoint reserve invariant를 나중에 실데이터로 채우기 위한 최소 evidence carrier다.
  - `FinalMarkedPayload d m`를 추가했다. 기존 `FinalMarkedTarget d m`은 ordinary
    alias로 유지하고, 새 payload가 ordinary target과 marked evidence를 함께 운반한다.
  - `finalMarkedPayload_forget`, `finalMarkedPayload_forgetOrdinary`를 추가해 기존
    ordinary theorem spine으로 언제든 잊을 수 있게 했다.
  - `finalMarkedPayload_weakOfTarget`를 추가했다. 이는 기존 open promotion을 새 payload
    형태로 임시 승격하는 bridge이며, faithful proof가 아니라 호환성 장치다.
- `EvenV11.LowD5M4Structural`
  - `ResetPortH2MarkedRibbonRealizationData`를 추가했다. 기존 H2 ribbon-realization
    입력 위에 `FinalMarkedEvidence 5 4`를 붙이는 최소 marked H2 입력이다.
  - `finalLowD5M4MarkedPayload_of_markedRibbonRealizationData`를 추가해 D5(4) root-flat
    certificate family 경로가 marked payload를 반환할 수 있게 했다.
  - 기존 `FinalMarkedTarget 5 4` 경로는 `finalMarkedPayload_forget`로 유지된다.
- `EvenV11.FinalTargetPhaseProductCertificateBridge`
  - `FinalOddEndpointPhaseProductMarkedPayloadPromotion`을 추가했다. endpoint successor가
    부모 marked payload를 받아 자식 marked payload를 반환하는 pilot target이다.
  - `finalOddEndpointPhaseProductTargetPromotion_of_markedPayloadPromotion`을 추가해 새
    payload promotion이 기존 target promotion을 공급하게 했다.
  - `finalOddEndpointPhaseProductMarkedPayloadPromotion_weakOfTargetPromotion`을 추가해
    기존 open target promotion을 새 payload shape로 임시 감쌀 수 있게 했다.

이 변경은 H2/H6를 닫지는 않는다. 대신 논문 RHD payload를 다시 Lean spine에 태울
최소 타입 경로를 만들고, 기존 ordinary alias 기반 최종 정리와의 호환성을 유지한다.
