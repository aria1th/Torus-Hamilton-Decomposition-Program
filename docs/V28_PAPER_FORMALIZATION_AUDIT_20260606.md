# v28 논문 ↔ Lean 형식화 대조 감사 및 과감한 정리안

작성일: 2026-06-06  
대상 논문 소스: `even_modulus_directed_tori_v28_finite_audit_source`  
대상 Lean 소스: `Torus-Hamilton-Decomposition-Program_lean_formalization_20260606`

## 0. 감사 결론

논문 v28의 최종 목표는 다음이다.

```text
∀ d m, 2 ≤ d → Even m → 4 ≤ m → CayleyHamiltonDecomposition d m
```

Lean 쪽의 최종 명제 `EvenV11.EvenModulusToriAllDimensionsGoal`은 이 목표와 정확히 같은 형태다. 그러나 현재 `EvenV11/Main.lean`의 정리

```lean
EvenV11.evenModulusToriAllDimensions
```

은 아직 완전한 형식화가 아니라, 6개의 논문-facing `sorry` 기반 `assume_*` 의존성을 가진 조립 스켈레톤이다. 원본 업로드본에는 실제 열린 `assume_* := sorry`가 5개였고 `D₇(4)`는 `LowD7M4Finite` generated blob로 닫혀 있었다. 이번 패치는 그 blob 의존을 기본 `Main.lean` spine에서 제거하여 H3도 구조적 obligation으로 드러낸다. 현재 열린 slot은 다음 6개다.

| hole | Lean 이름 | 논문 위치 | 현재 상태 |
|---|---|---|---|
| H1 | `assume_d3EvenRootFlat` | Proposition `D3-base`, terminal `A₂` block | 미완료. m=4 및 Route-E 실험은 있으나 전 even m 파라메트릭 증명이 아님 |
| H2 | `assume_lowD5M4RibbonRealizationData` | Section `D54_parity_reset` | 구조적 축소는 좋음. 실제 row-equivalence/ribbon/run-collapse 데이터가 미제공 |
| H3 | `assume_lowD7M4CycleData` | Proposition `rank-three endpoint bases` | 이번 패치에서 `RootFlatCycleData 6 4` structural slot으로 전환. two-rail relay RF1/RF2/RF3 미제공 |
| H4 | `assume_lowD7M6CycleData` | Proposition `rank-three endpoint bases` | 표/finite blob는 있으나 Main 기본 spine에서는 구조적 RF1/RF2/RF3 데이터가 미제공 |
| H5 | `assume_oddHighModulus` | finite anchors + high-even growth | 조립/감사/일부 coforest bridge는 있음. 실제 high-even promotion이 미제공 |
| H6 | `assume_oddEndpoint` | endpoint successor | support/completion 엔진은 매우 많이 닫혔으나 최종 endpoint promotion이 미제공 |

중요한 점: 논문상 H3인 `D₇(4)`는 원본 Main에서 `LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily`로 닫혀 있었다. 하지만 이 파일은 대량의 `native_decide` 유한 인증이다. 논문 v28의 구조적 proof spine과 일치시키기 위해 이번 패치는 `D₇(4)`도 `RootFlatCycleData 6 4` two-rail relay 구조 정리로 되돌렸다.

Lean 실행 환경에는 `lake`/`lean` 바이너리가 없어 `lake build`를 여기서 재검증하지 못했다. 대신 정적 감사와 논문 번들의 Python finite audit를 실행했다. 논문 번들의

```bash
python3 scripts/verify_finite_checks.py
```

는 통과했다.

## 1. 논문별 형식화 대응표

| 논문 항목 | 수학 내용 | Lean 대응 | 판정 |
|---|---|---|---|
| Theorem `even-main` | 모든 even `m ≥ 4`, `d ≥ 2` | `EvenV11.Main.evenModulusToriAllDimensions` | 명제 형식은 맞음. 이번 패치 기준 6개 구조적 `sorry` slot |
| Root-flat return criterion | RF1/RF2/RF3 → Hamilton decomposition | `Shared.RootFlat`, `EvenV11.FinalTargetRootFlatCertificateBridge` | 닫힘 |
| Unit-carry skew product | base cycle + unit carry → skew cycle | `Shared.Monodromy`, `Shared.RankCycle`, `EvenV11.UnitCarry` | 닫힘 |
| Comparison switch / cut-splice | switch가 cycle을 splice | `EvenV11.Switching`, `Shared.SwitchCalculus` | 핵심 엔진 닫힘 |
| Flag splicing criterion | packet/flag cells를 한 cycle로 splice | `Shared.SwitchCalculus.flagSplicingCriterion`, `Shared.MasterReturn` | 일반 정리는 닫힘. 구체 packet instantiation은 미완 |
| Product closure / phase doubling | even dimension step | `EvenV11.PhaseDoubling`, `FinalTargetPhaseDoublingBridge` | 조립 수준 닫힘 |
| Terminal `A₂` D3 base | every even m의 rank-three base | `D3EvenM4*`, `D3EvenRouteE*`, `TerminalA2LowMod` | 부분/실험 다수. 최종 `FinalD3EvenRootFlatCertificateFamily` 미닫힘 |
| Finite high-even anchors | D5/D7 coforest-splice anchor | `FiniteAudit`, `FiniteAuditBridge`, `TypeA.AnchorBridge`, `TypeA.PacketBridge` | bool audit/경계-cell bridge는 닫힘. 실제 `FlagSplicingCertificate`와 return promotion 연결 미완 |
| High-even growth | 7→9 chained 및 paired growth | `HighEvenSuccessorBridge`, `ProjectionKernel`, `GuideLocality` | 보조 엔진 닫힘. 최종 promotion 미완 |
| Endpoint successor | low-modulus `b ↦ 2b+1` | `EndpointCompletion`, `PhaseProductSupport`, `PhaseProductRealizationBridge`, `FinalTargetPhaseProductCertificateBridge` | 많은 엔진 닫힘. 최종 marked endpoint promotion 미완 |
| D5(4) parity reset | 5개 reset returns + marked reserve | `LowD5M4Structural`, `LowD5M4Seed`, `D54ResetData` | 구조적 축소는 적절. 실제 ribbon realization data 미완 |
| D7(4), D7(6) bases | folded rank-three bases | `RootFlatCycleData`; finite blobs are archived | 이번 패치에서 둘 다 Main structural slot. 실제 two-rail RF1/RF2/RF3 proof 미완 |
| Final induction | ordinary/marked simultaneous induction | `FinalInductionSchemeBridge`, `FinalRangeBookkeepingBridge` | 닫힘 |

## 2. 과감히 버릴 것 / 격리할 것

아래 항목들은 삭제보다 “기본 proof spine에서 격리”가 안전하다. 역사적/회귀 테스트 값은 보존하되, 최종 논문 대응 정리에서 의존하지 않게 한다.

### 버릴 것 A — finite blob를 최종 증명으로 쓰는 습관

- `EvenV11/LowD5M4Finite.lean`
- `EvenV11/LowD7M4Finite.lean`
- `EvenV11/LowD7M6Finite.lean`

용도는 회귀 테스트와 표 sanity check로 제한한다. 논문 v28은 “유한 brute force가 theorem을 대신한다”는 구조가 아니라, 표가 coforest/ribbon/unit-carry 가정을 만족함을 보이고 일반 엔진에 넣는 구조다.

### 버릴 것 B — D3 Route-E finite-case 중심 접근

- `D3EvenRouteEGeSix.lean`의 `m = 6,8,10,12` rank package
- tail rank package 기반 실험적 route

D3 base는 논문상 terminal `A₂` block의 파라메트릭 정리다. m=4 finite check와 몇 개 even tail case는 증거/디버깅용으로 남기고, H1은 `TerminalA2LowMod` + root-flat certificate family로 새로 닫아야 한다.

### 버릴 것 C — `Status.lean` 폐쇄 우산

`Status.lean`은 wrapper를 대량 재수출하는 역사적 파일이다. 지금 Main은 이미 명시적 `assume_*` 스켈레톤으로 바뀌었으므로, 최종적으로는 `EvenV11.lean`에서 `Status` import를 제거하고 필요한 모듈만 직접 import한다. 즉시 삭제하지 말고, 먼저 `lake build EvenV11.Main` 및 progress gate에서 빠지는지 확인한다.

### 버릴 것 D — odd/RouteE 잔여 연구 산출물을 even v28 spine에 끌어오는 것

`docs/D5_EVEN_ROUTE_E_*`, `certs/routeE_*`, 여러 search/summarize script는 연구 기록으로 보존하되, v28 정리의 dependency graph에는 넣지 않는다.

## 3. 즉시 수정 사항

이 패치는 다음을 적용한다.

1. `EvenV11/Main.lean`  
   `LowD7M4Finite` import와 직접 사용을 제거하고, H3를 `RootFlatCycle.RootFlatCycleData 6 4` obligation으로 전환했다. 따라서 기본 theorem spine도 논문-facing 6-slot 형태가 된다.

2. `EvenV11/V28PaperInterface.lean`  
   논문 충실 proof spine을 checklist interface로 제공한다. 각 H input에서 기존 final induction theorem까지 가는 closed adapter를 둔다.

3. `EvenV11.lean`  
   `EvenV11.V28PaperInterface`를 umbrella import에 추가했다.

4. `docs/V28_FORMALIZATION_STRATEGY_20260606.md`  
   H1–H6의 형식화 전략, 필요한 보조정리, 증명 스케치, 버릴 항목을 정리한다.

5. `scripts/verify_even_v28_finite_checks.py`  
   논문 번들의 finite audit script를 Lean 프로젝트 안에 복사한다. 이는 theorem 대체물이 아니라 표 전사 오류를 잡는 보조 도구다.

## 4. 최종 proof spine 권장 형태

최종적으로 Main은 다음 6개 구조 input을 받아 닫히는 형태가 가장 정직하다.

```lean
structure V28PaperChecklist : Prop where
  d3TerminalA2 : FinalD3EvenRootFlatCertificateFamily
  d5m4Reset : Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData
  d7m4TwoRail : Nonempty (RootFlatCycle.RootFlatCycleData 6 4)
  d7m6TwoRail : Nonempty (RootFlatCycle.RootFlatCycleData 6 6)
  oddHighModulus : FinalOddHighModulusTargetPromotion
  oddEndpoint : FinalOddEndpointPhaseProductTargetPromotion
```

이 checklist에서 기존 조립 정리까지 가는 adapter는 `V28PaperInterface.lean`에 들어 있다. 나중에 각 field를 실제 증명으로 채우면 `evenModulusToriAllDimensions`의 `sorryAx`가 사라진다.

## 5. 우선순위

1. **H1 D3 terminal `A₂`**: finite blob/Route-E를 버리고 전 even m용 파라메트릭 root-flat certificate family를 만든다.
2. **H2 D5(4)**: `LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`를 실제 row/ribbon/run-collapse 데이터로 채운다.
3. **H3/H4 D7(4), D7(6)**: 두 modulus 모두 `RootFlatCycleData 6 m` 구조로 통일한다.
4. **H6 endpoint**: 이미 닫힌 product/completion/support lemma를 묶어 marked payload promotion을 완성한다.
5. **H5 high-even**: 마지막 대형 작업. `TypeA.PacketBridge`에서 `Shared.SwitchCalculus.FlagSplicingCertificate`까지 가는 instantiation과 growth promotion을 닫는다.

