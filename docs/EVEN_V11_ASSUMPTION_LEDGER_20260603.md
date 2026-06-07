# EvenV11 가정 원장 (Assumption Ledger) — 정직한 진행 추적

작성일: 2026-06-03. 측정 환경: `/root/.elan`, `lake build EvenV11` 성공(약 4초).
업데이트: 2026-06-06 v28 방향 전환 이후 H3 `D7(4)`도 generated finite root-flat
certificate 직접 사용에서 빠졌다. H2 `D5(4)`, H3 `D7(4)`, H4 `D7(6)`의 generated
witnesses는 archive/명시 검증 target으로만 남기고, 논문 구조 포팅으로 대체하기
위해 기본 proof spine에서는 open input으로 둔다.

> 이 문서는 "closure-first" 전략이 숨긴 것을 드러낸다. 예전 `Status.lean` 경로는
> `sorry`도 `axiom`도 없이 빌드됐지만, **그것은 배관(plumbing)이 건전하다는 뜻이지
> 정리가 증명됐다는 뜻이 아니었다.** 현재 `Main.lean` proof spine은 이 숨은 입력을
> `assume_* := sorry`로 노출한다. 현재 기본 proof spine의 미증명 구멍은
> H1/H2/H3/H4/H5/H6 여섯 개다. 단 H2는 더 이상
> `FinalLowD5M4RootFlatCertificateFamily` 자체나 row-equivalence ribbon data
> 자체를 가정하지 않는다.
> `assume_lowD5M4RibbonCollapseInput :
> Nonempty LowD5M4RibbonCollapseInput`를 열어 둔다. 이 입력은 논문 §11의
> actual four-layer physical rows, RF2, 그리고 paper `LowD5M4.fullReturn`을 실제
> first-return map으로 운반하는 return-section reindexing을 담는다.
> `assume_lowD5M4RibbonRealizationData`는 이 입력에서 파생된다. final family는
> `LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData`
> 로 파생한다. broad paper table route와 core-tail prefix route는 기본 proof spine 밖의
> explicit/negative adapter (`EvenV11/LowD5M4H2PaperRow.lean`,
> `EvenV11/V28Hard/D5M4H2Skeleton.lean`)로 남아 있다.

---

## 0. 핵심 시연: 표준 무결성 검사가 거짓말을 한다

```
#print axioms finalTargetCayley_from_d3AndLowRootFlatChecklist_closed
⟹ depends on axioms: [propext, Classical.choice, Quot.sound]
```

최종(조건부) 정리가 **표준 mathlib axiom만 의존** — 완벽히 "깨끗"하게 보인다.
그러나 이 정리는 미구성 `checklist` 가정을 인자로 받는다. **미구성
`structure … : Prop`를 가정으로 넘기는 것은 시그니처로 옮긴 `sorry`이며,
`#print axioms`·closure 게이트·"no sorry" 검사 어디에도 잡히지 않는다.**
이것이 이전 전략으로 진행 판단이 불가능해진 근본 원인이다.

---

## 1. 부채 정량 (측정값)

| 항목 | 수치 | 성격 |
|---|---|---|
| `EvenV11/Status.lean` 줄수 | **16,769** | 게이트 강제 보일러플레이트 |
| Status.lean `_closed` 별칭 | **1,781** | 증명 0, 순수 재수출 |
| `structure … : Prop` (Status 외) | 73 | 가설 묶음 |
| └ 실제 증명/구성됨 (`_holds`/`where`) | **65** | 진짜 자산 |
| └ **미구성 leaf (진짜 구멍)** | **8** (원자 6 + 묶음 2) | ↓ §2 |
| `_holds` 정리 (증명된 조각) | 76 | 자산 |
| `…Certificate` 식별자 | 225 | 명명 인플레이션 |
| `…Input`/`…Promotion`/`…Checklist` | 153/81/16 | 배관 |

해석(2026-06-03 기준): **거대한 표면적(16,769줄 + 73 Prop + 1,781 별칭)이 단 6개의 수학적
구멍을 둘러싸고 있었다.** 65개의 증명된 조각은 진짜지만, 6개의 구멍과 동일한
`Final…/Certificate/Promotion/_closed` 작명 아래 섞여 있어 자산과 부채를
한눈에 구분할 수 없다.

---

## 2. 진짜 미증명 구멍 — 기본 spine 기준 원자 6개

`FinalRootFlatTorusCertificate d m`(payload)을 구성해야 했던 6개 지점:

| # | Lean 가정 (미구성) | 논문 | payload | 이를 닫는 도구 | 비고 |
|---|---|---|---|---|---|
| H1 | `FinalD3EvenRootFlatCertificateFamily` | §5 terminal A2 + D3 seed | `…Cert 3 m` (even m) | P8(six-turn)+P1 lift | 일반 m |
| H2 | `assume_lowD5M4RibbonCollapseInput : Nonempty LowD5M4RibbonCollapseInput` | §11 D5(4) parity reset | `…Cert 5 4` | actual four-layer rows + RF2 + return-section/ribbon-collapse realization | open input in `Main`; `assume_lowD5M4RibbonRealizationData` and `assume_lowD5M4` are derived; generated witness, layer-blind reset-port base-row route, broad paper-table route, and impossible core-tail prefix route stay archive/explicit-only |
| H3 | `assume_lowD7M4CycleData : Nonempty LowD7M4RootFlatCycleData` | App A/B two-rail | `…Cert 7 4` | structural `RootFlatCycleData 6 4` | open in `Main`; `LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily` is archive/explicit-only |
| H4 | `assume_lowD7M6CycleData : Nonempty LowD7M6RootFlatCycleData` | App A/B two-rail | `…Cert 7 6` | structural `RootFlatCycleData 6 6` | open in `Main`; `LowD7M6Finite.finalLowD7M6RootFlatCertificateFamily` is archive/explicit-only |
| H5 | `FinalOddHighModulusTargetPromotion` | §6–8 coforest+growth | 일반 | **P6**(coforest)+P1 growth | parametric |
| H6 | `FinalOddEndpointPhaseProductTargetPromotion` | §9–10 endpoint | 일반 | P3(cut-splice)+P1 completion | parametric |

묶음(파생, 별도 작업 아님): `FinalLowBaseRootFlatCertificateFamilies`(=H2+H3+H4, 현재 H2/H3/H4 open),
`FinalTargetCertificateChecklistWithD3AndLowRootFlat`(=H1+묶음+H5+H6).

**현재 임계 경로:** H1은 §5 terminal/D3 root-flat family, H2는 §11 D5(4)
paper reset-port table realization data 구성, H3/H4는 Appendix A/B D7(4)/D7(6)
two-rail structural replacement, H5는 odd high-modulus promotion, H6는 endpoint
successor promotion. H2의 final family 조립은 이미 구조 정리로 연결됐다.

2026-06-04 추가 확인: H1의 아카이브 D3 자산 중 `EvenV11/D3EvenM4.lean`은
`Shared.CayleyHamiltonDecomposition 3 4`를 닫고, `EvenV11/D3EvenRouteEGeSix.lean`은
`m=6,8,10` 및 일반 `m≥6` 조건부 Route-E bridge를 제공한다. 그러나 현재 H1의
payload는 `FinalD3EvenRootFlatCertificateFamily`이다. 추가로
`EvenV11/D3EvenM4RootFlat.lean`은 `m=4`를 H1 payload인
`FinalD3EvenRootFlatCertificate 4`로 승격한다. 또한
`EvenV11/D3EvenRouteERootFlatBridge.lean`은 Route-E schedule을
`FinalD3EvenRootFlatCertificate m`로 승격하며, `m=6,8,10` root-flat certificates를
제공한다. 따라서 H1의 D3-specific gap은 일반 `m≥6` zero-layer bijectivity /
`RouteEReturnModelRankPackage`로 좁혀졌지만, 아직 완전히 닫히지는 않았다.

---

## 3. 게으르게 미뤄둔 작업 (technical debt) 목록

1. **가정 원장 부재** — "무엇이 남았는가"를 한 곳에 적은 문서가 없었다. 본 문서가
   그것이다. (구멍 = 위 6개.)
2. **Status.lean 16,769줄/1,781 별칭** — 게이트가 모든 export에 `_closed` 별칭을
   강제. 증명 0, 탐색 불가, 6개 구멍을 가린다.
3. **`#print axioms` 맹점** — 구멍이 `axiom`이 아니라 가정이라 무결성 도구가
   탐지 못 함. "no sorry / clean axioms"가 완성으로 오독됨.
4. **자산/부채 미분리** — 65 증명 Prop과 6 구멍이 동일 작명. P1/P2/word-cert 같은
   재사용 자산이 배관에 묻혀 식별 어려움.
5. **게이트가 잘못된 것을 최적화** — `deferred_decl_pattern`이 메인 정리 *이름을
   금지* → 구멍이 단일 명제로 노출되는 것을 막음. 게이트가 깨끗할수록 진행이
   덜 보인다. (의도된 "미완성 표식"이었으나 진행 판단을 마비시킴.)
6. **splice 도구 부재(P3/P6)** — H3·H4·H5·H6의 공통 전제인 cut-splice/coforest
   single-cycle 정리가 코드에 없음. (`docs/…COMPLETION_PLAN…§6` 참조.)

---

## 4. 권고: closure-first를 뒤집어 progress-first로

**핵심 1수: 6개 구멍을 명시적으로 노출.**
초기 제안은 `EvenV11/Assumptions.lean` 신규 — 6개 leaf를 `axiom`으로 선언하고,
메인 정리를 그 위에서 **무조건(unconditional)** 서술하는 것이었다. 현재
`EvenV11/Main.lean`은 같은 진행 지표를 `assume_* := sorry` theorem으로 노출하며,
H3는 닫혔고 H2는 D54 audit을 제외한 paper table data 가정으로 낮아졌다:
```lean
-- EvenV11/Assumptions.lean (제안)
axiom assume_D3EvenRootFlat   : FinalD3EvenRootFlatCertificateFamily
axiom assume_LowD5M4          : FinalLowD5M4RootFlatCertificateFamily
axiom assume_LowD7M4          : FinalLowD7M4RootFlatCertificateFamily
axiom assume_LowD7M6          : FinalLowD7M6RootFlatCertificateFamily
axiom assume_OddHighModulus   : FinalOddHighModulusTargetPromotion
axiom assume_OddEndpoint      : FinalOddEndpointPhaseProductTargetPromotion

theorem evenModulusDirectedToriHamiltonDecomposition
    {d m : Nat} (hd : 2 ≤ d) (hm : Even m) (hm4 : 4 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := …  -- 위 axiom들을 checklist로 조립
```
그러면:
```
#print axioms evenModulusDirectedToriHamiltonDecomposition
⟹ [propext, Classical.choice, Quot.sound,
    assume_D3EvenRootFlat, assume_LowD5M4, assume_LowD7M4,
    assume_LowD7M6, assume_OddHighModulus, assume_OddEndpoint]
```
**진행 지표 = 남은 `assume_*` 개수 (목표 0).** 정리를 하나 형식화할 때마다
해당 `axiom`을 `theorem … := <증명>`으로 교체 → axiom 목록에서 사라짐.
이것이 closure-first의 정반대 — 부채를 숨기지 않고 셈한다.

**부수 작업:**
- (B) Status.lean 자동생성화 또는 `_closed` 관례 폐기 → 16,769줄 회수.
- (C) 재사용 자산(P1/P2/terminal·word cert)을 `Shared/SwitchCalculus.lean`로 분리.
- (D) closure 게이트 → progress 게이트: 메인 정리 무조건 서술 허용 + `axiom`
  허용(단 `assume_*` 접두사만) + 남은 `assume_*` 수를 CI가 출력.

---

## 5. 다음 시퀀스
1. (본 문서) 부채 파악 — 구멍 6개 확정. ✅
2. progress-first 전환 — **`EvenV11/Main.lean` 생성 완료. ✅**
   - `EvenModulusToriAllDimensionsGoal`(홀수 미러)를 무조건 메인 정리로 서술.
   - 최초 6개 구멍을 `assume_*` 정리(`:= sorry`)로 노출, `evenCertificateChecklist`로
     조립해 `evenModulusToriAllDimensions : EvenModulusToriAllDimensionsGoal` 증명.
     현재 H2는 `assume_lowD5M4RibbonCollapseInput` 데이터 가정으로 세분화됐고,
     H3/H4도 paper-structured root-flat cycle data 입력으로 열려 있다.
   - 검증: `lake build EvenV11.Main` 성공(현재 경고 = sorry 6개).
     `#print axioms evenModulusToriAllDimensions`
     ⟹ `[propext, sorryAx, Classical.choice, Quot.sound]` — **sorryAx 노출**.
   - **진행 지표(live):** 잔여 `sorry` 수 6 → 0, `#print axioms`에 `sorryAx` 소멸.
3. **closure 게이트 은퇴/교체 — 완료. ✅**
   - `scripts/check_evenv11_closure.sh` 제거 → `scripts/check_evenv11_progress.sh` 신설.
     CI(`.github/workflows/lean_action_ci.yml`)도 progress 게이트 호출로 갱신.
   - 우산 `EvenV11.lean`이 `EvenV11.Main`을 import → `lake build EvenV11`이 메인 정리까지 빌드.
   - progress 게이트: 빌드 green 검사 + `axiom`/`admit`/`native_decide` 금지(단 `sorry` 허용)
     + 메인 정리 무조건성 검사 + **OPEN HOLES 카운트 보고**. 초기에는 통과했으나,
     generated finite root-flat certificates와 archived D3 finite certificates를 포팅한 뒤
     `native_decide` 금지 규칙과 현재 certificate 전략이 충돌한다. 현재 progress
     gate는 H2 `LowD5M4Finite`와 H4 `LowD7M6Finite`가 기본 import closure로
     재유입되지 않는지 검사하고, 둘을 archive/명시 target으로만 허용한다.
     authoritative verification은 `lake build EvenV11`와 progress gate이다.
   - Status.lean(16,769줄)은 아직 존재(우산이 import). 점진 폐기는 별도 단계.
4. **P3 종이검증** (논문 Lemma 3.5 cut-splice 충분조건) → **P3-core 형식화 완료. ✅**
   - `Shared/SwitchCalculus.oneStepPacketSplice`
   - `Shared.SwitchCalculus.isCycleOn_univ_iff_isSingleCycleMap`
   - `Shared.SwitchCalculus.oneStepPacketSplice_singleCycleMap`
   - `Shared.SwitchCalculus.OneStepPacketSpliceCertificate`
   - `Shared.SwitchCalculus.OneStepPacketSpliceCertificate.isCycleOn`
   - `Shared.SwitchCalculus.OneStepPacketSpliceCertificate.isSingleCycleMap`
   → H2·H3·H4·H6 레버.
5. **P1 rank-coordinate unit-carry iff 완료. ✅**
   - `Shared.skewProduct_zmod_additive_rank_single_cycle_iff_unit_sum`
   - `EvenV11.UnitCarry.rankUnitCarrySingleCycle_iff`
6. **P6 flag-splicing layer 완료. ✅**
   - `Shared.SwitchCalculus.flagSplicingCriterion`
   - `Shared.SwitchCalculus.FlagSplicingCertificate`
   - `Shared.SwitchCalculus.FlagSplicingCertificate.isCycleOn`
   - `Shared.SwitchCalculus.FlagSplicingCertificate.isSingleCycleMap`
   - 실제 D7/H5 flag chain은 이 layer 정리를 단계별로 반복 적용하면 된다.
7. **M(master return single-cycle) generic wrapper 완료. ✅**
   - `Shared.SwitchCalculus.oneStepPacketSplice_unitCarrySingleCycle`
   - `Shared.SwitchCalculus.flagSplicingCriterion_unitCarrySingleCycle`
   - `Shared.SwitchCalculus.OneStepPacketSpliceCertificate.unitCarrySingleCycle`
   - `Shared.SwitchCalculus.FlagSplicingCertificate.unitCarrySingleCycle`
8. **Root-flat/promotion 조립 wrapper 완료. ✅**
   - `EvenV11.finalRootFlatTorusCertificate_of_fields`
   - `EvenV11.finalD3EvenBasePromotion_of_ordinaryTargetFamily`
   - `EvenV11.finalD3EvenBasePromotion_of_cayleyFamily`
   - `EvenV11.FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat`
   - `EvenV11.finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat`
   - `EvenV11.finalTargetCayley_from_d3PromotionAndLowRootFlatChecklist`
   - `EvenV11.finalLowD5M4RootFlatCertificateFamily_of_certificate`
   - `EvenV11.finalLowD7M4RootFlatCertificateFamily_of_certificate`
   - `EvenV11.finalLowD7M6RootFlatCertificateFamily_of_certificate`
   - `EvenV11.finalLowBaseRootFlatCertificateFamilies_of_certificates`
   - `EvenV11.finalOddHighModulusTargetPromotion_of_closedPromotion`
   - `EvenV11.finalOddEndpointPhaseProductPromotion_of_targetPromotion`
   - `EvenV11.finalOddEndpointPhaseProductPromotion_of_closedPromotion`
9. **C1 bool 의미 bridge 완료. ✅**
   - `EvenV11.primitiveDetBool_eq_true_iff`
   - `EvenV11.forestClosingDatumBool_detInt_eq_one_or_neg_one`
   - `EvenV11.forestClosingDatumBool_detInt_zmod_unit`
   - `EvenV11.EdgeUndirectedEquivalent`
   - `EvenV11.EdgeUndirectedEquivalent.symm`
   - `EvenV11.edgeMemberUndirected_eq_true_iff`
   - `EvenV11.edgeVectorCoeff`
   - `EvenV11.edgeVectorCoeff_head_of_tail_ne`
   - `EvenV11.edgeVectorCoeff_tail_of_head_ne`
   - `EvenV11.edgeVectorCoeff_off`
   - `EvenV11.reducedBasisVertices`
   - `EvenV11.reducedBasisVertex`
   - `EvenV11.reducedBasisVertices_length_of_lt`
   - `EvenV11.reducedBasisVertex_lt_of_row_lt`
   - `EvenV11.reducedBasisVertex_ne_basisBase_of_row_lt`
   - `EvenV11.vectorEdge_getD_of_row_lt`
   - `EvenV11.vectorEdge_getD_of_length_le`
   - `EvenV11.columnsToRows_get2D_of_lt`
   - `EvenV11.columnsToRows_get2D_of_height_le`
   - `EvenV11.columnsToRows_get2D_of_cols_length_le`
   - `EvenV11.listIntMatrix`
   - `EvenV11.closingMatrixFin`
   - `EvenV11.listIntMatrix_apply`
   - `EvenV11.closingMatrixFin_apply`
   - `EvenV11.closingMatrix_length`
   - `EvenV11.closingMatrix_row_length_of_lt`
   - `EvenV11.closingMatrix_row_length_eq_of_forest_length`
   - `EvenV11.closingMatrix_get2D_of_height_le`
   - `EvenV11.closingMatrix_get2D_of_width_le`
   - `EvenV11.closingMatrix_get2D_of_square_width_le`
   - `EvenV11.closingMatrix_forest_column_getD_of_lt`
   - `EvenV11.closingMatrix_forest_column_coeff_of_lt`
   - `EvenV11.closingMatrix_forest_column_coeff_of_lt_of_isolated_lt`
   - `EvenV11.closingMatrix_closing_column_getD_of_row_lt`
   - `EvenV11.closingMatrix_closing_column_coeff_of_row_lt`
   - `EvenV11.closingMatrix_closing_column_coeff_of_row_lt_of_isolated_lt`
   - `EvenV11.EdgeUndirectedEquivalent.edgeVectorCoeff_eq_or_neg`
   - `EvenV11.EdgeUndirectedEquivalent.vectorEdge_eq_or_neg`
   - `EvenV11.ForestClosingDatumFacts`
   - `EvenV11.forestClosingDatumBool_facts`
   - `EvenV11.ForestClosingDatumFacts.closing_head_coeff`
   - `EvenV11.ForestClosingDatumFacts.closing_isolated_coeff`
   - `EvenV11.ForestClosingDatumFacts.closing_off_coeff`
   - `EvenV11.forestClosingDatumBool_closing_head_coeff`
   - `EvenV11.forestClosingDatumBool_closing_isolated_coeff`
   - `EvenV11.forestClosingDatumBool_closing_off_coeff`
   - `EvenV11.ForestClosingDatumFacts.isolated_lt`
   - `EvenV11.forestClosingDatumBool_isolated_lt`
   - `EvenV11.ForestClosingDatumFacts.two_le`
   - `EvenV11.forestClosingDatumBool_two_le`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_length`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_row_length`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_height_zero`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_width_zero`
   - `EvenV11.forestClosingDatumBool_closingMatrix_length`
   - `EvenV11.forestClosingDatumBool_closingMatrix_row_length`
   - `EvenV11.forestClosingDatumBool_closingMatrix_height_zero`
   - `EvenV11.forestClosingDatumBool_closingMatrix_width_zero`
   - `EvenV11.ForestClosingDatumFacts.closingColumnFin`
   - `EvenV11.ForestClosingDatumFacts.closingColumnFin_val`
   - `EvenV11.ForestClosingDatumFacts.closingMatrixFin_forest_column_coeff`
   - `EvenV11.ForestClosingDatumFacts.closingMatrixFin_closing_column_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrixFin_forest_column_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrixFin_closing_column_coeff`
   - `EvenV11.ForestClosingDatumFacts.detInt_zmod_unit`
   - `EvenV11.forestClosingDatumBool_facts_detInt_zmod_unit`
   - `EvenV11.ClosingMatrixPayload`
   - `EvenV11.closingMatrixPayload_of_facts`
   - `EvenV11.closingMatrixPayload_of_bool`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_forest_column_coeff`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_closing_column_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrix_forest_column_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrix_closing_column_coeff`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff_of_row_lt`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff_of_row_lt`
   - `EvenV11.forestClosingDatumBool_closingMatrix_closing_column_head_coeff_of_row_lt`
   - `EvenV11.forestClosingDatumBool_closingMatrix_closing_column_off_coeff_of_row_lt`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff`
   - `EvenV11.ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrix_closing_column_head_coeff`
   - `EvenV11.forestClosingDatumBool_closingMatrix_closing_column_off_coeff`
   - `EvenV11.ForestClosingDatumFacts.closing_not_forest_undirected`
   - `EvenV11.ForestClosingDatumFacts.closing_not_forest_member`
   - `EvenV11.forestClosingDatumBool_closing_not_forest_member`
   - `EvenV11.SupportRowDatumFacts`
   - `EvenV11.supportRowDatumBool_facts`
   - `EvenV11.SupportRowDatumFacts.active_supported_inBounds`
   - `EvenV11.supportRowDatumBool_active_supported_inBounds`
   - `EvenV11.SupportRowDatumFacts.active_vectorEdge_eq_or_neg`
   - `EvenV11.supportRowDatumBool_active_vectorEdge_eq_or_neg`
   - `EvenV11.d5ForestClosingData_detInt_zmod_unit`,
     `EvenV11.d7ForestClosingData_detInt_zmod_unit`
   - `EvenV11.d5ForestClosingData_facts`,
     `EvenV11.d7ForestClosingData_facts`
   - `EvenV11.d5ForestClosingData_closingMatrixPayload`,
     `EvenV11.d7ForestClosingData_closingMatrixPayload`
   - `EvenV11.d5ForestClosingData_closingMatrix_length`,
     `EvenV11.d7ForestClosingData_closingMatrix_length`
   - `EvenV11.d5ForestClosingData_closingMatrix_row_length`,
     `EvenV11.d7ForestClosingData_closingMatrix_row_length`
   - `EvenV11.d5ForestClosingData_closingMatrix_forest_column_coeff`,
     `EvenV11.d7ForestClosingData_closingMatrix_forest_column_coeff`
   - `EvenV11.d5ForestClosingData_closingMatrix_closing_column_coeff`,
     `EvenV11.d7ForestClosingData_closingMatrix_closing_column_coeff`
   - `EvenV11.d5ForestClosingData_closingColumnFin_val`,
     `EvenV11.d7ForestClosingData_closingColumnFin_val`
   - `EvenV11.d5ForestClosingData_closingMatrixFin_forest_column_coeff`,
     `EvenV11.d7ForestClosingData_closingMatrixFin_forest_column_coeff`
   - `EvenV11.d5ForestClosingData_closingMatrixFin_closing_column_coeff`,
     `EvenV11.d7ForestClosingData_closingMatrixFin_closing_column_coeff`
   - `EvenV11.d5SupportRows_facts`,
     `EvenV11.d7SupportRows_facts`
   - `EvenV11.d5SupportRows_active_supported_inBounds`,
     `EvenV11.d7SupportRows_active_supported_inBounds`
   - `EvenV11.d5SupportRows_active_vectorEdge_eq_or_neg`,
     `EvenV11.d7SupportRows_active_vectorEdge_eq_or_neg`
10. **C2 boundary/transversal semantic bridge 완료. ✅**
   - `EvenV11.descendantCell`
   - `EvenV11.parentMapBoundary_child_mem_descendantCell_iff`
   - `EvenV11.coforestRootedBoundaryAudit_direct_child_mem_cell_iff`
   - `EvenV11.coforestRootedBoundaryAudit_iterated_child_mem_cell_iff`
   - `EvenV11.CellTransversal`
   - `EvenV11.CoforestRowCellBridge`
   - `EvenV11.coforestRowCellBridge_of_rootedBoundaryAudit`
   - `EvenV11.CoforestRowCellBridge.direct_crosses_cell_iff`
   - `EvenV11.CoforestRowCellBridge.iterated_crosses_cell_iff`
   - `EvenV11.D5CoforestRowsCellBridgeAudit`
   - `EvenV11.d5CoforestRowsCellBridgeAudit_holds`
   - `EvenV11.D7Stage12CoforestRowsCellBridgeAudit`
   - `EvenV11.d7Stage12CoforestRowsCellBridgeAudit_holds`
   - `EvenV11.v28FiniteInputPacketCellBridgeAudit_holds`
   - `EvenV11.parentMapBoundary_crosses_descendantCell_iff`
   - `EvenV11.d5Stage1Coforest_direct_crosses_cell_iff`
   - `EvenV11.d7Stage2Packet134Color34Coforest_direct_crosses_cell_iff`
11. **D2 generic layer-bijective bundler 완료. ✅**
   - `Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq`
   - `EvenV11.Switching.rootFlatLayerBijective_of_partialExchangeLeft_eq`
   - `EvenV11.Switching.rootFlatLayerBijective_of_partialExchangeRight_eq`
   - `EvenV11.Switching.rootFlatLayerBijective_of_partialExchangeChoice_eq`
12. 다음은 C1 row/carry instantiation의 실제 선형대수 연결, C2 packet
   `C/a/h/R/R'` instantiation의 실제 return-map 표 연결, 그리고 첫 파일럿
   certificate. H1은 §5 경로.

### 구멍 ↔ `assume_*` 대응 (Main.lean)
| 구멍 | Main.lean 정리 | 닫는 도구 |
|---|---|---|
| H1 | `assume_d3EvenRootFlat` | §5 + P1 |
| H2 | `assume_lowD5M4RibbonCollapseInput` (`assume_lowD5M4RibbonRealizationData`, `assume_lowD5M4`는 파생) | §11 reset-port rows + RF2 + ribbon/run-collapse realization |
| H3 | `assume_lowD7M4CycleData` (`assume_lowD7M4`는 파생) | D7(4) two-rail RF1/RF2/RF3 |
| H4 | `assume_lowD7M6CycleData` (`assume_lowD7M6`는 파생) | D7(6) two-rail RF1/RF2/RF3 |
| H5 | `assume_oddHighModulus` | P6 + P1 |
| H6 | `assume_oddEndpoint` | P3 + P1 |
