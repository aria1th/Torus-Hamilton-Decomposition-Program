# H2 D5(4) realization worksheet — 정본 작업 문서 (사용자용)

작성: 2026-06-04. **(a) 경로**(사용자가 realization 입력을 채움)를 위한 단일
정본 문서. 이 문서 하나만 보고 작업하시면 되며, 모든 단계가 논문의 어느 lemma를
형식화하는지 명시했습니다.

> **2026-06-05 경로 수정.** 이 문서의 기존 `returnMap = paperReturn`
> (`seedRootEquiv` 고정) 경로는 `docs/H2_REALIZATION_BLOCKER_20260605.md`의
> displacement counterexample 때문에 폐기됐다. 현재 기본 proof spine의 H2 open
> slot은 `EvenV11.Main.assume_lowD5M4RibbonRealizationData`이며, 입력 타입은
> `EvenV11.LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`이다. 즉
> 논문 row word와 local switches가 만드는 Latin row
> `row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5`, RF2, 그리고
> `ribbon-realization`/run-collapse가 만드는 wild
> `e : Seed ≃ RootState`를 구성하고
> `e.symm (returnMap c (e x)) = LowD5M4.fullReturn c x`를 증명하는 것이 정본
> 경로다. RF1은 row equivalence에서 자동 처리된다. 아래의
> `LowD5M4Realization`/`paperReturn` 세부 항목은 legacy adapter와 실패 분석
> 자료로만 본다.

## 0. 논문 충실성 선언 (중요)

이 작업은 v28 논문(`even_modulus_directed_tori_v28_finite_audit_source.tar.gz`)의
**§11 `D5(4)` 패리티 리셋**을 그대로 형식화하는 것입니다. 새 수학을 발명하지
않습니다. 근거 파일(tarball `subtex/`):

| 논문 파일 | 역할 | 이 작업에서 |
|---|---|---|
| `root_flat_first_returns.tex` | RF1/RF2/RF3 framework, unit-carry, δᵢ=eᵢ−e₀ | Lean 인터페이스(`Shared/RootFlat.lean`)와 1:1 |
| `terminal_A2_block.tex` | 행 단어 ωₘ, 터미널 carrier Fᵢ | `ω₄`/`F_i` (dir의 터미널 부분) |
| `D54_parity_reset.tex` | **§11 본문** — T_i,P₀,P₁,R̂_i, 사이트, Table | 구성의 본체 |
| `switching_ribbons.tex` | cut-splice / ribbon 실현 lemma | realization(`hReal`) 근거 |

**이미 논문대로 옮겨진 부분 (재작업 불필요):** `EvenV11/LowD5M4Seed.lean`은
`D54_parity_reset.tex`를 **축자 그대로** 형식화했고 빌드됩니다. 대조:

- `p0=(0,0), p1=(1,0), p2=(2,2)` — 논문 식 (52행) 일치.
- `Tᵢ(q,y)=(Fᵢq, y+1_{q=pᵢ})` — 논문 식 (60행) = `Seed.T`.
- `P₀(q,y)=(F₀^{1_{y=0}}q, y+1)` — 논문 (63행) = `Seed.P0`.
- `P₁=(F₁^{1_{y=3}}F₂^{1_{y=2}}F₀^{1_{y=1}}q, y+1)`, monodromy `W=F₁F₂F₀` —
  논문 (66–71행) = `Seed.P1` / `terminalResetTrace4`.
- `a₀..a₄`, `R̂ᵢ(x,z)=(Rᵢx, z+1_{x=aᵢ})` — 논문 Table D54-reset-ports / (127행)
  = `Seed.liftSite` / `Seed.fullReturn`.
- 단일순환 `lem:D54-active-core`+`prop:D54-reset` ⇒ `Seed.fullReturn_singleCycle`
  (unit-carry = `lem:unit-carry` = Bundle B). **256-cycle을 native_decide 없이 확보.**

즉 논문 §11에서 형식화가 남은 것은 **마지막 문단**("realize these return maps by
layer rows")뿐입니다. 그게 아래 `hReal`입니다.

**2026-06-05 진행 갱신:** `EvenV11/LowD5M4Structural.lean`은 세 개의 H2 handoff를
제공합니다.

- `ResetPortH2RowEquivRibbonRealizationData`: 현재 `Main`의 논문 충실 경로. 실제
  Latin `row`, wild `e`, RF2, `returnMap`과 `LowD5M4.fullReturn`의 conjugacy를
  받습니다. RF1은 `rowLatin_of_rowEquiv`로 닫힙니다.
- `ResetPortH2RibbonRealizationData`: 내부 일반 경로. 실제 `dir`, wild `e`,
  RF1/RF2, conjugacy를 직접 받습니다.
- `ResetPortH2RootFlatCycleData`: RF3 `returnsSingleCycle`을 직접 증명한 경우
  바로 certificate로 올리는 일반 RF 경로입니다.

`EvenV11/Main.lean`은 이제 row-equivalence handoff를 open input으로 사용합니다.

## 1. 작업 진입점 (Lean)

파일 `EvenV11/LowD5M4Structural.lean`의 정리:

```lean
theorem finalLowD5M4RootFlatCertificateFamily_of_returnRealization
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)   -- RootState = Fin 4 → ZMod 4
    (e   : Seed ≃ RootState)                                       -- Seed = (Q4 × Y) × Z
    (hRow   : (LowD5M4Schedule.schedule dir).rowLatin)
    (hLayer : (LowD5M4Schedule.schedule dir).layerBijective)
    (hReal  : ∀ c x, e.symm ((LowD5M4Schedule.schedule dir).returnMap c (e x))
                       = LowD5M4.fullReturn c x) :
    FinalLowD5M4RootFlatCertificateFamily
```

현재 작업 진입점은 `EvenV11/LowD5M4Structural.lean`의
`ResetPortH2RowEquivRibbonRealizationData`입니다. `EvenV11/LowD5M4H2PaperRow.lean`은
`EvenV11/LowD5M4Realization.lean`의 reset-port/paper-table 입력을 이 handoff로
올리는 explicit adapter입니다. 기본 proof spine에는 아직 import하지 않았지만,
paper-table facts를 재사용할 때는
`rowEquivRibbonRealizationData_of_paperTableData`가
`ResetPortH2RowEquivRibbonRealizationData`를 직접 만듭니다.

```lean
structure ResetPortH2RowEquivRibbonRealizationData where
  row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5
  e : Seed ≃ RootState
  layerBijective :
    (LowD5M4Schedule.schedule (dirOfRowEquiv row)).layerBijective
  returnRealization : ∀ c x,
    e.symm ((LowD5M4Schedule.schedule (dirOfRowEquiv row)).returnMap c (e x))
      = LowD5M4.fullReturn c x

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyRibbonRealizationData
    (hData : Nonempty ResetPortH2RibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData
    (hData : Nonempty ResetPortH2RowEquivRibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily
```

즉 `row`, RF2, 그리고 논문 run-collapse가 주는 wild `e`와 conjugacy를 채우면
H2 구조적 family가 나옵니다. 나머지(RF1, RF3 운반, stepConjugacy, 승격)는 이미
증명돼 있습니다.

RF1은 row를 직접 `TorusColor 5 ≃ TorusDirection 5`로 만들면
`rowLatin_of_rowEquiv`로 자동 처리됩니다. 그래서 가장 깨끗한 다음 형태는
`row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5`를 논문 row word와
Table D54-reset-ports의 두-entry 교환으로 만들고,
`finalLowD5M4RootFlatCertificateFamily_of_rowEquivFourLayer`에
`hLayer`와 `FourLayerRealizationGoal`만 공급하는 것입니다.

**추가 진행:** `TerminalA2LowMod.lean`에는 이제 논문 terminal row word
`012`, `210`, `021`, `102`, `120`, `201`가 `terminalRowEquiv : TerminalRow → Fin 3 ≃ Fin 3`
으로 노출됩니다. `LowD5M4Realization.lean`은 이를 D5의 첫 세 색/방향에 올린
`terminalRowEquiv5 : TerminalRow → TorusColor 5 ≃ TorusDirection 5`를 제공합니다.
또한 `terminalBaseRowEquiv5`, `postSwapRow`, `postSwapRowIf`,
`firstLiftCarrySite`, `finalLiftCarrySite`, `yResetTerminalFactor`가 추가되어
terminal row word와 Table D54-reset-ports의 site 데이터를 분리해 쓸 수 있습니다.
`TerminalA2LowMod.lean`에는 indexed 공식
`terminalDelta`, `terminalSymbolOfIndex`, `terminalEta`, `terminalReturn`,
`terminalSymbolStep_of_index`가 추가됐고, `LowD5M4Realization.lean`에는
`F_terminalSymbolOfIndex`와 `paperReturn_apply_terminal`이 있어 D54-reset-ports의
색 `0,1,2` 반환공식을 `i : Fin 3` 하나로 다룰 수 있습니다.
표준 root-flat lift의 실제 좌표 chart도 분리됐습니다:
`terminalStdDirection5 : Fin 3 → TorusDirection 5`는
`0↦0, 1↦1, 2↦4`이고, `liftYDirection5=2`, `liftZDirection5=3`입니다.
Lean 정리 `rootStep_terminalStdDirection5_eq_rootOfCoords`,
`rootStep_liftYDirection5_eq_rootOfCoords`,
`rootStep_liftZDirection5_eq_rootOfCoords`는 각각 표준 `rootStep`이
`q += a_i`, `y += 1`, `z += 1`로 작동함을 좌표식으로 검증합니다.
또한 `terminalStdRowEquiv5 : TerminalRow → TorusColor 5 ≃ TorusDirection 5`가
추가되어 논문 row word를 이 표준 chart로 통과시킨 실제 row equivalence를 제공합니다.
`rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords`는 terminal 색 `0,1,2`에 대해
한 generator step이 `q += a_{row(i)}`이고 `y,z`는 고정됨을 바로 쓸 수 있게 합니다.

또한 `terminalTailBase`, `terminalReturnTailBase`와
`rootStep_terminalTailBase_eq_terminalEta`,
`rootStep_terminalReturnTailBase_eq_terminalReturn`,
`rootStep_terminalReturnTailBase_eq_F_terminalSymbolOfIndex`가 추가되어 논문 공식
`eta_i(z)=(z-a_i)+a_{omega(z-a_i)_i}`와 D5 seed의 `F_i` 표기가 표준 `rootStep`
좌표식으로 연결됩니다.
`terminalReturnTailBaseOfSymbol`과
`rootStep_terminalReturnTailBaseOfSymbol_eq_F`는 같은 계산을 `TerminalSymbol.F0/F1/F2`
자체로 표현합니다.

Table D54-reset-ports의 local substitutions도 row 변환기로 분리됐습니다:
`postSwapColorWithDirection`, `firstLiftSwapRowIf`, `finalLiftSwapRowIf`,
`firstLiftSwappedRow`, `finalLiftSwappedRow`, `resetPortSwappedRow`가 한 source row에
두 unit-carry layer의 two-entry exchange를 적용합니다. 임의의 base layer-row family
`baseRow`에 대해 `resetPortRowOfBase baseRow`를 만들 수 있고,
`rowLatin_of_resetPortRowOfBase`가 RF1(rowLatin)을 즉시 닫습니다.
Table의 reset site 유일성도 Lean에 들어갔습니다:
`firstLiftSiteOfIndex_injective`, `firstLiftCarrySite_fin3_injective`,
`finalLiftSite_injective`, `finalLiftCarrySite_injective`가 각각
first-stage 세 사이트와 final-stage 다섯 사이트가 한 source에서 중복 활성화되지
않음을 제공합니다.
사이트 조건 아래의 실제 generator 효과도 닫혔습니다:
`rootStep_firstLiftSwapRowIf_color_of_site`는 first-lift substitution이
`y += 1`을 만들고, `rootStep_finalLiftSwapRowIf_color_of_site`는 final-lift
substitution이 `z += 1`을 만든다는 좌표식을 제공합니다.
또한 `rootStep_firstLiftSwapRowIf_color`,
`rootStep_firstLiftSwapRowIf_color_of_not_site`,
`rootStep_finalLiftSwapRowIf_color`,
`rootStep_finalLiftSwapRowIf_color_of_not_site`가 추가되어 Table의 local switch를
“carry site이면 lift step, 아니면 기존 row step”이라는 if-식으로 직접 전개할 수
있습니다. `pointCarry_firstLiftSiteOfIndex_eq_ite`,
`pointCarry_liftSite_eq_ite`는 이 site 조건을 논문 반환공식의 `pointCarry` 항과
연결합니다.
`D54ResetData.lean`의 `D54ResetTableCertificate`도 이제
`d54TerminalResetSites_eq_lowD5M4`와
`d54FinalCylinders_eq_lowD5M4_liftSites`를 포함합니다. 따라서 논문
Table D54-reset-ports의 reset sites/final cylinders가 `LowD5M4.p0,p1,p2` 및
`LowD5M4.liftSite`와 같은 데이터라는 사실을 별도 해석 없이 사용할 수 있습니다.
`LowD5M4Realization.ResetPortH2PaperCertificateData`는 이 audited table certificate를
H2 skew-product/table realization 입력과 함께 최상위 handoff로 보존합니다.
또한 `d54TerminalResetSite_eq_firstLiftSiteOfIndex`,
`firstLiftCarrySite_iff_d54TerminalResetSite`,
`d54FinalCylinderOfColor_eq_finalLiftCylinderOfColor`,
`finalLiftCarrySite_iff_d54FinalCylinderOfColor`가 추가되어 논문 표의 indexed site를
실제 reset-port row construction의 site predicate로 바로 옮길 수 있습니다.
`firstLiftSites`와 `finalLiftCylinders`는 이 row construction 이름의 표 list이며,
`ResetPortH2PaperCertificateData` projection으로 nodup, selector disjointness,
lifted selector avoidance, reserve-point nodup/count/avoidance를 certificate에서
바로 꺼냅니다.
`rootStateD54Cylinder`, `noFirstLiftSites_iff_d54TerminalResetSites`,
`noFinalLiftSites_iff_d54FinalCylinders`, `noResetPortSites_iff_d54TableSites`는
논문 표 언어의 site avoidance를 `NoResetPortSites` source predicate로 바로 변환합니다.
support proof가 list nonmembership으로 끝나는 경우에는
`noFirstLiftSites_iff_not_mem_firstLiftSites`,
`noFinalLiftSites_iff_not_mem_finalLiftCylinders`,
`noResetPortSites_iff_not_mem_tableLists`,
`noResetPortSites_iff_not_mem_d54TableLists`를 씁니다.
`d54TerminalSelectorSite`, `d54LiftedSelectorPointOfIndex`,
`noFirstLiftSites_of_d54TerminalSelectorSite`,
`noFinalLiftSites_of_d54LiftedSelectorPoint`,
`noResetPortSites_of_d54LiftedSelectorPoint`는 lifted selector의 각 점에서
reset-port substitution이 비활성임을 pointwise로 꺼내는 bridge입니다.
`d54ReservePointOfRole`, `d54ReserveD54PointOfRole`,
`noResetPortSites_of_d54ReservePointOfRole`도 reserve role별 source에 대해 같은
역할을 합니다. `rootStateD54Point` 등식으로 들어오는 경우에는
`noResetPortSites_of_rootStateD54Point_eq_liftedSelectorPoint`와
`noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole`를 바로 씁니다.
support proof가 list membership으로 끝나는 경우에는
`noResetPortSites_of_qCoord_mem_d54TerminalSelector`,
`noResetPortSites_of_rootStateD54Point_mem_liftedSelector`,
`noResetPortSites_of_rootStateD54Point_mem_reservePoints`가 인덱스 복원 없이 같은
변환을 수행합니다.
중첩된 Table 교환까지 포함한 정규화도 추가됐습니다:
`rootStep_firstLiftSwappedRow_fin3_of_site`는 first-stage 중첩 교환 뒤에도 해당
terminal 색이 정확히 `y += 1`을 수행함을 보이고,
`rootStep_finalLiftSwappedRow_color_of_site`와
`rootStep_resetPortSwappedRow_color_of_final_site`는 final site가 활성화된 색의
전체 reset-port row가 바로 `z += 1`로 정규화됨을 보입니다.
final site가 하나도 활성화되지 않은 source에서는
`finalLiftSwappedRow_of_no_site`와
`rootStep_resetPortSwappedRow_fin3_of_first_site_of_no_final_site`로 first-stage
carry만 분리해서 계산할 수 있습니다.
schedule-level proof에서는 `NoFinalLiftSites`를 바로 받는
`layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites`를 쓰고,
final-cylinder nonmembership이면 `_not_mem_final` / `_d54_not_mem_final` wrapper를
씁니다.
또한 inactive source 처리를 위해 `firstLiftSwappedRow_of_no_site`,
`resetPortSwappedRow_of_no_final_site`, `resetPortSwappedRow_of_no_site`가 추가되어
Table 교환이 언제 base row로 되돌아가는지 명시합니다.
path goal에서 바로 쓰도록 이 계산은 schedule 수준으로도 올라갔습니다:
`layerMap_resetPortDirOfBase_apply`,
`layerMap_resetPortDirOfBase_color_of_final_site`,
`layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_final_site`,
`layerMap_resetPortDirOfBase_color_of_no_site`가 각각 전체 reset-port row의 one-step
효과를 `layerMap` 등식으로 제공합니다.
inactive terminal step도 별도 adapter로 분리됐습니다:
`layerMap_resetPortDirOfBase_of_baseColor_of_no_site`는 base row의 색 엔트리 하나를
알 때 reset-port layerMap을 해당 `rootStep`으로 줄이고,
`layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_site`,
`layerMap_resetPortDirOfBase_terminalTailBase_of_no_site`,
`layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_site`는 각각 논문
`ω₄` row jump, `η_i`, run-collapsed `F_i` 계산을 schedule 수준에서 바로 제공합니다.
source predicate를 이미 `NoResetPortSites` 또는 table-list nonmembership으로 갖고
있으면 대응하는 `_no_resetPortSites` / `_not_mem` wrapper를 써서
`hFirst`/`hFinal`을 다시 분해하지 않습니다. nonmembership이 논문 D54 표 이름
`d54TerminalResetSites`/`d54FinalCylinders`로 들어오면 `_d54_not_mem` wrapper를
바로 씁니다.
2026-06-04 추가: 마지막 layer에서 base row가 실제로 무엇을 읽어야 하는지도
named predicate로 분리했습니다. `BaseRowReadsTerminalTailIndex`는 terminal 색
`i`가 collapsed tail에서 `F_i`를 읽는 조건, `BaseRowReadsTerminalTailSymbol`은
\(P_0/P_1\) terminal factor가 terminal symbol `s`를 읽는 조건,
`BaseRowReadsYShift`는 순수 `Y`-shift factor가 `liftYDirection5`를 읽는 조건입니다.
대응 adapter
`layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_site`,
`layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_site`,
`layerMap_resetPortDirOfBase_of_yShiftRead_no_site`가 이 계약을 schedule-level
one-step 등식으로 올립니다. 따라서 concrete `baseRow`를 만들 때 남은 의무는
앞선 residual path와 마지막-layer row-word read를 별도로 채우는 형태가 됩니다.
source predicate를 이미 `NoResetPortSites`로 갖고 있으면
`layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_resetPortSites`,
`layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites`,
`layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites`를 쓰고,
table-list nonmembership으로 갖고 있으면 대응하는 `_not_mem` wrapper를 씁니다.
논문 D54 표 list 이름으로 갖고 있으면 대응하는 `_d54_not_mem` wrapper를 씁니다.
또한 terminal A2 carrier와 reset-port substitutions를 분리하는 path 인터페이스가
추가됐습니다: `NoResetPortSites`, `BaseRowFourLayerPathGoal`,
`BaseRowNoResetFourLayerPathGoal`,
`resetPortPathGoal_of_baseRowNoResetPathGoal`이 base row의 네 layer 경로를
reset-port row 경로로 올리고, `terminalCoreReturn`,
`ResetPortTerminalCorePathGoal`,
`resetPortTerminalCorePathGoal_to_resetPortPath`가 terminal 색 `0,1,2`의
논문 terminal-A2 first-return 의무를 별도 core goal로 고정합니다.
논문 support 분리에 더 가까운 조건부 형태도 추가했습니다:
`FourLayerRealizationOnGoal`, `BaseRowNoResetFourLayerPathOnGoal`,
`resetPortRealizationOnGoal_of_baseRowNoResetPathOnGoal`,
`ResetPortTerminalCorePathOnGoal`,
`ResetPortTerminalCoreRealizationOnGoal`,
`ResetPortTerminalNoResetRealizationGoal`입니다. 이들은 "모든 source가 reset site를
피한다"는 강한 전역 가정 대신, `NoResetPortSites w`인 source에서 terminal-A2 core
return을 먼저 실현하고 reset-port 예외 source는 별도 switching-ribbon/cut-splice
case로 남기는 형태입니다.
조건부 path goal의 일반형 `FourLayerPathOnGoal`과
`fourLayerRealizationOnGoal_of_pathOnGoal`도 추가되어, source predicate가 붙은
네 layer 중간상태 계산을 바로 restricted realization으로 올릴 수 있습니다.
`paperReturn_apply_finalSite`와 `paperReturn_apply_terminal_sites`는 `paperReturn`
자체를 같은 site/if 표기로 정규화합니다.
final `Z`-carry도 일반 색 `0..4`에 대해 분리됐습니다:
`preFinalReturn`은 논문 \(R_i\) 단계(`Q4 x Y`, `Z` 고정),
`finalCarryReturn`은 final site에서의 `z += 1` target입니다.
이 target들은 이제 논문 본문 식으로도 전개됩니다:
`preFinalReturn_terminal_sites`는 색 `0,1,2`의 \(T_i(q,y)=(F_iq,y+1_{q=p_i})\),
`preFinalReturn_three`는 \(P_0\), `preFinalReturn_four`는 \(P_1\) 공식입니다.
`finalCarryReturn_terminal_sites`, `finalCarryReturn_three`,
`finalCarryReturn_four`는 같은 \(R_i\) target에 final `z += 1`만 붙인 형태입니다.
`ResetPortPreFinalRealizationGoal`,
`ResetPortFinalCarryRealizationGoal`,
`resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry`가
이 분해를 최종 H2 family까지 올립니다. 따라서 full `paperReturn` 등식을 직접
증명하지 않고, 논문 Table의 \(R_i\) case와 \(\widehat R_i\) final-carry case를
별도 switching-ribbon/cut-splice 의무로 공급할 수 있습니다.
색별 입력도 같은 표 구조로 쪼개졌습니다:
`ResetPortPreFinalTerminalRealizationGoal`,
`ResetPortPreFinalP0RealizationGoal`,
`ResetPortPreFinalP1RealizationGoal`과
`ResetPortFinalCarryTerminalRealizationGoal`,
`ResetPortFinalCarryP0RealizationGoal`,
`ResetPortFinalCarryP1RealizationGoal`을 공급하면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryColorGoals`가
최종 H2 family까지 조립합니다.
각 realization 의무에는 대응하는 path-goal 버전도 있습니다:
`ResetPortPreFinalTerminalPathRealizationGoal`,
`ResetPortPreFinalP0PathRealizationGoal`,
`ResetPortPreFinalP1PathRealizationGoal`,
`ResetPortFinalCarryTerminalPathRealizationGoal`,
`ResetPortFinalCarryP0PathRealizationGoal`,
`ResetPortFinalCarryP1PathRealizationGoal`입니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryPathGoals`는
이 여섯 path-goal 묶음을 최종 H2 family까지 바로 올립니다.
terminal 색의 pre-final \(T_i\) 부분은 Table D54-reset-ports의 첫 lift까지 더
분리했습니다. `terminalFirstCarryReturn`은 \(q=p_i\)인 active source에서의
\(y+=1\) target이고,
`ResetPortPreFinalTerminalNoFirstPathRealizationGoal`,
`ResetPortPreFinalTerminalFirstCarryPathRealizationGoal`을 공급하면
`resetPortPreFinalTerminalRealizationGoal_of_firstCarryPathGoals`가
`ResetPortPreFinalTerminalRealizationGoal`을 닫습니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalTerminalFirstSplitPathGoals`는
이 terminal first-carry split과 아직 통합된 \(P_0/P_1\), final-carry path-goals를
함께 받아 최종 H2 family까지 조립합니다.
\(P_0/P_1\)도 paper row-word 식으로 더 분리했습니다:
`preFinalYShiftReturn`은 순수 \(y+=1\) target이고,
`preFinalYTerminalReturn`은 \(Y\)-circuit의 특정 layer에서 \(F_0,F_2,F_1\) factor를
읽는 target입니다. 대응 path-goal은
`ResetPortPreFinalP0YShiftPathRealizationGoal`,
`ResetPortPreFinalP0F0PathRealizationGoal`,
`ResetPortPreFinalP1YShiftPathRealizationGoal`,
`ResetPortPreFinalP1Y1F0PathRealizationGoal`,
`ResetPortPreFinalP1Y2F2PathRealizationGoal`,
`ResetPortPreFinalP1Y3F1PathRealizationGoal`이고,
`ResetPortPreFinalYShiftLastStepPathOnGoal`과
`resetPortPreFinalYShiftPathOnGoal_of_lastStepPathOnGoal`은 순수 \(y+=1\) row-word를
마지막 layer의 `liftYDirection5` 입력으로 줄여 줍니다.
`ResetPortPreFinalYTerminalTailPathOnGoal`과
`resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal`은 이 terminal-factor path를
논문의 collapsed terminal tail `q + Delta_s - a_s` 형태로 줄여 줍니다.
이 tail path들의 마지막 layer 조건은 이제 raw equality가 아니라
`BaseRowReadsTerminalTailSymbol` / `BaseRowReadsYShift`로 표현됩니다.
구체 필드에는 `resetPortPreFinalP0F0PathRealizationGoal_of_tailPathOnGoal` 및
`resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailPathOnGoal`,
`resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailPathOnGoal`,
`resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailPathOnGoal`로 연결됩니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalRowWordSplitPathGoals`가
terminal first-carry split, \(P_0/P_1\) row-word split, final-carry split을 함께
받는 현재 가장 세분화된 논문식 진입점입니다.
final `Z` carry도 같은 target 계층으로 정규화했습니다:
`terminalCoreFinalCarryReturn`, `terminalFirstFinalCarryReturn`,
`finalYShiftReturn`, `finalYTerminalReturn`이 각각 terminal/no-first,
terminal/first, \(Y\)-shift, \(Y\)-terminal-factor target에 `z+=1`을 붙인 형태입니다.
대응 path-goal은
`ResetPortFinalCarryTerminalNoFirstPathRealizationGoal`,
`ResetPortFinalCarryTerminalFirstPathRealizationGoal`,
`ResetPortFinalCarryP0YShiftPathRealizationGoal`,
`ResetPortFinalCarryP0F0PathRealizationGoal`,
`ResetPortFinalCarryP1YShiftPathRealizationGoal`,
`ResetPortFinalCarryP1Y1F0PathRealizationGoal`,
`ResetPortFinalCarryP1Y2F2PathRealizationGoal`,
`ResetPortFinalCarryP1Y3F1PathRealizationGoal`입니다.
`ResetPortFinalYShiftLastStepPathOnGoal`과
`resetPortFinalYShiftPathOnGoal_of_lastStepPathOnGoal`은 final `Z` carry가 붙은 순수
Y-shift target을 같은 마지막-layer `liftYDirection5` 형태로 줄여 줍니다.
`ResetPortFinalYTerminalTailPathOnGoal`과
`resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal`은 같은 tail-path 입력에
final `Z` carry를 붙인 버전입니다.
구체 필드에는 대응하는
`resetPortFinalCarryP0F0PathRealizationGoal_of_tailPathOnGoal`,
`resetPortFinalCarryP1Y1F0PathRealizationGoal_of_tailPathOnGoal`,
`resetPortFinalCarryP1Y2F2PathRealizationGoal_of_tailPathOnGoal`,
`resetPortFinalCarryP1Y3F1PathRealizationGoal_of_tailPathOnGoal`이 있습니다.
더 세분화된 final-carry Z-first handoff에서는 이 구형 final-carry tail 입력 대신
`ResetPortFinalZFirstYShiftLastStepPathOnGoal`과
`ResetPortFinalZFirstYTerminalTailPathOnGoal`을 사용합니다. 즉 final carry site의
첫 layer는 local substitution의 강제 `z += 1` step으로 먼저 소모하고, \(P_0/P_1\)
row-word residual도 layers `1,2,3`만 남깁니다.
이 긴 path-goal 묶음은
`ResetPortPreFinalRowWordSplitPathGoals`,
`ResetPortFinalCarryRowWordSplitPathGoals`,
`ResetPortFullRowWordSplitPathGoals`로 패키징했습니다.
더 논문식 handoff로는
`ResetPortPreFinalTailRowWordSplitPathGoals`,
`ResetPortFinalCarryTailRowWordSplitPathGoals`,
`ResetPortFullTailRowWordSplitPathGoals`가 있습니다. 이 패키지는 \(P_0/P_1\)의
순수 Y-shift 필드는 `YShiftLastStep` 형태로, terminal-factor 필드는 위 collapsed
terminal tail 형태로 직접 받으며,
`resetPortFullRowWordSplitPathGoals_of_tail`이 기존 full path-goal 패키지로 변환합니다.
최상위 handoff는 이제 prefix/read 분리 entry 계열입니다. RF2를 이미 닫았다면
`ResetPortH2PrefixReadData`가 concrete `baseRow`,
`ResetPortLayerBijectiveGoal baseRow`, switching-ribbon prefix path 묶음
`ResetPortFullSplitPrefixGoals baseRow`, 그리고 concrete row-word read 묶음
`ResetPortFullSplitReadGoals baseRow`를 받습니다. RF2를 root-state equivalence로
운반한 상태라면 `ResetPortH2PaperLayerEquivPrefixReadData`를 쓰고, 논문 RF2 class
(ii)의 skew-product lift 그대로라면
`ResetPortH2PaperSkewProductPrefixReadData`를 씁니다. split goals가 이미 결합돼
있다면 `ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData`를 쓰면 됩니다.
더 논문 표에 가까운 read 입력으로는 `ResetPortFullPaperRowWordReadGoals`가 있으며,
terminal colors, pre-final \(P_0/P_1\), final-carry \(P_0/P_1\)의 read table을 따로
받아 `ResetPortFullSplitReadGoals`로 접습니다. 이 경로의 compact entry는
`ResetPortH2PrefixRowReadData`, `ResetPortH2LayerEquivPrefixRowReadData`,
`ResetPortH2SkewProductPrefixRowReadData`입니다.
prefix path side도 같은 표 단위로 묶은 `ResetPortFullPaperPrefixGoals`가 있으며,
이를 row-word read table과 합친 `ResetPortFullPaperTableGoals`가 현재 가장 compact한
§11 handoff입니다. RF2가 이미 닫힌 경우 `ResetPortH2PrefixTableData`, layer-equiv
RF2인 경우 `ResetPortH2LayerEquivPrefixTableData`, skew-product RF2 그대로인 경우
`ResetPortH2SkewProductPrefixTableData`를 씁니다.
base row와 RF2를 이미 갖고 있다면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals`가
`ResetPortFullPaperTableGoals`를 직접 split prefix/read realization으로 올립니다.
논문 Table D54-reset-ports 인증서는 이미 `D54ResetData.d54ResetTableCertificate`로
닫혀 있습니다. 이 paper-table 계열은 legacy adapter입니다. 2026-06-05 이후
`Main`의 H2 open slot은 `ResetPortH2PaperTableData`가 아니라
`LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`입니다. paper-table
facts를 재사용하는 경우 `EvenV11/LowD5M4H2PaperRow.lean`의
`rowEquivRibbonRealizationData_of_paperTableData`가 이를 현재 H2 입력으로 변환합니다.
이 adapter는 `paperReturn` 등식을 `seedRootEquiv` conjugacy로 접습니다. 반면 `Main`
기본 handoff는 여전히 더 일반적인 wild `e`를 허용합니다.
세 필드가 따로 준비되면
`resetPortH2PaperTableData_of_fields` 또는
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableFields`를 사용합니다.
prefix/read 두 표가 따로 준비된 경우에는
`resetPortFullPaperTableGoals_of_fields`,
`ResetPortFullPaperTableGoals.splitPrefixGoals`,
`ResetPortFullPaperTableGoals.splitReadGoals`,
`ResetPortFullPaperTableGoals.splitGoals`,
`resetPortH2PaperTableData_of_prefixReadFields`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperPrefixReadFields`가
split 내부 의무로 내려가는 표준 projection입니다.
논문 §11의 component들
`preFinalTerminalPrefix`, `preFinalP0P1Prefix`,
`finalCarryTerminalPrefix`, `finalCarryP0P1Prefix`,
`preFinalTerminalRead`, `preFinalP0P1Read`, `finalCarryP0P1Read`가
각각 준비된 경우에는
`resetPortFullPaperPrefixGoals_of_components`,
`resetPortFullPaperRowWordReadGoals_of_components`,
`resetPortFullPaperTableGoals_of_components`,
`resetPortH2PaperTableData_of_components`,
`nonempty_resetPortH2PaperTableData_of_components`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperComponents`를 바로 사용합니다.
support/reserve projection이 필요할 때는 canonical conversion
`resetPortH2PaperCertificateData_of_paperTableData`로
`ResetPortH2PaperCertificateData`를 만들면 됩니다.
component 입력에서 support/reserve projection까지 바로 필요하면
`resetPortH2PaperCertificateData_of_components`를 사용합니다.
`ResetPortH2PaperCertificateData.resetSitesEqFirstLift`와
`ResetPortH2PaperCertificateData.finalCylindersEqFinalLift`는 이 certificate에서
Lean row construction의 first/final lift table을 바로 꺼내는 projection입니다.
추가 projection
`ResetPortH2PaperCertificateData.firstLiftSitesNodup`,
`ResetPortH2PaperCertificateData.firstLiftSitesDisjointSelector`,
`ResetPortH2PaperCertificateData.finalLiftCylindersNodup`,
`ResetPortH2PaperCertificateData.finalLiftCylindersAvoidLiftedSelector`,
`ResetPortH2PaperCertificateData.reservePointsAvoidFinalLiftCylinders`,
`ResetPortH2PaperCertificateData.reservePointsDisjointLiftedSelector`,
`ResetPortH2PaperCertificateData.reservePointsNodup`,
`ResetPortH2PaperCertificateData.reservePointsCount`가 논문 support/reserve facts를
같은 row-construction 이름으로 제공합니다.
Boolean table predicates를 membership proof에서 바로 쓰려면
`listsDisjoint_ne_of_mem`, `cylindersAvoidPoints_avoid_of_mem`,
`cylindersAvoidPoints_ne_or_ne_of_mem`,
`reservesAvoidCylinders_avoid_of_mem`,
`reservesAvoidCylinders_ne_or_ne_of_mem`를 사용합니다.
paper certificate에서 바로 꺼내는 wrapper로는
`ResetPortH2PaperCertificateData.firstLiftSite_ne_selector_of_mem`,
`ResetPortH2PaperCertificateData.finalLiftCylinder_ne_selector_of_mem`,
`ResetPortH2PaperCertificateData.reservePoint_ne_finalLift_of_mem`,
`ResetPortH2PaperCertificateData.reservePoint_ne_selector_of_mem`가 있습니다.
indexed table entries를 membership proof로 바꾸는 기본 lemma는
`firstLiftSiteOfIndex_mem_firstLiftSites`,
`d54TerminalSelectorSite_mem_d54TerminalSelector`,
`d54LiftedSelectorPointOfIndex_mem_d54LiftedSelector`,
`finalLiftCylinderOfColor_mem_finalLiftCylinders`,
`d54ReserveD54PointOfRole_mem_reservePoints`입니다. 이 membership을 이미 내장한
indexed wrapper는
`ResetPortH2PaperCertificateData.firstLiftSiteOfIndex_ne_selectorSite`,
`ResetPortH2PaperCertificateData.finalLiftCylinder_avoids_liftedSelectorPoint`,
`ResetPortH2PaperCertificateData.finalLiftCylinder_ne_liftedSelectorPoint`,
`ResetPortH2PaperCertificateData.reservePoint_avoids_finalLiftCylinder`,
`ResetPortH2PaperCertificateData.reservePoint_ne_finalLiftCylinder`,
`ResetPortH2PaperCertificateData.reservePoint_ne_liftedSelectorPoint`입니다.
source predicate 쪽은 `noResetPortSites_iff_d54TableSites`가 맡습니다. 즉
cut-splice/support 분리 proof에서 D54 표의 terminal reset sites와 final cylinders를
피한다는 조건을 얻으면, 이를 `NoResetPortSites`로 바로 넘길 수 있습니다.
그 조건이 list nonmembership이면
`noResetPortSites_of_not_mem_tableLists` 또는
`noResetPortSites_of_not_mem_d54TableLists`를 바로 쓰면 됩니다.
selector 자체를 source로 다룰 때는 `noResetPortSites_of_d54LiftedSelectorPoint`를
바로 쓰면 됩니다. reserve role별 source는
`noResetPortSites_of_d54ReservePointOfRole` 또는
`noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole`로 처리합니다.
membership 형태의 support 결론은
`noResetPortSites_of_rootStateD54Point_mem_liftedSelector`와
`noResetPortSites_of_rootStateD54Point_mem_reservePoints`로 처리합니다.
기존 combined entry
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailData`도 호환 entry로 남아 있으며,
`resetPortFullCoreYFirstZFirstTailRowWordGoals_of_split`은 필요한 경우 split goals를
combined goals로 접는 호환 변환으로 남아 있습니다. 다만 현재 기본 split theorem은
`resetPortPreFinalRealizationGoal_of_coreYFirstTailSplitRowWordGoals`와
`resetPortFinalCarryRealizationGoal_of_zFirstTailSplitRowWordGoals`를 사용해 split
prefix/read handoff를 바로 realization goal로 올립니다.
이 core-Y-first/Z-first tail 목표는 pre-final terminal no-first를
`TerminalCoreTailPathGoal`(no-reset terminal-A2 core)과
`ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal`(다른 reset-port site와
충돌하는 residual)로 나눕니다. pre-final terminal first-carry도
`ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal`로 no-final source의
첫 `y += 1` layer 뒤 남은 terminal-A2 run을 collapsed terminal tail 입력으로 받고,
다른 final-stage site와 충돌하는 source만
`ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal`로 남깁니다.
split 형태에서는
`resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailSplitPathGoal`
및
`resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplitNoFinal_and_finalConflict`
가 `NoResetPortSites` tail prefix를 분해하지 않고 바로 씁니다.
pre-final \(P_0/P_1\)는 Y-shift last-step과 collapsed terminal tail 입력을
받습니다. final carry의 terminal 색과 \(P_0/P_1\) row-word tail은
`ResetPortFinalCarryZFirstTailRowWordGoals`로 첫 layer의 강제 `z += 1` step을
분리하고, 나머지 세 layer만 residual path로 남깁니다.
`P_0/P_1` split 입력도
`resetPortYShiftPathOnGoal_of_lastStepSplitPathOnGoal`,
`resetPortYTerminalPathOnGoal_of_tailSplitPathOnGoal`,
`resetPortFinalYShiftPathOnGoal_of_zFirstLastStepSplitPathOnGoal`,
`resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal`을 통해
`NoResetPortSites`를 직접 마지막 row-word read adapter로 넘깁니다.
`ResetPortLayerEquivData`는 각 `(layer,color)`의 실제 `layerMap`을 명시적
`RootState ≃ RootState`와 동일시하는 호환 RF2 형식입니다. 논문에서
\(\widehat R_i\) layer들이 skew-product lift라 RF2 class (ii)로 처리되는 부분은
`ResetPortLayerSkewProductData`로 seed 좌표 `(Q4 × Y) × Z`의 base/fiber equivalence와
layerMap 등식을 주며, 최상위 theorem은 이 데이터를 그대로 받습니다. 필요하면
`resetPortLayerEquivData_of_layerSkewProductData`로 layer-equiv 호환 형식에 올립니다.
singleton RF2 데이터 `ResetPortSingletonSwitchLayerData`는 각 `(layer,color)` row마다
비교 row `T/R`, switching site, left/right 선택, common-image 조건
`T site = R site`, 그리고 실제 `layerMap` 등식을 요구합니다. 이 데이터는
`resetPortLayerEquivData_of_singletonSwitchLayerData`와
`resetPortPartialExchangeLayerData_of_singletonSwitchLayerData`를 통해 각각
direct layer-equiv RF2 또는 일반 partial-exchange RF2 패키지로 변환됩니다.
덜 분해된 core-split entry
`ResetPortH2PaperSingletonCoreSplitTailRealizationData`, singleton-tail entry
`ResetPortH2PaperSingletonTailRealizationData`와
일반 RF2 handoff인 `ResetPortH2PaperTailRealizationData`도 호환 entry로 남아 있습니다.
prefix/read 최상위 theorem은
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductPrefixReadData`입니다.
RF2가 이미 layer-bijective로 닫혀 있으면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixReadData`를 바로 쓰고,
root-state equivalence 형태라면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivPrefixRead`를
씁니다.
paper row-word read table을 쓰는 경우에는 각각
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixRowRead`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2LayerEquivPrefixRowRead`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixRowRead`가
같은 조립을 수행합니다.
legacy paper prefix table까지 함께 쓰는 theorem은
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixTable`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2LayerEquivPrefixTable`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixTable`입니다.
constructed data 자체가 이미 있으면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData`를 직접 써도 됩니다.
이 table theorem들은 공통으로
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals`에 내려갑니다.
skew-product prefix/read, row-read, table entry는 모두
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductSplitData`를
거쳐 direct split realization route를 사용합니다.
표 인증서 projection까지 같은 패키지에서 쓰는 compatibility theorem은
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperCertificate`입니다.
이 theorem도 certificate의 skew-product RF2와 paper table goals를 바로
base-level paper-table theorem에 넘깁니다.
split 최상위 theorem은
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductSplitData`입니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductCoreYFirstZFirstData`는
combined 데이터 항으로 최종 H2 family를 만듭니다. layer-equiv split 호환 entry
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstSplitData`와
combined layer-equiv 호환 entry
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstData`와
기존 core-split용
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreYFirstZFirstData`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreZFirstData`,
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreSplitData`,
singleton-tail용
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonTailRealizationData`,
일반 RF2용
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTailRealizationData`, 기존
`ResetPortH2PaperRealizationData`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperRealizationData`도 호환 entry로
남아 있습니다. RF2가 이미 별도 정리로 닫혀 있다면
`ResetPortH2RealizationData`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2RealizationData`도 사용할 수 있습니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoal`는
이 패키지와 RF2를 따로 받는 하위 entry입니다.
기존의 낱개 인자형
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoals`도
호환 adapter로 남겨 두었습니다.
여기에 `paperReturn_terminal_eq_terminalCoreReturn_of_no_resetPortSites`를 추가해
reset-port site가 모두 비활성인 source에서는 논문 terminal-A2 core가 곧 terminal 색
`paperReturn`임을 직접 쓸 수 있게 했습니다. 예외 source는
`paperReturn_terminal_of_no_final_site`,
`paperReturn_terminal_of_first_site_of_no_final_site`,
`paperReturn_terminal_of_final_site`가 각각 no-final, first-stage, final-stage
case로 분리합니다.
또한 `TerminalCoreTailPathGoal`과
`resetPortTerminalCorePathOnGoal_of_tailPathGoal`를 추가했습니다. no-reset terminal
core에서는 처음 세 layer가 `terminalReturnTailBase i (qCoord w)`까지 도달하고, 네
번째 layer에서 `BaseRowReadsTerminalTailIndex` 계약을 만족한다는 조건만 주면
`ResetPortTerminalCorePathOnGoal`이 나옵니다. 즉 마지막 terminal jump
`F_i(z)=eta_i(z+Delta_i)`는 더 이상 매번 다시 펼칠 필요가 없습니다.
RF2도 이제 논문식 partial-exchange 인터페이스로 내려갔습니다:
`resetPortLayerBijective_of_partialExchangeLeft_eq`,
`resetPortLayerBijective_of_partialExchangeRight_eq`,
`resetPortLayerBijective_of_partialExchangeChoice_eq`는 각 layer map을
`partialExchangeLeft`/`partialExchangeRight`와 동일시하고
`ComparisonSetInvariant`(`T^{-1}R(U)=U`)만 공급하면
`ResetPortLayerBijectiveGoal baseRow`를 닫습니다.
계산 전개용으로 `layerMap_dirOfRowEquiv_apply`와
`layerMap_resetPortRowOfBase_apply`도 추가되어, 이후 RF2 equality와 four-layer
return 계산에서 schedule 정의를 직접 펼칠 필요가 줄었습니다.

주의: `terminalBaseRowAtState`는 논문 row word 자체를 `qCoord w`에서 읽는 보조
정의입니다. 실제 physical layer-row `row t w`는 root-flat layer `t`와 표준 lift
좌표계의 방향 차이를 반영하는 chart를 한 번 더 통과해야 합니다. 따라서 다음
concrete `row`는 `terminalBaseRowEquiv5 (terminalOmega ...)`를 그대로 최종 `dir`로
쓰는 것이 아니라, 논문 §terminal-A2의 triangle-base 좌표와
`LowD5M4Schedule.rootStep`의 표준 방향을 맞춘 `terminalStdRowEquiv5`를 시작점으로
삼은 뒤 `resetPortRowOfBase`/`resetPortSwappedRow`로 두 lift의 local two-entry swaps를
얹는 방식으로 작성합니다.

**기본 빌드 정책:** 논문 구조 포팅을 우선하기 위해 generated
`LowD5M4Finite`/`LowD7M6Finite` witness는 기본 `EvenV11` proof spine에서
제외했습니다. 파일은 archive/명시 target으로 보존하되, `lake build EvenV11`은
`EvenV11.lean`의 import closure와 현재 구조적 인터페이스를 검증하는 형태로 좁혀
H2 구조화 작업의 피드백 시간을 유지합니다.
`scripts/check_evenv11_progress.sh`도 이 정책에 맞춰 보존용 generated/archive
finite 파일의 `native_decide`를 구조 포팅 실패로 보지 않고, structural module의
새 `native_decide`와 H2/H4 generated finite target의 기본 import 재유입을 막습니다.
따라서 `Main.assume_lowD5M4`는 이제
`LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData`
를 적용한 파생 정리입니다. 실제 open slot은
`Main.assume_lowD5M4RibbonRealizationData :
Nonempty LowD5M4RibbonRealizationData`이며, concrete Latin `row`, RF2, wild
run-collapse reindexing `e`, 그리고 `returnRealization`이 채워질 때 닫힙니다.

## 2. 현재 의무 ↔ 논문 대응표

| Lean 의무 | 논문 근거 | 난이도 |
|---|---|---|
| `row` (구성) | `terminal_A2_block.tex` ω₄ + `D54_parity_reset.tex` Table D54-reset-ports의 5 치환 | 구성(데이터), RF1 자동 |
| `e : Seed ≃ RootState` | `switching_ribbons.tex` / `D54_parity_reset.tex` run-collapse return-section correspondence | open; 반드시 wild 재색인으로 구성 (`seedRootEquiv` 고정 금지) |
| `hLayer` (RF2) | `lem:partial-exchange`(`T⁻¹R(U)=U`) | **인터페이스 완료**: `resetPortLayerBijective_of_partialExchange*`에 `hU`와 layerMap equality 공급 |
| **`hReturn` / `hReal`** (realization) | **`lem:switching-ribbons`** + `lem:cut-splice` | **핵심 hard math** |

## 3. `dir` 구성 (논문 데이터, m=4)

`dir t w c`는 높이 `t`, 루트 상태 `w`에서 색 `c`가 쓰는 generator 방향(δ∈Fin 5,
δ=eδ−e₀)을 주는 표. 논문대로 **기저 layer schedule + 5개 치환**:

1. **기저**: 터미널 A₂ layer word `ω₄`(`terminal_A2_block.tex`, eq:terminal-word)
   × Y-좌표 row word(매 layer y+1) × neutral Z-row. 기저의 색별 first-return은
   `(F₀,F₁,F₂, F₀-as-P₀, W-as-P₁)`가 되도록 색을 배치.
   표준 `rootStep` chart에서는 terminal 꼭짓점 이동이 방향 `0,1,4`에 대응하고,
   Y/Z lift가 각각 방향 `2,3`에 대응합니다. 즉 논문 row word의 target index
   `0,1,2`를 물리 방향으로 읽을 때는 `terminalStdDirection5`를 통과시켜야 하며,
   row 전체는 `terminalStdRowEquiv5 (terminalOmega ...)`로 시작합니다.
2. **5개 치환**(`Table D54-reset-ports`, 각 사이트에서 두 색 엔트리의 2-entry 교환):
   - 색0: `T₀` carry at `p₀=(0,0)` → Z-사이트 `((0,0),0)`
   - 색1: `T₁` at `p₁=(1,0)` → `((0,0),1)`
   - 색2: `T₂` at `p₂=(2,2)` → `((0,0),2)`
   - 색3: `P₀`(F₀ once) → `((0,0),3)`
   - 색4: `P₁`(W once) → `((0,1),0)`
   Lean에서는 first lift를 `firstLiftSwapRowIf`, final lift를 `finalLiftSwapRowIf`로
   기록합니다. 각 치환은 기존 Latin row 내부의 2-entry 교환이라 RF1은
   `rowLatin_of_resetPortRowOfBase`로 이미 보존됩니다. RF2와 return-map equality는
   여전히 `lem:layer-comparison-switch`/`lem:switching-ribbons`에 해당하는 남은 부분입니다.
   단 RF2는 이제 `resetPortLayerBijective_of_partialExchangeChoice_eq` 등으로
   논문의 `partial-exchange` 불변집합 조건과 layerMap 등식만 증명하면 됩니다.

**baseRow negative controls (2026-06-04):** 다음 단순 모델들은 terminal 세 색의
4-layer return `F_i`조차 동시에 만들지 못합니다.

- `baseRow t w = terminalStdBaseRowEquiv5 (qCoord w)`.
- layer별 offset만 허용한
  `terminalStdRowEquiv5 (terminalOmega (qCoord w + s_t))`.
- layer별 offset, terminal 색 재라벨링, terminal 출력 방향 재라벨링을 모두 허용한
  모델.

따라서 concrete `baseRow`는 단순히 terminal word를 현재 `qCoord`에서 읽는 row가
아니라, 논문 terminal block의 quotient/fiber chart를 root-flat layer `t`와 함께
반영해야 합니다. Lean 쪽에서는 이 부담을 `TerminalCoreTailPathGoal`의 처음 세
layer path 조건과 마지막 `BaseRowReadsTerminalTailIndex` /
`BaseRowReadsTerminalTailSymbol` / `BaseRowReadsYShift` 조건으로 분리했습니다.

최종 조립용 Lean 진입점은 기본 spine 기준으로
`LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData`입니다.
paper-table 경로를 명시적으로 쓸 때는
`LowD5M4H2PaperRow.rowEquivRibbonRealizationData_of_paperTableData` 또는
`LowD5M4H2PaperRow.finalLowD5M4RootFlatCertificateFamily_of_nonemptyPaperTableData`를
사용합니다.
가장 논문식으로 남은 H2 입력은
`ResetPortH2PaperSkewProductPrefixReadData`입니다. 이 데이터의 필드는 `baseRow`,
`ResetPortLayerSkewProductData baseRow`,
`ResetPortFullSplitPrefixGoals baseRow`, 그리고
`ResetPortFullSplitReadGoals baseRow`입니다. RF2를 이미 별도 lemma로 닫았다면
`ResetPortH2PrefixReadData`, root-state equivalence로 운반했다면
`ResetPortH2PaperLayerEquivPrefixReadData`가 같은 prefix/read 입력을 공유합니다.
skew-product prefix/read entry는 prefix/read를 합친 split data로 바로 접힌 뒤
direct split realization theorem을 호출합니다.
read side를 논문 §11 표 그대로 terminal/pre-final/final-carry row-word table로
나누어 공급하려면 `ResetPortFullPaperRowWordReadGoals`를 쓰고,
`ResetPortH2SkewProductPrefixRowReadData`를 최상위 handoff로 사용합니다.
prefix path side까지 terminal/pre-final/final-carry 표 단위로 공급하는 legacy
adapter로는 `ResetPortFullPaperTableGoals`와 `ResetPortH2PaperTableData`가 있습니다.
각 표 component가 따로 있으면 `resetPortH2PaperTableData_of_components`,
`nonempty_resetPortH2PaperTableData_of_components` 또는
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperComponents`가 최단 경로입니다.
이미 RF2를 닫은 base row라면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals`를 바로 쓸 수
있습니다.
논문 reset-port 표 인증서 projection이 필요하면
`ResetPortH2PaperCertificateData`를 쓸 수 있습니다. 이는 support/reserve 표 facts
재사용용 compatibility layer이지 현재 `Main` handoff는 아닙니다.
split 형태로 이미 묶은 증명이 있다면
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductSplitData`를
사용하면 됩니다. combined 형태로 이미 묶은 증명이 있다면 기존
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailData`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductCoreYFirstZFirstData`를
그대로 사용할 수 있습니다.
`ResetPortLayerEquivData`는 skew-product RF2를 이미 root-state equivalence로 운반한
호환 형식입니다.
singleton two-entry switching으로 RF2를 보이는 경우에는
`ResetPortH2PaperSingletonCoreYFirstZFirstTailData`와
`ResetPortSingletonSwitchLayerData`를 사용할 수 있습니다. 일반 비교집합 `U`가 필요한
경우에는 호환 entry `ResetPortH2PaperTailRealizationData`와
`ResetPortPartialExchangeLayerData`를 그대로 사용할 수 있습니다.
`ResetPortFullTailRowWordSplitPathGoals`는 pre-final `R_i` 계산과 final `Z` carry 계산을
논문 row-word 단위로 나누되, \(P_0/P_1\)의 terminal factors를 collapsed terminal tail
입력으로 받는 path-goal 패키지입니다.
`ResetPortFullCoreSplitTailRowWordGoals`는 여기서 한 단계 더 나아가 terminal no-reset
core를 `TerminalCoreTailPathGoal`로 분리하고, 남은 pre-final terminal no-first
예외만 residual path-goal로 둡니다.
`ResetPortFullCoreZFirstTailRowWordGoals`는 여기에 final-carry terminal 색과
\(P_0/P_1\) row-word tail의 첫 `z += 1` layer까지 자동화해, final side에는
3-layer residual path만 남깁니다.
`ResetPortFullCoreYFirstZFirstTailRowWordGoals`는 추가로 pre-final terminal
first-carry의 no-final source에서 첫 `y += 1` layer를 자동화한 뒤 collapsed
terminal tail만 요구하고, final-site 충돌 source만 residual로 남기는 combined
패키지입니다. 현재 최상위 split 패키지
`ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals`는 같은 내용을
`TerminalCoreTailSplitPathGoal`, `ResetPortYTerminalTailSplitPathOnGoal`,
`ResetPortYShiftLastStepSplitPathOnGoal`,
`ResetPortFinalZFirstYTerminalTailSplitPathOnGoal`,
`ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal`로 더 나누어, collapsed tail까지의
prefix path와 마지막 row-word read 계약을 별도 필드로 받습니다.
이 split 패키지는 이제 combined 패키지로 접히지 않고
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailSplitGoals`
에서 직접 pre-final/final-carry realization으로 조립됩니다.
가장 분리된 `ResetPortFullSplitPrefixGoals` /
`ResetPortFullSplitReadGoals`는 이 split fields를 switching-ribbon prefix proof와
concrete row-word read proof 두 묶음으로 한 번 더 나눕니다.

RF2를 이미 `ResetPortLayerBijectiveGoal baseRow`로 닫은 경우에는 하위 패키지
`ResetPortH2RealizationData`를 그대로 쓸 수 있습니다.

하위 호환 진입점도 유지합니다.
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer`는 `baseRow`, RF2,
`ResetPortFourLayerRealizationGoal baseRow`를 직접 받습니다. 후자는 다시 논문 Table의 세 묶음:
`ResetPortTerminalRealizationGoal baseRow`(색 0,1,2),
`ResetPortP0RealizationGoal baseRow`(색 3), `ResetPortP1RealizationGoal baseRow`(색 4)
로 나눌 수 있고, `resetPortFourLayerRealizationGoal_of_colorGoals`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseColorGoals`가 이를 조립합니다.
더 낮은 계산 인터페이스로는
`ResetPortTerminalPathRealizationGoal`, `ResetPortP0PathRealizationGoal`,
`ResetPortP1PathRealizationGoal`이 있으며, 이는 각 색의 네 layer 중간상태
`x1,x2,x3`를 제공하는 형태입니다.
`resetPortFourLayerRealizationGoal_of_pathGoals`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePathGoals`가 이 path 의무들을
최종 H2 family로 올립니다.
final `Z`-lift를 논문 표 그대로 분리해서 공급하려면 더 직접적인 진입점
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry`를 쓰면 됩니다.
이 경우 남은 realization 입력은
`ResetPortPreFinalRealizationGoal baseRow`와
`ResetPortFinalCarryRealizationGoal baseRow`이고, 전자는 \(\widehat R_i\) 이전의
`R_i` return 계산, 후자는 final switching site의 local `z += 1` 계산입니다.
표의 행별로 공급하려면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryColorGoals`가
terminal 세 색, `P0`, `P1`의 pre-final/final-carry 의무 여섯 묶음을 받습니다.
cut-splice 증명이 중간 상태를 산출하는 형태라면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryPathGoals`가
더 직접적인 진입점입니다.
terminal 세 색의 pre-final \(T_i\)를 논문 Table의 \(q=p_i\) first-lift case까지
쪼개서 공급하려면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalTerminalFirstSplitPathGoals`가
중간 진입점입니다. \(P_0/P_1\) row-word도 함께 분리해 공급하려면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalRowWordSplitPathGoals`가
pre-final 쪽의 세분화된 진입점입니다. final `Z` carry까지 같은 row-word target으로
분리해 공급하려면
`ResetPortFullRowWordSplitPathGoals`와
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoal`가
하위 진입점입니다. RF2를 partial-exchange 데이터로 보존해 이 세 필드를 하나로 묶은
`ResetPortH2PaperRealizationData`는 호환 패키지입니다. 현재 `Main`의 H2 open
slot이 요구하는 최상위 패키지는
`ResetPortH2RowEquivRibbonRealizationData`입니다.
skew-product RF2와
core-Y-first/Z-first tail 입력을 직접 받는
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData` 및 combined
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailData`는 호환 패키지로 남아 있습니다.

## 4. `e` 좌표 동치 (논문)

`Seed = (Q4×Y)×Z = (ℤ/4)²×(ℤ/4)×(ℤ/4) = (ℤ/4)⁴`,
`RootState = Fin 4 → ℤ/4 = (ℤ/4)⁴` (루트-플랫 단면 K_root의 자유 4좌표,
`root_flat_first_returns.tex`). 예전 문서의 `seedRootEquiv`는 단순 좌표 chart였고,
`returnMap = paperReturn` 목표에는 사용할 수 없다는 blocker가 확인됐습니다.
현재 필요한 `e`는 `switching_ribbons.tex`의 run-collapse correspondence가 만드는
wild return-section 재색인입니다.

```lean
((q0, q1), y), z  ↦  fun i =>
  match i with
  | 0 => q0
  | 1 => q1
  | 2 => y
  | 3 => z
```

## 5. `hReal` — 핵심 (논문 `lem:switching-ribbons`)

`hReal c : e.symm (returnMap c (e x)) = fullReturn c x`, 즉
`returnMap c = e ∘ fullReturn c ∘ e.symm` (켤레). 현재 Lean 목표는
`ResetPortH2RowEquivRibbonRealizationData.returnRealization` 필드입니다. 이것을
`paperReturn` 등식으로 바꾸면 다시 blocker에 걸립니다.

`returnMap c`(=`step=rootStep` generator-move의 4-layer 합성, `Shared/RootFlat.lean`
`returnMap` 정의)가 §3 기저+5치환으로 만들어졌을 때, **`lem:switching-ribbons`**
("support-separated ribbon 족의 first-return 효과 = cut-splice 식들의 순서곱")에
의해 정확히 `R̂_c = fullReturn c`가 됨. 이를 형식화.

**이미 형식화된 Lean 도구(이걸로 조립):**
- `EvenV11/Switching.lean`:
  - `ComparisonSetInvariant`, `partialExchangeLeft`, `partialExchangeRight` =
    `lem:partial-exchange`.
  - `rootFlatLayerBijective_of_partialExchangeLeft_eq`,
    `rootFlatLayerBijective_of_partialExchangeRight_eq`,
    `rootFlatLayerBijective_of_partialExchangeChoice_eq` = RF2 보존.
- `Shared/SwitchCalculus.lean`:
  - `oneStepPacketSplice` / `flagSplicingCriterion` = `lem:cut-splice`.
  - `splice_mapsTo`, `within_coset_reach`, `splice_eq_orig_off_tail` = 보조.
- `Shared/MasterReturn.lean`:
  - `oneStepPacketSplice_unitCarrySingleCycle`,
    `flagSplicingCriterion_unitCarrySingleCycle` = unit-carry와의 결합.

**작업 절차(논문 순서 그대로):**
1. 기저 schedule의 색별 first-return을 계산 → 터미널 `F_i`/Y-monodromy 형태 확인
   (m=4 유한이므로 `decide`로 layer 합성 = 기저 return 검증 가능).
2. 5개 치환을 cut-splice 식(`oneStepPacketSplice`)으로 순차 적용, support 분리
   (`within_coset_reach`/`splice_mapsTo`)를 확인.
3. 순서곱 = `R̂_c` (= `fullReturn c` after `e`) 를 등식으로 마무리.

support 분리(사이트들이 서로·선택자 C₄ 근방과 disjoint)는 논문 (56–57행:
`C₄∪F₁^{±1}(C₄)∪F₂^{±1}(C₄)`와 disjoint)·(125행) 데이터로 보장.

## 6. 완료 후 (제가 재개)

`dir`, RF1/RF2, wild `e`, return-realization conjugacy가
`ResetPortH2RowEquivRibbonRealizationData`로 채워지면:
1. `EvenV11/Main.lean`의
   `assume_lowD5M4RibbonRealizationData :
   Nonempty LowD5M4RibbonRealizationData := sorry`를 constructed data의
   `Nonempty.intro`로 교체. `assume_lowD5M4`는 이미
   `finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData`를
   통해 구조적으로 파생된다.
2. `lake build EvenV11`로 기본 spine이 generated `LowD5M4Finite` 없이 닫히는지 검증.
3. 필요하면 `lake build EvenV11.LowD5M4Finite`를 archive/명시 target으로만
   보존/검증하고,
   기본 import closure에는 다시 넣지 않음. H4도 같은 정책으로
   `LowD7M6Finite`를 archive/명시 target으로만 두고, 논문 Appendix A/B 기반
   structural replacement가 들어올 때까지 기본 proof spine에서는 비활성으로 둔다.

## 7. 참조 (열기)

- 정리: `EvenV11/LowD5M4Structural.lean`
- 단일순환(완료): `EvenV11/LowD5M4Seed.lean`
- schedule 인프라: `EvenV11/LowD5M4Schedule.lean` (torusEquiv, rootStep, stepConjugacy_of_dir)
- RF 프레임: `Shared/RootFlat.lean`
- cut-splice/ribbon 도구: `Shared/SwitchCalculus.lean`, `Shared/MasterReturn.lean`
- 논문 §11: tarball `subtex/D54_parity_reset.tex` (+ `terminal_A2_block.tex`,
  `switching_ribbons.tex`, `root_flat_first_returns.tex`)
