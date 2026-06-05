# 가장 어려운 부분들 (사용자 해결용 핸드오프)

작성일: 2026-06-04. H3 `D7(4)`는 generated finite root-flat certificate로 닫혔다.
H2 `D5(4)`와 H4 `D7(6)`의 generated witnesses는 archive/명시 검증 target으로
남기되, 논문 구조 포팅으로 대체하기 위해 기본 `EvenV11` proof spine에서는
비활성화했다. 남은 핵심은 H1/H2/H4/H5/H6의 concrete family/promotion 실현이다.
아래는 현재 정밀 obligation.

## 0. 현재 상태 (빌드되는 자산)
- `EvenV11/LowD5M4Seed.lean` — **clean, sorry-free**. D5(4) 5색 return이 256-cycle:
  `fullReturn_singleCycle : ∀ i:Fin 5, Shared.IsSingleCycleMap (fullReturn i)`.
  여기서 `fullReturn i = additiveSkewMap (baseReturn i) (pointCarry (liftSite i) 1)`,
  `baseReturn` = `T_i`(=`additiveSkewMap (F sᵢ) (pointCarry pᵢ 1)`) 또는 `P0/P1`.
  `F s = terminalSymbolStep 4 s` (터미널 A2 carrier, 16-cycle).
- `EvenV11/LowD5M4Schedule.lean` — **clean, sorry-free**.
  표준 lift: `RootState = Fin 4 → ZMod 4`, `rootStep`, `torusEquiv`, `torusEquiv_step`.
  추가로 `schedule`, `liftedColorDir`, `stepConjugacy_of_dir`가 있어, 임의의
  `dir`에 대한 `stepConjugacy`는 자동으로 따라온다.
- `EvenV11/LowD5M4Finite.lean` — **clean, sorry-free generated certificate**.
  아카이브의 Round10 D5(4) root-flat 배열 certificate를 현재 `EvenV11`
  인터페이스로 포팅했다. 제공 정리:
  `finalLowD5M4RootFlatCertificateFamily : FinalLowD5M4RootFlatCertificateFamily`.
- `EvenV11/FiniteArrayCert.lean` — **clean, sorry-free**. 아카이브의 array/blob
  certificate checker를 `EvenV11` namespace로 격리 포팅했다.
- `EvenV11/StandardRootFlatLift.lean` — **clean, sorry-free**. 표준
  `ZMod m × (Fin n → ZMod m) ≃ TorusVertex (n+1) m` lift와 `torusEquiv_step`.
- `EvenV11/LowD7M4Finite.lean` — **clean, sorry-free generated certificate**.
  `RootState = Fin 4096` blob certificate를 `FinalRootFlatTorusCertificate 7 4`로 승격.
- `EvenV11/LowD7M6Finite.lean` — **clean, sorry-free generated certificate**.
  `RootState = Fin 46656` blob certificate를 `FinalRootFlatTorusCertificate 7 6`로 승격.
  현재는 기본 `EvenV11` library root/import spine에서 제외되어, 명시적 target으로만
  검증하는 대체 예정 자산이다.
- `EvenV11/D3EvenM4.lean` — **clean, sorry-free archived certificate**.
  `ordinary_three_four : Shared.CayleyHamiltonDecomposition 3 4`를 제공한다.
- `EvenV11/D3EvenM4RootFlat.lean` — **clean, sorry-free root-flat certificate**.
  `D3EvenM4`의 64-cycle에서 4-step root-flat returns를 추출해
  `rootFlatCertificate : FinalD3EvenRootFlatCertificate 4`를 제공한다.
- `EvenV11/D3EvenRouteEGeSix.lean` — **clean, sorry-free archived Route-E bridge**.
  `ordinary_three_m6/m8/m10`은 finite rank-table로 닫혀 있고,
  일반 `m ≥ 6`은
  `ordinary_three_ge_six_of_routeE_zero_layer_return_rank_package`로 남는다. 즉
  zero-layer bijectivity와 `RouteEReturnModelRankPackage m`가 있으면 D3 ordinary
  decomposition으로 승격된다. 추가로
  `routeELayerMap_zero_layer_bijective_of_even_mod_cases`,
  `routeEReturnModelRankPackageOfEvenModCases`,
  `ordinary_three_ge_six_of_routeE_residue_rank_packages`가 있어 이 두 일반 입력을
  `m % 6 = 0∨2`와 `m % 6 = 4` residue 의무로 분해한다. 또한
  `routeELayerMap_zero_layer_bijective_of_even_ge_six_tail`,
  `routeEReturnModelRankPackageOfEvenGeSixTail`,
  `ordinary_three_ge_six_of_routeE_tail_residue_rank_packages`가
  finite heads `m=6,8,10,12`를 제거해 남은 증명 범위를 짝수 `m≥14` tail로 낮춘다.
  추가로 `routeEReturn{Zero,One,Two}Model_singleCycle_of_even_ge_six_tail`이 있어
  rank package가 아니라 색별 return-model single-cycle 입력으로도 같은 finite head
  제거를 재사용할 수 있다.
  이 파일만으로 H1 전체가 닫히지는 않는다.
- `EvenV11/D3EvenRouteERootFlatBridge.lean` — **clean, sorry-free Route-E root-flat bridge**.
  위 Route-E schedule을 `FinalD3EvenRootFlatCertificate m`로 승격한다.
  `rootFlatCertificate_m6/m8/m10/m12`는 닫혀 있고,
  `D3EvenM4RootFlat.rootFlatCertificateFamily_of_routeE_zero_layer_rankPackage`는
  일반 `m≥6` zero-layer bijectivity/rank package가 있으면
  `FinalD3EvenRootFlatCertificateFamily`를 준다. 따라서 H1의 D3-specific 잔여는
  일반 `m≥6` 두 입력으로 축소됐다.
- `EvenV11/CycleOnBridge.lean` — **clean, sorry-free compatibility bridge**.
  old `TorusD4.CycleOn N f x` orbit certificate를 현재의
  `Shared.IsSingleCycleMap f`로 바꾸는 `isSingleCycleMap_of_cycleOn`을 제공한다.
  `formal/TorusD3Even/Color2.lean`의 `cycleOn_color2` 같은 기존 first-return proof를
  `EvenV11` Route-E return-model 경로로 가져오기 위한 표준 변환이다.
- `EvenV11/D3EvenRouteEColor2Bridge.lean` — **clean, sorry-free old Color2 bridge**.
  좌표 equivalence `routeEColorTwoCoordEquiv : RootState m ≃ TorusD3Even.P0Coord m`
  (`w ↦ (w.1,-w.2)`)와 `oldR2xy_singleCycle`을 제공한다. 후자는 old
  `TorusD3Even.Color2.cycleOn_color2`를 `CycleOnBridge.isSingleCycleMap_of_cycleOn`으로
  현재 `Shared.IsSingleCycleMap (TorusD3Even.R2xy)` 형태로 변환한다.
- `EvenV11/Main.lean` — `assume_lowD7M4`는 generated certificate로 교체됨.
  H2는 `assume_lowD5M4RibbonRealizationData :
  Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`, H4는
  `assume_lowD7M6CycleData`를 논문 구조 포팅으로 대체하기 위한 open input으로
  두었다. 실제 `sorry`는 H1/H2/H4/H5/H6 다섯 개.

### H1/D3 비교 메모

v28 논문은 §5 terminal `A₂` row word로 모든 짝수 `m ≥ 4`의 D3 base를 처리한다.
아카이브 Lean도 같은 방향의 중간 산물을 갖고 있지만, 현재 재사용 가능한 닫힌 조각은
두 층이다.

- `D3EvenM4`는 `m=4` ordinary decomposition을 닫고, `D3EvenM4RootFlat`은 이를
  현재 H1 payload인 `FinalD3EvenRootFlatCertificate 4`로 승격한다.
- `D3EvenM4RootFlat.rootFlatCertificateFamily_of_routeE_residue_rankPackages`는
  Route-E의 residue별 zero-layer bijection/rank package 네 입력을 곧바로
  `FinalD3EvenRootFlatCertificateFamily`로 올린다.
- `D3EvenM4RootFlat.rootFlatCertificateFamily_of_routeE_tail_residue_rankPackages`는
  이미 닫힌 `m=4,6,8,10,12` head를 사용해 H1의 Route-E 잔여를 짝수 `m≥14`의
  residue별 zero-layer bijection/rank package로 낮춘다.
- `D3EvenM4RootFlat.rootFlatCertificateFamily_of_routeE_tail_returnModels`는 같은
  finite head 제거를 rank package 대신 zero-layer tail + 세 색 return-model
  single-cycle tail 입력으로 제공한다. 이는 old `TorusD3Even` first-return proofs가
  rank table이 아니라 `CycleOn`/single-cycle 형태로 끝나는 점에 맞춘 연결부다.
- `D3EvenRouteEGeSix`는 `m=6,8,10,12` finite head와 일반 `m≥6` 조건부 브리지를
  제공한다.
- `D3EvenRouteERootFlatBridge`는 Route-E ordinary bridge를 현재 H1 타입에 맞는
  root-flat certificate bridge로 올렸다. 따라서 H1에서 남은 D3-specific gap은
  일반 `m≥6` zero-layer bijectivity/rank package이다.
- 2026-06-04 추가: `D3EvenRouteEGeSix`에 residue-case wrapper를 넣어 이 gap을
  `m % 6 = 0∨2` 계열과 `m % 6 = 4` 계열의 zero-layer bijection/rank package로
  분리했다. 이는 H1을 닫지는 않지만, 다음 sprint의 symbolic proof 단위를 더 작게
  만든다.
- 2026-06-04 추가(2): finite heads `m=6,8,10`을 wrapper 내부에서 사용하도록 해서,
  실제 symbolic Route-E proof는 짝수 `m≥12` tail만 남기도록 더 줄였다.
- 2026-06-04 추가(3): `m=12`도 zero-layer bijection과 세 return-model
  orbit-search rank certificate로 닫아, 남은 Route-E tail 의무를 짝수 `m≥14`로
  낮췄다.
- 2026-06-04 추가(4): old `TorusD3Even`의 `CycleOn` 결과를
  `Shared.IsSingleCycleMap`으로 변환하는 bridge와, return-model single-cycle 입력만으로
  H1 root-flat family까지 올리는 wrapper를 추가했다. 아직 H1이 닫힌 것은 아니며,
  남은 핵심은 색 0/1의 full first-return counting 또는 동등한 일반 return-model
  single-cycle proof, 그리고 zero-layer bijection tail이다.
- 2026-06-04 추가(5): `even_modulus_directed_tori_v28_finite_audit_source.tar.gz`와
  대조했다. v28의 H1/D3 base는 `subtex/terminal_A2_block.tex`의 terminal
  row word `ω_m`로 서술되고, 핵심 cyclicity는 Lemma `terminal-cyclicity`
  (`F_0,F_1,F_2`가 `Q_m`에서 cyclic)이다. 이는 현재 Lean의
  `Route-E` tail 의무와 별개의 새 우회로라기보다 같은 `A_2` first-return
  cyclicity를 다른 좌표/이름으로 적은 것이다. old Lean 쪽에서는 색 2만
  `TorusD3Even.Color2.cycleOn_color2`까지 닫혀 있고, 색 0/1은 full
  `m^2` return cycle이 아니라 lane-cycle 조각 위주다. 따라서 "방법을 바꾼다"의
  실질적 의미는 Route-E rank-table 일반화가 아니라 v28/old Lean의 terminal
  first-return counting을 current return-model single-cycle 입력으로 연결하는 것이다.
  color 2는 좌표 `w ↦ (w.1,-w.2)`로 old `R2xy`와 맞는 것으로 finite sanity
  check가 되었지만, 일반 Lean 정리로 올리려면 `m % 6 = 4` zero-layer color-2
  table 또는 더 추상적인 `match-if` 분배 lemma가 먼저 필요하다. 이 table을 직접
  자동화로 추가하는 시도는 빌드 비용/분기 정리가 나빠 철회했다.
- 2026-06-04 추가(6): 위 철회 지점은 `apply_word_ite`로 해결했다.
  `D3EvenRouteEGeSix.routeELayerMap_zeroLayer_color_two_of_not_mod_zero_or_two`가
  닫혀서 color 2의 `m % 6 = 4` zero-layer table도 사용 가능하다. 또한
  `D3EvenRouteEColor2Bridge.oldR2xy_singleCycle`이 old `cycleOn_color2`를
  current `Shared.IsSingleCycleMap`으로 변환한다. 남은 color-2 연결은
  `routeEColorTwoCoordEquiv (routeEReturnTwoModel m w) =
  TorusD3Even.R2xy (routeEColorTwoCoordEquiv m w)` 형태의 prefix-3 켤레 정리다.
  이 정리는 zero-layer table만으로 끝나지 않고 `routeEPrefix3TwoModel`의
  두 후속 조건(`z.1.val = 0`, `v.2.val = 0`)까지 분해해야 한다.
- 2026-06-04 추가(7): 목표를 약간 낮춘다. 당장 "H1 전체를 닫기"가 아니라,
  H1의 다음 결정을 위한 최소 브리지 의무를 분리한다. v28 tarball의
  `subtex/root_flat_first_returns.tex`는 RF1/RF2/RF3 criterion을 제시하고,
  `subtex/terminal_A2_block.tex`는 terminal row-word `ω_m`의 일반 cyclicity를
  endpoint-pair recurrence로 증명한다. 반면 현재 Lean에는
  `TerminalA2LowMod.lean`의 `m=4,6` finite terminal carriers와 old
  `TorusD3Even.Color2.cycleOn_color2`가 닫혀 있을 뿐, v28의 일반
  `terminal-cyclicity` 전체가 current `FinalD3EvenRootFlatCertificateFamily`로
  연결되어 있지는 않다. 따라서 지금의 더 작은 목표는 둘 중 하나다:
  (a) current Route-E `routeEReturnTwoModel`을 old `R2xy`와 conjugacy로 연결해
  color 2 tail을 확정하고 같은 패턴이 색 0/1에도 재사용 가능한지 판단한다;
  (b) Route-E tail을 우회해 v28의 terminal endpoint-pair recurrence를 Lean의
  ordinary D3 promotion 경로에 직접 올릴 수 있는지 확인한다. 오늘 확인한 바로는
  (a)는 `R2xy` 쪽 branch bookkeeping만으로도 길고, 진짜 남은 난점은 current
  table의 `val` 조건을 `ZMod` branch 조건으로 번역하는 부분이다. 그러므로
  "방법을 바꾼다"면 전체 형식화 완료가 아니라 이 두 경로의 비용을 비교하는
  audit/proof-spike 목표로 바꾸는 것이 맞다.
- 2026-06-04 추가(8): 위 "목표를 낮춘다"는 최종 성공 조건을 바꾼다는 뜻이 아니라
  H1을 닫기 위한 다음 작업 단위를 낮춘다는 뜻으로 정정한다. 실제 Lean 쪽에서는
  `D3EvenRouteEColor2Bridge.routeEReturnTwoOldConjModel`을 추가했고,
  old `TorusD3Even.R2xy` 순환성을 current Route-E root 좌표로 운반하는
  `routeEReturnTwoOldConjModel_singleCycle` 및
  `routeEReturnTwoModel_singleCycle_tail_of_eq_oldConj`가 빌드된다. 또한
  current `routeEReturnTwoModel`이 zero-layer color-2 map 뒤에 두 root-shift를
  적용한 것이라는 `routeEReturnTwoModel_eq_shifted_zeroLayer`와, old-conjugated
  모델의 `R2xy` case table인 `routeEReturnTwoOldConjModel_eq_cases`를 추가했다.
  따라서 color-2 tail의 남은 의무는 더 이상 순환성 정리가 아니라
  `routeELayerMap_zeroLayer_color_two_of_(not_)mod_zero_or_two`의 `val` 기반
  table을 이 old-conjugated case table과 맞추는 symbolic case proof다.
- `RoundComposite/EvenRound14TerminalD3.lean`은 terminal row-word / direct layer /
  return-rank / finite-certificate boundary를 많이 갖지만, 최종적으로는
  `TerminalD3StructuredRFGoal` 또는 `DirectD3...CertificatePackage` 같은 일반 D3
  입력을 요구한다.

따라서 H1에 대해서도 "이 방법뿐"은 아니다. 선택지는 (1) 논문 §5 row-word를
직접 형식화해 일반 `m≥6` D3 입력을 닫는 길, (2) 이미 존재하는
`FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat` 경로를 사용해 H1을
root-flat family가 아니라 ordinary D3 promotion으로 낮춘 뒤 `D3EvenM4` + 일반
Route-E package를 연결하는 길, (3) H2-H4처럼 D3 root-flat family를 generated
certificate 계열로 별도 생성하는 길이다. 현 시점에서 Lean에 이미 닫힌 것은 (1)의
일반부가 아니라 위 finite/conditional 조각이다.

외부 sanity check로 Route-E 구성 자체는 `m=12,14,...,30`에서 zero-layer
permutation과 세 return cycle이 모두 맞았다. 이는 Lean 증명이 아니라 구성 검산일
뿐이지만, Route-E 경로가 반례 때문에 막힌 상태는 아니라는 신호다. 남은 문제는
일반 `m`에 대한 symbolic bijection/cycle proof를 어떻게 세우느냐다.

## 1. 완료: H2 `dir` 구성 + returnMap 연결

H2의 generated witness `LowD5M4Finite.finalLowD5M4RootFlatCertificateFamily`는
명시 target으로 보존되어 있다. 기본 `EvenV11` proof spine에서는 이 witness를
import하지 않는다. 현재 `assume_lowD5M4`는
`LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`에서 파생되며, 실제 open
input은 `assume_lowD5M4RibbonRealizationData`다. §11 skew-product/prefix-table
entry는 `EvenV11/LowD5M4H2PaperRow.lean`에서 이 row-equivalence handoff로 변환하는
explicit adapter로 남아 있다.

일반적으로 `finalRootFlatTorusCertificate_of_fields`는 다음 필드를 요구
(`schedule = { dir := fun t w c => dir t w c, step := LowD5M4Schedule.rootStep }`):

```lean
-- RootState := Fin 4 → ZMod 4,  m = 4,  d = 5
-- 구성해야 할 것:
def dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5 := ?  -- §11 folded+reset 색칠

theorem rowLatin       : schedule.rowLatin           -- ∀ t w, Bijective (c ↦ dir t w c)
theorem layerBijective : schedule.layerBijective
theorem returnsSingleCycle : schedule.returnsSingleCycle  -- ∀ c, IsSingleCycleMap (returnMap c)
theorem stepConjugacy  : ... -- `LowD5M4Schedule.stepConjugacy_of_dir dir`로 즉시 해결
```

**남겨둘 교훈 (핵심 간극):**
`schedule.returnMap c` = 4개 layer map의 합성 = **generator 이동(rootStep)의 합성**.
그런데 제가 증명한 `fullReturn`은 **추상 `F_i = terminalSymbolStep`**(복잡한 16-cycle
순열)로 만들어졌습니다. `F_i`는 단일 generator 이동이 **아닙니다**. 따라서:

> **핵심 obligation**: dir의 generator-이동 returnMap이 단일순환임을 보여야 하는데,
> 이는 (a) 논문 §5 terminal A2 block의 layer-row가 합성되어 `F_i`를 실현함을
> 증명하거나, (b) dir의 returnMap을 직접 단일순환으로 증명(skew 구조 재발견)해야 함.

**대체 접근(semantic parity-reset 증명으로 교체하고 싶을 때)**:
1. **`F_i`를 generator-row 합성으로 재정의** — `terminalSymbolStep` 대신, 터미널
   A2 block의 실제 4-layer generator 합성으로 `F_i`를 정의하고 16-cycle을 `decide`로
   재증명. 그러면 returnMap = fullReturn이 구성적으로 성립.
2. **dir → returnMap 직접 계산** — dir을 좌표로 정의하고 `returnMap c`를 `decide`/
   계산으로 단일순환 증명. (256-cycle을 orbit cert로 직접은 비현실적 → skew 구조 필요.)
3. **추상↔구체 conjugation** — dir의 returnMap이 제 `fullReturn`과 켤레임을 보임.

기본 proof spine은 finite-array certificate를 사용하지 않는다. H2의 open slot은
`assume_lowD5M4RibbonRealizationData :
Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`이며,
generated witness는 명시 target으로만 남겨 둔다.
`D54ResetTableCertificate`는 reset orbit/selector/reserve facts에 더해
`d54TerminalResetSites_eq_lowD5M4`와
`d54FinalCylinders_eq_lowD5M4_liftSites`를 포함하므로, 논문 Table D54-reset-ports의
site 데이터가 `LowD5M4`의 `p0,p1,p2`/`liftSite`와 일치함을 Lean 패키지 안에서
재사용할 수 있다.
`ResetPortH2PaperTableData`는 H2 skew-product/table realization 입력을
보존하는 explicit paper-table adapter다. 현재 `Main` handoff는 더 작은
row-equivalence ribbon data이고,
`LowD5M4H2PaperRow.rowEquivRibbonRealizationData_of_paperTableData`가 paper-table
data를 그 입력으로 변환한다. 닫힌 D54 audit을 함께 쓰는 support projection이
필요하면 `resetPortH2PaperCertificateData_of_paperTableData`로
`ResetPortH2PaperCertificateData`를 만든다.
`d54TerminalResetSite_eq_firstLiftSiteOfIndex`와
`finalLiftCarrySite_iff_d54FinalCylinderOfColor`가 표 site를 실제 reset-port row
construction의 site predicate로 옮긴다.
`firstLiftSites`/`finalLiftCylinders`는 row construction 이름의 표 list이며,
certificate projection으로 selector/reserve disjointness도 이 이름으로 재사용한다.
`noResetPortSites_iff_d54TableSites`는 표 site avoidance를 `NoResetPortSites`
source predicate로 바꾼다.
list nonmembership 형태는 `noResetPortSites_iff_not_mem_tableLists`와
`noResetPortSites_iff_not_mem_d54TableLists`로 바로 처리한다.
`d54TerminalSelectorSite`, `d54LiftedSelectorPointOfIndex`,
`noResetPortSites_of_d54LiftedSelectorPoint`는 lifted selector의 각 점을
path/read source로 잡을 때 first/final reset-port substitutions가 비활성임을
pointwise로 넘기는 bridge다.
`d54ReservePointOfRole`, `d54ReserveD54PointOfRole`,
`noResetPortSites_of_d54ReservePointOfRole`와
`noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole`는 reserve role별
source에 대한 같은 bridge다.
list membership 형태로 support 결론이 나오면
`noResetPortSites_of_qCoord_mem_d54TerminalSelector`,
`noResetPortSites_of_rootStateD54Point_mem_liftedSelector`,
`noResetPortSites_of_rootStateD54Point_mem_reservePoints`를 바로 쓴다.

## 2. 완료된 기계적 부분 — `LowD5M4Schedule.lean`
순수 `Fin` 인덱싱 bookkeeping은 완료:
- `torusEquiv.left_inv`  : `invFun (toFun (t,w)) = (t,w)`.
- `torusEquiv.right_inv` : `toFun (invFun x) = x`.
- `torusEquiv_step` : `torusEquiv tw + torusBasis 5 4 δ = torusEquiv (tw.1+1, rootStep δ tw.2)`.
- `stepConjugacy_of_dir` : 모든 `dir`에 대해 final root-flat model의 `stepConjugacy`를 제공.

**중요 통찰(형식화 완료)**: `stepConjugacy`는 **dir과 무관**이다. 남은 H2 필드는
`rowLatin`, `layerBijective`, `returnsSingleCycle`이며, 본질은 concrete `dir`이
`LowD5M4Seed.fullReturn`과 같은 returnMap을 실현한다는 연결이다.

## 3. H2 조립 상태
```lean
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixReadData
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivPrefixRead
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductPrefixReadData
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixRowRead
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixTable
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_nonemptyResetPortH2PaperTableData
LowD5M4Realization.finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperCertificate
LowD5M4H2PaperRow.rowEquivRibbonRealizationData_of_paperTableData
LowD5M4H2PaperRow.finalLowD5M4RootFlatCertificateFamily_of_nonemptyPaperTableData
```

`EvenV11/Main.lean`의 `assume_lowD5M4`는 현재 구조 정리로 파생된다. 실제 `sorry`
open slot은 `assume_lowD5M4RibbonRealizationData :
Nonempty LowD5M4RibbonRealizationData`다.
RF2가 이미 layer-bijective로 닫혀 있으면 `ResetPortH2PrefixReadData`
(concrete `baseRow`, `ResetPortLayerBijectiveGoal`, prefix path goals,
last-layer row-word read goals)를 공급해 paper table data까지 올리면 된다.
layer-equiv RF2로 이미 운반한 경우
`ResetPortH2PaperLayerEquivPrefixReadData`가 대응 prefix/read 호환 entry다. 논문
RF2 class (ii)의 skew-product lift 그대로라면
`ResetPortH2PaperSkewProductPrefixReadData`가 최상위 handoff다. split goals를 이미
묶었다면 `ResetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData`와
`ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData`가 대응 split 호환 entry이고,
combined `ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData`도 호환 entry로 남아 있다.
read side를 논문 §11 표처럼 terminal/pre-final/final-carry row-word table로
공급하는 경우 `ResetPortFullPaperRowWordReadGoals`와
`ResetPortH2SkewProductPrefixRowReadData`를 쓰면 된다.
prefix path side까지 같은 표 단위로 공급하는 경우
`ResetPortFullPaperTableGoals`와 `ResetPortH2PaperTableData`가 현재 가장
compact한 H2 handoff다. RF2를 이미 닫은 base row라면
`finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals`가 이 table을
직접 split realization route로 올린다.
세 필드가 따로 있으면 `resetPortH2PaperTableData_of_fields`로 최상위 handoff를
조립한다.
prefix/read component별 proof가 따로 준비되는 경우에는
`resetPortH2PaperTableData_of_components`,
`nonempty_resetPortH2PaperTableData_of_components`, 또는
`finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperComponents`로 바로
최상위 H2 handoff까지 조립한다.
논문 reset-port 표 인증서를 같은 top-level 입력에 남기려면
`ResetPortH2PaperCertificateData`를 쓴다. component 입력에서 바로 만들려면
`resetPortH2PaperCertificateData_of_components`를 쓴다.
이때 `ResetPortH2PaperCertificateData.resetSitesEqFirstLift`와
`ResetPortH2PaperCertificateData.finalCylindersEqFinalLift`가 certificate의 표와
row construction의 first/final lift table을 연결한다.
support 분리에는 `firstLiftSitesDisjointSelector`,
`finalLiftCylindersAvoidLiftedSelector`,
`reservePointsAvoidFinalLiftCylinders`, `reservePointsNodup`,
`reservePointsCount` projection을 쓴다.
membership proof에서 바로 쓰는 inequality/avoidance wrapper는
`firstLiftSite_ne_selector_of_mem`, `finalLiftCylinder_ne_selector_of_mem`,
`reservePoint_ne_finalLift_of_mem`, `reservePoint_ne_selector_of_mem`이다.
색/selector-index/reserve-role이 이미 있으면 indexed wrapper
`firstLiftSiteOfIndex_ne_selectorSite`,
`finalLiftCylinder_ne_liftedSelectorPoint`,
`reservePoint_ne_finalLiftCylinder`,
`reservePoint_ne_liftedSelectorPoint`를 바로 쓴다.
source predicate 변환에는 `noFirstLiftSites_iff_d54TerminalResetSites`,
`noFinalLiftSites_iff_d54FinalCylinders`,
`noResetPortSites_iff_d54TableSites`를 쓴다. selector/reserve point source는
각각 `noResetPortSites_of_d54LiftedSelectorPoint`와
`noResetPortSites_of_d54ReservePointOfRole`로 바로 처리한다. membership 형태이면
`noResetPortSites_of_rootStateD54Point_mem_liftedSelector` /
`noResetPortSites_of_rootStateD54Point_mem_reservePoints`를 쓴다.
list nonmembership 형태이면 `noResetPortSites_of_not_mem_tableLists` /
`noResetPortSites_of_not_mem_d54TableLists`를 쓴다.
inactive terminal/read adapter에도 `_no_resetPortSites` / `_not_mem` wrapper가 있어
support proof가 만든 `NoResetPortSites`를 그대로 schedule-level one-step 계산에 넘긴다.
논문 D54 표 list nonmembership은 `_d54_not_mem` wrapper로 이름 변환 없이 넘긴다.
first-carry/no-final 첫 step은
`layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites`와
final-cylinder `_not_mem_final` / `_d54_not_mem_final` wrapper로 처리한다.
split tail 입력은
`resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplitNoFinal_and_finalConflict`
로 바로 realization goal에 올린다.
`P0/P1` split tail/read 입력도
`resetPortYShiftPathOnGoal_of_lastStepSplitPathOnGoal`,
`resetPortYTerminalPathOnGoal_of_tailSplitPathOnGoal`,
`resetPortFinalYShiftPathOnGoal_of_zFirstLastStepSplitPathOnGoal`,
`resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal`으로 바로 올린다.
singleton partial-exchange RF2가 필요한 경우
`ResetPortH2PaperSingletonCoreYFirstZFirstTailData`가, 일반 partial-exchange RF2가
필요한 경우 `ResetPortH2PaperTailRealizationData`가 호환 entry로 남아 있다.
pre-final terminal no-first는 no-reset terminal-A2 core와 reset-port residual로
분리되어 있고, pre-final terminal first-carry는 no-final source의 forced `y += 1`
first step 뒤 collapsed terminal tail, 그리고 final-site conflict residual로
분리되어 있다. final-carry terminal 색과
`P0/P1` row-word tail은 forced `z += 1` first step과 residual 3-layer path로
분리되어 있다.
순수 Y-shift는 `ResetPortPreFinalYShiftLastStepPathOnGoal` 및
`ResetPortFinalZFirstYShiftLastStepPathOnGoal`로 마지막 `liftYDirection5` layer를
지정한다.
`P0/P1`의 terminal factors는 `ResetPortPreFinalYTerminalTailPathOnGoal` 및
`ResetPortFinalZFirstYTerminalTailPathOnGoal`로 논문 terminal tail
`q + Delta_s - a_s`에 맞춰 공급할 수 있다.
이 마지막-layer 지정은 현재 raw row equality가 아니라
`BaseRowReadsTerminalTailIndex`, `BaseRowReadsTerminalTailSymbol`,
`BaseRowReadsYShift` 계약으로 분리되어 있다. 즉 concrete `baseRow` handoff는
collapsed tail까지 가는 residual path와, 그 tail에서 논문 row-word가 읽는 방향을
증명하는 마지막-layer 계약으로 나뉜다. 최상위에서는 이 둘을
`ResetPortFullSplitPrefixGoals`와 `ResetPortFullSplitReadGoals`로 따로 받는다.
기본 split theorem은 이제 combined package 변환 대신
`resetPortPreFinalRealizationGoal_of_coreYFirstTailSplitRowWordGoals`와
`resetPortFinalCarryRealizationGoal_of_zFirstTailSplitRowWordGoals`를 직접 사용한다.
skew-product prefix/read, row-read, table entry도 이 split-data route로 내려가므로
layer-equiv/combined 변환은 호환 adapter로만 남는다. paper table과 paper certificate
entry는 base-level paper-table theorem으로 바로 내려간다.

## 4. H3 완료, H4 generated witness 비활성화 (D7(4)·D7(6))

아카이브의 generated blob root-flat certificates는 둘 다 포팅되어 개별 target으로는
검증 가능하다. 다만 H4 `D7(6)`은 대형 blob certificate 의존을 줄이고 논문 Appendix
A/B의 two-rail 구조를 포팅하기 위해 기본 proof spine에서 제외했다. 즉
`LowD7M6Finite`는 archive/명시 검증 target이지, `Main.assume_lowD7M6`의 discharge로
쓰지 않는다.

```lean
LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily
  : FinalLowD7M4RootFlatCertificateFamily

LowD7M6Finite.finalLowD7M6RootFlatCertificateFamily
  : FinalLowD7M6RootFlatCertificateFamily
```

두 파일 모두 generated schedule의 `rowLatin`, `layerBijective`,
`returnsSingleCycle`를 blob certificate로 검증한다. 최종 torus 연결은
`StandardRootFlatLift.torusEquiv 6 m`와 `rootIndexEquiv :
Fin (m^6) ≃ (Fin 6 → ZMod m)`를 합성해 얻는다.

주의: 논문 v28의 `finite_audit` 소스와 비교하면 이 경로는 논문 표를 구조적으로
재현한 증명이 아니라, 같은 저차원 base에 대한 더 직접적인 finite root-flat
certificate 검증이다. v28의 `scripts/verify_finite_checks.py`는 D5/D7 표의
one-isolate forests, primitive closing columns, support rows, reserve coordinates,
folded terminal words를 재현 검증한다. 반면 현재 Lean 포팅은 실제 root-flat
schedule 전체의 Latin/bijective/single-cycle 조건을 kernel에서 확인한다.

따라서 이 방법이 유일한 것은 아니다. 논문 충실형 대안은 D7 folded rank-three
endpoint proof를 `word-skew product`, `unit-carry`, seven-site separation,
singleton selector, reserve cylinder 정리로 직접 형식화하는 것이다. 다만 현재
`FinalMarkedTarget`은 ordinary torus decomposition의 abbrev이므로, 현재 proof graph의
저차원 base를 닫는 데는 generated root-flat certificate가 충분하다. 반대로 H5/H6는
파라메트릭 high-even growth와 endpoint successor 자체가 남은 promotion이므로, 단순
finite certificate 우회만으로는 맞지 않고 논문식 구조 포팅이 더 자연스럽다.

## 5. H6 (endpoint successor) — §9–10
- 파라메트릭(b→2b+1). 단일순환은 `UnitCarry.productExponentSingleCycle`/
  `squareSubOneProductExponentSingleCycle`(exponent 1 / m²−1)로 거의 준비됨.
- 하드코어: endpoint schedule의 dir(terminal exchange + completion rows) + 4필드 +
  promotion 조립(`finalOddEndpointPhaseProductPromotion_of_*`).

## 6. 요약 — 남은 핵심 1줄
> H3는 generated finite root-flat certificate로 닫혔다. H2와 H4는 generated witness를
> archive/명시 target으로 보존하되 기본 spine에서는 비활성화했다. 남은 것은 H1(D3 even root-flat family),
> H2(D5(4) structural reset-port replacement), H4(D7(6) structural replacement),
> H5(odd high-modulus promotion), H6(endpoint successor promotion)이다.

관련 파일: `LowD5M4Finite.lean`(H2 generated witness, 기본 spine 비활성),
`LowD7M4Finite.lean`(H3 certificate ✅), `LowD7M6Finite.lean`(H4 generated witness,
기본 spine 비활성),
`FiniteArrayCert.lean`(array/blob checker), `StandardRootFlatLift.lean`(D7 lift),
`LowD5M4Seed.lean`(단일순환 ✅), `LowD5M4Schedule.lean`(D5 인프라),
`docs/H2_D5M4_RECIPE_20260603.md`(D5(4) 구성 레시피 + §7 잔여 의무).

검증(2026-06-04):
- `lake build EvenV11.LowD7M4Finite` ✅
- `lake build EvenV11.LowD7M6Finite` ✅ (대형 blob certificate, 약 703초)
- `lake env lean EvenV11/D3EvenM4.lean` ✅
- `lake env lean EvenV11/D3EvenM4RootFlat.lean` ✅
- `lake env lean EvenV11/D3EvenRouteEGeSix.lean` ✅
- `lake env lean EvenV11/D3EvenRouteERootFlatBridge.lean` ✅
- 2026-06-04 갱신: `LowD5M4Finite`와 `LowD7M6Finite`를 기본 proof spine에서 제외.
  이후
  `lake env lean EvenV11/Main.lean` / `lake build EvenV11`의 예상 `sorry`는
  5개(H1/H2/H4/H5/H6; H2 warning은 `assume_lowD5M4RibbonRealizationData`).
- `scripts/check_evenv11_progress.sh`는 `lake build EvenV11`을 확인하고, 보존용
  generated/archive finite 파일의 `native_decide`는 구조 포팅 실패로 보지 않는다.
  대신 structural module에서 새 `native_decide`가 나오거나 H2/H4 generated finite
  target이 기본 import closure로 재유입되면 실패한다.
