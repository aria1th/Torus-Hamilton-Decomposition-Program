# 형식화 번들 지도 — 무엇을 묶어 한 번에 증명할까

작성일: 2026-06-03. 전제: P3-core(`oneStepPacketSplice`) 형식화 완료(sorry-free,
`#print axioms` = propext/Classical/Quot). 6개 구멍(H1–H6, 가정 원장 참조)을 닫기
위해, **한 번 증명해 모든 구멍이 얇은 인스턴스화가 되도록** 재사용 번들을 설계.

## 0. 원칙
각 구멍 = `FinalRootFlatTorusModel d m`의 4필드:
`rowLatin` · `layerBijective` · `returnsSingleCycle` · `stepConjugacy`.
이 중 `returnsSingleCycle`만이 어렵고, 그것은 (단일순환 merge) + (unit-carry lift)
로 분해된다. 따라서 **공통 경로를 번들로 뽑고, 구멍별로는 데이터만 끼운다.**

## 1. 번들 지도 (재사용 단위)

### Bundle A — 추상 cut-splice 계산 (`Shared/SwitchCalculus.lean`)
| | 정리 | 상태 |
|---|---|---|
| A1 | `oneStepPacketSplice` (q개 coset-cycle → 1 cycle) | ✅ **완료** |
| A2 | `flagSplicingCriterion` (P6 step): 한 flag layer에서 모든 target cell에 A1을 병렬 적용 | ✅ **완료** |
| A3 | `IsCycleOn (Set.univ) ↔ IsSingleCycleMap` 다리 (mathlib ↔ repo 술어) | ✅ **완료** |
| A4 | `oneStepPacketSplice_singleCycleMap` (A1+A3, 전체 cover일 때 repo 술어로 바로 반환) | ✅ **완료** |
| A5 | `flagSplicingCriterion_singleCycleMap` (A2+A3, final target cell이 전체일 때 repo 술어로 반환) | ✅ **완료** |
| A6 | `OneStepPacketSpliceCertificate`/`FlagSplicingCertificate` (구체 표 instantiation용 가정 bundle) | ✅ **완료** |
구성-무관. 실제 flag chain은 `flagSplicingCriterion`를 단계별로 반복 적용한다.

### Bundle B — unit-carry lift (`EvenV11/UnitCarry.lean`) — **완료된 공통핵**
- `rankUnitCarrySingleCycle` (P1 핵심: base 단일순환 + `IsUnit(∑carry)` → skew 단일순환). ✅
- `Shared.skewProduct_zmod_additive_rank_single_cycle_iff_unit_sum` 및
  `rankUnitCarrySingleCycle_iff` (rank-coordinate P1 iff). ✅
- `Shared.zmod_add_single_cycle_iff_unit`,
  `sectionReturn_skewProductMap_zmod_add_single_cycle_iff_unit`
  (fiber/section-return converse 핵심). ✅
- `pointCarry*`, `singlePointCarry*` (한 점 carry → 단일순환). ✅
- `productExponentSingleCycle`, `squareSubOneProductExponentSingleCycle`
  (endpoint exponent 1 / m²−1 carry). ✅ ← **H6 endpoint용이 이미 준비됨**
- `squareSubOneUnitZModPow` 등 unit 산술. ✅
→ 신규 거의 불필요. 필요시 "fiber별 단일순환 + 몫 cycle 결합" wrapper만.

### Bundle C — anchor 데이터 → A의 가정 (`EvenV11/TypeA`, `FiniteAudit`)
| | 내용 | 상태 |
|---|---|---|
| C1a | 행렬식 ±1 (`closed-one-isolate-tree`) bool 의미: `primitiveDetBool → det=±1 → ZMod unit` | ✅ **완료** (`forestClosingDatumBool_detInt_zmod_unit`; D5/D7 list membership wrapper 포함) |
| C1b | type-A 트리+closing edge가 Z-basis임을 실제 row/carry에 연결 | ⏳ **bool/incidence/readout/shape facts 완료** (`ForestClosingDatumFacts`, `ClosingMatrixPayload`, `SupportRowDatumFacts`, `EdgeUndirectedEquivalent`, `edgeVectorCoeff`, `reducedBasisVertex`, `reducedBasisVertices_length_of_lt`, `reducedBasisVertex_*_of_row_lt`, `vectorEdge_getD_*`, `columnsToRows_get2D_*`, `closingMatrix_*_column_*`, `closingMatrix_length`, `closingMatrixFin`, `ForestClosingDatumFacts.closingMatrix*`, D5/D7 closing-matrix/Fin/payload wrappers, `*_vectorEdge_eq_or_neg`); 실제 row/carry 선형대수 연결 TODO |
| C2a | `rooted-coforest-completions`: D5/D7 rooted/incidence audit surface | ✅ **완료** (`v28FiniteInputCoforestAudit_holds`) |
| C2b | TypeA boundary audit → child/parent Set-cell transversal 해석 glue | ✅ **완료** (`descendantCell`, `coforestRootedBoundaryAudit_*_mem_cell_iff`) |
| C2c | TypeA row data → A1/A2 packet `C/a/h/R/R'` 가정 instantiation | ⏳ **packet-cell bridge audit 완료** (`CellTransversal`, `CoforestRowCellBridge`, D5/D7 `*RowsCellBridgeAudit_holds`, `*_crosses_cell_iff`); 실제 `R/R'` 표 instantiation TODO |

### Bundle D — 나머지 세 필드
| | 내용 | 상태 |
|---|---|---|
| D1 | `rowLatin` (각 색=서로 다른 generator, 구조적) | per-schedule, 경량 |
| D2 | `layerBijective` ← P2 `partialExchange*_bijective` | ✅ **generic bundler 완료** (`RootFlatSchedule.layerBijective_of_layerMap_apply_eq`, `rootFlatLayerBijective_of_partialExchangeChoice_eq`); per-schedule equality proof는 case별 |
| D3 | `stepConjugacy` (torusEquiv 좌표 계산) | per-case |
| D4 | 네 필드 → `FinalRootFlatTorusModel`/`FinalRootFlatTorusCertificate` 조립 | ✅ **완료** (`finalRootFlatTorusCertificate_of_fields`, low-base `*_RootFlatCertificateFamily_of_certificate`) |

### ★ Bundle M — 마스터 조립 정리 (A2+A3+B+C1 묶음) — **generic wrapper 완료**
> **MasterReturnSingleCycle**: 색 `c`의 return이 (i) 최종 forest-quotient의 각
> coset에서 단일순환(A2)이고 (ii) 총 carry가 unit(±1; C1+B)이면,
> `IsSingleCycleMap (returnMap c)` (전체 root flat에서 단일순환).
한 번 증명 → H3·H4·H5 anchor의 `returnsSingleCycle`가 전부 이 정리의 인스턴스.

Lean 상태(2026-06-03):
- `Shared.MasterReturn.oneStepPacketSplice_unitCarrySingleCycle` 완료.
- `Shared.MasterReturn.flagSplicingCriterion_unitCarrySingleCycle` 완료.
- certificate 입력형 wrapper
  `OneStepPacketSpliceCertificate.unitCarrySingleCycle`,
  `FlagSplicingCertificate.unitCarrySingleCycle` 완료.
- 남은 작업은 구체 row 데이터가 이 wrapper의 packet/carry 가정을 만족함을 보이는
  C1/C2 instantiation. C2의 coforest-row cell bridge/transversal 부분은
  `EvenV11.TypeA.PacketBridge`에서 D5/D7 전체 row audit로 닫혔고, 남은 C2c는 구체 return permutation
  `R/R'`와 packet coset `C/a/h` 표를 연결하는 단계다.

## 2. 구멍 ↔ 번들 의존표
| 구멍 | returnsSingleCycle 경로 | 추가 |
|---|---|---|
| H1 D3-even | terminal-A2 orbit(작음) + B | D1/D2/D3; root-flat family 경로 외에 `FinalD3EvenBasePromotion` 직접 경로 준비 |
| H2 D5(4) | `LowD5M4.fullReturn_singleCycle`(B) + ribbon/run-collapse wild reindexing, 또는 RF3 직접 cycle data | D; tame `returnMap = paperReturn` 경로는 2026-06-05 blocker로 폐기 |
| H3 D7(4) | **A2 flag + M + C2** | D |
| H4 D7(6) | **A2 flag + M + C2** (큰 표) | D |
| H5 high-mod | **A2 flag + M + growth(B)** parametric | D |
| H6 endpoint | A1 cut-splice + **B(productExponent✅)** | D |

공통 재사용: **A2, A3, M, D2-bundler.** 이 넷이 6개 구멍의 90%를 덮는다.

## 3. 임계 경로 (권장 순서)
1. **A3** `IsCycleOn univ → IsSingleCycleMap` 다리. ✅
2. **P1 iff** rank-coordinate unit-carry criterion. ✅
3. **A2** `flagSplicingCriterion` (A1 위 병렬 flag-layer step). ✅
4. **M** generic wrapper (A2+A3+B 결합 → unit-carry skew return). ✅
5. **D2-bundler** (P2 → `layerBijective`) ✅ + D1/D3 패턴 정립.
6. **Promotion bridge cleanup** — closed/target promotion을 Main의 세분화된
   certificate-promotion 타입으로 올리는 wrapper. ✅
   (`finalOddHighModulusTargetPromotion_of_closedPromotion`,
   `finalOddEndpointPhaseProductPromotion_of_targetPromotion`,
   `finalOddEndpointPhaseProductPromotion_of_closedPromotion`)
7. **파일럿 1개 end-to-end** — 가장 단순한 구멍으로 schedule→model→Cayley→
   `assume_*` 교체까지 전 파이프라인 검증. 후보: **H6 endpoint**(B가 이미 풍부)
   또는 **H1 D3-even**(작은 terminal orbit). 유한 전(全)구체가 좋으면 **H2 D5(4)**.
8. 파일럿으로 틀이 서면 **H3 D7(4) → H4 D7(6) → H5 → 나머지** 크랭크.

## 4. 다음 작업
- 즉시: 실제 D7/H5 데이터용 C1/C2 instantiation을 `Shared.MasterReturn` wrapper에
  연결한다.
- 필요시: 구체 flag chain wrapper를 `flagSplicingCriterion` 반복 적용으로 추가.
- 병행: 파일럿 구멍 선정(H6/H1/H2 중) → D 패턴 + 첫 `assume_*` 교체로 OPEN HOLES 6→5.
