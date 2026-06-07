# v28 H2 skeleton and D7 checkpoint isolation — 2026-06-07

## 2026-06-07 active-surface cleanup

이 문서는 `even_v28_h2_skeleton_checkpoint_patch_20260607.patch`의 역사적 기록을
보존한다. 현재 active Lean surface에서는 아래 archive-dependent staging modules를
직접 build target으로 쓰지 않는다.

- `archive/EvenV11/V28Hard/D5M4RibbonRows.lean`
- `archive/EvenV11/V28Hard/D5M4H2Skeleton.lean`
- `archive/EvenV11/V28Hard/D5M4H2PaperRows.lean`
- `archive/EvenV11/V28Hard/D7FiniteToCycleData.lean`
- `archive/EvenV11/V28Hard/D7Checkpoint.lean`

현재 H2 본선 target은 `EvenV11/LowD5M4RibbonInterface.lean`의
`PhysicalRowsSingletonSwitchMapConjInput`이다. 또한
`EvenV11/LowD5M4TameObstruction.lean`이 tame `seedRootEquiv` direct paperReturn
route를 Lean에서 반례로 차단하므로, `PaperRowsDirectPath...`/`seedRootEquiv`
형태의 shortcut은 본선 target이 아니다.

## 목적

이번 패치는 Lean/Lake 빌드 없이도 다음 작업 단위를 코드 레벨에서 분리하기 위해 작성되었다.

1. `D₇(4)`, `D₇(6)` generated finite audit는 checkpoint theorem 전용으로 격리한다.
2. H2 `D₅(4)` reset은 기존 `ResetPortH2PaperTableData` 본선 고정 대신 세 트랙으로 나눈다.
3. 최종 theorem wiring을 확인할 수 있도록 H2-root-flat checklist variant를 둔다.

기본 `EvenV11.lean`은 건드리지 않는다. `EvenV11.Main`의 H2 open slot은
2026-06-07 추가 Lean 반례 이후 broad ribbon-collapse input으로 되돌렸다.
실험/negative checkpoint는 `EvenV11.V28Hard` umbrella 아래 opt-in이다.

## 새 모듈

### `EvenV11/V28Hard/D5M4H2PaperRows.lean`

2026-06-07 row-read audit 결과, 기존 `ResetPortFullPaperRowWordReadGoals`
route는 다음 target으로 쓰면 안 된다. 특히 pre-final P0 쪽에서
`p0F0Tail`의 `y=0` terminal-factor read와 `p0YShiftLast`의 `y=1` pure-`Y`
read가 같은 layer-3/root/color source를 동시에 요구할 수 있다. Lean에는 이
불가능성이

```lean
not_preFinalP0P1RowWordReadGoals
H2TableRouteSkeleton_false
```

로 기록되어 있다. 따라서 다음 H2 route는 full prefix/read table이 아니라
`H2SkewProductPathRouteSkeleton` 또는 `H2RibbonCollapseInput`이어야 한다.

### `EvenV11/V28Hard/D7Checkpoint.lean`

`D7FiniteToCycleData`를 직접 theorem spine에서 부르지 않고 다음 wrapper 뒤로 숨긴다.

```lean
structure FiniteBackedD7Checkpoint where
  d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4)
  d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6)
  checkpointOnly : True
```

사용 theorem 이름은 반드시 `checkpoint` 또는 `finiteBackedD7`를 포함해야 한다. 본선 paper-faithful D7 theorem에는 이 파일을 쓰지 않는다.

### `EvenV11/V28Hard/D5M4H2Skeleton.lean`

H2를 세 구간으로 나눈다.

#### 1. row-read transcription

```lean
structure PaperLayeredBaseRows where
  layer0 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer1 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer2 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer3 : RootState → TorusColor 5 ≃ TorusDirection 5
```

`layer3` row-word read 목표는 다음으로 묶여 있지만, 2026-06-07 audit 이후
이 package는 본선 목표가 아니라 legacy/negative checkpoint다.

```lean
structure PaperRowReadPieces (baseRow : BaseRow) where
  preFinalTerminal : ResetPortPreFinalTerminalReadGoals baseRow
  preFinalP0P1 : ResetPortPreFinalP0P1RowWordReadGoals baseRow
  finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordReadGoals baseRow
```

이를 통해 곧바로 다음으로 조립되지만

```lean
ResetPortFullPaperRowWordReadGoals baseRow
```

`not_preFinalP0P1RowWordReadGoals` 때문에 현재 predicate 폭에서는 불가능하다.
terminal/P0Y 단일 read leaf는 유용한 sanity check로 남기고, 전체 H2 본선은
직접 ribbon-collapse/root-flat route로 진행한다.

#### 2. RF2

두 형식을 모두 유지한다.

```lean
abbrev PaperRF2SkewProductInput (baseRow : BaseRow) :=
  ResetPortLayerSkewProductData baseRow

abbrev PaperRF2LayerEquivInput (baseRow : BaseRow) :=
  ResetPortLayerEquivData baseRow
```

skew-product가 막히면 먼저 layer-equivalence로 RF2를 닫고, 나중에 normal form으로 승격한다.

#### 3. RF3 / ribbon-collapse

기존 prefix-table route는 checkpoint로 보존한다.

```lean
structure H2TableRouteSkeleton where
  baseRow : BaseRow
  rf2 : PaperRF2SkewProductInput baseRow
  prefix : ResetPortFullPaperPrefixGoals baseRow
  read : ResetPortFullPaperRowWordReadGoals baseRow
```

본선 후보는 직접 RF-cycle route다.

```lean
structure H2RootFlatRouteSkeleton where
  baseRow : BaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  returnsSingleCycle : (ResetSchedule baseRow).returnsSingleCycle
```

현재 `Main.lean` H2 slot에 꽂는 강한 형태도 별도로 둔다.

```lean
structure H2RibbonCollapseInput where
  baseRow : BaseRow
  e : Seed ≃ RootState
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  returnRealization : ∀ c x,
    e.symm ((ResetSchedule baseRow).returnMap c (e x)) =
      LowD5M4.fullReturn c x
```

`H2RibbonCollapseInput`은 다음으로 내려간다.

```lean
ResetPortH2RowEquivRibbonRealizationData
```

`H2RibbonCollapseInput`/`ResetPortBaseRowRibbonRealizationData`는
layer-blind reset-port transformer compatibility route로 남아 있지만, 현재
`Main.lean`의 lower H2 open slot은 직접
`ResetPortH2RowEquivRibbonRealizationData`를 받는다.

`PaperLayeredBaseRows`에서 직접 Main H2 slot으로 가는 target도 추가했다.

```lean
def d54PaperProductRows : PaperLayeredBaseRows

structure PaperRowsLayerEquivRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperBaseRowLayerEquivRF2Goal rows
  e : Seed ≃ RootState
  returnRealization : PaperBaseRowReturnRealizationGoal rows e

structure PaperRowsSkewProductRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperBaseRowSkewProductRF2Goal rows
  e : Seed ≃ RootState
  returnRealization : PaperBaseRowReturnRealizationGoal rows e

theorem PaperRowsSkewProductRibbonCollapseInput.nonemptyMainH2Input

structure PaperRowsDirectRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  e : Seed ≃ RootState
  layerBijective : PaperPhysicalRowsLayerBijectiveGoal rows
  returnRealization : PaperPhysicalRowsReturnRealizationGoal rows e

theorem PaperRowsDirectRibbonCollapseInput.nonemptyRibbonData
theorem PaperRowsDirectRibbonCollapseInput.lowBaseFamily

abbrev PaperPhysicalRowsPathRealizationGoal
  (rows : PaperLayeredBaseRows)

structure PaperRowsDirectPathRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  layerBijective : PaperPhysicalRowsLayerBijectiveGoal rows
  pathRealization : PaperPhysicalRowsPathRealizationGoal rows

theorem PaperRowsDirectPathRibbonCollapseInput.nonemptyRibbonData
theorem PaperRowsDirectPathRibbonCollapseInput.lowBaseFamily

structure PaperPhysicalSingletonSwitchLayerData
  (rows : PaperLayeredBaseRows)

structure PaperRowsSingletonDirectRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperPhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  returnRealization : PaperPhysicalRowsReturnRealizationGoal rows e

theorem PaperRowsSingletonDirectRibbonCollapseInput.nonemptyRibbonData
theorem PaperRowsSingletonDirectRibbonCollapseInput.lowBaseFamily

structure PaperRowsSingletonDirectPathRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperPhysicalSingletonSwitchLayerData rows
  pathRealization : PaperPhysicalRowsPathRealizationGoal rows

theorem PaperRowsSingletonDirectPathRibbonCollapseInput.nonemptyRibbonData
theorem PaperRowsSingletonDirectPathRibbonCollapseInput.lowBaseFamily

structure D54PaperProductLayerEquivRibbonCollapseInput where
  rf2 : PaperBaseRowLayerEquivRF2Goal d54PaperProductRows
  e : Seed ≃ RootState
  returnRealization : PaperBaseRowReturnRealizationGoal d54PaperProductRows e

theorem D54PaperProductLayerEquivRibbonCollapseInput.nonemptyMainH2Input

structure D54PaperProductSingletonSwitchRibbonCollapseInput where
  rf2 : ResetPortSingletonSwitchLayerData d54PaperProductRows.baseRow
  e : Seed ≃ RootState
  returnRealization : PaperBaseRowReturnRealizationGoal d54PaperProductRows e

def D54PaperProductSingletonSwitchRibbonCollapseInput.toResetPortBaseRowData
theorem D54PaperProductSingletonSwitchRibbonCollapseInput.nonemptyMainH2Input
theorem not_d54PaperProductRows_layerBijective
theorem not_nonempty_D54PaperProductSingletonSwitchRibbonCollapseInput
```

2026-06-07 추가 검산: `d54PaperProductRows`처럼 네 layer를 모두
`terminalStdBaseRowAtState`로 둔 naive product-row candidate는 RF2가 아니다.
Lean에서 layer `0`, color `0`의 explicit collision을 증명했다.

```lean
theorem not_d54PaperProductRows_layerBijective :
  ¬ ResetPortLayerBijectiveGoal d54PaperProductRows.baseRow
```

따라서 다음 H2 construction은 product-row wrapper가 아니라 일반
`PaperRowsLayerEquivRibbonCollapseInput`/`PaperRowsSkewProductRibbonCollapseInput`
target으로 돌아가야 한다. 먼저 논문 §11 row table의 네 displayed layer rows를
`PaperLayeredBaseRows`에 다시 전사하고, 그 row table에 대해 “RF2 + e +
returnRealization” 세 조각을 닫으면 `Main.lean`의
`assume_lowD5M4RibbonCollapseInput`을 교체할 수 있다. RF2 leaf는 reset-port
compatibility 타입이 아니라 직접 physical schedule 위의
`PaperPhysicalSingletonSwitchLayerData rows` 형태가 가장 작다. 이 타입은
각 layer/color map을 singleton partial exchange로 식별하면 곧바로
`PaperPhysicalRowsLayerBijectiveGoal rows`를 준다.

RF3는 `PaperPhysicalRowsPathRealizationGoal rows`로 먼저 닫는 것이 가장 작다.
이 목표는 direct physical row schedule의 네 layer가 각 color에서
`paperReturn`을 실현한다는 `FourLayerPathGoal` 묶음이며, 닫히면
`seedRootEquiv` conjugacy를 통해
`PaperPhysicalRowsReturnRealizationGoal rows seedRootEquiv`가 자동으로 나온다.
따라서 현재 가장 구체적인 H2 handoff는
`PaperRowsSingletonDirectPathRibbonCollapseInput`이다.

추가로, `LowD5M4Realization`의 decomposed core-tail package는 adapter와 함께
남겨 두었지만, 2026-06-07 Lean check 결과 본선 target으로 쓰면 안 된다.

```lean
structure H2SkewProductCoreYFirstZFirstRouteSkeleton where
  baseRow : BaseRow
  rf2 : PaperRF2SkewProductInput baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

theorem H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData
theorem H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData_ofPaperData
theorem not_terminalCoreTailPrefixPathGoal
theorem not_nonempty_resetPortH2PaperSkewProductCoreYFirstZFirstTailData
```

핵심 반례는 `TerminalCoreTailPrefixPathGoal`가 세 번의 literal D5 root step으로
`terminalReturnTailBase 0 q`에 도달하라고 요구한다는 점이다. 구체 정상 source
`(q,y,z)=((0,2),0,0)`에서 어떤 세 방향도 이 displacement를 만들 수 없음이
Lean으로 닫혔다. 따라서 `ResetPortH2PaperSkewProductCoreYFirstZFirstTailData`는
현재 정의상 nonempty일 수 없고, paper route는 collapsed tail을 literal prefix
path로 강제하지 않는 `PaperRowsDirectRibbonCollapseInput` 또는 직접
`ResetPortH2RowEquivRibbonRealizationData` 쪽으로 가야 한다.

### `EvenV11/V28Hard/ChecklistH2RootFlat.lean`

기존 `V28PaperInterface.PaperFaithfulChecklist`는 H2를 `ResetPortH2RowEquivRibbonRealizationData`로 받는다. 이번 파일은 H2를 더 relaxed한 root-flat cycle input으로 받는 alternate checklist다.

```lean
structure PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 : D3TerminalA2Input
  d5m4Reset : D5M4RootFlatResetInput
  d7m4TwoRail : D7M4TwoRailInput
  d7m6TwoRail : D7M6TwoRailInput
  oddHighModulus : OddHighModulusInput
  oddEndpoint : OddEndpointInput
```

핵심 theorem:

```lean
theorem evenModulusToriAllDimensions_of_h2RootFlatChecklist
```

실용 checkpoint:

```lean
theorem evenModulusToriAllDimensions_checkpoint_H2RootFlat_finiteBackedD7

theorem evenModulusToriAllDimensions_checkpoint_H2RibbonCollapse_finiteBackedD7
```

## 권장 다음 작업 순서

1. `Main.lean`의 H2 open slot은
   `LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`로 유지한다.
2. 구체적 closure target은
   `LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput`이다.
3. 논문 §11의 실제 four-layer physical row table을 `PhysicalLayerRows` 값으로
   전사한다.
4. RF2는 `PhysicalSingletonSwitchLayerData rows`로 닫는다.
5. RF3는 tame `seedRootEquiv`/`paperReturn` path가 아니라 paper의
   ribbon-collapse/run-collapse가 주는 wild `e`에 대해
   `PhysicalRowsReturnMapConjGoal rows e`를 직접 닫는다.

## 주의

2026-06-07 cleanup 이후 active 관련 target은 다음으로 확인한다.
`lake build EvenV11.Main EvenV11.LowD5M4RibbonInterface EvenV11.LowD5M4TameObstruction EvenV11.V28Hard`
가 통과해야 한다. H2를 더 이상 하나의 거대한 `ResetPortH2PaperTableData`
obligation이나 impossible tame path obligation으로 보지 않고, physical rows, RF2,
wild-e RF3/ribbon-collapse로 분리한다.
