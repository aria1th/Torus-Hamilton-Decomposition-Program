# v28 exact paper-facing structure — 2026-06-07

이 문서는 업로드된 v28 TeX 원고의 hard section을 Lean 구조체로 어떻게 대응시켰는지 기록한다.
목표는 열린 증명을 익명 상수로 남기지 않고, 원고가 실제로 요구하는 데이터를 명시적 record 값으로 드러내는 것이다.

## H1: terminal A2

원고의 `terminal_A2_block.tex`는 다음 세 층으로 구성된다.

1. terminal word `omega_m`와 local jump `eta_i`;
2. active endpoints `A_i(r), B_i(r)`와 compressed return `h_i=n_i eta_i`;
3. odd-length selector `c_j`를 이용한 interlacing.

Lean 대응 파일은 `EvenV11/V28Hard/D3TerminalA2Parametric.lean`이고, H2의
`m=4` terminal realization을 이 인터페이스로 연결하는 얇은 bridge는
`EvenV11/V28Hard/D3TerminalA2M4Bridge.lean`이다. 별도로
`EvenV11/V28Hard/D3M4DirectRootFlat.lean`은 closed full-torus
`D3EvenM4.colorDir`를 standard root-flat chart로 접어 얻은 **direct**
`D₃(4)` root-flat cycle-data witness를 제공한다. 이 direct witness는
terminal `F_i` realization이라고 주장하지 않는다.
핵심 구조체는 다음과 같다.

- `TerminalA2EndpointRecurrence m`:
  `A_i(r), B_i(r)`, puncture endpoint `E+_i/E-_i`, generic recurrence, 그리고
  paper endpoint order의 boundary bridge들을 그대로 field로 갖는다.
- `endpointDescSucc`:
  위 recurrence field들이 실제 active endpoint descriptor successor를 준다는 중간
  theorem의 대상이다. raw pointwise rank-step은 이 descriptor successor가
  `endpointRankSucc`와 일치한다는 closed-form table equality로 축소된다.
- `TerminalA2InterlacingSelector m`:
  `L=m-1`, selector point, `F_1` inverse, successor map, successor single-cycle을 갖는다.
- `TerminalA2LowModFiniteBundle`:
  이미 Lean에서 닫힌 `m=4`, `m=6` terminal carrier cyclicity를 한 값으로 묶는다.
- `TerminalA2CarrierCyclicityFamily`:
  모든 짝수 `m≥4`에 대해 collapsed carrier `terminalReturn i`가 `Q_m` 위 단일
  cycle이라는 순수 terminal 명제이다.
- `TerminalA2RootFlatRealizationFamily`:
  root-flat row schedule의 first return이 explicit `sectionEquiv : TerminalQ m ≃ RootState m`를
  통해 `terminalReturn`과 켤레라는 realization 명제이다. 고정 chart `rootPairEquiv`를
  요구하지 않는다.
- `TerminalA2RootFlatRealizationAt m`:
  같은 realization 명제를 단일 modulus에서 쓰는 pointwise record이다. 현재
  `terminalA2M4RealizationAt_of_physical`이 H2/D54의
  `TerminalA2M4PhysicalRealization`을 이 record로 재포장한다.
- `TerminalA2ParametricSolution`:
  terminal cyclicity, `m=4` finite cyclicity, `m≥6` selector, 그리고 standard root-flat RF cycle-data family를 함께 제공한다.

`cycleDataFamily_of_carrierCyclicity_and_realization`은 위 두 핵심 입력
(`TerminalA2CarrierCyclicityFamily`, `TerminalA2RootFlatRealizationFamily`)에서 H1의
`RootFlatCycle.D3EvenCycleDataFamily`를 닫는 adapter이다.
단일 modulus 쪽에서는 `cycleData_of_finiteCyclicity_and_realizationAt`과
`terminalA2M4CycleData_of_physical`이 같은 conjugacy 논리를 `m=4`에 적용한다.
`D3M4DirectRootFlat.cycleData`는 conjugacy-to-`F_i` 없이 `m=4` 존재성만
finite certificate로 확정한 보조 witness이다.
`terminalA2ParametricSolution_of_realization`은 cyclicity/interlacing/realization 세
입력에서 전체 `TerminalA2ParametricSolution`을 조립한다. 전체
`TerminalA2ParametricSolution` 값이 주어지면 `rootFlatCertificateFamily_of_solution`이
기존 final D3 bridge로 닫힌다.

## H2: D5(4) parity reset

D5(4)는 두 경로를 분리한다.

- `EvenV11.D54DirectRF`의 direct finite RF certificate는 이미 bundle 안에서 사용할 수 있다.
- 원고의 paper-facing route는 `V28PaperInterface.D5M4ParityResetInput`의 ribbon/reset data로 남아 있다.

따라서 main assembly는 direct finite route를 paper route로 위장하지 않는다.  paper checklist에는 stronger ribbon field가 그대로 남는다.

## H3/H4: D7(4), D7(6) two-rail relay

원고의 finite-audit Python script는 D7 row table, coforest closure, primitive signs,
reserve separation, folded terminal words를 검사한다.  Lean 대응 파일은
`EvenV11/V28Hard/D7TwoRailRelay.lean`이다.

- `RelayFiniteAuditEvidence`:
  stage rows, skeletons, closure data, primitive signs, support containment,
  reserve separation, folded terminal word, terminal alignment을 record화한다.
- `TwoRailRelayRealization m`:
  실제 RF1/RF2/RF3 schedule `dir`를 요구한다.
- `TwoRailRelaySolutions`:
  finite audit evidence와 `m=4`, `m=6` realization을 함께 묶는다.

`cycleData_of_realization` 이후의 final low-base bridge는 닫혀 있다.

## H5: odd high-even branch

원고의 high-even proof는 coforest-splice anchor와 four-point growth row를 사용한다.
Lean 대응 파일은 `EvenV11/V28Hard/HighEvenEndpointPromotions.lean`이다.

- `HighEvenFourPointGrowthRow D`:
  `(s a)(b c)` row, leaf `s`, quotient line/plane, inactive flag, unit carry를 기록한다.
- `OddHighModulusEngine`:
  finite anchor audit, projection kernel, guide locality, return/word/range inputs를 받아 marked target을 만든다.

## H6: endpoint successor

원고의 endpoint successor는 terminal exchange rows와 completion rows를 phase product로 결합한다.
Lean 대응은 다음 구조체로 분리했다.

- `EndpointSuccessorPhaseProductDatum b m`:
  terminal colors, completion rows, exponent sum unit, marked-payload transfer를 갖는다.
- `OddEndpointPayloadEngine`:
  parent marked payload와 certificate inputs에서 child marked payload를 만든다.

## Final assembly

`EvenV11/V28Hard/PaperExactStructure.lean`의 `ConstructiveV28Solution`은 위 섹션 데이터를 다음과 같이 묶는다.

```lean
structure ConstructiveV28Solution where
  sectionData : ManuscriptHardSectionData
  terminalA2 : D3TerminalA2Parametric.TerminalA2ParametricSolution
  d5m4Reset : V28PaperInterface.D5M4ParityResetInput
  d7TwoRail : D7TwoRailRelay.TwoRailRelaySolutions
  promotions : HighEvenEndpointPromotions.HardPromotionEngines
```

이 값 하나가 주어지면 `EvenV11.Main.evenModulusToriAllDimensions`는 기존 final induction spine을 통해 결론을 낸다.
