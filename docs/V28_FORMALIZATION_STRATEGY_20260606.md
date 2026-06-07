# v28 형식화 전략, 보조정리, 증명 틀

## 0. 핵심 원칙

최종 목표를 직접 증명하지 말고 다음 세 층으로 고정한다.

1. **RF layer**: concrete row schedule에서 RF1/RF2/RF3를 증명한다.
2. **engine layer**: RF3는 cut-splice/flag-splice/unit-carry 같은 일반 정리에 넣어 얻는다.
3. **final induction layer**: 이미 닫힌 range bookkeeping과 simultaneous induction에 certificate promotions만 공급한다.

현재 Lean에서 2, 3층의 대부분은 이미 닫혀 있다. 남은 일은 “논문 표와 row construction이 1층과 engine hypotheses를 만족한다”는 구체 instantiation이다.

## 1. H1 — D3 terminal `A₂` base

### 목표

```lean
FinalD3EvenRootFlatCertificateFamily
```

### 버릴 것

`D3EvenRouteEGeSix`의 m=6/8/10/12 case split과 tail rank package를 최종 경로로 쓰지 않는다. 논문은 terminal `A₂` block의 parametric theorem을 사용한다.

### 새 Lean 틀

권장 파일:

```text
EvenV11/D3TerminalA2RootFlat.lean
```

핵심 구조:

```lean
structure TerminalA2RootFlatData (m : Nat) [NeZero m] where
  dir : ZMod m → (ZMod m × ZMod m) → TorusColor 3 → TorusDirection 3
  rowLatin : (schedule dir).rowLatin
  layerBijective : (schedule dir).layerBijective
  returnsSingleCycle : (schedule dir).returnsSingleCycle
```

### 필요한 보조정리와 증명

#### Lemma H1.1 — terminal row Latin

명제: terminal `A₂` word의 각 layer/source에서 세 color가 세 generator를 정확히 한 번씩 쓴다.

증명: `TerminalA2LowMod.terminalRowEquiv`가 이미 `Fin 3 ≃ Fin 3` 형태다. `rowLatin`은 각 행의 함수가 equivalence라는 사실에서 바로 나온다.

Lean 모양:

```lean
theorem terminalA2_rowLatin {m : Nat} [NeZero m] :
    (terminalA2Schedule m).rowLatin := by
  intro t w
  exact (terminalA2RowEquiv t w).bijective
```

#### Lemma H1.2 — terminal layer bijective

명제: 각 color/layer map은 root-flat section의 permutation이다.

증명: 논문 Lemma `terminal-latin` 및 `six-turn boundary closure`의 계산을 `ZMod m × ZMod m` affine map으로 전사한다. 각 piece는 translation 또는 coordinate shear이므로 equivalence. piecewise 정의의 경계가 `terminalOmega`의 disjoint cases로 나뉘므로 `by_cases`/`fin_cases` 대신 `simp [terminalOmega]`와 extensional equality lemma를 먼저 만든다.

#### Lemma H1.3 — terminal return cyclicity

명제: terminal `A₂` schedule의 세 first return이 single cycle이다.

증명 틀:

1. 각 return을 rank `ρ_i : TerminalQ m ≃ ZMod (m^2)` 또는 skew rank로 conjugate한다.
2. rank가 매 step `+1` 또는 `-1` 이동함을 보인다.
3. `Shared.single_cycle_of_zmod_rank_equiv` 또는 `EvenV11.UnitCarry.rankUnitCarrySingleCycle`을 적용한다.

m=4의 예외적 finite check는 보조 sanity check로만 사용하고, 최종 lemma는 `∀ even m ≥ 4`여야 한다.

## 2. H2 — D5(4) parity reset

### 목표

```lean
Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData
```

### 이미 닫힌 축소

`LowD5M4Structural`이 좋은 방향으로 이미 정리돼 있다.

- row equivalence가 있으면 RF1은 자동.
- RF2와 return realization만 공급하면 된다.
- cyclicity는 `LowD5M4.fullReturn_singleCycle`과 conjugacy로 나온다.

핵심 닫힌 정리:

```lean
LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData
```

### 필요한 보조정리와 증명

#### Lemma H2.1 — row-equivalence construction

명제: 논문 Table `D54-reset-ports`의 five substitutions를 terminal `A₂` × Y-row × Z-row에 적용하면 각 row는 `TorusColor 5 ≃ TorusDirection 5`다.

증명: 각 source에서 base row가 equivalence이고, substitutions는 disjoint two-entry swaps이다. disjoint transpositions의 composition은 equivalence. Lean에서는 방향 table 자체를 equivalence로 정의하면 RF1은 `rowLatin_of_rowEquiv`로 끝난다.

#### Lemma H2.2 — RF2 layer bijectivity via ribbon switches

명제: reset rows의 각 layer map은 bijective.

증명:

1. base terminal/product layer maps are bijective.
2. 각 substitution은 comparison set 위의 partial exchange다.
3. support separation으로 substitutions commute.
4. `Shared.RootFlatSchedule.layerBijective_of_layerMap_bijective` 또는 기존 `partialExchange` lemma를 적용한다.

#### Lemma H2.3 — run-collapse realization

명제:

```lean
e.symm ((LowD5M4Schedule.schedule dir).returnMap c (e x)) =
  LowD5M4.fullReturn c x
```

증명:

- `e : ((Q4 × Y) × Z) ≃ (Fin 4 → ZMod 4)`는 논문 ribbon-realization이 주는 section reindexing이다.
- 각 ribbon switch가 return-section에서 `LowD5M4.fullReturn`의 해당 generator/symbol step과 같은 cut-splice arrow를 만든다는 것을 시간 순서대로 보인다.
- disjointness로 ordered product와 실제 layer composition이 일치한다.

## 3. H3/H4 — D7(4), D7(6) two-rail bases

### 목표

```lean
RootFlatCycle.RootFlatCycleData 6 4
RootFlatCycle.RootFlatCycleData 6 6
```

### 이번 패치의 변경

`D₇(4)`는 더 이상 `LowD7M4Finite`에서 Main으로 직접 들어가지 않는다. 이번 패치에서 `Main.lean`의 H3를 `RootFlatCycleData 6 4` slot으로 되돌렸으므로, `m=4`와 `m=6`이 같은 proof schema를 공유한다.

### 필요한 보조정리와 증명

#### Lemma H3.1/H4.1 — two-rail row Latin

표의 각 row를 `TorusColor 7 ≃ TorusDirection 7`로 정의한다. rowLatin은 equivalence bijective.

#### Lemma H3.2/H4.2 — layer bijective

folded rank-three chart의 seven port가 서로 다른 terminal fiber/neutral prefix에 있다는 separation lemma를 사용한다. Lean 쪽에는 다음 자료가 이미 있다.

- `FoldedSiteTrace`
- `FoldedReserveSeparation`
- `FoldedCommonEdgeWitness`
- `EndpointMarkedTransferBridge`

부족한 것은 “이 표가 실제 `RootFlatCycle.schedule dir`의 layerMap과 같다”는 row-to-schedule equality lemma다.

#### Lemma H3.3/H4.3 — reused plus-lane cyclicity

논문은 reused plus lane branch가

```text
m=4: W4 = F1 F0^2
m=6: W6 = F1^2 F0^3
```

를 읽고, 둘이 full cycle임을 finite word check로 보인다. Lean에는 terminal word/trace single-cycle이 이미 존재한다. 남은 일은 folded row return이 해당 wordEval과 conjugate라는 lemma다.

```lean
theorem d7m4_folded_return_conj_wordEval : ...
theorem d7m6_folded_return_conj_wordEval : ...
```

## 4. H5 — odd high-even branch

### 목표

```lean
FinalOddHighModulusTargetPromotion
```

### 이미 닫힌 엔진

- finite bool audit: `FiniteAudit`, `FiniteAuditBridge`
- rooted coforest boundary: `TypeA.AnchorBridge`
- cell/transversal bridge: `TypeA.PacketBridge`
- flag splicing: `Shared.SwitchCalculus.flagSplicingCriterion`
- master return wrapper: `Shared.SwitchCalculus.FlagSplicingCertificate.unitCarrySingleCycle`
- projection/growth locality: `ProjectionKernel`, `GuideLocality`, `HighEvenSuccessorBridge`

### 아직 필요한 핵심 lemma

#### Lemma H5.1 — packet bridge → `FlagSplicingCertificate`

명제: finite coforest row data와 tail-head row identity tables가 `Shared.SwitchCalculus.FlagSplicingCertificate`의 fields를 만족한다.

증명 구조:

1. `TypeA.PacketBridge.CoforestRowCellBridge`에서 각 edge가 descendant cell을 정확히 한 번 cross함을 얻는다.
2. 논문 tail-head identity `h_j = a_j + δ_old`, `h_{j+1}=a_j + δ_new`를 Lean table로 넣는다.
3. `head`, `splice`, `rest`, `cosetDisjoint`, `packetDisjoint`, `cell` fields를 각각 채운다.
4. `cycles`는 이전 quotient cycle/induction hypothesis에서 온다.

권장 theorem 이름:

```lean
theorem d5FiniteAnchor_flagSplicingCertificate : ...
theorem d7FiniteAnchor_flagSplicingCertificate : ...
```

#### Lemma H5.2 — closing determinant → unit carry

명제: closed one-isolate tree의 closing column determinant가 ±1이면 total carry가 `ZMod m` unit이다.

이미 가까운 Lean 정리:

```lean
forestClosingDatumBool_detInt_zmod_unit
ForestClosingDatumFacts.detInt_zmod_unit
```

부족한 연결은 “이 determinant column이 실제 return carry sum과 같다”는 row/carry readout lemma다.

#### Lemma H5.3 — finite anchor criterion

명제: D5/D7 printed relays satisfy finite coforest-splice anchor datum and hence produce marked high-even anchors.

증명: H5.1 + H5.2 + `Shared.MasterReturn` + reserve-plane audit.

#### Lemma H5.4 — high-even growth promotion

명제: anchors plus chained/paired growth supply all odd `d`, even `m`, `m>d`.

증명: existing `HighEvenSuccessorBridge`의 projection kernel/locality facts를 실제 growth row construction에 instantiate한다.

## 5. H6 — endpoint successor

### 목표

```lean
FinalOddEndpointPhaseProductTargetPromotion
```

### 이미 닫힌 엔진

- `productExponentSingleCycle`
- `squareSubOneProductExponentSingleCycle`
- `EndpointCompletion.*singleCycle`
- `PhaseProductSupport`의 support/reserve/protected commutation lemmas
- `FinalOddEndpointPhaseProductMarkedPayloadPromotion` adapter

### 필요한 보조정리와 증명

#### Lemma H6.1 — active terminal-product returns

명제: terminal × auxiliary product return이 active colors에서 single cycle이다.

증명: terminal return cycle과 product exponent carry를 결합한다. 이미 `EvenV11.UnitCarry.productExponentSingleCycle` 계열이 거의 직접 쓴다.

#### Lemma H6.2 — successive completion

명제: 남은 coordinates는 one-point carry rows를 순차적으로 붙여도 single cycle이 유지된다.

증명: 각 completion row의 carry는 한 점에서 `±1`, 나머지 0. 따라서 total carry는 unit이고 `completionCarryCertificate_singleCycle` 또는 `finCompletion...singleCycle`을 적용한다.

#### Lemma H6.3 — marked transfer and reserve renewal

명제: parent marked selector/reserve가 endpoint extension 뒤 renewed marked payload로 이동한다.

증명: `EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit_holds`와 `PhaseProductSupport`의 disjoint/protected-cylinder lemmas를 조합한다. 최종 interface는 target-only가 아니라 payload-preserving theorem을 먼저 만들고, 기존 target promotion은 forgetful adapter로 얻는다.

## 6. 최종 Main 정착 순서

1. Lean/Lake가 있는 환경에서 `lake build EvenV11.Main`과 `lake build EvenV11.V28PaperInterface`를 먼저 확인한다.
2. 각 H proof가 닫힐 때마다 Main의 corresponding `assume_* := sorry`를 실제 theorem으로 교체한다.
3. 모든 slot이 닫히면 `#print axioms EvenV11.evenModulusToriAllDimensions`에서 `sorryAx`가 없어야 한다.
4. 그 뒤 `Status.lean`과 finite blob imports를 default umbrella에서 제거한다. 현재는 역사적 wrapper와 회귀 자료를 보존하기 위해 파일 자체는 남긴다.

