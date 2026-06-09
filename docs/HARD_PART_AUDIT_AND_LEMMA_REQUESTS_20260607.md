# 남은 hard 부분 감사 + 보조정리 요청 (순서대로 논문 대조, 2026-06-07)

> **상태 갱신 (2026-06-08)**: H2·H3·H4는 **유한 존재성 witness(native_decide)**로
> 닫혔다(`LowD5M4Finite`/`LowD7M4Finite`/`LowD7M6Finite`). 따라서 **현재 유효한 요청은
> H1 계열(A + A-realization), H5=C+D, H6=E**다. 요청 B(ribbon realization)는 H2/H3/H4가 finite 경로로
> 우회돼 더 이상 닫기에 필요하지 않으며, native_decide-free 구조 증명을 원할 때의
> **선택적 장기 목표**로 보존한다. 자세한 검증 상태는
> `CURRENT_STATE_GROUND_TRUTH_20260608.md` 참조.
> H1은 다시 H1a(carrier cyclicity)와 H1b(root-flat realization)로 분리되어 있으므로
> main 기준 열린 홀은 H1a/H1b/H5/H6 네 개다.

엔진/골격은 완증(sorry-free). 6홀을 **순서대로** 논문과 대조해 남은 hard 부분을
짚고, 사용자께 요청할 보조정리(A–E)를 형식화한다. (역사적 기록: 작성 시점엔
요청 B가 H2·H3·H4 동시 해결의 최고 레버리지였음.)

판정 근거: `Shared/MasterReturn.lean`·`SwitchCalculus.lean`은 cyclicity 판정
(packet/flag-splice → 단일순환)만 제공. **추상 return → root-flat schedule 실현
정리는 부재** → realization은 기존 엔진 조립 불가, genuine hard core.

---

## H1 — D3, 모든 짝수 m  (`assume_d3CycleData : RootFlatCycle.D3EvenCycleDataFamily`)

- 논문: `prop:D3-base` ← `lem:terminal-cyclicity`.
- Lean 현재: terminal carrier 정의(`TerminalA2LowMod`); F_i 유한순환 m=4(Seed)·
  m=6(`TerminalFiniteCyclicity`); m≤12 Python 검증. 2026-06-08 현재 A2 payload는
  `TerminalA2CarrierCyclicityFamily`와 `TerminalA2RootFlatRealizationFamily`로 분리했고,
  realization은 `sectionEquiv : TerminalQ m ≃ RootState m`를 명시적으로 갖는다. 둘이
  주어지면 `cycleDataFamily_of_carrierCyclicity_and_realization`이 H1
  `D3EvenCycleDataFamily`를 닫는다. `rootPairEquiv` 고정 realization은 계산상 너무
  강하므로 제외한다. 같은 분리를 단일 modulus로 쓴
  `TerminalA2RootFlatRealizationAt`도 추가했고, H2의
  `TerminalA2M4PhysicalRealization`은
  `terminalA2M4RealizationAt_of_physical`로 이 pointwise interface에 연결된다.
  또한 `D3M4DirectRootFlat.cycleData`로 `m=4` direct root-flat witness는
  확정했다. 단 이것은 terminal `F_i` realization이 아니므로 H1의 parametric
  paper-realization 입력을 대체하지 않는다.
  2026-06-08 추가: `TerminalA2EndpointRank`에 paper endpoint order를
  `EndpointLabel m = Fin (2*m)`로 기록했고, rank successor의 단일순환성과
  injective endpoint image로의 transfer(`endpointImageSucc_singleCycle`)를 닫았다.
  이어 `compressedEndpointImageMap_singleCycle_of_rank_step`으로
  `TerminalA2EndpointRecurrence`의 compressed map이 rank list를 한 칸 전진시킨다는
  pointwise table만 있으면 active endpoint image 위 단일순환이 자동으로 나오게 했다.
  따라서 H1a는 이제 (a) recurrence fields를 closed-form rank list에 대입하는 rank-step,
  (b) active interval-splice lemma, (c) m=4 finite base와 m≥6 generic split로 분해된다.
  이후 `terminalEndpointA_injective`/`terminalEndpointB_injective`와
  `terminalEndpointA_eq_B_forces_exception`도 닫아, no-collision의 좌표 핵심은
  A/B within-tag injectivity와 cross-tag exceptional collision lemma로 분리됐다.
  2026-06-09 추가: `EndpointDesc`/`endpointDescPoint` 층에서 valid descriptor의
  point-level injectivity(`endpointDescPoint_injective_of_valid`)와
  `endpointPoint_injective_of_desc_injective` bridge를 닫았다. 이어 color별
  left-inverse proof로 `endpointDesc_injective_of_even_six_le`와
  `endpointPoint_injective_of_even_six_le`까지 닫았다. 이 정리는 정확히
  `Even m ∧ 6 ≤ m` 범위이며, 홀수 color 2 실패는
  `endpoint2Point_odd_collision`/`endpointPoint_odd_color2_not_injective`로 Lean에
  기록했다. 구체 `m=7` 반복도
  `endpoint2Point_m7_collision`/`endpointPoint_m7_color2_not_injective`로 남겼다.
  따라서 generic endpoint no-collision의 정확한 범위는 완료됐고, 남은 H1a는
  recurrence rank-step 및 interval-splice 승격이다.
  이어 `endpointImageSucc_singleCycle_of_even_six_le`와
  `compressedEndpointImageMap_singleCycle_of_even_six_le_rank_step`도 추가해,
  `Even m ∧ 6 ≤ m`에서는 no-collision 결과가 active endpoint image cyclicity
  handoff까지 바로 공급된다. 이제 compressed endpoint image 쪽은 논문 recurrence의
  pointwise rank-step table만 남았다.
  2026-06-09 추가 수정: `TerminalA2EndpointRecurrence`의 boundary fields를
  puncture endpoint를 건너뛰는 compressed form에서
  `terminalEndpointEplus`/`terminalEndpointEminus`를 포함한 paper-faithful bridge form으로
  바꿨다. 따라서 rank-step 목표는 실제 endpoint order의 `B3 -> E+ -> A1`,
  `A3 -> E- -> B1` 타입 bridge와 정합된다.
  이어 `endpointDescSucc`와 `terminalCompressedEndpointReturn_endpointDescSucc`를
  닫아 recurrence record가 valid descriptor를 paper successor로 보냄을 증명했다.
  `compressedEndpoint_rank_step_of_desc_rank_step`으로 raw pointwise rank-step은
  이제 descriptor equality
  `endpointDescSucc c (endpointDesc m c n) = endpointDesc m c (endpointRankSucc m n)`
  하나로 축소됐다.
- 남은 hard: (1) **parametric** terminal-cyclicity, (2) D3 realization(returnMap=F_i).

> **요청 보조정리 A** (`lem:terminal-cyclicity`). 모든 짝수 m≥4, i∈{0,1,2}에서
> terminal carrier `F_i`가 `Q_m=(ℤ/m)²` 위의 단일 `m²`-cycle.
> (논문 증명: endpoint-recurrence `Aʳ/Bʳ`.)
> Lean 목표: `∀ m, EvenModulusRange m → ∀ i, Shared.IsSingleCycleMap (terminalReturn m i)`.

---

## H2 — D5(4)  (`assume_lowD5M4RibbonData : Nonempty ResetPortH2RowEquivRibbonRealizationData`)

- 논문: `prop:D54-reset` (`RHD(5,4)`).
- Lean 현재: 5색 추상 return 단일순환 **완료**(`LowD5M4Seed.fullReturn`). active
  physical-row ribbon 인터페이스 준비됨(`LowD5M4RibbonInterface`). **남은 건 추상
  return → schedule 실현뿐.**
- 인터페이스가 요구하는 정확한 미증명 필드:
  ```
  row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5     -- RF1 자동
  e   : Seed ≃ RootState                                          -- chart 켤레
  layerBijective : (schedule (dirOfRowEquiv row)).layerBijective  -- RF2
  returnRealization : ∀ c x,
      e.symm ((schedule (dirOfRowEquiv row)).returnMap c (e x)) = LowD5M4.fullReturn c x
  ```
- 남은 hard: **ribbon realization** = `row`,`e` 구성해 RF2 + returnRealization.
  (displacement·fiber-collision 때문에 naïve 구성은 실패; t-의존 row + 올바른 e 필요.)

  현재 최단 Lean target:
  ```
  LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput
  ```
  즉 §11 네 physical rows, singleton-switch RF2, wild `e`, 그리고 map-level
  `returnMap = e ∘ LowD5M4.fullReturn ∘ e.symm`.

> **요청 보조정리 B** (D5(4) realization = `lem:layer-comparison-switch` +
> `lem:switching-ribbons`의 root-flat schedule 버전). standard lift + reset 스위칭
> 사이트로 `row`,`e`를 구성하면 (i) schedule이 layer-bijective, (ii) returnMap이
> `e`로 `fullReturn`에 켤레. **이게 H2를 닫는 유일한 잔여물.**

---

## H3/H4 — D7(4), D7(6)  (`Nonempty (RootFlatCycleData 6 4 / 6 6)`)

- 논문: `prop:rank-three-endpoint-bases`, realization은 `lem:folded-port-realization`.
- Lean 현재: reused plus-lane 추상 return 단일순환 **완료**(`LowD7Seed.reusedReturn{4,6}`,
  word-skew over W4/W6); 7-site 좌표(`tab:rank-three-seven-port-coordinates`)·W4/W6
  포팅·(P1)-(P4) 분리는 유한(decide 포팅 가능) 보유.
- `lem:folded-port-realization`의 구조(=조립): `lem:layer-comparison-switch`(disjoint
  switch가 Latin+bijective 보존) + product/word-skew/unit-carry(전부 보유) +
  `lem:switching-ribbons`(ribbon 합성) + (P1)-(P4)(유한).
- 남은 hard: **H2와 동일한 ribbon realization**. (P1)-(P4) 분리는 내가 포팅 가능;
  핵심은 schedule↔ribbon 브리지.

> **요청: 보조정리 B의 D7 일반화.** H2의 B를 "표준 lift + 분리 스위칭 사이트 ⟹
> returnMap이 추상 return에 켤레"로 일반화하면 **H3/H4가 H2와 함께 닫힘**.
> 내 연결작업(가능): D7용 ribbon 인터페이스 신설(H2 미러) + (P1)-(P4) decide 포팅 →
> H3/H4 홀을 H2와 **같은 한 줄 realization 요청**으로 축소.

---

## H5 — odd high modulus  (`assume_oddHighModulus : FinalOddHighModulusTargetPromotion`)

- 논문: `cor:odd-high-even-closure` ← `thm:finite-anchors` + high-even-growth(§).
- Lean 현재: promotion 타입·consumer·input bridge sorry-free; **실제 구성 통째 sorry**.
  단, closing-primitivity 표(`D5D7SeedTables`)·reserve 포팅됨(anchor 근거 일부).
- 남은 hard: anchor 구성 + 2좌표 growth (논문 섹션 전체, parametric).

> **요청 보조정리 C** (`thm:finite-anchors`). D5·D7 coforest-splice anchor가 marked
> 분해 + endpoint reserve를 줌. (closing primitivity·support·reserve는 Lean 포팅 완료;
> 남은 건 이들로부터 anchor 분해 단일순환.)
> **요청 보조정리 D** (high-even growth). anchor에서 모든 high-even target
> (d, odd m>d)으로의 2좌표 성장 사슬(7→9→…).

---

## H6 — odd endpoint  (`assume_oddEndpoint : FinalOddEndpointPhaseProductTargetPromotion`)

- 논문: `prop:endpoint-successor` (`b ↦ 2b+1`).
- Lean 현재: promotion 타입·bridge sorry-free; 구성 sorry.
- 남은 hard: endpoint successor 구성(low-modulus 확장, phase-product).

> **요청 보조정리 E** (`prop:endpoint-successor`). marked `RHD(b, ·)`에서
> `RHD(2b+1, ·)`로의 endpoint 확장.

---

## 통합 우선순위

| 요청 | 닫는 홀 | 성격 | 내 연결작업 |
|---|---|---|---|
| **A** (terminal-cyclicity) | **H1a** | hard, parametric, 현재 최단 닫힘 단위 | endpoint rank/image transfer 진행 중 |
| A-realization | H1b | hard, paper-realization | common `sectionEquiv` + color translation lemma |
| B (ribbon realization) | 선택적 structural H2/H3/H4 | hard, 장기 목표 | D7 인터페이스·(P1)-(P4) decide 포팅 |
| C+D (anchors+growth) | H5 | hard, 섹션 전체 | 표 포팅됨 |
| E (endpoint successor) | H6 | hard, 섹션 | bridge 준비됨 |

**한 줄 결론**: H2/H3/H4는 finite witness로 main에서 닫혔고, 현재 닫힘 순서는
(1) **terminal-cyclicity A**(H1a), (2) **terminal realization**(H1b), (3) H5·H6
섹션(C/D/E)이다. B는 논문-faithful structural certificate를 원할 때 되살릴 장기
목표다.
