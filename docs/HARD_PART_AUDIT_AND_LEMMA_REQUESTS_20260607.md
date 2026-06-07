# 남은 hard 부분 감사 + 보조정리 요청 (순서대로 논문 대조, 2026-06-07)

엔진/골격은 완증(sorry-free). 6홀을 **순서대로** 논문과 대조해 남은 hard 부분을
짚고, 사용자께 요청할 보조정리(A–E)를 형식화한다. 핵심: **요청 B(ribbon
realization)가 H2·H3·H4를 동시에 닫는 최고 레버리지**.

판정 근거: `Shared/MasterReturn.lean`·`SwitchCalculus.lean`은 cyclicity 판정
(packet/flag-splice → 단일순환)만 제공. **추상 return → root-flat schedule 실현
정리는 부재** → realization은 기존 엔진 조립 불가, genuine hard core.

---

## H1 — D3, 모든 짝수 m  (`assume_d3CycleData : RootFlatCycle.D3EvenCycleDataFamily`)

- 논문: `prop:D3-base` ← `lem:terminal-cyclicity`.
- Lean 현재: terminal carrier 정의(`TerminalA2LowMod`); F_i 유한순환 m=4(Seed)·
  m=6(`TerminalFiniteCyclicity`); m≤12 Python 검증.
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
| **B** (ribbon realization) | **H2 + H3 + H4** | hard, 최고 레버리지 | D7 인터페이스·(P1)-(P4) decide 포팅 |
| A (terminal-cyclicity) | H1 | hard, parametric, 가장 clean | RF1/RF2 패턴(D2) 재사용 |
| C+D (anchors+growth) | H5 | hard, 섹션 전체 | 표 포팅됨 |
| E (endpoint successor) | H6 | hard, 섹션 | bridge 준비됨 |

**한 줄 결론**: 추상 cyclicity는 H1·H2·H3·H4 모두 Lean에 거의 다 있음(H2/H3/H4
완료, H1은 유한·요청 A 남음). 남은 진짜 hard는 (1) **realization 브리지 B**
(H2/H3/H4 공통), (2) **terminal-cyclicity A**(H1), (3) H5·H6 섹션(C/D/E). B가
하나로 셋을 닫으므로 최우선 요청.
