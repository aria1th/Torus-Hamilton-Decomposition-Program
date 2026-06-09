# H3/H4 (D7(4), D7(6)) — 논문 정밀 분석 (2026-06-07)

> **상태 갱신 (2026-06-08)**: H3·H4는 **유한 존재성 witness**로 닫혔다 —
> `LowD7M4Finite`(Fin 4096)·`LowD7M6Finite`(Fin 46656)의 구체 `dir`가 RF1/RF2/RF3를
> native_decide로 만족(`Main.assume_lowD7M4/M6`에 배선). 아래 분석의 ribbon
> realization 경로(요청 B)는 **닫기에 필요하지 않게 됐고**, native_decide-free 구조
> 증명을 원할 때의 선택적 장기 목표로 남는다. 검증:
> `CURRENT_STATE_GROUND_TRUTH_20260608.md`.

요청: H3/H4를 논문에서 더 파봄. 결론: **H3/H4는 H2/D5(4)와 구조적으로 동일**하며,
유일한 새 터미널 입력(W4/W6)은 이미 포팅됐다. 남은 hard core는 H2와 같은
**ribbon realization** 하나.

근거: `subtex/rank_three_*`, `subtex/appendix/low_modulus_witnesses.tex`,
`final_induction_framework.tex` (`prop:rank-three-endpoint-bases`).

## 1. 구성 (folded rank-three endpoint chart)

- chart `E = Y × Q × Z`, `Y = K₃,m`(터미널 부모 root-flat, m²), `Q=(ℤ/m)²`(터미널 A₂),
  `Z=(ℤ/m)²`(2 successor lane). `|E| = m⁶` = D7(m) 단면.
- 7 switching site: 터미널 교환 `X₀X₁X₂`(τ_i ↔ p_{ρ(i)}⁺, fold ρ=(0↦1,1↦2,2↦1),
  p₁⁺ 재사용), reset `R₀R₁`(p₁⁻,p₂⁻ → 공통상 I), completion `C₁C₂`(unit-carry 2좌표 추가).
- **7-site 좌표 명시됨**(`tab:rank-three-seven-port-coordinates`): D7(4)·D7(6) 각각
  `(y;q;z)` + code + reused-return trace. 예) D7(4): x₀=(0,0;0,0;0,0), …, c₂=(0,0;2,1;0,0).

## 2. cyclicity = 이미 가진 엔진들 (핵심 발견)

`low_modulus_witnesses.tex`가 reused plus-lane return의 순환성을 다음으로 환원:

| 단계 | 논문 | Lean |
|---|---|---|
| 재사용 lane word | `W₄=F₁F₀²`(16-cyc), `W₆=F₁²F₀³`(36-cyc) | **`TerminalFiniteCyclicity` 포팅 ✅** (orbit 정확 일치) |
| word-skew product | `lem:word-skew-product` (`S(q,y)=(Tq,A_q y)` cyclic) | **`single_cycle_of_skewProduct_base_orbit_monodromy` ✅** (Seed P0/P1에 사용) |
| completion (2좌표) | `lem:unit-carry` ×2 | **`pointCarrySingleCycle` ✅** (Bundle B) |
| 다른(비재사용) branch | endpoint product/unit-carry | proven 엔진 |
| parity 장애 | `lem:folded-two-kick-parity` (FαFβ even) → odd reset word | D5(4) `lem:D54-parity-obstruction`와 동형 |

→ **rank-three folded return의 단일순환은 D5(4) Seed와 완전히 같은 tower**:
터미널 cycle(W4/W6) → word-skew → unit-carry 완성. 모든 엔진이 Lean에 있음.

## 3. 통합 관점 (전략적)

H2·H3·H4는 **동일한 패턴**의 인스턴스다:

```
터미널 carrier (F_i, W4/W6)  --word-skew + unit-carry-->  abstract return (단일순환)
                                                            |
                                          ribbon realization (= hard core)
                                                            v
                                  root-flat schedule returnMap (= 단일순환, RF3)
```

- **D5(4)** (H2): abstract return = `LowD5M4Seed.fullReturn` (단일순환 **완료**).
- **D7(4)/D7(6)** (H3/H4): abstract return = folded rank-three return (단일순환 **구축
  가능**, W4/W6 포팅 + word-skew + unit-carry로 Seed와 동일하게).
- 셋 다 남은 hard core는 **같은 ribbon realization**(`lem:folded-port-realization` /
  D5(4)의 layer-row realization). 이걸 표준 lift에 대해 일반적으로 풀면 H2·H3·H4가
  함께 닫힌다.

## 4. 지금 구축 가능한 것 (다음 표적)

1. **D7(4)/D7(6) abstract 단일순환 (`LowD7Seed`, Seed 미러)**: 7-site → folded return
   정의 + W4/W6 + word-skew + unit-carry로 단일순환 증명. H3/H4를 H2와 같은 상태로
   (단일순환 끝, realization 남음). **achievable, sorry-free 목표.**
2. **7-site/separation 데이터** (P1)–(P4): 유한 좌표 분리, `decide` 가능 (D5/D7 표처럼).
3. **common-edge witness** (`R_a(c)=R_b(c)=I`): 구체 좌표 있으나 R_a/R_b는 realization
   의존.

## 5. hard core (H2와 공유)

`lem:folded-port-realization`(switching-ribbons): 표준 lift schedule의 returnMap이 위
abstract folded return과 켤레임. = H2의 run-collapse/ribbon. **H2·H3·H4 공통 난점**이며
협업상 사용자 영역. 표준-lift ribbon 일반정리를 만들면 셋이 동시에 해결.

## 6. 한 줄 결론

> H3/H4는 새 hard 수학이 아니라 **D5(4)와 같은 word-skew/unit-carry tower**다. 새 터미널
> 입력 W4/W6는 포팅 완료. 따라서 H3/H4의 abstract 단일순환은 Seed처럼 sorry-free로
> 구축 가능하고, 남은 건 H2와 **공유되는 ribbon realization** 하나뿐이다.
