# 논문 table = 올바른 certificate인가 — 검산 · 구현 체크 · pseudocode (2026-06-07)

사용자가 Lean 형식화를 진행하는 동안 준비한 **독립 검증** 산물. 목적: 논문의
finite table / 각 Lean 홀이 쓰는 구성이 **올바른 root-flat certificate**임을
Lean과 무관하게 계산으로 확인하고, Lean `dir` 구성을 위한 pseudocode와
즉시-검증 도구를 제공.

## 0. 스크립트

- `scripts/verify_finite_checks.py` — **논문 원본**. forest 1-isolate, closing
  column primitivity(`|det|=1`), support-row rank, reserve 좌표, terminal word
  W4/W6. **재실행 통과 ✅** (인쇄된 table이 산술적으로 정확).
- `scripts/verify_rootflat_certificates.py` — **신규**. 아래 RF1/RF2/RF3 검증기 +
  certificate 핵심 cyclicity 독립 검증 + 검증기 자체 검증. **통과 ✅**.

## 1. certificate 조건 (Lean ↔ Python 정확 일치)

root-flat schedule = `dir : ZMod m → (Fin n → ZMod m) → Color(n+1) → Dir(n+1)`,
`step = StandardRootFlatLift.rootStep` (방향 `d<n`이면 좌표 `d`를 +1, `d=n`이면
no-op). 세 조건:

| 조건 | Lean | 의미 |
|---|---|---|
| RF1 `rowLatin` | `∀ t w, Bijective (c ↦ dir t w c)` | 각 (t,w)에서 색→방향이 전단사 |
| RF2 `layerBijective` | `∀ t c, Bijective (w ↦ rootStep (dir t w c) w)` | 각 layer map 전단사 |
| RF3 `returnsSingleCycle` | `∀ c, IsSingleCycleMap (returnMap c)` | 색별 first-return이 단일 `m^n`-cycle |

`returnMap c w = (layer 0 ∘ … ∘ layer m-1)` = `m`개 layer 합성. 이게
`RootFlatCycle.RootFlatCycleData n m`의 세 필드입니다. **검증기 `verify_rootflat
(n, m, dir_fn)` 가 이 셋을 그대로 검사** → 통과하면 valid certificate 후보.

## 2. 구현 체크 워크플로 (사용자용)

Lean `dir`을 만들면 **kernel 증명 전에** 먼저 Python으로 즉시 확인:

```python
from verify_rootflat_certificates import verify_rootflat
# n = d-1.  dir_fn(t, w, c): t∈0..m-1, w=tuple len n over Z/m, c∈0..n → dir 0..n
print(verify_rootflat(6, 4, my_d7m4_dir))   # {'RF1':?, 'RF2':?, 'RF3':?}
```
- 전부 True → 그 dir은 `RootFlatCycleData 6 4`의 valid 입력. Lean에서 RF1(Equiv면
  자동)/RF2(decide)/RF3(decide 또는 ribbon)만 증명하면 됨.
- 하나라도 False → dir이 틀림. Lean 증명 시도 전에 차단.

상태 수: D7(4)=4096, D7(6)=46656 — 둘 다 Python 검증 가능(수 초~수십 초).

## 3. 검증된 사실 (이번 실행)

| # | 사실 | 관련 홀 |
|---|---|---|
| A | 논문 finite checks 전부 통과 (forest/closing `|det|=1`/support/reserve/W4·W6) | 전체 base |
| B | terminal `F_0,F_1,F_2`가 짝수 `m∈{4,6,8,10,12}`에서 `m²`-cycle | H1 (D3), H2 |
| C | D5(4) §11 returns `R̂_0..R̂_4`가 256-cycle | H2 — **`LowD5M4Seed.fullReturn_singleCycle` 독립 교차검증 일치** |
| E | D2(m) anti-diagonal이 RF1/RF2/RF3 통과 (짝수 m) | 검증기 신뢰성 + 템플릿 |

## 4. pseudocode — dir 구성

### 4.1 완결 예제: D2(m) anti-diagonal (검증 완료)
```
# n=1 (d=2).  root_flat_first_returns.tex, Prop D2-antidiagonal
dir(t, w, c):
    if c == 0:  return 0 if t == 0 else 1     # returnMap_0 = +1  (m-cycle)
    else:       return 1 if t == 0 else 0     # returnMap_1 = +(m-1) (m-cycle)
# RF1: 두 색이 상보 → Latin.  RF3: gcd(±1, m)=1.  → 검증기 통과.
```
이게 root-flat dir의 **최소 동작 템플릿**입니다. Lean `RootFlatCycle.RootFlatCycleData
1 m`로 그대로 옮길 수 있습니다(d=2는 홀이 아니지만 패턴 참조용).

### 4.2 D3/D5/D7 — abstract return은 검증됨, dir 실현이 hard part
핵심 구조(모든 d≥3 base 공통):
```
# abstract return (검증됨, 단일 cycle):
#   D3:  F_i               (terminal carrier, m²-cycle)         ← 사실 B
#   D5(4): R̂_i            (skew tower, 256-cycle)              ← 사실 C
#   D7: two-rail relay return (forest+unit-carry, |det|=1)     ← 사실 A
#
# root-flat dir(t,w,c)의 returnMap_c 는 위 abstract return과 "run-collapse 재색인 e"로
# 켤레다(좌표별이 아님).  returnMap은 layer당 +1 단일증분이라 변위 ≤ m이고,
# abstract return은 고변위 → 동일 좌표로는 같지 않다(H2 blocker 참조).
#
# 따라서 dir 실현 = "default run을 m개 layer로 펼치고 η 점프를 끼우는" 스케줄.
# 이게 paper의 'realize by layer rows' = genuine hard part (사용자 Lean 작업).
```
**구현 체크 연결**: 사용자가 실현 dir을 만들면 §2 워크플로로 즉시 RF1/RF2/RF3 확인.
통과 dir을 `RootFlatCycleData`(D7) 또는 ribbon `e`(D5) 경로에 투입.

### 4.3 D7 cycle-data 입력 형태 (Lean)
```
RootFlatCycle.RootFlatCycleData 6 m :=
  { dir : ZMod m → (Fin 6 → ZMod m) → Fin 7 → Fin 7   -- §App-A two-rail relay
  , rowLatin            -- dir이 색≃방향 Equiv면 자동
  , layerBijective      -- 유한, decide (maxRecDepth↑)
  , returnsSingleCycle  -- 유한, decide 또는 ribbon e 켤레 }
# → RootFlatCycle.finalLowD7M{4,6}RootFlatCertificateFamily_of_nonemptyCycleData
```

## 5. unit-carry ⟹ RF3 (논문 table이 certificate인 이유)

논문 `check_closing_signs`의 `|det|=1`은 우연이 아니라 **RF3 그 자체의 판정**입니다:
`lem:unit-carry`에 의해 색 c의 return `T(x,r)=(Bx, r+γ(x))`는 `∑γ`가 unit일 때
단일 cycle인데, closing column의 `|det|=1`(primitivity)이 정확히 그 unit 조건입니다.
즉 **논문 table이 통과한 `|det|=1` 검사 = 각 색 return이 single cycle이라는 RF3 증명의
유한 핵심**. 사실 A가 이를 모든 색에 대해 확인합니다.

## 6. 결론

- 논문의 finite table들은 **올바른 certificate**입니다: 조합 불변량(forest/primitivity/
  rank)과 cyclicity 내용(F_i, R̂_i, W)이 독립 계산으로 전부 확인됨.
- 남은 것은 table의 정확성이 아니라 그 abstract return을 **root-flat dir로 실현**하는
  부분(run-collapse)이며, 이는 Lean 형식화의 hard part(사용자)입니다.
- `verify_rootflat`가 그 실현 dir을 Lean 증명 전에 즉시 검증하는 도구를 제공합니다.
