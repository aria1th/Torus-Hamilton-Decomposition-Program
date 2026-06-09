# 논문 수치 정보 전수 audit + 필요 구조 판정 (2026-06-09)

방법: v28 finite-audit 논문 소스(`even_modulus_directed_tori.tex` + subtex 29개,
~5,700줄)를 4개 영역(H1 / H5 / H6 / 닫힌 홀+spine)으로 나눠 **모든 수치 표·상수·
closed-form·witness 데이터**를 추출하고, 대응 Lean 정의와 값 단위로 대조했다.
논문 번들의 자체 재현 스크립트 `scripts/verify_finite_checks.py`도 실행: **passed**
(one-isolate forest, |det|=1 closing column, support rank, reserve plane, W4/W6).

## 0. 한 줄 결론

**값 단위 불일치는 전체에서 정확히 1건** — `D7TwoRailRelay.stageSkeletons` stage 3
shifted pair `(3,5)`(논문 `(3,0)`) 전사 오류. 본 audit에서 `edge03`으로 수정하고
재발 방지 guard `stageSkeletons_shift_consistent`(shift 적용 = shifted 열, `decide`)를
추가했다. 그 외 대조한 모든 수치(아래 §1)는 논문과 Lean이 정확히 일치한다.
**1단계(H1a) 착수에 필요한 추가 구조는 식별 완료**(§2) — 계획 변경 없이 세부만
구체화하면 된다.

## 1. 값 단위 대조 결과 (일치 확인된 항목)

| 영역 | 대조 항목 | 결과 |
|---|---|---|
| H1 | 행 치환표(τ02/τ12/τ01/χ±) 15엔트리, ω_m turn 6점, Δ_i, A/B closed-form, E± 경계점 6개, 예외 집합, next=r∓1, m=4 궤도 3×16=48엔트리 | **전부 일치** |
| H1 | endpointDescSucc의 순환 순서 vs 논문 `B3→E+→A1`, `A3→E−→B1` 등 | 일치 |
| H2–H4 | 7-site 표 14행+code, protected 8점+code, explicit reserve 20상태+code, W4/W6 궤도 16+36엔트리, W=F₁F₂F₀ 16궤도, C₄, p₀–p₂, a₀–a₄, D5(4) reserve 8점 | **전부 일치** (code 산술 수기 재검산 포함) |
| H5 | D5 support 5행, D7 support 14행, 양쪽 determinant 표(ι/closing/sign), D7 stage data, D7 terminal alignment, reserve 좌표 8+10점 | 일치 (stage 3 shifted pair 1건만 오기 → 수정) |
| H5 | growth row 표((s,δ), support, boundary, leaf line, quotient generator), boundary-avoiding phase ρ=3,7,1,5 | 일치 (`GuideLocality`) |
| H6 | b=4 chart의 C₁ crossing(`ZMod 9`, target 8, shift 1, tail 7), folded selector/image 68→1352, 2910→10908, reserve role 10개, 1/m²−1 지수 산술 | 일치 |
| spine | 범위 산술: `MarkedDimensionRange = 4≤d ∧ Even ∧ m≤2d+1`, 예외 분기 (5,4)/(7,4)/(7,6), b≥4 endpoint step | 논문과 정확히 일치 |

상세 근거는 audit 에이전트 보고 4건(본 문서의 소스)을 요약한 것이며, 항목별 논문
file:line은 각 절에 기록돼 있다.

## 2. H1 — 1단계 착수 전 필요 구조 (확정)

기존 골격(recurrence record, closed-form rank list, no-collision, single-cycle
reduction)은 완비. **신규로 만들 것은 정확히 4가지**:

1. **`TerminalA2EndpointRecurrence m` 인스턴스 구성** — 현재 구조체는 가설로만
   소비되고 인스턴스가 없다. 필요물:
   - 논문 `n_i`를 실현하는 `terminalExchange : TorusColor 3 → TerminalQ m → TerminalQ m`
     (각 ℓ_c-fiber의 두 active endpoint 교환, collision fiber에선 E⁺↔E⁻, 그 외 항등)
   - `generic_A/B` 증명: η_c를 A/B점에서 ω_m 행 case 분석. 주의 — "generic"도 작은
     r에서 turn row를 지나간다(예: color 0, r=1은 χ₋ 행 경유). `6 ≤ m`로 작은 상수
     분리(보조정리 ER:50–53 기존재).
   - 12개 boundary field: 유한 `ZMod m` 계산.
2. **`hdesc` rank-step 항등식** —
   `endpointDescSucc c (endpointDesc m c n) = endpointDesc m c (endpointRankSucc m n)`
   (`Even m ∧ 6 ≤ m`). 색별 4개 segment 경계의 parity/wrap 산술.
   ⚠️ injectivity는 color 0,1에서 `6 ≤ m`만 필요했지만, **hdesc는 세 색 모두
   `Even m`이 필요**(segment 경계 k=m−3, m−1의 교대가 홀수 m에서 뒤집힘).
3. **Active-set 식별 (논문 `lem:terminal-six-turn-cap`의 Lean 화)** —
   `S_c = {z | terminalEta c z ≠ z} = Set.range (endpointPoint m c)`,
   fiber당 active 2점, `η_c(S_c)=S_c`. 특히 off-list 방향(`z ∉ range ⇒ η_c z = z`)이
   splice의 "default interval"을 떠받친다. (논문의 six-removal failure 표는 설계
   정당화일 뿐, 형식화 불요.)
4. **Interval-splice 승격 — 최대 신규 구조.** 2m-endpoint 순환 → m² carrier 순환.
   기존 엔진 부적합: `Shared.SwitchCalculus.oneStepPacketSplice`/`MasterReturn`은
   **coset당 tail 1개** 전제, terminal fiber는 **2개**. 두 가지 설계안:
   - (a) **two-tail packet splice** 신규 lemma (m개 fiber, tail→next-head 짝은 h_c가 제공);
   - (b) **full-carrier rank 확장**: endpoint별 default 구간 길이
     `len : EndpointLabel m → ℕ`(fiber 합 = m, 총합 m²), 좌표
     `TerminalQ m ≃ Σ n, Fin (len n)`, `terminalReturn`이 유도된 `ZMod (m²)` rank를
     +1 전진 → `Shared.RankCycle.single_cycle_of_zmod_rank_equiv`로 종결
     (endpoint 층의 `endpointRankSucc_singleCycle`과 동형 패턴).
   권고: **(b)** — 기존 rank 패턴 재사용, 신규 splice calculus 불요.

H1b(2단계) 추가 확인사항:
- 인터페이스 위험: 논문 η_i는 색별 `z − a_i` 앵커(색별 평행이동)인데 Lean 구조는
  **색 공통 단일 `sectionEquiv`** 요구. 단일 chart가 평행이동을 흡수할 수 있는지
  증명하거나, `sectionEquiv : TorusColor 3 → (TerminalQ m ≃ RootState m)`로 일반화
  필요 — **채우기 전에 인터페이스 재설계 여부 판단이 선행**돼야 한다.
- naive chart는 반증 존재(`terminalDir_m4_plainChart_not_rowLatin`): t-의존 dir 필수.
- convention 주의: Lean 전역은 `F_i(z)=η_i(z+Δ_i)`(논문 appendix convention).
  H1b의 `return_eq_terminal`과 interlacing 공통 head 계산은 convention 민감.

부수 갭(차단 아님): `TerminalA2InterlacingSelector` 인스턴스 부재 + 필드 부족
(구체 `c_j=(−j−1,j)`, cut order ±2, `|C|=m−1` unit), m=4 marked parent
(`C₄`, (F₁,F₂) 쌍) 구조 전무 — 둘 다 marked(RHD) 충실도 작업으로, H1a/H1b 닫기엔
불요하나 H5/H6의 marked payload에서 재등장(§5).

## 3. H5 — 기록된 필요 구조 (3단계용)

표 데이터(R1 primitivity, R2 support rank, reserve 좌표)는 포팅 완료. 미포팅:

**유한/decide 가능** — D5 stage skeleton(+ shift rule `e_{c,r}={c+s_r, σ_r(c+s_r)}`로
forest 재생성하는 derivation 정리; 현재 forest는 stage row와 무연결 데이터),
Latin-skeleton 검사, D7 stage 3–5 contracted coforest 18행(현 TypeA 포팅은 D5 전체
+ D7 stage 1–2 = 26중 8행뿐 — `v28FiniteInputCoforestAudit` 이름이 전체처럼 들리는
함정), R3(laminar contour, old-head transversal 12+32셀, tail–head 항등식 19행),
D5 terminal alignment, reserve projection-separation 7행(전제인 N(C)·ribbon trace의
Lean 정의 자체가 선행 필요).

**Parametric** — `RHD(d,m)` predicate(marked 분해 + endpoint reserve; spine엔
`FinalMarkedTarget`뿐), splice 합성(`one-step/triple-packet-splice`,
`flag-splicing-criterion`), quotient-to-layer lift + `prop:seed-realization`
(모든 even m>D), covolume-carry 정규화, growth 두 명제(7→9 chained,
paired D−2→D for D≥11) + `cor:odd-high-even-closure` 반복, reserve transport.

위험 기록: ① B_c 부호 열은 논문/Python/Lean 모두 primitivity만 검사(부호 자체는
기계 검증 없음 — 수학적으론 충분), ② reserve 검사는 최소 modulus(6/8) 고정 —
모든 even m 버전은 별도 (쉬운) lemma 필요, ③ closing edge 방향이 데이터(0,6)와
audit(6,0) 사이 반전 — 부호 민감 작업 시 함정, ④ `ManuscriptHardSectionData.
finiteCoforestAnchor`가 모든 홀수 D≥5에 anchor를 요구(논문은 D∈{5,7}+growth) —
충실 포팅엔 잘못된 모양, ⑤ engine 모양: `FinalOddHighModulusTargetPromotion`은
audit boolean들에서 모든 odd d<m을 내야 하므로 RHD 귀납을 엔진 내부화하거나
endpoint 분기처럼 marked-payload refactor 필요.

## 4. H6 — 기록된 필요 구조 (4단계용)

입력 bridge sorry-free 확인(transfer/phase-product/completion). 그러나:

- **숨은 의존성: H6 ⊃ H1a.** `lem:endpoint-active-core`는 일반 even m의 terminal
  cyclicity(`thm:terminal-A2`)를 인용하는데
  `FinalOddEndpointPhaseProductCertificateInputs`에는 m=4/6 trace뿐 — engine 구축 시
  입력 레코드 확장 또는 H1a family import 필요. **H1a를 먼저 닫는 현 계획 순서가
  이 의존성과 정합.**
- 미구현 구조 9종: endpoint chart `E=Y×Q×(ℤ/m)^{b−1}`+Ω 순서+임베딩 Φ, 행 템플릿
  치환(N/X_i/R/C_h — b=4 표 포함), 일반 row list `𝒫∈E^{b+4}`+reset common-image
  방정식의 parametric 판, renewal capacity `2b+4 < 4^{b−1}`+역할 분할(현 위상선
  slot은 익명 `Fin(2a+3)` — **2a+3과 2b+4 혼동 금지**, 역할 enum도 b=3 하드코딩
  10개라 parametric 화 필요), 실데이터 marked payload(현 `FinalMarkedPayload`는
  PUnit으로 채워짐 — 논문 충실도 0), lifted completion fiber RF2, b−1개 completion
  순차 tower(현 인증서는 1좌표용), parametric RF-criterion(차원 2b+1), phase-doubling
  marked 내용(R₀/R₁, B₀, a₀=m/2, selector (0,0), common image (1,m/2) — Lean 전무).
- 산술 함정: sketch datum의 unit 조건이 `ZMod m`인데 논문은 `ZMod (m^k)` — 지수가
  `≡−1 (mod m)`일 땐 동치지만 일반 지수에선 불충분, `squareSubOneUnitZModPow` 사용.

## 5. 닫힌 홀(H2/H3/H4)·spine — 추가 의무 없음

값 전수 일치. 미포팅 항목은 전부 **request B(구조적 증명, 선택적 장기 목표)**
범주: 공통 edge 등식 `R₀(68)=R₁(68)=1352`/`R₂(2910)=R₅(2910)=10908`의 실제 return
map 구성, D5(4) 5개 substitution의 ribbon 실현, D5 stage data·terminal alignment,
D7 flag 표 34행, parity 장애 lemma(동기 부여용), interlacing selector corollary,
`|C₄|=3` unit 정리. **현 finite-witness 경로의 닫힘에는 영향 없음.**

기타 기록: trace(연대순) vs word(머리-우선) 이중 상수 존재 — 정리는 전부 trace
형에 걸려 있고 word 상수는 미사용 혼동 위험만.

## 6. 이번 audit에서 적용한 수정

- `EvenV11/V28Hard/D7TwoRailRelay.lean`: stage 3 `shiftedPair₁ := edge35` →
  `edge03` (논문 `(3,0)`), `shiftEdge` 정의 + guard 정리
  `stageSkeletons_shift_consistent` 추가 (`decide`; 양 열의 전사 오류를 이후
  기계적으로 차단).

## 7. 1단계 세부 계획 (audit 반영 확정판)

`FORMALIZATION_STATUS_AND_PLAN_20260609.md` 1단계를 다음 순서로 구체화:

1. `hdesc` descriptor table equality (§2-2) — 순수 산술, 선행물 없음.
2. Active-set 식별 (§2-3) — η_c off-list 항등 + range 일치.
3. `terminalExchange` 정의 + `TerminalA2EndpointRecurrence` 인스턴스 (§2-1) —
   2의 active-set 사실을 case 분석에 재사용.
4. Full-carrier rank 확장(설계안 b) (§2-4) — 구간 길이 `len`, Σ-좌표, rank-step
   정리 → `single_cycle_of_zmod_rank_equiv`.
5. 조립: m=4 finite + m≥6 generic → `TerminalA2CarrierCyclicityFamily`,
   `Main.lean:57` sorry 제거.

각 항목 종료마다 게이트 green 유지. 2단계(H1b) 착수 전에 §2의 sectionEquiv
색별/공통 인터페이스 결정을 먼저 내린다.
