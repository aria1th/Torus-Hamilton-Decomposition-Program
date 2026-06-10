# Growth 수선 feasibility gate — budget 판정 (2026-06-10)

A3(chained 7→9 단계 반증) 이후 수선 탐색의 선행 게이트. 결과: **탐색 불필요,
budget 논증이 결정적**. 도구: `scripts/search_growth_newcolor_repair.py`
(`--budget-gate`, `--child-evidence`), 요약 `scripts/growth_repair_gate_summary.json`,
교차 증거 `scripts/growth_repair_child_evidence_m{4,6}.json`.

## 판정

**R3-old 동등(old return을 growthDir return과 pointwise 동등하게 유지)
조건 하에서는 수선이 양 기반에서 불가능.** d, m에 일양적이므로 7→9→11→…
모든 chained 단계에서 동일 — `oldReturns_eq`는 어떤 수선에서도 그대로
재사용 불가.

논증 사슬 (각 단계 기계 확인):
1. **L1 (count-vector 유일성, 전수)**: 고정점 없는 return의 m-step 궤적은
   방향별 step 수 n_i가 잔차 r_i(p)로 유일 결정 (m=4: C(12,8)=495,
   m=6: C(14,8)=3003 전수).
2. **L2**: RF2 ⟹ 방향별 read 총량 = Σ_p r_i(p) — return만의 함수.
   R3-old 동등이 old 색의 x-read 총량을 전부 고정.
3. **L3 (포화, 수치)**: 기반의 Latin 행 + 단일순환 return이 모든 x-방향에서
   D_i = m·K를 강제 (m=4: 16384, m=6: 279936).
4. **Kill**: child의 방향별 x-슬롯 = old 색 필요량과 정확히 일치 ⟹ 새 색의
   x-read 예산 = 0 ⟹ leaf return이 모든 {x}×(Z/m)² fiber 보존 ⟹
   ≥ m⁶ 순환 vs 필요 1.

## 최저가 완화 (다음 관문)

R3-old를 **conjugate**(old return은 단일 K₂-순환 + growthDir carry 모양,
pointwise 동등은 아님)로 완화 시 필요조건:
- (a) old 색이 방향당 ≥ 2m x-read를 양도해야 함 (새 색이 좌표당 ≥ m 전이
  필요; 동등은 0 양도).
- (b) 수정되는 old 색은 ≥ 3점에서 변경 (짝치환 패리티).
- (c) O3 유지: leaf read는 z-gated.
`growth_step_replay.py`에 스케치된 rotor constellation이 (a)–(c)를 만족하는
최소 기지 모양. 이 완화 하의 가능성은 **미결** (미탐색).

## 부수 발견 2건

1. **`growth_step_replay.load_seed`가 seed의 `stages` 필드를 무시.** m=4는
   무해(stages 없음), m=6은 이 loader의 기반이 RF3 실패(색별 7776/7669/
   7655/7671 순환). 이를 거친 m=6 기록(check_oldgens_span*의 C2 수송 ledger,
   old-incidence 수치)은 적정 재구성(rewrite 레포
   `certificates/scripts/verify_rank7_rootflat_certificates.py` 미러,
   RF1/2/3 전부 PASS) 위에서 재도출 필요. 구조적 결론(알파벳 감금,
   z-단조성 한계)은 기반 무관 — A3 판정은 영향 없음.
2. **`GrowthPlacement.order`(GrowthStepCore.lean:407, 강한 t1 < t0)가 적정
   (7,6) 기반에서 충족 불가** — 색 0/1/4의 last-read가 단일 layer(색 0은
   36 사이트). 즉 형식화된 growthDir 구성 자체가 (7,6)에서 인스턴스화
   불가(R3-old 질문은 거기서 추가로 공허). 수치적으로는 같은-layer
   사이트-구별 완화로 RF1+RF2+old 단일순환(1679616) 전부 성립 — 강한 order
   필드가 문제, 구성이 문제가 아님. old 색 기계를 재건할 때 함께 수정.

## 다음 수순

1. loader 수정 + m=6 ledger 재도출 (적정 기반 위).
2. conjugate 완화 하의 구조 탐색: rotor constellation / z-gated 역할 교환,
   (7,4)와 적정 (7,6) 양쪽, chaining 성질 포함.
3. 탐색 hit 시에만 Lean 재설계 (GrowthStepCore old-색 경로 재건 +
   GrowthPlacement.order 완화 포함).
