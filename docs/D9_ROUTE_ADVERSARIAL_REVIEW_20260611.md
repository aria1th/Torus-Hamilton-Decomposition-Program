# D9 경로 적대 심사 — 오류·파기·대체 루트 판정 (2026-06-11)

저자 요청에 따른 적대적 종합 심사. 저자 동의(2026-06-11) 하에 기록.
대상: `d9_all_even_proof_bundle_20260611` + `d9_reinforced_lowmod_formal_
bundle_20260611` (vendor/ 편입본). 기계 근거는 각 절에 명시.

## 0. 심사 기준

이 감사 시리즈에서 미검증 다리(사람 lemma chain에만 의존하는 연결부)의
기계 검사 타율: **4/4 파손** (W2, X₁/X₂, A3 chained step, D9 실현
게이트). 따라서 "검증기가 통과한다"와 "정리가 성립한다" 사이의 모든
간극을 잠재 오류로 취급한다.

## 1. 증명 자체가 틀린 곳 (기계 근거)

### 1a. Signed anchor-realization theorem — 서술 수준 unsound

`d9_reinforced_realization_bridges_20260611.md`의 정리는 증명 첫 문장
"The Latin row condition gives RF1"에서 **가설 목록(1–8)에 없는 조건**을
사용한다. 인쇄된 가설만으로는 m=4 인증서가 가설을 만족하면서 결론이
거짓이다 — 실현 게이트(`scripts/realize_d9_anchor_schedule.py`,
`d9_realization_gate_m4.json`, 커밋 53122a5)가 4⁸ 전수·지정 6·판독 4로
확인한 반례. Latin 조건을 가설 9로 명시하면 정리는 참일 수 있으나,
lowmod 인증서는 그 가설을 만족할 수 없다(§1b의 행 예산).

### 1b. 행 예산 — lowmod에서 실현 규칙은 원리적으로 불가능

실현 규칙은 stage 높이 7종의 행 + closing 클래스 {3,6}의 hosting 행,
서로 다른 행 유형 9개를 요구한다. m∈{4,6,8}의 행 수는 4/6/8. 접기가
강제되고 closing 클래스는 수용 불가 ⟹ closing carry = 0 ⟹ RF3 구조적
불가. 접힌 행은 치환-대-기저 라벨 충돌로 RF1도 점별 파괴(모든 판독).
보강 번들의 절 6(접힌 높이 support 분리)은 치환-대-치환만 다루므로
무관하다.

### 1c. Theorem A (m>9) — 실현 메커니즘 부재로 미증명

stage 3/5/6 삼중항 part에서 물리 증분 α(tail,head)가 span(M)∪span(active)
**밖** (8건; 예: stage 5 part 0 color 4, edge (0,5), M={03,07,26}) —
모듈러스 무관. 기록된 유일한 실현 메커니즘(D5/D7 support-tube switch)의
전제("deviation lies in S_β")가 깨져 있어, **상징 범위에서도 인증서 ⟹
스케줄의 다리가 없다**. D5/D7 anchor에서는 전제가 성립했다(전례 게이트
PASS). D9 anchor 탐색의 체크리스트에 이 절이 없었던 것 — B6/G7과 동일한
실패 모드(load-bearing 조건의 검증기 부재).

### 1d. Theorem B (보정 paired growth) — 기계 증거 0

"projection-kernel criterion saturates the new leaf"는 A3에서 깨진 종류의
문장이다. ordinary 인터페이스는 four-point 행에서 old read를 leaf에
양도하므로 budget kill(보존형 전용)에는 걸리지 않는다고 판단 — chained와의
결정적 차이. 그러나 leaf 포화·chain-field 수송은 어떤 (D,m)에서도 점별
재생된 적이 없다. **실행 가능한 게이트**: 기존 검증 기반에서 보정
ordinary step을 5→7 (m=6, 46656 — 즉시) 또는 7→9 (m=10, C++ 규모)로
재생. 이 게이트가 깨지면 아키텍처 전면 재설계, 통과하면 잔여 과제가
"seed 확보"로 압축된다.

## 2. 부분 파기 권고

### 파기: anchor 경로의 lowmod 분지 (보완이 아니라 범주 오류)

결정적 논거 — **D7(4)의 존재**: m=4 < D=7의 wild pointwise 인증서가
이미 있다. 저모듈러스 스케줄은 실현 규칙의 사정권 밖에서 사는 것이
정상이며, 규칙으로는 m<9에서 짓지 못한다(§1b). K_{9,m} 배치 절은
정합하지만 뒤에 스케줄이 없다(기계 확정). **HED(9,4)/(9,6)은 wild
pointwise 탐색으로 사냥할 것** — seam 전선이 D9(4)에서 80점 거리에
동결되어 있다(`search_snapshot_20260611/`, E=2, 순환 요약
[[65536]×3,[65456,50,30],[65536]×5]).

### 유지

- active anchor의 quotient 골격 (양 구현 독립 검증: 번들 스위트 +
  Codex C1a–C4 + 자체 의미론 검증기).
- terminal A₂ block — **번들에서 가장 단단한 부분**: m=4,6,8에서 세
  terminal 국소 return의 m²-순환까지 점별 검증, 물리 증분과의 unimodular
  binding(M=[[1,1],[0,1]]) 확인, 오염 15/15 적발.
- reserve 의미론 (Q_R∩N(C)=∅ 전 범위, ordered family 라벨링 존재).
- C_r midpoint-collision calculus (반례 0, 방전=회피 정확).

## 3. 대체 루트 (신규 기계 최소화)

### 우선 확인: pass38 자산

pass38의 고짝수 분지는 encoded bases **d=5,7,9,11** + D≥13 ordinary
step이었다. D9(m>9) seed가 검증 전통과 함께 이미 존재할 가능성이 높고,
그렇다면 새 D9 anchor의 m>9 부분은 기존 자산의 재발명이다. pass38 번들
(`/tmp/paper_versions/even_modulus_directed_tori_pass38_review_revision/`)
의 seeds/·WITNESS_LIST에서 즉시 확인 가능. pass38의 D≥13 step은 packet
재실현(embedded-base 이식 아님)이라 이번 장애 계열에 면역인 형태.

### 제안 아키텍처

| 구간 | seed/메커니즘 | 검증 상태 |
|---|---|---|
| m>9 seed | pass38 D9 기반 (또는 수선된 anchor) | 확인 필요 (재구성 게이트 전례 있음) |
| m∈{4,6} seed | wild D9 pointwise (seam 완성 또는 직접 탐색) | seam E=2 동결분 재개 가능 |
| 8 ≤ m ≤ d | modulus-free restart | 기존 스파인 |
| 전파 | C_r paired growth | **게이트 통과 후에만** |

### 미적 판정 (집필 헌장 기준)

한 문장 증명 요약 비교 — wild pointwise: "유한하므로 검사한다" ✓;
packet 재실현: "seed가 가설을 운반하므로 같은 규칙으로 다시 짓는다" ✓;
anchor-realization 다리: **현재 한 문장 요약이 없다** (정리가 아니라
조건 묶음 보고서 상태). quotient 골격·terminal A₂·C_r calculus는 어느
루트에서든 재사용되는 진짜 수학이므로 보존.

## 4. 요약 판정표

| 주장 | 판정 | 근거 |
|---|---|---|
| Signed realization theorem | 서술 오류; 가설 보강 시 lowmod 적용 불가 | §1a, 게이트 m4 |
| Theorem A (m>9) | 미증명 — 실현 메커니즘 부재 | §1c, switch-closure ledger 8건 |
| Theorem B (paired growth) | 미검증, 높은 사전 위험 | §1d, 타율 4/4 |
| lowmod anchor 분지 | 파기 — wild 탐색으로 대체 | §2, D7(4) 전례 |
| quotient 골격·A₂·reserve·C_r | 견고, 유지 | 이중 구현 녹색 |

## 5. 다음 한 수

**Theorem B 게이트** (5→7, m=6 재생, 46656 규모): 가장 값싸고 가장
결정적. 결과에 따라 — 깨짐 ⟹ 전파 엔진 재설계(아키텍처 우선순위 재배치);
통과 ⟹ 잔여 과제 = seed 확보 (pass38 확인 + wild D9(4)/(9,6) 사냥)로
압축.

## 6. 기계 근거 색인

`scripts/realize_d9_anchor_schedule.py` + `d9_realization_gate_m{4,6,8,10}
.json` (실현 게이트, 점 증인 포함); `scripts/codex_independent_d9/`
(절 수준 독립 검증 PASS); `scripts/verify_d9_terminal_a2_block.py`·
`verify_d9_marked_reserve.py`·`d9_chain_datum_fields.json` (의미론 층);
`docs/D9_ADVERSARIAL_AUDIT_20260611.md` (저자 감사);
`docs/D9_CHAIN_FIELDS_NOTE_20260611.md`. 관련 커밋: 3148d2f → c03aa78 →
53122a5 → 454190c.
