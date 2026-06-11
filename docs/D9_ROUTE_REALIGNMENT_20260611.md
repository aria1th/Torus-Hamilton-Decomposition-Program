# D9 전면 경로 재정렬 (2026-06-11)

저자 제공 `d9_all_even_proof_bundle_20260611`(vendor/에 편입, tar sha256
`f92118e5…af63c9`)이 증명 아키텍처를 재편한다. 이 문서는 (i) 새 구조,
(ii) 검증 상태, (iii) Lean 스파인 재정렬 계획, (iv) 결정적 잔여 기계
게이트를 기록한다.

## 1. 새 아키텍처

```
HED(9,m)  [모든 짝수 m ≥ 4]
  ├─ m > 9 : 상징적 D9 anchor (분리 상수 |·| ≤ 9 ⟹ m>9 일양)
  │    = active anchor(quotient 골격, 모듈러스-무관)
  │    + affine splice 배치 ledger (높이 shift {2,1,8,0,5,4,7})
  │    + terminal/reserve frame (q_T+⟨06,01⟩, q_R+⟨24,35⟩, 12 사이트)
  ├─ m ∈ {4,6,8} : 유한 배치 인증서 (동일 골격, K_{9,m} 전수 검증;
  │    28 splice supports + T/R + 12 사이트, 분리 전수)
  └─ (C_r-보정 paired growth) ⟹ HED(d,m), 홀수 d ≥ 11, 모든 짝수 m ≥ 4
       (행당 midpoint 충돌 ≤ 2 ⟹ 금지 phase ≤ 6 ⟹ D ≥ 11에서 존재)
```

- **chained 7→9는 아키텍처에서 완전 제거** (A3 반증의 최종 처리).
- conjugate seam 전선(E=2, `search_snapshot_20260611/`)은 HED(9,4)의
  **대체 경로 후보**로 격하 보존.
- D7 기반(HED(7,4)/(7,6))은 odd d=7 자체와 d≤7 범위에만 남음.

## 2. 검증 상태 (2026-06-11)

- 번들 자체 스위트: ALL VERIFIED (상징 3종 + lowmod 1종) — 재현 완료.
- 첫 번들(`d9_high_even_…`)과 상징 인증서 3종 byte-identical.
- 독립 적대 재검증: Codex(GPT-5.5)가 증명 노트만으로 자체 검증기 작성
  중(/tmp/d9_codex_test, 검사 명세 C1a–C4) — 검증기-구현 독립성 확보용.
- **미검증 핵심**(아래 §4): "인증서 절 ⟹ 실제 RF1/2/3 스케줄" 실현
  정리는 논문 수준 주장 — 종단 기계 게이트 필요.

## 3. Lean 스파인 재정렬

현 스파인 구멍 2개의 내용이 모두 새 경로로 흐른다:

- `assume_oddHighModulus` (H5): D9 상징 anchor + paired growth가 본체.
- `assume_oddLowClosure` (H6′): chainPropagation(m∈{4,6}, D7 입력)은
  **D7 입력 없이** HED(9,m) 유한 인증서 + paired growth로 방출 가능;
  modulusFreeRestart도 동일 경로가 대체 가능(8≤m≤d ⊂ 위 커버리지).
  어댑터 정리로 기존 인터페이스를 그대로 방출(스파인 무변경 원칙 유지,
  rail-seam 때의 `oddEndpointPromotion_of_oddLowClosure` 패턴).

형식화 모듈 계획 (순서대로):
1. `D9AnchorCert.lean` — 인증서 데이터 타입 + Bool 절 audit
   (`_holds` bridge + `ofBool`; m∈{4,6,8}은 native_decide 후보 →
   게이트 인벤토리 절차).
2. `D9AnchorRealization.lean` — 실현 기준 ⟹ RF1/RF2/RF3 (§4 게이트
   통과 후 설계; interval-splice/skew 기계 재사용: 쌍 행 = rank-1
   ±1 splice ⟸ 기존 `single_cycle_of_interval_splice`, 삼중항 =
   unimodular A₂ ⟸ TerminalA2 기계).
3. `PairedGrowthCr.lean` — C_r midpoint-충돌 보조정리 (GuideLocality의
   endpoint-collision 형식이 이미 정합 — 검증기 G7g가 절 모양 제공).
4. `Main.lean` 어댑터 — 두 sorry를 새 경로로 방출.

## 4. 결정적 잔여 기계 게이트 (Lean 착수 전 필수)

번들은 인증서가 **실현 기준의 절**을 만족함을 검증하지만, 절 ⟹
HED(9,m)의 실현 정리 자체는 검증 대상이 아니다. 종단 게이트:

> m=4 (section 4^8=65536, 기존 replay 규모)에서 인증서 데이터로 실제
> D9 root-flat 스케줄을 **구성**하고 RF1/RF2/RF3 + marked 구조를 직접
> 검증한다. m=6(6^8≈1.7M)은 C++ 또는 샘플링, m=10(상징 범위 대표)도
> 동일 패턴.

전례: `scripts/reconstruct_high_even_anchor_schedules.py` (D5 fan/D7
two-rail에서 동일 게이트 PASS). 이 게이트가 실패하면 그것이 곧 다음
중대 발견이다(W2/A3 패턴 — 증명이 인증서를 반영하는가의 검사).

## 5. 논문 측

- 번들 appendix/ LaTeX insert 2종 + lowmod note가 개정판 삽입 후보.
- PAPER_REVISION_SUPPORT §A3/A4의 "산출물 B(직접 HED(9,m) family)"가
  실현된 형태 — §A4 권고(삭제/강등 목록)와 정합.
- AI disclosure: D9 경로 자체는 저자+GPT-5.5 Pro 작업(추정 — 저자
  확인 필요); 본 레포의 기여는 반증(A3)·C_r 검증·독립 재검증·종단
  게이트로 기록.
