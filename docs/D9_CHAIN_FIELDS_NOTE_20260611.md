# D9 감사 보강 1–3 결과: terminal A2 / marked reserve / chain fields (2026-06-11)

`D9_ADVERSARIAL_AUDIT_20260611.md`의 보강 4종 중 1–3을 구현한 기록.
vendor/ 원본 불변; 신규 산출물 3종 + 본 노트.

## 산출물

- `scripts/verify_d9_terminal_a2_block.py` — 보강 1. 번들 verifier가
  출력만 하던 `terminal_alignment`(rows/permutation/signs)의 실제 대수
  검증. 36 검사 전부 PASS. `--self-test`: 15종 변조(감사의 결정적 실험
  포함) 전부 CAUGHT.
- `scripts/verify_d9_marked_reserve.py` — 보강 2 + 3 검증기.
  marked comparison cycle C, N(C), Q_R∩N(C)=∅, 12-사이트 ordered family.
  90 검사 전부 PASS. `--chain-fields`: 아래 JSON의 수치 전수 검증(33).
  `--self-test`: 12종 변조 전부 CAUGHT.
- `scripts/d9_chain_datum_fields.json` — 보강 3. HED(9,m) 승격용
  chain-datum 표 (def:high-even-chain-datum 항목별).

## 의미론 근거

- terminal block: `terminal_A2_block.tex` (ω_m, F_i, lem:terminal-interlacing
  C_m, m=4 marked parents), Lean `EvenV11/TerminalA2LowMod.lean` +
  `V28Hard/TerminalA2*.lean` (m=4 궤도표·m≥6 selector 전부 직접 계산으로
  재현 일치).
- N(C) = C ∪ R_a(C) ∪ R_b(C) ∪ R_a⁻¹(C) ∪ R_b⁻¹(C)
  (`product_phase_doubling.tex` lem:phase-product-rootflat).
- family 정의: `induction_data_reserved_sites.tex`
  (def:endpoint-ready-reserve, lem:admissible-singleton-reserve),
  `coforest_splice_algebra.tex` lem:affine-reserve-plane.
- chain fields: `high_even_chain_datum.tex`, `high_even_growth.tex`
  (ordinary 행 (0 1)(−1 −2), (3 4)(2 1); lem:growth-old-generator-invariant),
  C_r 기계는 rewrite tree `check_hed_clauses.py` G7g 절 의미론 그대로
  Z/11에서 재계산.

## 핵심 검증 내용 (요지)

1. alignment rows [(−1,0),(1,1),(0,−1)]는 (a) primitive·합 0·쌍 det ±1의
   A₂ packet이고, (b) 실제 terminal triple (6,0,1)의 물리 증분
   g=((−1,0),(0,1),(1,−1)) (기저 ⟨06,01⟩)의 unimodular 像
   (M=[[1,1],[0,1]], det 1, 세 색 동시)이며, (c) D5/D7 공표 표와 동일한
   표준 datum. signs (1,1,−1)는 anchor 인증서에서 재계산한 종말 단계
   unit closing carry λ=(−1,−1,1)의 ∓ (전역 방향 반전 허용).
2. C는 carrier 평면의 표준 selector(m≥6: C_m, 쌍 (F₀,F₁); m=4:
   C₄={(0,3),(3,0),(3,3)}, 쌍 (F₁,F₂)). N(C)⊂Q_T 구조적 + Q_T∩Q_R 분리
   functional 독립 재계산(diff −3)·자체 탐색, m=10,12 직접 전수, m=4,6,8
   lowmod 배치로 K_{9,m} 전수 — **Q_R∩N(C)=∅ 전부 성립**. 차트 규약
   양쪽(direct/M-twisted) 모두 검사.
3. family labeling: **유효한 labeling 존재** — 고짝수 인증서의 row-major
   {0..3}×{0..2} 격자 명명이 정의의 모든 절(12=d+3, 역할 3+8+1, 계수
   distinct ⟹ 모든 짝수 m≥4 distinct, fixed-fiber, N(C)·carrier 분리)을
   만족.

## 발견 (저자 확인 권장)

- **F9**: D5/D7 고짝수 표의 renewal 단일-fiber 배치(U_j^c=(j−1,1))는
  d=9의 4×3 격자에서 불가능(a-범위 0..7 필요). row-major 규약(= d=7
  lowmod rank-3 인증서 규약)으로만 확장됨 — 표기 규약 충돌이지 수학적
  장애는 아님.
- **F10**: lowmod 인증서는 family 라벨 없이 U0..U11만 기록(또한 m별
  계수 격자 모양이 제각각: 3×4, 2×6, 1×8+1×4). 위치 기반 정규 라벨링은
  검증 통과하나 인증서 자체가 ordered family를 운반하지 않음.
- alignment의 rows/permutation/signs에는 번들·논문·Lean 어디에도 형식적
  정의가 없음(Lean `D7TwoRailRelay.TerminalAlignment`도 무제약 데이터).
  본 검증기는 위 (a)–(c)+λ-carry로 고정했으나, "N·Δ_i = s_i·row_i" 식의
  자연스러운 읽기로는 일관 부호가 (1,−1,1)이지 공표값 (1,1,−1)이 아님 —
  signs의 공식 정의 명문화 필요.

## chain JSON의 UNDERIVABLE 항목 (저자 입력 필요)

1. 재라벨링 Z/9→Z/11∖{0,3}의 구체 사상(질서보존 열거를 제안값으로 수록;
   논문은 라벨 집합만 고정).
2. G⁻_r 범위: ledger 종말 stage-7 active(02,24,38,57)의 포함 여부(D7
   전례는 최종 stage pair active 포함; 본 표는 포함).
3. carrier 출력 라벨 {5,6,7}(미사용 {5,6,8,7} 중 선택; 논문 예시값) 및
   incoming selector의 carrier 재배치(U0,U1,U2 terminal exchange) 기제 —
   번들 인증서에 미표현. 제안 재라벨링 하에서 anchor carrier {0,1,6}의
   像 {1,2,8}은 성장 window와 교차하므로 재배치가 실제로 필요.

## 재현

```bash
python3 scripts/verify_d9_terminal_a2_block.py            # 36/36
python3 scripts/verify_d9_terminal_a2_block.py --self-test
python3 scripts/verify_d9_marked_reserve.py               # 90/90
python3 scripts/verify_d9_marked_reserve.py --chain-fields # 33/33
python3 scripts/verify_d9_marked_reserve.py --self-test
```
