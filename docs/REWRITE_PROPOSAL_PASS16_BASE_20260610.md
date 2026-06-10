# 논문 재작성 제안서 + 심사 — pass16_special57 기준 (2026-06-10)

입력: pass16_special57(기준), pass38(소실 정보 원천), rank7 인증서 패키지,
그리고 Lean 형식화가 확정한 사실들(반례 2건, 값 대조, 닫힌 기계).
분석 원문: pass16/pass38 조사 보고(세션 기록, 에이전트 2건).

## 0. 한 줄 결론

pass16의 뼈대(인증서-조건부 귀납 + endpoint 폐기)는 **이미 옳다**. 재작성은
(1) pass38의 pointwise 인증서 3종 + 인증서 프레임워크를 재수입해 조건부를
무조건으로 바꾸고, (2) 깨진 folded 잔재와 죽은 장식을 전부 삭제하고,
(3) growth 사슬을 pass38의 검증된 창(D9/D11 anchor + D≥13)으로 교체하면
된다. endpoint successor는 **완전 삭제**를 권고한다(심사 §3).

## 1. 완전 삭제 목록 (rationale 포함)

| 대상 | 근거 |
|---|---|
| `unused/` 전체 (endpoint_successor 509줄, b4_chart 84, site_separation 154) | 두 버전 모두에서 최종 증명 무관. Lean 반례 2건의 서식지. pass16이 이미 격리 — 삭제로 승격 |
| `rank_three_coordinate_model.tex`, `rank_three_site_avoidance.tex`, `rank_three_endpoint_summary.tex` | 죽은 folded 경로의 장식(TikZ 포함). 인증서 수입 후 무의미 |
| `rank_three_site_selection.tex`의 양성 주장부(:1–152, :299–327 — `lem:folded-site-realization`, (P1)–(P4) 배치) | **Lean이 반증한 교환행 배치와 중첩** — 증명으로 생존 불가. no-go(:253–275)와 탐색 감사(:277–297)만 인증서 부록으로 이전 |
| `prop:rank-three-output-datums` (`rank_three_output_datum.tex`:30–34) | 미완 골격에 기대 과잉 주장. 인증서 정리로 대체 |
| special 5→7 블록 (`high_even_growth.tex`:755–851) + `explore_special_five_seven_terminal_words.py` | 자체 status remark가 "최종 증명 미사용" 명시. gcd(5,m²)=1 관찰만 한 문단 remark로 |
| `D54_parity_reset.tex`의 realization 문단(:191–198) — 가능하면 절 전체를 인증서로 대체 | 재검수 B3: certificate 미확인 기술. pass38의 D5(4) pointwise 인증서((0,1), C={48}→57)가 증명-of-record |
| pass16의 chained 7→9 step + D≥11 paired window (`high_even_growth.tex` 해당부) | §2-3의 교체안 채택 시. pass38 분석이 "less audited" 판정 — 새 기계 대신 검증된 anchor |
| 미참조 label 67개, pass38 App D/E(라우터 가족·edge-case 표) | 위생. pass38 스스로 "not required" |

## 2. 재수입 목록 (pass38 → 새 판)

1. **D7(4)/D7(6)/D5(4) pointwise 인증서** — thm:finite-inputs 산문(1637–1663),
   (P1)–(P4)(776–787), 디코딩 규약(802–810), seeds+witnesses(byte-identical,
   `rank7_cert_pass38/certs/`), 준비된 `latex/low_modulus_rank7_rootflat_
   certificates.tex`(이스케이프 손상 수리 필요: `egin`→`\begin` 등).
   `final_induction_framework.tex`:100의 인용처를 이것으로 교체 →
   **main theorem 무조건화**.
2. **인증서 프레임워크 + 재현성 부록** — def:certificate-predicate-packages,
   prop:finite-verification, cor:certificate-use + 의존 지도(759–885),
   App. B(3581–3616)의 WITNESS_LIST/FILE_LIST + 이중 SHA-256 매니페스트 규율.
3. **재구성형 검증기 패턴** — pass38 `verify.py`(전체 section 위 RF1–RF3 재구성
   검사). v28의 `verify_finite_checks.py`(표 산술만)는 보조 감사로 강등.
   **folded 오류가 살아남은 이유가 정확히 이 차이다** — 표 검사기는 return map을
   재구성하지 않는다.
4. **D9/D11 encoded seeds + lem:good-centre(D≥13)** — §3 심사 채택 시.
5. (조건부) pass38의 b≥4 endpoint realization 증명(2889–3107) — §3에서
   기각하더라도, **서고 보존**(별도 supplement)을 권고: 건전한 증명이고
   미래의 차원 확장에서 재사용 가치.

## 3. 심사 — 갈림길 판정

### 3-1. endpoint successor: 폐기(pass16) vs 복원(pass38 b≥4) → **폐기 권고**

- pass16의 대체 경로(D₀=m−1 재시작 + `lem:growth-modulus-free` + chain
  propagation)는 case-exhaustive로 확인됨(pass16 분석 §2).
- 아름다움 기준: endpoint 기계 ~650줄(+RF2 ledger 의무 일체)이 통째로
  사라진다. 정리 사슬도 "유한 인증서 + 성장"이라는 단일 서사로 수렴.
- 위험: 대체 경로가 의존하는 growth 사슬의 감사 수준 — §3-2로 해소.
- 단서: 폐기하더라도 pass38의 건전한 endpoint 증명은 supplement로 보존
  (§2-5). Lean 측에도 동일 판정 적용: 현 H6 홀(`assume_oddEndpoint
  Realization`)은 새 아키텍처에서 **불요**해진다.

### 3-2. growth 사슬: pass16의 7→9 chain + D≥11 창 vs pass38의 D9/D11
anchor + D≥13 창 → **pass38 교체 권고**

- pass16의 7→9 chained step과 D≥11 paired window는 v28 계열의 신작으로
  pass38 수준의 기계 검증이 없다. 반면 pass38은 D=5,7,9,11 네 anchor를
  (H1)–(H7)로 전수 검증했고 good-centre 분석이 D≥13 창을 증명한다.
- 교체 시 순효과: 새 증명 의무 0(전부 기존 검증물), 본문은 오히려 단순
  ("anchors는 4 ≤ D ≤ 11 홀수 전부, growth는 D ≥ 13 균일").
- 절충 fallback: 7→9 chain을 유지하고 싶다면 — Lean 측 displacement 예산
  검사(이번 세션에서 모든 사각지대를 잡아낸 그 검사)를 선행할 것.

### 3-3. D5(4): parity-reset 구성 vs pointwise 인증서 → **인증서를 증명으로,
구성은 exposition으로**

- parity-reset은 folded와 같은 "derived 스타일" 계열이고 realization 문단이
  certificate 미확인(B3). 인증서는 즉시 검증 가능.
- 단, parity-reset의 서사 가치(W=F₁F₂F₀ 16-cycle, reset 기하)는 남기되
  "구성 스케치 + 인증서가 증명" 구조로.

### 3-4. 검증 한 건 선행 필요 (병합 전 유일한 TODO)

pass16의 HED(7,m)는 reserve singleton + chain field 절을 포함하는데, rank7
README는 reserve에 침묵한다. `D7_m6_seed.json`에는 chain field 5종이 있음이
확인됐으나(분석 §1), **reserve 절의 witness-level 확인**이 병합 전 필요:
`verify_rank7_rootflat_certificates.py`를 확장해 pass16의 HED 정의
(R1)–(R4) 절을 직접 검사하거나, 부족 시 그 절만 보강 탐색.

### 3-5. 용어·label 위생 (재작성 시 일괄)

- "completion sites"(reserve 어휘, 생존) vs "completion rows"(폐기된 기계)
  동음이의 분리 — 전자를 "renewal sites" 등으로 개명 권고.
- 경계 재사용 label 2건(`lem:endpoint-active-core`,
  `lem:no-localized-full-completion-row`)은 unused/ 삭제로 자동 해소되나,
  개명 이력을 변경록에 명시.

## 4. 목표 아키텍처 (새 판 차례 제안)

```
§1 서론 (parity 장애, 문헌, 아키텍처 — pass16 유지; '인증서+성장' 서사로 §1.3 갱신)
§2 root-flat 사전 + RF criterion        (유지)
§3 switch calculus + ribbons            (유지; 합성 보조정리에 색-분리 가설 명시 ← Lean 재검수 B2)
§4 marked/reserve 사다리 (HD/RHD/HED)   (유지; 어휘 정리, '다음 endpoint 확장' 잔재 제거)
§5 곱·phase-doubling                    (유지)
§6 terminal A₂ 블록 → D3 even base      (유지; Lean 완전 검증 사실 + rail-seam 대안 각주)
§7 coforest splice algebra              (유지 — pass16 신작, 잘 쓰임)
§8 인증서 프레임워크                     (pass38 재수입: (P1)–(P4), 디코딩, prop:finite-verification)
§9 유한 기반: D5(4)·D7(4)·D7(6)         (pass38 인증서 = 증명; D54 구성은 스케치로)
§10 high-even anchors D5/7/9/11          (pass16 표 + pass38 D9/D11 seeds)
§11 growth: paired D≥13 + modulus-free 재시작 (pass38 창 + pass16 재시작 정리 — 3곳 서사를 정리 1개로 승격)
§12 최종 동시 귀납                       (pass16 구조, 무조건화)
§13 토의
App A 인증서·검증(재구성형 verify + 매니페스트; no-go 보조정리 + 탐색 감사 이전 수용)
App B anchor 표 (현 A–D 병합: summary는 A로, D(검증)는 A로)
App C folded 단어 W₄/W₆ (유지 — 독립 가치)
[supplement] pass38 endpoint 증명 보존
```

병합 지침: `finite_high_even_anchor_summary` → App B로; 현 App D → App A로;
modulus-free 재시작 서사 3곳(abstract :67, intro :222–224, discussion
:418–420) → §11의 정리 하나로.

## 5. 추정 효과

- 삭제: unused/ 747줄 + rank_three 장식 ~500 + special57 ~100 + chained
  growth부 + D54 realization 문단 등 — **본문 ~1,300줄 이상 감축**, 페이지로
  최소 1/5 추정.
- 획득: main theorem 무조건화, 모든 유한 입력이 "재구성형 검증기 + 매니페스트"
  규율 아래 통일, 증명 서사 단일화("유한 인증서 + 균일 성장").
- Lean 동기화: H6 홀 폐기, H5를 새 §10–11 구조로 재정렬(anchor 인증서 수입 +
  D≥13 growth + 재시작) — 남은 형식화 전선이 단일 트랙으로 수렴.
