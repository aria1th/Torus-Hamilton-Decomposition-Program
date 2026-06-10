# 논문 개정 지원 패키지 — 발견 사항 통합 체크리스트 (2026-06-10)

새 버전 논문 개정 작업을 위한 단일 참조 문서. 각 항목: 위치(파일:라인, v28
finite-audit 소스 기준) / 상태 / 기계 검증 anchor / 개정 방향 제안.

## A. 수정 필요 (확정)

### A1. `lem:completion-fiber-bijectivity` — C_h fiber 국소화 (저자 확인 완료)

- 위치: `subtex/endpoint_successor.tex` :265–281 (`def:lifted-completion-fiber`),
  :283–298 (lemma), :300–335 (`lem:endpoint-local-row-realization`의 C_h 행).
- 내용: full cyclic row C_h를 lifted fiber(진부분 cylinder)에 치환하면 색별
  layer 전단사성이 반드시 깨짐. 증명의 image-disjointness 논증은 사이트 분리를
  쓰지만 충돌 쌍은 old-section 방향을 따름.
- Lean anchor: `EndpointChRowObstruction.lean` —
  `layerMap_bijective_iff_cylinder_invariance`(기준의 iff),
  `completionRow_substitution_not_bijective`(**parametric**: 임의 (b,m,h)·임의
  상수 기저·임의 고정좌표 cylinder), `b4_collision`(b=4 명시 충돌 쌍).
- 개정 방향: completion carry를 C_h 국소화가 아닌 다른 메커니즘으로.
  후보: (i) 상수 C_h layer(RF2 자명) + two-color swap으로 one-point carry 생성
  (`QUESTION_W2_COMPLETION_FIBER_20260610.md` Q3), (ii) rail-seam식 3색 zigzag
  (§C 참조). 추상 수준(1점 carry → 단일순환)은 Lean에서 이미 닫혀 있으므로
  (`EndpointCompletion`, `CompletionTower`) 개정은 행 실현 수준만 손대면 됨.

### A2. X₁·X₂ 교환행 — q-pin 충돌 + 지수 합 파괴 (재검수 발견, 증명 가능)

- 위치: `endpoint_successor.tex` :74–78 (`lem:endpoint-active-core`의 "한
  터미널 상태에서의 교환"), :300–335 (X_i ribbon 실현).
- 내용: X₁/X₂의 차 벡터 `e_{p_{i+1}⁺} − e_{τ_i}`가 firing support가 고정해야
  하는 터미널 좌표를 움직임 → (★) 위반(b=4,m=4 decide 가능). (★)-합법으로
  ribbon을 닫으면 터미널 m-직선을 쓸어 지수 합 = m, `gcd(m, M_i) ≠ 1` —
  product-cycle 논증 파괴. X₀만 생존(τ₀ 방향이 q-pin 회피).
- Lean anchor: 기준 자체는 `EndpointRowSchedule`/`EndpointChRowObstruction`에
  닫혀 있음. X₁/X₂ 전용 negative theorem은 미작성(요청 시 E6d 스타일로 박제
  가능 — 개정 일정에 맞춰 지시).
- 개정 방향: 교환 메커니즘 2/3 재설계. 상세 분석과 대안:
  `ENDPOint_REAUDIT_SANS_CH_20260610.md` §1a (파일명 대소문자 주의:
  `ENDPOINT_REAUDIT_SANS_CH_20260610.md`).

## B. 재서술 필요 (메커니즘은 생존)

### B1. Reset 행 — 2-점이 아니라 m-점 직선

- 위치: `endpoint_successor.tex` reset 부분 + `general_endpoint_port_room.tex`
  :52–73 (`lem:endpoint-reset-common-image`).
- 내용: 두 reset tail은 한 비교 직선 위 → (★)-합법 closure는 m-점 직선 전체.
  RF2는 그 위에서 구성상 성립, 공통 이미지 I는 swap 전후 강건(검증됨).
  support·marked-transfer 보호·μ-ledger 서술을 m-점 형태로 갱신 필요.
- Lean anchor: `EndpointPortRoom.ResetPair.common_image_eq` (parametric, 닫힘).

### B2. `lem:switching-ribbons` 합성 — 색-분리 조건 명시 필요

- 위치: `subtex/switching_ribbons.tex` (합성 보조정리).
- 내용: "support 분리 ⟹ 가환"은 ribbon들의 영향 색 쌍이 pairwise 분리일 때만
  기준-정확. 색 공유 시 layer가 ≥3값이 되어 추가 image 조건 필요. C_h 제외
  endpoint 가족 {X₀,X₁,X₂,R}은 색-분리(안전); D5(4) §11 동일-layer 치환은
  여기 해당(실측 RF2 실패 전례, `H2_REALIZATION_BLOCKER_20260605.md`).
- 개정 방향: 보조정리에 색-분리 가설을 명시하거나 ≥3값 합성 조건을 추가.

### B3. D5(4) §11 realization 문단 — certificate 미확인 기술

- 위치: `subtex/D54_parity_reset.tex` :191–198.
- 내용: 출하된 검증물(`LowD5M4Finite` dirTable)은 탐색-발견물로 논문의 다섯
  치환 구조와의 켤레 관계가 확인되지 않음. 문단을 "존재성은 별도 certificate로
  확인" 형태로 완화하거나 구조적 certificate로 교체 필요.

## C. 개정에 활용 가능한 신규 양성 결과

### C1. rail-seam 구성 (D3-even 직접 실현)

- `docs/WILDE_SEARCH_20260610.md` + `scripts/search_d3_even_dir.py` +
  인증서 m=4..12 (construct-scan은 m≤60 전수 통과).
- m−1 상수 Latin layer + wild rail-seam layer 1개; RF3는
  `T_{u_c}∘ρ_c`(translation + 2m-zigzag) 단일순환으로 환원.
- parity calculus(홀수 개 3색-얽힘 seam 필요; pair-swap 불가능 정리) + trigger
  계열 no-go 4종 — 논문의 "why hard" 서사를 정리(定理)로 승격 가능.
- §9–10 재설계(A1/A2)의 후보 문법: X-교환의 q-부착을 3색 zigzag로 우회.
- Lean 형식화 진행 중 (`D3EvenRailSeam` 등; 완료 시 H1b 홀 닫힘).

### C2. 기계 검증 완료 자산 (개정판이 인용 가능)

- H1a (`lem:terminal-cyclicity`) 완전 형식화: native_decide 없는 구조 증명
  (커밋 `43a866e`; endpoint rank list·no-collision·interval splice).
- 논문 수치 표 전수 audit: 값 단위 불일치 1건(이미 수정)·그 외 전부 일치
  (`PAPER_NUMERIC_AUDIT_20260609.md`).
- 추상 endpoint 기계 전부 닫힘: product-cycle 지수(1/m²−1), completion tower,
  부모 cycle 추출, reset common image, renewal capacity.

## D. 개정 시 형식화 측 동기화 절차 (새 논문 수령 후)

1. 새 tex 소스 diff → 변경 보조정리 목록화.
2. A1/A2 교체 메커니즘을 `EndpointRunCollapseRealization` 인터페이스와 대조,
   필요 시 인터페이스 조정 (현 홀 모양은 메커니즘-중립이라 대부분 무변경 예상).
3. audit 문서들의 paper line 참조 갱신.
4. 신규/변경 수치 표가 있으면 값 단위 재대조.

## 추가 (2026-06-10 저녁, anchor 재구성 완결에서 나온 §6/§8 정밀화 항목)

재구성 스크립트가 D5 fan(m=6/8/10/12)·D7 two-rail(m=8/10)의 RF1/2/3 전면
통과를 달성하며 확정한 산문 정밀화 2건 (기계 반례 포함):

- **B4. support forest의 label 독해는 slot**: chronological 독해는 RF2를
  깨뜨림(기계 반례: m=6, height 1, color 1). §8/부록 표 캡션에 명시 필요.
- **B5. terminal 블록 layer 표는 공유-점 ω 평가**: 세 carrier 색이 같은
  점에서 ω를 읽어야 pointwise Latin (per-color η 평가는 m=6에서 12개
  비-Latin 점 발생 — η는 collapsed-return 분석 전용임을 §6에 명시).
  cf. Lean의 `terminalDir_m4_plainChartNot_rowLatin`(같은 함정의 D3 판).
- placement 자유도: RF3는 carrier slot 배정 6종·word offset m²종 전부에
  불변(1296/1296) — κ/row-band 값은 분리·reserve 절에서만 load-bearing.
  D7 stage-5 행은 chronological (0,2,3)|(1,6),(4,5)로 확정.
- 동반 자료: `scripts/anchor_certs/` (D5_m6/m8, D7_m8 seed + 검증 출력,
  rank7 규약 + affine-base 확장) — 개정판 동반 패키지에 병합 권장.

## E. 추가 개선 기회 (2026-06-10 저녁 — 정정 아닌 품질 향상)

### E1. 재시작 corollary 단순화
`cor:modulus-free-restart`의 D₀ = m−1 경유는 불필요: m ≥ 8 ⟹ m > 7이므로
HED(7,m)이 D7 anchor에서 직접 나오고, 7에서 위로 성장하며 D = m 선을
지나면 끝. 가동 부품 하나가 줄고 증명문이 한 문장 짧아진다.
(growth 엔진 설계 검증에서 확인.)

### E2. parity 부기를 "이유" 서사로 승격 — 저자 우려(가독성·이유 제시) 직격
기계 발견된 parity 법칙 2개가 구성들의 모양을 설명한다:
- line-support layer는 홀치환 ⟺ |U|/m 홀수; 단일순환 return은 홀치환이므로
  **각 색은 홀수 개의 line-support layer가 필요** → anchor 표의 support-rank
  countdown D−r−1이 왜 그 모양인지의 이유.
- D3-even은 pair-swap만으로는 영원히 불가(3색-얽힘 seam이 홀수 개 필요) →
  terminal 블록/seam이 왜 존재해야 하는지의 이유.
§7(coforest splice algebra)에 "parity bookkeeping" 소절 하나(보조정리 2개 +
remark)를 넣으면 독자가 표를 따라가는 부담이 크게 준다.

### E3. 강건성(slack) remark
RF3는 carrier slot 배정 6종·word offset m²종 전체에 불변(1296/1296 전수 확인);
κ/row-band 값은 분리·reserve 절에서만 load-bearing. "어떤 선택이 본질이고
어떤 것이 관례인지"를 한 remark로 명시하면 검증 서사가 가벼워진다.

### E4. 동반 패키지 확장
`scripts/anchor_certs/`(D5 m=6/8, D7 m=8)를 개정판 certificates/에 병합하고,
균일성 증거로 anchor당 큰 m 하나(예: m=12)를 추가 수록. 재구성형 검증기
규약은 rank7과 동일 + affine-base 확장(문서화됨).

### E5. 표 캡션 확정 사항
D7 stage-5 행은 chronological (0,2,3)|(1,6),(4,5)로 기계 확정 — 캡션에 반영.
(B4의 slot-label 규칙과 함께 부록 표 캡션 일괄 정비.)

## F. 집필 헌장 (저자, 2026-06-10 — polish 단계 전 작업의 전제)

피할 것: 업적 대비 약화·기여 누락 / 과방어적 태도 / 비전통 수학 어휘 /
AI-assisted풍 어휘·문장 / 부자연스러운 전개 / 리터러처 리뷰 부족 / 독자가
당연히 아는 것의 과설명.

지킬 것: 방어가 아니라 증명과 예시를 쓴다 / 논문은 프로그램이 아니다 /
독자는 verifier가 아니라 인간 동료다.

모든 정리·절에 묻는 두 질문: (1) 이것은 정리인가, 조건 묶음이 잘 돌아간다는
보고서인가? (2) 증명의 한 문장 요약은 무엇인가?

적용: polish 단계의 모든 집필 에이전트 프롬프트에 이 헌장을 원문 주입.
E2(parity 소절) 초안부터 적용 — 정리와 한 문장 증명 아이디어를 앞세우고
예시를 들며 비계 언어를 제거. 리터러처 리뷰 적정성 검사를 polish 단계
점검 항목에 추가(현 §1.2 ~24편 — 커버리지 감사).
