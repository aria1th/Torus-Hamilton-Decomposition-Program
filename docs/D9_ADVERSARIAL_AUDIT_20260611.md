# D9 번들 적대 감사 (저자, 2026-06-11)

저자가 직접 수행한 적대적 감사의 기록. 판정: **"매우 강한 D9 anchor
package가 생겼지만, '전체 무조건성 완료'라고 쓰기에는 몇 개의 semantic
bridge가 검증 밖에 있다."** 번들 스위트 통과(ALL VERIFIED)의 의미는
"인증서가 실현 기준의 여러 가설을 만족" 까지이며, `∀ even m≥4,
HED(9,m)` 자체의 직접 증명이 아니다.

## 살아 있는 부분 (감사 확인)

- A. active anchor: one-isolate treeing, 동시 rooted coforest, 쌍 ±1,
  삼중항 primitive A₂, 종말 (6,0,1) — 견고. stage-5 triple 장애 제거
  확인.
- B. high-even 배치(m>9): old-head transversality(quotient 수준),
  동일높이 band 분리, T/R 분리, |차| ≤ 9 ⟹ m>9 일양 — 타당.
- C. lowmod 압축(m=4,6,8): 유한 coset 분리 전수 — "배치 장애가 기반점
  선택으로 해소"의 좋은 증거.

## 7개 취약점

1. **기준의 적용 범위**: anchor-schedule realization 원 정의는
   D∈{5,7}, m>D용. D=9·모든 짝수 m으로의 확장(unit successor ±1,
   primitive A₂ packet)이 본문 정리로 미승격.
2. **terminal A₂ algebra 미검증** (감사의 결정적 실험: alignment의
   rows/permutation/signs를 무의미한 값으로 바꿔도 verifier 통과 —
   분리만 검사하고 selector/carry algebra는 출력만 함). 필요:
   (6,0,1)+⟨06,01⟩+rows [-1,0],[1,1],[0,-1]가 terminal block lemma
   입력과 일치하는지, marked comparison cycle C와 N(C)의 정의까지.
3. **endpoint reserve 의미론 미검증**: 12개 distinct point만 확인.
   원 정의는 ordered family 𝒰=(U₀,U₁,U₂,U₁^c,…,U_{d−1}^c,U_*)가
   N(C)와 기존 switching ribbon trace 밖에 있을 것을 요구. C, N(C),
   Q_R∩N(C)=∅, site label 의미 전부 기계 검사 밖.
4. **lowmod verifier는 pointwise certificate가 아님**: D7(4)/(7,6)
   인증서와 달리 실제 layer map/return 순환형을 구성·검사하지 않음.
   닫으려면 선택지 A(실현 정리 엄밀화 + 배치 가정만 검증임을 명시)
   또는 B(m=4,6,8 실제 pointwise 구성·검증). 현 번들은 A에 가까움.
5. **comparison map 하 support 닫힘 미검증**: RF2-local switch에는
   support가 comparison 순열의 궤도 합집합이어야 함. 쌍 행은 거의
   자동이나 삼중항·terminal block은 주의 필요.
6. **old-head transversality는 quotient 수준**: 실제 pre-row return
   R_{c,<r} 합성 미계산 — default-run collapse lemma 의존. signed
   unit·primitive A₂·lowmod height folding 포함 형태로 재명시 필요.
   특히 lowmod에서 height 분리가 기반점 분리로 대체되는데 이 대체와
   collapse의 비충돌도 lemma에 포함해야.
7. **HED chain fields 미명시**: 현 증명은 RHD(9,m)/marked anchor에
   가깝고, HED 승격에는 chain-datum 표 필요 — label chart W₉,
   다음 paired growth 행 (0 1)(−1 −2)/(3 4)(2 1), 𝒢⁻₁/𝒢⁻₂,
   midpoint-충돌 집합 C₁/C₂, terminal label의 성장 window 회피,
   reserve 고정-fiber 수송 형식.

## 안전한 서술 (원고용)

- 명제로: "인증서들이 signed anchor-realization 기준의 quotient/
  coforest·배치·분리 절을 모든 짝수 m≥4에서 만족한다."
- 조건부 정리로: "signed D9 anchor-realization 정리와 D9 chain-field
  assembly lemma를 가정하면 인증서가 HED(9,m)을 증명한다."
- "HED(9,m) 완전 증명"은 아직 쓰면 안 됨.

## 보강 4종 (저자 제안 — 작업 배정)

1. terminal A₂ algebra 검사 추가 → 본 레포 scripts/ 신규 verifier
   (vendor/ 원본 불변).
2. marked comparison cycle C + N(C) + reserve label 의미론 verifier.
3. D9 chain-datum fields JSON (표 형태).
4. **m=4,6,8 실제 pointwise 검증 (RF1/2/3 + 9 return [m⁸])** —
   진행 중인 종단 실현 게이트 에이전트가 정확히 이것. **실패 시 추가
   진행 중단, 저자 직접 작업으로 전환** (저자 지시).
