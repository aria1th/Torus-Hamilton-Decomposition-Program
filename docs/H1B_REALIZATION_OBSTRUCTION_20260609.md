# H1b realization — tame 경로 차단 분석 (2026-06-09)

H1a 닫힘 직후 H1b(`TerminalA2RootFlatRealizationFamily`) 착수 과정에서, H2
blocker(`H2_REALIZATION_BLOCKER_20260605.md`)와 동형이되 더 정밀한 두 가지
장애를 도출했다. 결론: **sectionEquiv는 선형(tame) 불가 — wild 재색인이
필수이고, 이는 m ≡ 0 (mod 3)인 짝수 m(6, 12, …)에서 차트 수준에서 이미
증명 가능한 장애다.**

## 1. 장애 A — 선형 차트의 mod-3 격자 장애

물리 토러스 (ℤ/m)³의 단위 스텝 e₀,e₁,e₂를 임의 선형 차트로 K=(ℤ/m)²에
내리면 세 이미지 u₀,u₁,u₂는 u₀+u₁+u₂=0을 만족한다. 한 주기(m 스텝)의
변위는 Σkⱼuⱼ (Σkⱼ=m, kⱼ≥0)이고, (a,b)-좌표로 풀면 **3k₂ = m − a − b** 꼴의
정수 조건이 나온다:

- m ≢ 0 (mod 3): 대표원 선택(±m 이동)으로 항상 해소 가능 — 장애 없음.
- **m ≡ 0 (mod 3)**: 주기당 드리프트 (a,b)는 a+b ≡ 0 (mod 3)을 강제.
  그러나 terminal 기본 드리프트 Δ₀=(0,1)은 a+b=1 ≢ 0. **모순.**

따라서 m ∈ {6, 12, 18, …}에서는 어떤 선형 sectionEquiv로도
`returnMap = e ∘ F_i ∘ e⁻¹`가 불가능하다. (m=6은 짝수 범위의 두 번째
원소이므로 family 전체가 즉시 차단된다.)

## 2. 장애 B — 선형 shear의 Latin 방향 예산 모순

shear S(x,y)=(x,x+y)는 아홉 변위 클래스의 스텝 수를 모두 ≤ m로 만들어
변위-총량(H2 blocker §1) 검사는 통과한다. 그러나 Latin 조건은 모든 (t,z)
셀에서 세 색이 {α, β, 0}을 정확히 하나씩 쓰도록 강제하므로, 색·시작점 합산
α-스텝 총량은 정확히 **m³**이어야 한다. 반면 S-켤레 변위 클래스가 강제하는
주기당 스텝 수(mod-m 모호성이 n_α+n_β ≤ m로 고정됨)를 전수 합산하면:

- 색 0: 2m(m−1), 색 1: m²+m, 색 2: m²+m → **총 4m² − 2m + 2m = 4m² ≠ m³** (m ≥ 6).

즉 변위 보존(선형) 동치로는 Latin 스케줄 자체가 존재할 수 없다. 이는 H2
blocker의 "저변위 returnMap vs 고변위 추상 return" 논증의 가족 단위 정밀화다.

## 3. 의미 — H1b의 실제 난이도와 올바른 경로

- 논문 `lem:terminal-latin`의 한 문단 증명("multiplying the physical rows
  over one terminal period…")은 이 wild 대응의 구성을 암묵에 묻는다. §1·§2에
  의해 그 대응은 **본질적으로 비선형 run-collapse 재색인**이며, H2에서
  관측된 것과 같은 종류다(H2는 유한이라 native witness로 우회했지만 H1b는
  무한 family라 우회 불가).
- 올바른 경로(H2 blocker §4(B)의 family 판): 물리 스케줄 dir(default run
  전개)와 run-collapse `e`를 **함께 구성**하고 색별 conjugacy를 증명.
  주목할 단서: H1a interval-splice가 만든 (구간 label, offset) 좌표가
  정확히 default run의 collapse 좌표다 — `e`의 후보 원료. 단, 현 구조는
  **색 공통 단일 e**를 요구하므로 세 색의 구간 구조를 동시에 존중하는
  공통 재색인이 필요하다. 이것이 H1b의 진짜 수학적 핵심이다.
- 이 분석은 §1, §2를 Lean negative theorem으로 기록할 수 있다
  (H2의 `not_terminalCoreTailPrefixPathGoal` 전례). 우선순위는 낮음.

## 4. 전략 조정 (2026-06-09)

H1b는 위 wild-e 구성이라는 미해결 설계 문제에 차단돼 있으므로, 계획 순서를
조정한다: **H6(요청 E, endpoint successor) → H5(요청 C+D) → H1b**. 근거:

1. H6의 숨은 H1a 의존성은 오늘 H1a 닫힘으로 해소됐다.
2. H6은 phase-product 기계가 대부분 sorry-free로 준비돼 있고, audit
   (`PAPER_NUMERIC_AUDIT_20260609.md` §4)이 필요 구조 9종을 구체화해 놓았다.
3. H5는 섹션 전체 이식 + RHD refactor로 가장 크다.
4. H1b는 wild-e 구성의 수학적 설계가 선행돼야 하며, 그 설계에는 H1a
   interval 좌표가 원료로 쓰일 가능성이 있어 숙성 기간이 유익하다.
