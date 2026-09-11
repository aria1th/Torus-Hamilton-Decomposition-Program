# E5 seed의 실제 incidence parity

후속 entry와 최종 조립은 [E5 완료 기록](E5_COMPLETION_20260911.md)에 있다.
아래 완료 범위와 남은 작업은 이 문서의 단계별 검증 시점 기준이다.

`Seed.incidence_even`은 모든 p≥2, 짝수 m≥4에서 합성 seed의 세 방향 모두에 대해
실제 `blockSupport xChart`의 `EvenComponents`를 증명한다. 이 정리는 이미 완료된
`Seed.replacement_hamilton`과 함께 entry 조립에 사용할 구체적인 입력이다.
Matched selection과 active voltage의 일치, p별 entry 조립은 아직 남아 있다.

## 증명 구조

`NumericRows.lean`은 `ZMod.val`을 사용하여 실제 shell 선택과 방향을 자연수 행 표에
연결한다. Core 회로는 방향 표와 `(w−max(h−2,0)) mod 2`로 구분한다.
`support_eq_nat`는 모든 실제 행에, `support_natCast`는 h,w<m인 자연수 행에 적용된다.
따라서 높이·행 번호 0·1·2·3의 membership 증명을 모든 m≥4에 전달할 수 있다.

`Collar.Incidence.evenComponents_of_pairs`는 전체 열을 둘씩 짝지은 전단사와 각 pair의
동일 성분 소속에서 성분별 짝수성을 얻는다. p≥4에서는 shell의 원래 완전 짝짓기와
core pair `(F₀,F₂,₁)`, `(F₁,F₂,₀)`를 결합한다.

- x·y 방향: shell의 selected·complementary row coherence를 전체 seed support로
  전달한다. 각 auxiliary pair의 두 endpoint가 해당 방향을 쓰는 행을 갖기 때문에
  같은 성분에 속한다. Core pair는 높이 0·1·2·3의 구체적인 행과 B₀/B₁로 연결한다.
- w 방향: A₀와 A₁을 거쳐 모든 auxiliary 색을 연결하고 네 core 회로를 붙인다.
  `w_connected`는 이 방향의 전체 연결성을 모든 p≥2에서 증명한다.

p=2·3에는 `Small.lean`의 명시적인 forest와 짝짓기를 쓴다. Rank는 parent를 따라
엄격히 감소하며, 모든 parent edge는 0≤h,w<4인 한 support 안에 있다.
`SmallCertificate`는 각 edge와 pair의 공통 root를 커널 `decide`로 검사한다.
`eq_root_of_descent`와 실제 행 대응을 적용하면 같은 pair의 열은 실제 incidence에서도
같은 성분이다. 짝짓기는 다음과 같다.

| p | 열의 pair 목록 |
|---|---|
| 2 | (F₀,F₂,₁), (F₁,B₀), (A₀,B₁), (F₂,₀,A₁) |
| 3 | (F₀,F₂,₁), (A₁,B₂), (F₁,B₀), (A₀,B₁), (F₂,₀,A₂) |

이 증서는 작은 p의 **유한 행 패턴**에 대한 것이며, m=4의 전체 토러스 검사로
일반 m을 대체하지 않는다. `support_natCast`가 임의의 짝수 m≥4로 전달하는 근거다.
`Seed.evenComponents_all`이 작은 두 경우와 p≥4를 합치고, 기존 `evenComponents_iff`가
실제 회로 quotient로 옮겨 `incidence_even`을 준다.

완료 범위는 closure가 요구하는 parity 결론이다. 원고 `lem:seed-incidence`의 p≥4
전체 연결성과 `lem:small-seed`의 정확한 성분 분류는 이 증명에서 모두 계산하지 않았다.
Mate incidence 삭제 뒤의 residual parity도 별도의 미완료 입력이다.

## 검증과 복구

CPU `lake build TorusEven` 통과(8478 jobs), 새 코드 경고 0개. Isolation 통과:
main-path 120개, attic 4개, 등록된 native 파일 3개. 새 공개 선언 47개는 모두
`propext`, `Classical.choice`, `Quot.sound`의 부분집합만 사용한다. 새 `sorry`, `admit`,
author axiom, `native_decide`는 없다. 조건부 전체 차원 endpoint의 기존 axiom 집합은
native leaf 18개를 포함해 그대로다.

제어 노드와 CPU 사본의 소스 121개(root 포함)의 SHA256이 일치한다. Lean과 mathlib,
노드 경로는 [shell 기록](SHELL_PROGRESS_20260911.md)과 같고 기존 mathlib 캐시를 사용했다.
Audit 소스와 axiom 출력은 `evidence/lean_audit_20260911/incidence/`에 있다:
[audit 소스](../evidence/lean_audit_20260911/incidence/IncidenceAudit.lean),
[axiom 출력](../evidence/lean_audit_20260911/incidence/axioms.log).
