# E5 matched selection

후속 entry와 최종 조립은 [E5 완료 기록](E5_COMPLETION_20260911.md)에 있다.
아래 완료 범위와 남은 작업은 이 문서의 단계별 검증 시점 기준이다.

`Collar.Incidence.MatchedData.exists_selection`은 원고 `lem:matched`를 증명한다.
지정된 서로 다른 anchor 블록과 eligible mate, active 사건 행, residual 성분마다
짝수 개의 nonmate라는 조건에서 정확한 절반 quota, 모든 열의 ±1 carry, 양쪽
폭이 2 이상일 때의 coherence를 갖는 선택을 만든다. `active_card`는 각 active 열의
실제 선택 수가 1임을, `mem_pattern_left`는 선택 위치가 지정된 anchor와 사건 행
하나뿐임을 증명한다. 실제 seed의 mate 삭제 후 parity는 다음 단계에 남아 있다.

## 증명 구조

`EvenOnComponents A target`은 지정된 열 집합만 성분별로 짝수임을 뜻한다.
`exists_parity_join_on`은 target 열에서 홀수, 다른 열과 블록에서 짝수인 parity join을
만든다. `exists_mixed_orientation`은 홀수 차수 정점에만 hub edge를 추가하여 target에서
±1, 나머지 정점에서 0인 divergence를 준다. 이를 블록의 pair에 적용하는
`exists_directed_pairs_on`이 residual 선택을 제공한다. 기존 전체 열 parity join,
odd orientation, directed pair API는 target을 전체 집합으로 두는 특수화로 보존했다.

`MatchedData`는 anchor/mate 단사성, active 블록 일치, mate membership을 데이터로
받는다. Mate incidence는 지정된 블록에서만 삭제한다. `quota_bounds`와
`exists_fillers_of_quota`가 anchored/unanchored 블록의 서로 다른 quota를 채운다.
`Collar.switchedRow`는 사건 행에서 active를,
그 외 행에서 mate를 넣는다. `pattern_sum`은 이 예약 슬롯의 기여를 active +1,
mate −1로 분리하며, `auxiliary_carry`가 residual divergence와 결합한다.

Residual pair 사건은 unanchored 블록에서 rank 0·1, anchored 블록에서 rank 1·2를
사용한다. Anchored rank 0의 active 행과 rank 3의 residual 행은 같으므로, 해당
child 폭이 2 이상이면 공통 residual 원소로 연결된다. Complement에는 같은 논리를
반대 예약 색에 적용한다. 이 네 rank의 구별에 m≥4를 쓰며, 일반 선택 정리 자체는
m이 짝수라는 가정을 요구하지 않는다.

## 검증

CPU `lake build TorusEven` 통과(8485 jobs). 새 코드 경고 0개, isolation 통과:
main-path 127개, attic 4개, 등록된 native 파일 3개. 새 공개 선언 60개를 포함한
97개 선언의 axiom을 검사했다. 새 선언과 기존 선택 API, `even_degree_collar`는 모두
표준 axiom만 사용한다. 조건부 전체 endpoint의 기존 native leaf 18개는 그대로다.
Root를 포함한 소스 128개의 SHA256이 CPU 사본과 일치하며 컴파일 산출물도 회수했다.

Audit 소스와 axiom 출력은 `evidence/lean_audit_20260911/matched/`에 있다:
[audit 소스](../evidence/lean_audit_20260911/matched/MatchedAudit.lean),
[axiom 출력](../evidence/lean_audit_20260911/matched/axioms.log).
Lean·mathlib와 실행 경로는 [shell 기록](SHELL_PROGRESS_20260911.md)과 같다.

다음 작업은 실제 seed의 mate 자격·단사성, mate 삭제 뒤 residual parity,
실제 `BlockSelection`과 `anchorVoltage`의 일치, entry와 closure 조립이다.
`EvenOddDegreeGoal`은 아직 열려 있다.
