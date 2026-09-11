# E5 auxiliary shell과 합성 seed

후속 entry와 최종 조립은 [E5 완료 기록](E5_COMPLETION_20260911.md)에 있다.
아래 완료 범위와 남은 작업은 이 문서의 단계별 검증 시점 기준이다.

원고 `lem:shell`의 Hamilton factorization을 구성하고 near-core와 합성했다.
`p≥2`, `m≥4`에서 모든 auxiliary 색이 Hamilton이다. 짝수 m에서는 seed의 회로 열이
네 core 회로와 2p개 보조 색으로 식별되며, anchored star replacement 뒤의 모든 색이
Hamilton이다. E5 전체와 `EvenOddDegreeGoal`은 아직 열려 있다.
후속 [incidence 기록](INCIDENCE_PROGRESS_20260911.md)에서 실제 seed의 성분별 짝수성도
모든 p≥2, 짝수 m≥4에 대해 증명했다. 아래는 shell 단계 당시의 검증 경계다.

## 증명된 결과

| Lean 선언 (`TorusEven.Entry` 아래) | 결과 |
|---|---|
| `Shell.pairs`, `fillers`, `pairEquiv` | 원고의 순서 있는 pair·filler 목록, 각 보조 색이 정확히 한 pair에 속함 |
| `Shell.wVoltage_sum`, `yVoltage_sum` | 첫 lift에서 A는 −1, B는 +1; 두 번째 lift에서 각 pair endpoint는 ±1 |
| `Shell.factorization`, `hamilton`, `xChart_consistent` | 폭 `(p−⌊p/2⌋,⌊p/2⌋,p)`의 실제 Hamilton factorization과 블록 일관성 |
| `Shell.selected_coherent`, `complement_coherent` | p≥4에서 각 높이의 selected·complementary 행 모두 coherent |
| `Seed.factorization`, `width`, `activeSeparated` | 폭 `(p−⌊p/2⌋+1,⌊p/2⌋+1,p+1)`의 합성 seed와 active 분리 |
| `Seed.circuitCount_left`, `circuitCount_right`, `labels`, `circuitLabel_card` | 한 색은 두 회로, 다른 색은 한 회로; 전체 회로 열 수 2p+4 |
| `Seed.replacement_hamilton` | 기존 anchored star를 적용한 합성 seed의 모든 색이 Hamilton |
| `Seed.support_eq`, `mem_blockSupport_left`, `mem_blockSupport_right` | 명시적인 support 표와 실제 orbital block support의 정확한 대응 |
| `Seed.evenComponents_iff` | support 표의 성분별 짝수성과 실제 seed incidence의 성분별 짝수성이 동치 |

Shell은 `Aᵢ=i`, `Bᵢ=p+i`로 색을 표현한다. 높이 0·1·2의 pair 목록, pair index 1에서
w=1인 사건과 나머지 pair의 w=0 사건, 원고의 순서로 채운 filler를 그대로 사용한다.
`LocalPairs.row`를 재사용하여 정확한 quota와 carry를 얻는다. Shell 자체의 정리들은
짝수성 가정 없이 모든 m≥4에 성립한다.

`Collar.MultitorusFactorization.superpose`와 `Recolouring.superpose`는 palette의 합타입으로
두 factorization과 왼쪽 palette의 recolouring을 합성하는 일반 도구다. Width는 더해지고,
회로 열은 두 회로 열 집합의 합으로 식별된다. 오른쪽 색의 step이 원래대로 보존됨을
증명하여 shell Hamilton성과 기존 `Star.replacement_hamilton`을 결합했다.

`Seed.support`는 `Fin 4 ⊕ Fin (2*p)` 위의 명시적 유한집합이다. 앞의 두 core 색은
단일 회로이고, 세 번째 색은 `NearCore.baseDefect`의 0·1 값으로 나뉜다. 이 표가
실제 `blockSupport xChart`를 `Seed.labels`로 재색인한 것임을 증명했다. 따라서
다음 성분 계산은 물리 step의 실제 회로에 적용할 수 있다. **성분별 짝수성 자체는
아직 증명하지 않았다.** Matched selection, mate 삭제 뒤의 성분, p별 entry도 남아 있다.

## 검증과 복구

지정 CPU에서 `lake build TorusEven` 통과(8471 jobs). 새 코드의 linter 경고는 0개다.
Isolation 통과: main-path 113개, attic 4개, 등록된 native 사용 파일 3개.
새 공개 선언 87개 모두 표준 axiom `propext`, `Classical.choice`, `Quot.sound`의
부분집합만 사용한다. 새 `sorry`, `admit`, author axiom, `native_decide`는 없다.
기존 조건부 전체 차원 endpoint의 axiom 집합은 native leaf 18개를 포함해 그대로다.

제어 노드와 CPU의 Lean 소스 114개(root 포함)의 SHA256이 일치한다. Lean 4.30.0-rc2와
mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`을 사용했고 기존 mathlib 캐시를 재사용했다.
노드 경로는 [entry 기록](ENTRY_PROGRESS_20260911.md)과 같다. CPU Git HEAD는 소스 식별에
사용하지 않았다.

Audit 소스와 axiom 출력은 `evidence/lean_audit_20260911/shell/`에 있다:
[audit 소스](../evidence/lean_audit_20260911/shell/ShellAudit.lean),
[axiom 출력](../evidence/lean_audit_20260911/shell/axioms.log).
남은 의존관계와 완료 조건은 [E5 실행 계획](E5_REMAINING_PLAN_20260911.md)을 따른다.
