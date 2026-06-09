# H1a 닫힘 보고 (2026-06-09)

## 결론

**H1a(terminal carrier cyclicity, 논문 `lem:terminal-cyclicity`)가 닫혔다.**
`Main.lean`의 `assume_d3TerminalCarrierCyclicity`는 더 이상 sorry가 아니라
`V28Hard.TerminalA2IntervalSplice.terminalA2CarrierCyclicityFamily`를 가리키는
닫힌 정리다. 게이트: **passed, OPEN HOLES 4 → 3** (남은 홀: H1b·H5·H6).
전 과정 native_decide 없음 — H1a는 순수 구조 증명이다.

## 증명 체인 (오늘 적층된 커밋)

| 커밋 | 모듈 | 내용 |
|---|---|---|
| `65c9247` | `TerminalA2EndpointRank` | `endpointDesc_rank_step`(hdesc): `endpointDescSucc`가 closed-form rank list 위에서 `endpointRankSucc`와 일치 (`Even m ∧ 6 ≤ m`; Even은 m−3/m−2 wrap parity에서만 사용) |
| `6235f7d` | `TerminalA2RecurrenceInstance` | `terminalExchange`(논문 `n_i`) + `terminalA2EndpointRecurrence`: 16개 recurrence 필드 전부 증명 (`6 ≤ m`만 필요). endpoint 층 무가설 닫힘: `terminalEndpointImage_singleCycle` |
| `b1ebc13` | `TerminalA2ActiveSet` | `activePred`: `η_c z ≠ z` ⟺ 색별 두 affine 직선 ∪ 두 puncture 점. 양방향 + endpoint family 대응 + fiber별 active 쌍 |
| `43a866e` | `TerminalA2IntervalSplice` | 추상 orbit-splice 보조정리 + carrier 승격 + family 조립 + Main sorry 제거 |

## 핵심 설계 결정 (기록 가치)

1. **Interval-splice는 누적합 rank 없이 닫힌다.** 추상 보조정리
   `single_cycle_of_interval_splice`: label 단일순환 σ + 구간 순회
   `F^[len l](head l) = head (σ l)` + 커버리지 ⟹ `IsSingleCycleMap F`.
   `|X| = m²` 카운팅 불요.
2. **`head k := exchange(pt(k+1))` 매개화.** 구간 머리를 endpoint rank 리스트의
   다음 점의 fiber-파트너로 잡으면 구간열의 successor가 정확히
   `endpointRankSucc`(이미 단일순환)가 되어, 당초 예상한 켤레 논증
   (σ = n∘h∘n)이 통째로 사라진다.
3. **`range(endpointPoint) = active set`은 카드리널리티로.**
   `EndpointDesc m ≃ (ZMod m ⊕ ZMod m) ⊕ Bool`(card 2m+2), invalid = collision
   쌍 2개 → valid 2m; desc 단사 + `Set.eq_of_subset_of_ncard_le`. decoder
   right-inverse 불요.
4. **가설 분포**: recurrence 인스턴스·active-set은 `6 ≤ m`만, parity는 hdesc
   한 곳에만. fiber 내 A≠B no-collision도 Even 불요(충돌은 정확히 collision
   index에서만).

## 남은 작업 (계획 문서 기준)

- **H1b** (2단계): `TerminalA2RootFlatRealizationFamily` — 착수 전
  `sectionEquiv` 색 공통/색별 인터페이스 결정 필요
  (`PAPER_NUMERIC_AUDIT_20260609.md` §2 참조; 논문 η_i는 색별 `z−a_i` 앵커).
- **H5** (3단계): 요청 C(anchors) + D(growth) — audit §3의 구조 목록.
- **H6** (4단계): 요청 E(endpoint successor) — audit §4; H1a family를 입력으로
  소비하도록 입력 레코드 확장 필요(이제 H1a가 닫혀 의존성 해소됨).
