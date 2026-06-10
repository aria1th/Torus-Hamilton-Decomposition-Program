# AI 사용 Disclosure 초안 (2026-06-10)

새 버전 논문에 들어갈 AI 사용 공개 문안 초안. 사실 관계는 이 저장소의 커밋
이력(`ac3d384`..현재)과 각 docs 문서로 추적 가능. 학술지/arXiv 정책에 맞춰
길이를 조절할 수 있도록 3단계 버전을 제공한다. **과장 금지 원칙**: 모든
수학적 주장의 최종 검증은 Lean 4 kernel(및 명시된 곳에서 native_decide)이고,
방향 설정·수용 판단은 저자가 했다.

## 버전 1 — 한 문단 (Acknowledgements/Disclosure 절용, 영문)

> **AI assistance disclosure.** Large-language-model agents (Anthropic Claude,
> operating the Lean 4 toolchain) were used in three capacities: (i) to
> formalize parts of this paper in Lean 4 — in particular Lemma
> \ref{lem:terminal-cyclicity} is fully machine-checked without
> `native_decide`, and the finite tables of Appendix A were audited
> value-by-value against the formal artifacts; (ii) to stress-test the proofs
> against an exact layer-bijectivity criterion, which uncovered the errors
> corrected in this revision (the localized completion-row argument of the
> previous version's Lemma \ref{lem:completion-fiber-bijectivity}, and the
> exchange-row supports of \ref{lem:endpoint-active-core}) — both failures are
> pinned as machine-checked counterexamples in the accompanying repository;
> and (iii) to search for and verify the explicit schedule construction of
> Section~\ref{...} [rail-seam, 채택 시], whose certificates for all even
> $m \le 60$ are included. All mathematical claims accepted into this paper
> were either verified by the Lean kernel or re-derived and checked by the
> author; the author directed the work and takes full responsibility for the
> content. The formalization is available at [repository URL].

## 버전 2 — 짧은 형 (정책상 한두 문장만 허용될 때)

> AI agents (Anthropic Claude with a Lean 4 toolchain) assisted in
> formalizing and auditing this paper; this revision corrects two errors
> found by that audit, each pinned by a machine-checked counterexample.
> All accepted claims are kernel-verified or author-verified.

## 버전 3 — 상세 (부록/저장소 README용)

구성 요소별 사실 기록:

1. **형식화 (Lean 4 + Mathlib)**
   - `lem:terminal-cyclicity` (H1a): 완전 형식화, sorry/native_decide 없음.
     구성 요소: endpoint 순위 리스트와 no-collision(짝수 m ≥ 6 정확 범위),
     recurrence 인스턴스, active-set 특성화, interval-splice 승격.
   - 보조 기계: product-cycle 지수 보조정리, completion tower(+ 단일순환→rank
     열거 역방향), 부모 cycle 추출, reset common-image, renewal capacity 등.
   - 유한 기반 사례(D5(4), D7(4), D7(6))는 별도의 탐색-발견 certificate를
     native_decide로 검증(이전 작업; 본 개정의 AI 작업 이전부터 존재).
2. **감사(audit)**
   - 본문·부록의 모든 수치 표를 형식 정의와 값 단위 대조: 전사 오류 1건
     (D7 stage-3 shifted pair) 발견·수정, 그 외 전부 일치.
   - 정확한 layer-전단사성 기준(2값 치환의 평행이동 불변성과의 동치)을
     형식화하고 §9–10의 행 실현 주장 전수를 이 기준으로 재검사.
3. **반례 발견 (이번 개정의 직접 원인)**
   - 이전 판 `lem:completion-fiber-bijectivity`: 임의 (b,m,h)에서 성립 불가
     (parametric Lean 정리 + b=4 명시 충돌 쌍).
   - 이전 판 X₁/X₂ 교환 support: q-pin 충돌 및 지수 합 m 파괴.
4. **탐색·구성**
   - D3-even 직접 스케줄(rail-seam): parity calculus로 탐색 공간을 좁힌 뒤
     구조적 탐색으로 발견, 닫힌 형태로 정리, 짝수 m ≤ 60 전수 정확 검증.
5. **검증 위계와 책임**
   - 수학적 수용 기준: Lean kernel 검증(게이트: axiom/admit 금지, 구조 모듈
     native_decide 금지) > 명시된 native_decide 유한 검증 > 저자 수기 검증.
   - AI 산출물 중 위 기준을 통과하지 못한 것은 본문에 반영하지 않음.
   - 연구 방향, 문제 선택, 결과 수용은 전적으로 저자 판단.

## 메모 (저자용, 논문에는 미포함)

- venue 정책 확인 필요: arXiv는 disclosure 권장, 일부 저널은 생성형 AI의
  저자성 불인정 + 사용 공개 요구. 버전 1이 대부분의 정책을 충족.
- 인용 가능한 고정점이 필요하면: 저장소의 태그/커밋 해시(rail-seam 완결 커밋)
  + Lean 정리 이름(`completionRow_substitution_not_bijective` 등)을 각주로.
- [repository URL], Section \ref 빈칸은 새 판 구조 확정 후 채움.
