# H2 D5(4) realization — 차단 발견 (blocker), 2026-06-05

PoC 진행 중 발견. **현재 `LowD5M4Realization` architecture(`returnMap = paperReturn`,
tame 좌표 동치 `seedRootEquiv` 고정)는 증명 불가능합니다.** "어렵다"가 아니라
"unsatisfiable"입니다. 근거는 변위(displacement) counting + eval 실측.

## 1. 핵심 부등식

- **`returnMap c`** = `m=4`개 layer의 합성. 각 layer `layerMap t c x = rootStep d x`
  = 한 좌표 +1 (또는 d=4 no-op). 따라서 4 layer의 **변위 metric**
  (`∑ⱼ ZMod.val (Δⱼ)`, 좌표 0..3)은 **항상 ≤ 4**.
  - 실측(canonical dir): `sched.returnMap {0,3,4}` 변위 sup = **4, 4, 4**.
- **`paperReturn c`** = `seedRootEquiv ∘ fullReturn c ∘ seedRootEquiv.symm`.
  `seedRootEquiv`는 좌표별 1:1(q→0,1; y→2; z→3)이라 **변위 metric 보존**.
  `fullReturn`(skew tower, `F_i`/W carry)은 고변위.
  - 실측: `paperReturn {0,3,4}` 변위 sup = **5, 6, 6**. 색0은 256개 중 **64개**가 >4.

⟹ `returnMap c = paperReturn c`는 색 0,3,4에서 **거짓**(4 < 5,6). prefix decide도
독립적으로 `false` 확인(아래 §3). 즉 `assume_lowD5M4PaperData :
Nonempty ResetPortH2PaperCertificateData`는 현재 형태로 **닫을 수 없음**.

## 2. 왜 — 의미

`returnMap`은 **저변위**(매 w를 4-증가 이내 점으로 보냄) 순열이고,
`fullReturn`은 **고변위** 256-cycle입니다. 둘 다 256-cycle이지만 **다른 순열**이며,
tame 좌표 동치로는 같아질 수 없습니다. 논문의 "realize by layer rows"는
`returnMap = fullReturn`을 주장하지 **않습니다** — RF criterion은 returnMap이 *어떤*
256-cycle이기만 하면 되고, 그 cyclicity를 **run-collapse(cut-splice/ribbon)
대응**으로 fullReturn에서 옮깁니다(`lem:ribbon-realization`:
"alternating components ∩ return section = cycles of R_B⁻¹R_A"). 이 대응은
**좌표별이 아닌(wild) 재색인**입니다.

## 3. PoC에서 실증된 것 (요약)

- ✅ read leaf(`BaseRowReadsTerminalTailSymbol`)는 canonical baseRow
  `fun _ w => terminalStdBaseRowEquiv5 (qCoord w)`에서 **`rfl`**로 닫힘.
- ✅ 함수타입 `decide`(`Fin 4 → ZMod 4`)는 `maxRecDepth 4000`로 ~수 초에 통과
  (native_decide 불필요) — leaf가 유한 등식이면 닫을 수 있음.
- ❌ prefix leaf(`TerminalCoreTailPrefixPathGoal`, 색0): canonical baseRow에서
  256개 중 **0개** 도달. tail base 변위 `Δ₀−a₀=(3,1)`은 q-좌표에 **4 증가** 필요,
  prefix는 **layer 3개**뿐 → 어떤 baseRow로도 불가(layer 예산 부족). 이는 §1의
  특수 사례.

## 4. 따라서 올바른 경로 (선택)

`returnMap = paperReturn`(tame e) 경로는 폐기. 대안:

- **(A) native_decide 수용** — blob(`LowD5M4Finite`)이 `returnMap`을 직접 256-cycle로
  증명함(저변위여도 cyclic 가능). gate 정책만 native_decide 허용으로 완화.
  가장 확실·즉시. 단 논문 구조 재현은 아님.
- **(B) wild 재색인 e 구성** — run-collapse 동치 `e : Seed ≃ RootState`(좌표별 아님)를
  터미널 A₂ collapse 구조에서 **구성**하고 `returnMap c = e ∘ fullReturn c ∘ e.symm`
  증명 → 내 `LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_returnRealization`
  (e를 **파라미터**로 받음 — tame 고정 안 함)에 투입. 이게 논문 충실 경로.
  단 e 구성 = run-collapse 대응 재유도 = genuine hard math.
- **(C) ribbon 직접** — `Shared/SwitchCalculus.lean`의 `flagSplicingCriterion`로
  returnMap cyclicity를 fullReturn에서 cut-splice로 직접 전달. (B)와 유사 난도.

## 4.1. 2026-06-05 구현 반영

기본 proof spine은 이제 (B)를 따릅니다.

- `EvenV11.LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`를 현재
  `Main`의 H2 open input으로 사용한다. 필드는 실제 Latin row
  `row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5`, wild
  `e : Seed ≃ RootState`, RF2, 그리고
  `e.symm (returnMap c (e x)) = LowD5M4.fullReturn c x`이다. RF1은
  `rowLatin_of_rowEquiv`로 자동 처리된다.
- 더 일반적인 내부 handoff로
  `EvenV11.LowD5M4Structural.ResetPortH2RibbonRealizationData`도 남아 있다. 이는
  arbitrary `dir`, wild `e`, RF1/RF2, return-realization을 직접 받는다.
- `ResetPortH2RootFlatCycleData`도 추가했다. 이는 ribbon 증명 없이도 RF3
  `returnsSingleCycle`을 직접 얻었을 때 바로 certificate로 가는 일반 RF handoff다.
- `EvenV11.Main`의 H2 가정은
  `assume_lowD5M4RibbonRealizationData : Nonempty LowD5M4RibbonRealizationData`로
  교체했다. `assume_lowD5M4`는
  `finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData`에서
  파생된다.
- 기본 `EvenV11.lean` import closure에서 `EvenV11.LowD5M4Realization`을 제거했다.
  paper-table compatibility는 `EvenV11/LowD5M4H2PaperRow.lean`의 explicit adapter로
  유지한다.
  해당 파일은 `paperReturn`/tame-chart 실험과 호환 adapter로 남지만 더 이상 기본
  H2 경로가 아니다.

## 5. 영향 (정직)

- 사용자 `LowD5M4Realization.lean`(356KB, sorry-free 환원)의 **목표 goal이
  unsatisfiable** — prefix-path가 `returnMap`을 fullReturn 궤적으로 강제하나 layer
  예산이 막음. 재구조화(특히 e를 tame `seedRootEquiv`로 고정하지 말 것) 필요.
- 내 `LowD5M4Structural.lean` reduction은 **정리 자체는 valid**(조건부)이고, e를
  파라미터로 두어 **(B)에 그대로 쓸 수 있음**. 다만 tame e로는 `hReal` 충족 불가.

## 6. 검증 (eval, `/tmp`에서)

```
returnMap {0,3,4} disp sup = 4,4,4        (poc_eval4)
paperReturn {0,3,4} disp sup = 5,6,6      (poc_eval3)
paperReturn 0 disp>4 인 상태 수 = 64/256  (poc_eval3)
canonical prefix(색0) tail-base 도달 수 = 0/256, decide=false  (poc_prefix/poc_eval)
read leaf rfl로 닫힘                       (poc.lean)
```
