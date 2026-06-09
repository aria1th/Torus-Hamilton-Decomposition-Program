# 현재 상태 ground-truth (2026-06-08, 작업 후)

방법: 코드 직접 판독 + `#print axioms` + 풀빌드 + 게이트 grep 복제로 **검증된 사실**만.

## 0. 한 줄 결론

**열린 홀 = 4개의 정밀 수학 의무: H1a(carrier cyclicity)·H1b(realization)·H5·H6.**
(H1을 두 별개 수학으로 분리.) H2·H3·H4는 **유한 존재성 witness(native_decide)**로
닫혔다. 남은 넷은 모두 **무한 family**(모든 짝수 m / 모든 high-even target / 모든
endpoint)라 단일 유한 witness가 불가능 → parametric 수학이 필요. connective(조립)로
닫을 수 있는 것은 **전부 닫힘** — 전체 트리에 sorry 정확히 4개, 나머지 reductions·
inputs·bridges는 모두 sorry-free.

배경: 사용자 방향 — "native_decide는 사람이 따라갈 수 있고, Lean에서 결국 보여야 할
것은 *그런 해가 (적어도) 하나 존재하는가*다." 유한 base(D5(4)·D7(4)·D7(6))는 구체
schedule 한 개로 존재성이 증명되므로 native_decide가 정당한 vehicle.

## 1. `#print axioms evenModulusToriAllDimensions` (검증)

```
[propext, sorryAx, Classical.choice, Quot.sound,
 + native_decide axioms:
     EvenV11.LowD5M4Finite   54개   (H2, Fin 256)
     EvenV11.LowD7M4Finite   74개   (H3, Fin 4096)
     EvenV11.LowD7M6Finite  102개   (H4, Fin 46656)]
```
- `sorryAx` = 열린 4홀 (H1a, H1b, H5, H6).
- 목표 위생 `[propext, Classical.choice, Quot.sound]`은 H2/H3/H4의 native 때문에
  여전히 미달(의도된 trade-off: 존재성 우선).

## 2. Main.lean 홀 상태 (sorry 4개 — H1을 두 정밀 의무로 분리)

| 홀 | Main 심볼 | 상태 |
|---|---|---|
| H1a | `assume_d3TerminalCarrierCyclicity : TerminalA2CarrierCyclicityFamily` | **열림** (수론, `Fᵢ` m²-cycle 모든 짝수 m; m=4,6 finite 완료) |
| H1b | `assume_d3TerminalRealization : Nonempty TerminalA2RootFlatRealizationFamily` | **열림** (root-flat realization, wild sectionEquiv) |
| H2 | `assume_lowD5M4 → LowD5M4Finite` | **닫힘** (finite witness, Fin 256) |
| H3 | `assume_lowD7M4 → LowD7M4Finite` | **닫힘** (finite witness, Fin 4096) |
| H4 | `assume_lowD7M6 → LowD7M6Finite` | **닫힘** (finite witness, Fin 46656) |
| H5 | `assume_oddHighModulus` | **열림** (engine `run`, §6 coforest + §8 growth) |
| H6 | `assume_oddEndpoint` | **열림** (engine `run`, §9 transfer + §10 endpoint) |

`assume_d3CycleData`는 닫힌 어댑터
`cycleDataFamily_of_carrierCyclicity_and_realization`로 H1a+H1b에서 파생(sorry 아님).
H5/H6의 입력 보조정리(audit/kernel/locality/return/word/range, transfer/phase-product/
completion 등)는 **전부 sorry-free로 닫혀** 있고, 열린 건 각 engine의 `run` 구성뿐.

풀빌드: `lake build EvenV11` green (8407 jobs). Main sorry 경고 = 라인 55(H1)·
402(H5)·405(H6).

## 3. 게이트 상태 (검증)

`scripts/check_evenv11_progress.sh`: 무조건 main 정리 + 정직한 `sorry`, 인벤토리된
finite witness에서 `native_decide` 허용, 그 밖의 structural module에서는 금지.

2026-06-08 현재 정책은 H2/H3/H4 finite existence witness를 기본 spine에 허용한다.
허용 목록은 정확히 다음 셋이다.

```
EvenV11.LowD5M4Finite
EvenV11.LowD7M4Finite
EvenV11.LowD7M6Finite
```

검증:

```
scripts/check_evenv11_progress.sh
```

결과: **passed**. 출력 요지:

```
EvenV11 OPEN HOLES (assume_* := sorry): 4
progress gate passed (build green, no axiom/admit, no structural native_decide)
```

## 4. 되살린 finite witness (이번 작업)

archive → active 복원, 둘 다 sorry-free, 구체 `dir`/`step` + RF1/RF2/RF3 native_decide:
- `EvenV11/LowD7M4Finite.lean` (767KB, `RootState = Fin 4096`):
  `finalLowD7M4RootFlatCertificateFamily : FinalLowD7M4RootFlatCertificateFamily`.
- `EvenV11/LowD7M6Finite.lean` (16.7MB, `RootState = Fin 46656`):
  `finalLowD7M6RootFlatCertificateFamily : FinalLowD7M6RootFlatCertificateFamily`.

import: `StandardRootFlatLift`, `FiniteArrayCert`,
`FinalTargetLowBaseRootFlatCertificateBridge`, `Shared.RootFlat` (전부 live).

## 5. 빌드/캐시 동향 (검증)

- M6 최초 빌드: ~10분, RSS ~4GB plateau, CPU ~300%(멀티스레드). 일회성.
- **캐시-히트 실증**: 무변경 재빌드 = **4.9s** ("8407 jobs 전부 캐시 히트, M6
  재컴파일 없음, native_decide 재실행 없음" — 결과가 olean에 axiom-backed term으로
  구워짐).
- 캐시 무효화 조건: `LowD7M6Finite.lean` 자체 또는 그 import만. `Main.lean` 등
  하류 수정은 무효화 안 함.
- ⚠️ clean 빌드(CI·새 클론, `.lake` 없음)는 매번 full M6 비용 지불.

## 6. V28Hard 계층 (6/7–6/8) — 참고

`ConstructiveV28Solution → main goal` 조건부 spine은 sorry-free(별도 어댑터).
유한/표 측면 전부 닫힘: terminal cyclicity m=4,6(`terminalA2M4/M6FiniteCyclicity`),
D7 finite audit(`relayFiniteAuditEvidence`: support/forest/reserve/anchor JSON 일치
+ closing-matrix payload + folded-word 단일순환 m=4,6). 단, 그 계층의
`TwoRailRelayRealization`/`TerminalA2ParametricSolution`/`HardPromotionEngines`는
구조적(native_decide-free) 입력이라 여전히 미구성 — 현재 main은 그 계층이 아니라
직접 finite witness 경로로 H2/H3/H4를 닫는다.

## 7. 남은 4홀 = native_decide로 **불가**

유한 base가 닫힌 이유는 유한(4096/46656)이라 한 witness가 존재성을 증명하기 때문.
남은 넷은 무한 family라 동일 트릭 불가:

| 홀 | 무한한 것 | 요청 |
|---|---|---|
| H1a | 모든 짝수 m≥4의 terminal carrier 단일 m²-cycle | **A** (endpoint recurrence A^r/B^r) |
| H1b | 모든 짝수 m≥4의 terminal carrier root-flat realization | **A-realization** (common sectionEquiv + color translation) |
| H5 | 모든 high-even target (d, odd m>d) | **C** finite anchors + **D** 2좌표 growth |
| H6 | 모든 endpoint 확장 b↦2b+1 | **E** endpoint successor |

세부 요청 형식은 `HARD_PART_AUDIT_AND_LEMMA_REQUESTS_20260607.md` 참조(H1 계열/H5/H6만
유효; H2/H3/H4 요청 B는 finite 경로로 우회됨, 선택적 장기 목표로 보존).

2026-06-08 추가 A2 배관: `D3TerminalA2Parametric` 안에서 low-mod evidence를
`TerminalA2LowModFiniteBundle`로 묶고, 남은 H1을
`TerminalA2CarrierCyclicityFamily` + `TerminalA2RootFlatRealizationFamily` 두 입력으로
분리했다. realization 쪽은 고정 `rootPairEquiv`가 아니라 explicit
`sectionEquiv : TerminalQ m ≃ RootState m`를 요구한다. 닫힌 adapter
`cycleDataFamily_of_carrierCyclicity_and_realization`은 이 두 입력에서
`RootFlatCycle.D3EvenCycleDataFamily`를 바로 만든다. 또한
`TerminalA2RootFlatRealizationAt` pointwise record와
`D3TerminalA2M4Bridge`를 추가해서, H2/D54의
`TerminalA2M4PhysicalRealization`이 있으면 즉시 `m=4` A2
`RootFlatCycleData`로 변환된다. 이어 `D3M4DirectRootFlat`에
`D3EvenM4.colorDir`를 root-flat chart로 접은 direct `D₃(4)` cycle-data
witness를 추가했다. 이것은 terminal carrier `F_i`와의 paper-realization이 아니라
`m=4` root-flat existence를 finite certificate로 확정하는 보조 데이터다.

2026-06-08 추가 H1a 분해: `TerminalA2EndpointRank`를 추가했다. 이 파일은 paper
endpoint order를 `EndpointLabel m = Fin (2*m)`로 두고
`endpointRankSucc_singleCycle`을 닫은 뒤, 세 color의 closed-form inverse rank list
`endpoint0Point`/`endpoint1Point`/`endpoint2Point`를 기록한다. injectivity가 주어지면
rank successor를 active endpoint image subtype으로 옮기는
`endpointImageSucc_singleCycle`도 제공한다. 이어
`endpointImageMapOfRankStep_singleCycle`과
`compressedEndpointImageMap_singleCycle_of_rank_step`을 닫아, 논문 recurrence map
`h_i = n_i ∘ eta_i`에 대해 closed-form rank-step table만 주면 active endpoint image
위의 단일순환이 자동으로 따라오게 했다. 따라서 H1a의 다음 닫힘 단위는
`TerminalA2EndpointRecurrence` fields를 rank list에 대입해 pointwise rank-step을
증명하는 부분, 그리고 active interval-splice lemma로 `h_i` cycle을 `F_i` cycle로
올리는 부분이다. 또한 `terminalEndpointA_injective`/`terminalEndpointB_injective`와
`terminalEndpointA_eq_B_forces_exception`을 닫아, endpoint no-collision의 좌표 핵심은
"A/B 각각은 fiber index에 injective이고, A/B cross-collision은 exceptional fiber에서만
가능하다"는 논문 수준 명제로 사용할 수 있다.

2026-06-09 추가 H1a endpoint no-collision: `TerminalA2EndpointRank`에서
rank label을 generic `A`/`B`와 두 puncture endpoint로 분리한 `EndpointDesc` 층을
추가했고, 실제 terminal point 해석 `endpointDescPoint`가 valid descriptor 위에서
injective임을 `endpointDescPoint_injective_of_valid`로 닫았다. 이어
`endpointPoint_injective_of_desc_injective`를 추가해, 남은 순수 rank/parity 목표
`Function.Injective (endpointDesc m c)`가 닫히면 즉시 `endpointPoint m c`의
injectivity가 따라오게 했다.

2026-06-09 추가 H1a endpoint no-collision 완료: 세 color별 closed-form descriptor
decoder의 left-inverse를 `endpoint0DescRank?_endpoint0Desc`,
`endpoint1DescRank?_endpoint1Desc`, `endpoint2DescRank?_endpoint2Desc`로 닫고,
`endpointDesc_injective_of_even_six_le` 및
`endpointPoint_injective_of_even_six_le`를 추가했다. 정확한 정리 범위는 논문 조건과
같이 `Even m ∧ 6 ≤ m`이다. 홀수에서는 color 2가 항상 실패하며,
`endpoint2Point_odd_collision`/`endpointPoint_odd_color2_not_injective`로 이를
Lean에 기록했다. `m=7`의 구체 반복도
`endpoint2Point_m7_collision`/`endpointPoint_m7_color2_not_injective`로 남겼다.
따라서 generic endpoint no-collision의 정확한 범위는 확정됐고, H1a의 다음 닫힘
단위는 recurrence rank-step table과 active interval-splice lemma다.

2026-06-09 추가 H1a endpoint-image handoff: 위 no-collision 결과를
`endpointImageSucc_singleCycle_of_even_six_le`와
`compressedEndpointImageMap_singleCycle_of_even_six_le_rank_step`에 연결했다. 따라서
모든 `Even m ∧ 6 ≤ m`에서 closed-form endpoint rank successor는 active endpoint
image 위 단일순환이고, 논문 recurrence map이 rank를 한 칸 전진시킨다는 pointwise
table만 주면 compressed endpoint image cyclicity는 추가 injectivity 의무 없이 바로
따라온다. 남은 H1a generic 의무는 실제 recurrence fields의 rank-step 대입과
그 endpoint cycle을 전체 `F_i` carrier cycle로 올리는 interval-splice 승격이다.

2026-06-09 추가 H1a recurrence interface 수정: `TerminalA2EndpointRecurrence`의
boundary fields가 기존에는 `B3 -> A1`, `A3 -> B1`처럼 puncture endpoint를 건너뛰는
compressed 형태였는데, 이는 `TerminalA2EndpointRank`의 paper rank list
`B3 -> E+ -> A1`, `A3 -> E- -> B1`와 맞지 않았다. 이를
`terminalEndpointEplus`/`terminalEndpointEminus`와 color별 bridge fields로 분해했다.
따라서 다음 rank-step proof는 논문식 active endpoint 2m개를 그대로 대상으로 삼는다.

2026-06-09 추가 H1a descriptor successor handoff: `TerminalA2EndpointRank`에
paper endpoint successor `endpointDescSucc`를 추가했고,
`terminalCompressedEndpointReturn_endpointDescSucc`를 닫았다. 즉
`TerminalA2EndpointRecurrence` record가 주어지면 valid descriptor는 정확히
`endpointDescSucc`로 이동한다. 이어
`compressedEndpoint_rank_step_of_desc_rank_step`과
`compressedEndpointImageMap_singleCycle_of_even_six_le_desc_rank_step`을 추가해, 남은
rank-step 의무를 raw terminal point 계산에서
`endpointDescSucc c (endpointDesc m c n) = endpointDesc m c (endpointRankSucc m n)`
라는 closed-form descriptor table equality 하나로 낮췄다.
