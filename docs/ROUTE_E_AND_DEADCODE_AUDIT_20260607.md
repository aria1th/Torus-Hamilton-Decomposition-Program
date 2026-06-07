# 감사(audit): Route E 및 중첩·사장된 방법론 (2026-06-07)

요청: 형식화에 실패/과거 방법론이 겹쳐 비효율·방해가 되는 부분, 특히 **Route E**
(v28가 D3-even을 완전히 닫았으나 예전 시도가 겹침)를 구체적으로 감사.

방법: `EvenV11.Main`(실제 정리)과 `EvenV11`(umbrella) 각각의 **import closure**를
계산해 *spine*(정리가 의존)과 *umbrella-only*(빌드되나 정리는 안 씀)를 분리.

## 0. 핵심 사실 (확정)

- **Main spine은 native_decide가 실제로 0개.** (스캔이 센 5개는 `LowD5M4Structural`/
  `RootFlatCycleData` **docstring의 "no native_decide" 문구** 오탐 — 실제 tactic 사용 없음.)
  → 정리 spine은 이미 깨끗합니다(honest sorry 6개: H1, H2, H3, H4, H5, H6).
- 따라서 모든 native_decide·중첩 방법론은 **spine 밖**에 있고, 다음 셋으로 갈립니다.

## 1. 세 가지 중첩된 저차원 base 방법론

| 방법론 | 파일 | 상태 | 정리 기여 |
|---|---|---|---|
| ① native_decide blob | `LowD5M4Finite`, `LowD7M4Finite`, `LowD7M6Finite` | **고아(import 0)** | 없음 |
| ② Route E (D3-even) | `D3EvenRouteEGeSix` 외 3 | **umbrella-only** | 없음(H1=sorry) |
| ③ 구조적/논문충실 (LIVE) | `LowD5M4Structural`, `RootFlatCycleData`, `TerminalA2LowMod`, `LowD5M4Seed/Schedule` | **spine** | H2/H3/H4 핸드오프 |

세 방법론이 같은 저차원 base를 서로 다르게 다뤄 겹칩니다. ③만 살아 있습니다.

## 2. ① 고아 blob — 즉시 제거 권장 (위험 0)

```
LowD5M4Finite.lean   108 KB   native_decide 54
LowD7M4Finite.lean   768 KB   native_decide 74
LowD7M6Finite.lean  16.7 MB   native_decide 102      ← 단일 최대 부채
합계 ~17.5 MB 소스, native_decide 230,  import하는 파일 0개
```
- 구조적 cycle-data 경로(`RootFlatCycle.RootFlatCycleData`)로 대체됨. **아무도 import
  안 함** → 빌드에도 안 들어가나, **gate(`grep -r native_decide EvenV11/`)가 디렉터리를
  스캔하므로 gate 실패의 주원인**.
- **권장: 삭제** (또는 gate 스캔 밖 `archive/`로 이동). 위험 0(고아).

## 3. ② Route E — 사용자 지목 대상

### 무엇인가
v28 이전 D3-even base 시도. `subtex/terminal_A2_block.tex`의 terminal-cyclicity와
**같은 A₂ first-return 순환성을 다른 좌표(rank-table/zero-layer/return-model)로** 적은 것.
HARDEST_PARTS 기록상 H1을 "일반 m≥6 zero-layer bijection/rank package"로 **축소만**
했고 **닫지 못함**.

### 현재 상태 (감사 결과)
```
D3EvenRouteEGeSix.lean        3048 줄   (대형)
D3EvenRouteERootFlatBridge    302 줄
D3EvenRouteEColor2Bridge      110 줄
CycleOnBridge                 66 줄   (old TorusD3Even.CycleOn → IsSingleCycleMap 어댑터)
```
- import 관계: 서로 + `EvenV11.lean`(umbrella)만. **Main spine 미포함.**
- H1(`assume_d3EvenRootFlat`)은 spine에서 **그냥 sorry** — Route E 결과를 **전혀 안 씀**.
- 즉 Route E는 빌드 비용·개념적 혼란만 주고 **정리에 0 기여**.

### v28의 대체 경로 (LIVE, 검증됨)
- v28는 D3-even을 **terminal A₂ block**(`lem:terminal-cyclicity`: 모든 짝수 m에서
  F₀,F₁,F₂가 m²-cycle)으로 닫음.
- `scripts/verify_rootflat_certificates.py` [B]에서 **짝수 m∈{4,6,8,10,12} 유한 검증 통과**.
- Lean 측 자산: `TerminalA2LowMod`(spine), `terminalStdBaseRowEquiv5`(터미널 row word).
  H1의 올바른 Lean 경로는 이쪽(task #5)이며 Route E와 **무관**.

### 권장
- **Route E 4파일 retire** (umbrella import 제거 + `archive/`이동 또는 삭제).
- H1은 terminal-A2 cycle-data로 새로 연결(③ 패턴). Route E의 rank-table 잔재는 불필요.
- 주의: `CycleOnBridge`/`D3EvenRouteEColor2Bridge`가 old `TorusD3Even` first-return
  proof를 끌어오는데, 그 경로 자체가 Route E 전용이므로 함께 retire.

## 4. ③ 추가 중첩 — spine 안의 사장 코드

### 4.1 `LowD5M4Realization.lean` (356 KB) — **spine 안 active 방해**
- tame 좌표(`seedRootEquiv`) `returnMap = paperReturn` 경로. **목표 goal이 unsatisfiable**
  (`docs/H2_REALIZATION_BLOCKER_20260605.md`: returnMap 변위 ≤4 vs paperReturn 5–6).
- sorry-free 환원이지만 **닫을 수 없는 의무**를 향함. `LowD5M4H2PaperRow`가 이를
  import → **Main spine에 356KB가 끌려 들어옴**.
- LIVE H2 경로는 ribbon(`ResetPortH2RowEquivRibbonRealizationData`, `LowD5M4Structural`).
- **권장: `H2PaperRow`가 실제로 쓰는 정의(예: `terminalStdBaseRowEquiv5`)만 작은
  모듈로 추출하고, 356KB unsatisfiable 스캐폴딩을 spine에서 분리.** (먼저 의존 정밀
  확인 필요.)

### 4.2 `Status.lean` (730 KB) — closure-first 레거시
- Main.lean 리팩터가 폐기한 "closure-first" 부기. umbrella-only. **순수 레거시.**
- **권장: 삭제/archive.** (사용자가 명시적으로 벗어난 방법론.)

### 4.3 umbrella-only 기타
```
D3EvenM4 / D3EvenM4RootFlat   native_decide 19   (m=4 D3 유한, H1에 미연결)
EndpointReservePlacement      ~201 KB            (endpoint, H6 관련? spine 밖)
EndpointRowPlacement          ~53 KB
V28PaperInterface             (사용자 신규, 아직 spine 미연결)
TypeA.PacketBridge
```
- `D3EvenM4*`: terminal-A2 H1의 m=4 케이스로 **재사용 가능** — retire 말고 H1 연결 시 흡수 권장. 단 native_decide라 gate에 걸림.
- Endpoint*: H6용일 수 있으나 spine 미포함 — H6 작업 시 관련성 재확인.

## 5. gate 메모

native_decide를 디렉터리에서 없애려면: ②③blob 제거 + `D3EvenM4*` 처리 **그리고**
`LowD5M4Structural`/`RootFlatCycleData` docstring의 "native_decide" 문구를 바꿔야
gate 정규식(`\bnative_decide\b`, 주석도 매칭)을 통과. (또는 gate가 주석 제외하도록 보정.)

## 6. 정리 — 우선순위 cleanup 계획

| # | 조치 | 효과 | 위험 |
|---|---|---|---|
| 1 | 고아 blob 3개 삭제/archive | gate 주원인 제거, −17.5MB·−230 nd | **0** (import 0) |
| 2 | Route E 4파일 retire(umbrella서 제거) | 중첩 제거, −3500줄, 개념 정리 | 낮음(spine 미사용) |
| 3 | `Status.lean` 삭제/archive | closure-first 레거시 −730KB | 낮음(umbrella-only) |
| 4 | `LowD5M4Realization` spine 분리 | 356KB unsatisfiable 제거 | 중(H2PaperRow 의존 확인 선행) |
| 5 | `D3EvenM4*` H1 terminal-A2에 흡수 | m=4 base 재사용, nd 처리 | H1 작업과 결합 |

**1·2·3은 정리 spine에 무영향**(전부 spine 밖). 실행 전 사용자 승인 권장(사용자 파일).

---

## 7. 실행 결과 + Realization 분리 조사 (2026-06-07)

### 7.1 archive 완료 (조치 1·2·3) ✅
`git mv` 로 9개 파일을 `archive/EvenV11/`로 이동, umbrella import 6줄 제거.
`lake build EvenV11` **green (8390 jobs)**. spine 무영향. 옮긴 파일:
blob 3 + Route E 4(`D3EvenRouteE*`,`CycleOnBridge`) + `D3EvenM4RootFlat`(Route-E 의존) + `Status`.
`D3EvenM4`(standalone)는 유지. 복원법은 `archive/EvenV11/README.md`.

### 7.2 LowD5M4Realization 분리 — 조사 결과 (조치 4)
- **Main의 LIVE H2 obligation은 올바른 wild-e ribbon 경로**다:
  `LowD5M4H2PaperRow.ResetPortBaseRowRibbonRealizationData`(22–52행)는
  `e : Seed ≃ RootState`(wild) + `returnRealization … = LowD5M4.fullReturn`을 쓴다 —
  tame `paperReturn`이 **아님**. 즉 H2 spine은 blocker의 unsatisfiability를 상속하지 않음.
  이 경로가 Realization에서 쓰는 건 **`ResetPortBaseRow` + `resetPortRowOfBase` 2개뿐**.
- **356KB가 spine에 끌려오는 진짜 원인**: H2PaperRow **54–210행의 죽은 tame-`paperReturn`
  빌더들**(`_of_paperTableData`, `_of_fullSplitGoals`, … ; `e:=seedRootEquiv`,
  `simp[paperReturn]`). 이들은 blocker가 unsatisfiable로 판정한 경로이고 Realization
  후반 goal machinery(`ResetPortFullPaperTableGoals`@7706 등)를 끌어온다.
- `resetPortRowOfBase`@1603 = `fun t w => resetPortSwappedRow w (baseRow t w)`,
  cone = prefix ~1–1900행(자기완결, Lean 순서상 뒤 참조 불가). goal machinery는 7129행+.

### 7.3 안전한 분리 계획 (실행 보류 권장)
spine에서 356KB를 빼려면 둘 다 필요:
1. **Realization prefix 추출**: 1–~1900행(seedRootEquiv, terminal row, swap,
   `resetPortRowOfBase`)을 새 `EvenV11/LowD5M4ResetRow.lean`로. prefix는 자기완결이라
   Lean-safe. Realization은 이를 import.
2. **H2PaperRow 죽은 빌더 분리**: 54–210행(tame 경로)을 별도 파일(umbrella-only)로
   옮기거나 삭제. LIVE 22–52행만 `LowD5M4ResetRow` import.
→ 그러면 Main spine은 `LowD5M4ResetRow`(~1900행)만 의존, 356KB Realization 제거.

**보류 이유**: ①②은 사용자가 활발히 편집 중인 H2 설계(Realization·H2PaperRow)에
대한 수술이고, 죽은 tame 빌더 제거는 진행 중인 H2 탐색과 얽혀 있다. prefix-추출은
안전하나 active 파일 충돌 위험이 있어, H2 경로(wild-e ribbon)가 확정된 뒤 실행 권장.

### 7.4 미해결 핵심 질문 (사용자 확인 요망)
LIVE H2 obligation은 `resetPortRowOfBase baseRow`의 **RF2(layerBijective)** 를 요구한다.
blocker §4.1: "layer index 없이 first/final reset substitution을 동시 적용하는
resetPortRowOfBase는 RF2에 안 맞아 compatibility/negative route로만 유지." →
**현재 Main H2 slot이 RF2 때문에 닫힐 수 있는지**가 핵심. 닫히지 않으면 H2 dir 설계
(layer별 substitution 분리)를 바꿔야 함. 이는 displacement blocker와 별개의 RF2 이슈.
