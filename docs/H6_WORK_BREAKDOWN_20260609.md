# H6 (endpoint successor, 요청 E) 작업 분해 (2026-06-09)

전제: H1a 닫힘(`43a866e`)으로 H6의 숨은 terminal-cyclicity 의존성 해소.
대상: `OddEndpointPayloadEngine.run : 4 ≤ b → MarkedDimensionRange b m →
FinalMarkedPayload b m → FinalOddEndpointPhaseProductCertificateInputs →
FinalMarkedPayload (2b+1) m` (`HighEvenEndpointPromotions.lean:113`).

## 0. Audit 정정 (2026-06-09 검증)

`PAPER_NUMERIC_AUDIT_20260609.md` §4 항목 9 정정: **parametric RF-criterion은
이미 존재한다** — `finalRootFlatTorusCertificate_of_cycleData :
RootFlatCycleData n m → FinalRootFlatTorusCertificate (n+1) m`
(`RootFlatCycleData.lean:61`)이 (n,m) 일반. 없는 것은 child 차원 `n = 2b`의
**cycle data 구성**(schedule + RF1/RF2/RF3)이며, 이것이 엔진의 본체다.

## 1. 엔진 스파인 (설계)

부모 `FinalMarkedTarget b m`(HD_b) + 인증서 입력에서 child
`RootFlatCycleData (2b) m`을 만들고 닫힌 bridge로 target화:

```
parent HD_b  ──(Y-dynamics: parent return cycles, M = m-power 주기)──┐
terminal A2  ──(H1a family: F_i 단일순환, 전 짝수 m)────────────────┤
                                                                    ▼
   child schedule on E = Y × Q × (ℤ/m)^{b−1}  (Ω-rows: N/X_i/R/C_h)
                                                                    ▼
   RF1(행 Latin) · RF2(layer 전단사) · RF3(product-cycle exponent
   1/m²−1 + completion tower 캐리 ±1 → 단일순환)
                                                                    ▼
   RootFlatCycleData (2b) m → FinalRootFlatTorusCertificate (2b+1) m
                                                                    ▼
   FinalMarkedPayload (2b+1) m  (selector/reserve는 현 인터페이스상
   PUnit-충전 가능; 충실 marked 전달은 후속)
```

## 2. 조각 분해 (의존 순서)

| # | 조각 | 내용 | 상태 |
|---|---|---|---|
| E1 | **EndpointChart** | `Ω : Fin (2b+1)` 순환 순서(τ₀τ₁τ₂ p₁⁺p₁⁻…), 색 이름표(t/d/μ), 행 `N/X_i/R/C_h`를 `Equiv.Perm Ω`로, Latin성, b=4 지표 = 논문 chart 6행 대조 | **완료** `d64a289` (`EndpointChart.lean`) |
| E2 | Completion tower | 1좌표 `FinCompletionCarryCertificate`를 b−1좌표 순차 부가로 일반화 + **역방향 rank 보조정리** `rankEquiv_of_singleCycle`(부모 주기 정규화도 해결) | **완료** `fd03ffd` (`CompletionTower.lean`) |
| E3 | Reset common-image (parametric) | `r₀+δ_{p₁⁻} = r₁+δ_{p₂⁻} = I`의 `(ℤ/m)^{b−1}` 판 + row list `𝒫 ∈ E^{b+4}` 분리 (가설 `1<m`뿐) | **완료** `f13fee3` (`EndpointPortRoom.lean`) |
| E4 | Renewal capacity + 역할 분할 | `2b+4 < 4^{b−1} ≤ m^{b−1}` + `RenewalRole`(3⊕2b⊕1, card 2b+4) + base-m digit 단사 슬롯 | **완료** `f13fee3` (동일 파일) |
| E5 | Child schedule + RF1/RF2 | `rowSchedule`(행=치환 → RF1 무료), RF2 = swap-on-cylinder의 평행이동 불변 `U+(e_β−e_α)=U` 환원, `LayerDesc` plan | **완료** `4508ce6` (`EndpointRowSchedule.lean`) |
| E6 | RF3 | layer plan 구체 선택(어느 layer가 N/X_i/R/C_h + support) → returnMap 계산 → product-cycle exponent(`UnitCarry` 닫힘) + H1a family(`terminalA2CarrierCyclicityFamily`) + E2 tower 합성으로 `returnsSingleCycle` | **다음 작업** |
| E7 | 조립 | `RootFlatCycleData (2b) m` → `finalRootFlatTorusCertificate_of_cycleData` → `OddEndpointPayloadEngine.run`, Main `assume_oddEndpoint` 제거 | E6 후 |

### E6 설계 메모 (2026-06-10 시점 핸드오프)

- 입력 준비물: E5 `rowSchedule`+`LayerDesc` plan, E2 `towerMap_singleCycle`+
  `rankEquiv_of_singleCycle`, E3/E4 사이트·슬롯, H1a
  `terminalA2CarrierCyclicityFamily`(닫힘), `UnitCarry`의
  `complementSingletonSquareProductExponentSingleCycle`(1/m²−1 지수, 닫힘).
- 본체: (i) layer plan의 구체 선택 — 논문 §localized rows의 ribbon support를
  E3 사이트의 cylinder로 잡고 E5 불변성 가설 충족 확인; (ii) `returnMap c`의
  m-fold 합성을 색 클래스별(터미널 t_i / lane d_j·μ_j)로 추상 skew 구조에
  대응 — 여기서 E2 역방향 rank로 부모/터미널 주기를 정규화; (iii) E± fiber의
  lifted RF2(audit 항목 6)는 E5 cylinder 기준으로 처리 예상.
- 위험: returnMap 합성↔추상 return의 동일성이 (H1b처럼) wild 대응을 요구하지
  않는지 — 논문은 endpoint chart에서 **선형 임베딩 Φ**(audit §1.7)를 명시하므로
  H1b와 달리 tame하게 닫힐 것으로 예상되나, E6 착수 시 displacement 예산
  검사(주기당 스텝 수 합 ≤ m)를 색 클래스별로 먼저 수행할 것.

부모 주기 `M_i = m-power` 정규화(`rank : Base ≃ ZMod N` 요구)는 E6에서
부모 HD의 cyclic enumeration으로 처리 — 위험 항목(audit §4 산술 함정 참조).

## 3. 오늘 세션 기록

- H1b는 wild-e 차단으로 보류(`H1B_REALIZATION_OBSTRUCTION_20260609.md`),
  순서 조정 H6 → H5 → H1b.
- E1 착수.
