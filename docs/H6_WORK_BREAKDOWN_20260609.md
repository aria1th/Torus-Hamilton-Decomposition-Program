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
| E1 | **EndpointChart** | `Ω : Fin (2b+1)` 순환 순서(τ₀τ₁τ₂ p₁⁺p₁⁻…), 색 이름표(t/d/μ), 행 `N/X_i/R/C_h`를 `Equiv.Perm Ω`로, Latin성, b=4 지표 = 논문 chart 6행 대조 | **착수 (2026-06-09)** |
| E2 | Completion tower | 1좌표 `FinCompletionCarryCertificate`를 b−1좌표 순차 부가로 일반화 (각 단계 캐리 ±1, off-crossing 0 재확립) | 대기 |
| E3 | Reset common-image (parametric) | `r₀+δ_{p₁⁻} = r₁+δ_{p₂⁻} = I`의 `(ℤ/m)^{b−1}` 판 + row list `𝒫 ∈ E^{b+4}` 분리 | 대기 |
| E4 | Renewal capacity + 역할 분할 | `2b+4 < 4^{b−1}` (b≥4) + `Fin 3 ⊕ Fin 2b ⊕ Unit` 역할 슬롯 (2a+3과 구분!) | 대기 |
| E5 | Child schedule + RF1/RF2 | E1 행을 support 위에 깔아 `dir : ZMod m → RootState (2b) m → …` 구성, 행 Latin → RF1, ribbon RF2 | E1 후 |
| E6 | RF3 | product-cycle exponent(닫힘: `UnitCarry`) + H1a family + E2 tower 합성으로 `returnsSingleCycle` | E1,E2,E5 후 |
| E7 | 조립 | `RootFlatCycleData (2b) m` → bridge → `run` 구성, Main `assume_oddEndpoint` 제거 | 전체 후 |

부모 주기 `M_i = m-power` 정규화(`rank : Base ≃ ZMod N` 요구)는 E6에서
부모 HD의 cyclic enumeration으로 처리 — 위험 항목(audit §4 산술 함정 참조).

## 3. 오늘 세션 기록

- H1b는 wild-e 차단으로 보류(`H1B_REALIZATION_OBSTRUCTION_20260609.md`),
  순서 조정 H6 → H5 → H1b.
- E1 착수.
