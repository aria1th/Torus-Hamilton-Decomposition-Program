# Contributions record (even-modulus theorem and its Lean formalization)

This file records who did what for the even-modulus extension: the mathematical
proof in the manuscript `even_directed_tori_integrated.tex` (bundle SHA256
`29f11797cfab9c68f7f33dcca2d5458f4f976f4bbb2fd600a7e3347c47214885`) and the Lean
formalization on branch `even-modulus` of this repository. The odd-modulus theorem
(`0.0.3-allodd`) has its own history in the release notes and is not restated here.

## Mathematical proof (manuscript)

| Role | Contributor | Detail |
|---|---|---|
| Proof completion | GPT-6-Pro | Completed the proof of the even-modulus theorem in a 30-turn session, about 12 hours of model reasoning in total. |
| Direction, generalization, corrections | Human author (repository owner) | Set the direction of the argument, supplied the generalizations, and corrected some of the ideas during the session. |

## Lean formalization (branch `even-modulus`)

| Phase | Contributor | Scope |
|---|---|---|
| Design and early formalization | Claude Fable 5.1 | Formalization plan (`docs/EVEN_MODULUS_FORMALIZATION_PLAN_20260910.md`), environment lock, isolation of retired attempts (`TorusEvenAttic`, `attic/`), parity-neutral dispatcher (E1), `D_3` even by vendoring (E2), `D_5` even for `m ≥ 6` by the chronological transversal route (E3). Commits `2f94a33` … `8306446` (2026-09-10). |
| Middle and late formalization | GPT 6 Astra (max) | Relative collar closure and every even degree (E4, `TorusEven/Collar/`), anchored cyclic star, near core, shell, matched selection and the odd-degree entry (E5, `TorusEven/Entry/`), the final assemblies `even_modulus_tori_all_dimensions` and `TorusAll.all_moduli_tori_all_dimensions`, per-stage `#print axioms` audits. Commits `d335aa4` … `7e9fbd5` (2026-09-11). |
| Record and review | Claude Fable 5.1 | Independent re-verification of the final endpoints on the source checkout (`evidence/lean_audit_20260911/final-control-check/`), import of the per-stage audit artifacts, ledger and documentation consolidation, release preparation (2026-09-11). |
| Direction and acceptance | Human author (repository owner) | Chose the route, set the acceptance criteria (kernel-checked theorems, standard axioms plus the registered finite `native_decide` leaves, no import of retired attempts) and reviewed the outputs. |

## What the record means

- Every theorem named above is checked by the Lean 4 kernel (toolchain
  `leanprover/lean4:v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`).
  The provenance of a proof text does not enter the trust argument; the axiom
  lists in `docs/EVEN_AXIOM_LEDGER.md` do.
- The final even endpoint depends on `propext`, `Classical.choice`, `Quot.sound`
  and 18 registered finite leaves (the `D_5(4)` and `D_3` seeds). The theorems
  `even_odd_degree`, `even_degree_collar` and `d5_even_large` use the three
  standard axioms only.
- Retired attempts are kept under `TorusEvenAttic/` and `attic/` with their own
  ledger and are imported by no proof path.
