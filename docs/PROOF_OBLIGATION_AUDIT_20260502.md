# Proof Obligation Audit

Date: 2026-05-02.

This audit records what the current Lean/program artifacts actually prove for
the active D7/D5-even research goal.  It is deliberately not a completion
claim: the finite manifests and green builds below are evidence for specific
interfaces, not substitutes for the remaining uniform theorems.

## Goal-To-Artifact Map

| Goal item | Current artifact | What is covered | What is not covered |
|---|---|---|---|
| Keep closed D7 odd torus/Cayley endpoint as regression target | `D7Odd/Cayley.lean`, `D7Odd/Torus.lean`, `D7Odd/Handoff/Additive4Plus2Goal.lean` | The existing odd D7 endpoint remains closed in Lean.  The additive bridge can lower to the same torus/Cayley endpoint once the bridge certificate target is supplied. | This does not by itself prove the new structural `4+2` explanation uniformly for all odd `m`. |
| D7 odd additive `A7 ~= A5 x A3` bridge | `D7Odd/Handoff/Additive4Plus2*.lean` | Root-state product chart, local bridge schedule, row/layer local facts, and endpoint adapters are formalized. | Uniform construction of the all-odd bridge data remains open. |
| D7 Target A base rank-step | `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`, `D7Odd/Handoff/TargetASeamQuotient.lean`, `scripts/verify_targetA_23_32_seam_quotient.py` | `BridgeConcreteFullRankPackage` names the Lean-facing base rank `A5 -> ZMod (m^4)` and derives base orbit coverage from rank step.  The `23/32` seam quotient arithmetic is closed in Lean for `h >= 6`; the verifier checks Q-hitting, Q-first-return formulas, and length sums over the tested range. | Lean still needs actual Q-hitting and length-sum proofs, small-modulus packaging, and a seven-row column exact-cover family.  The current `23/32` branch covers the good class structurally, not the full Target-A row-family problem. |
| D7 Target B' fiber rank-step | `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`, `D7Odd/Handoff/Additive4Plus2TargetB.lean`, `scripts/verify_zero_set_k_cert.py`, `scripts/verify_d7_4plus2_rank_fingerprints.py` | `BridgeConcreteFullRankPackage` names the fiber rank `A3 -> ZMod (m^2)` and derives monodromy single-cycle from rank step.  `Additive4Plus2TargetB.lean` proves the triangular A3 scalar criterion: a clock/carry map `(s,x) |-> (s+A, x+phi(s))` is one `m^2` cycle when the clock scalar `A`, full-round carry scalar `E`, and round-return equation are supplied with `A,E` units.  It also combines this with the base `m^4` rank-step as `BridgeConcreteScalarMonodromyPackage`, lowering scalar Target-B' data to the bridge torus/Cayley endpoints.  The `m=9` scalar zero-set-only `K(Z)` certificate now checks scalar units, extracts finite `phi(s)` tables, verifies the triangular `roundAtZero` equations, and runs the full finite bridge replay.  Compact `m=11,13,17` witnesses have committed base/fiber rank fingerprints. | No uniform zero-set-only or congruence-family `K_m(Z)` theorem is proved.  The remaining Lean gap is to derive the triangular round-return equation and scalar units from the selected row schedule and `K_m(Z)`. |
| D5 even Route-E periodic-excursion track | `D5Odd/EvenRouteE.lean`, `D5Odd/EvenRouteEM4.lean`, `scripts/verify_d5_even_routeE.py`, `scripts/verify_d5_routeE_nonopen_bundle.py`, `scripts/verify_d5_routeE_small_seam_rank_certs.py` | The finite `m=4` branch is closed.  The canonical `Theta_s` small-seam certificate lowers to D5 Hamilton/Torus/Cayley endpoints.  The ranked piecewise certificate derives the seam one-cycle from a rank into `ZMod (m-1)`.  The finite `m=6,8,...,60` bundle table is checked against the repo table and verifier transcript; the rank/block certs verify rank step, maximal translation blocks, and return-time sum. | The all-even symbolic proof is still open: count/slot residue families, first-return equations/minimality, uniform seam rank formulas, and return-time sums must be proved. |
| D7 even separate track | `D7Odd/Even.lean` | The even D7 target remains isolated behind the `RootFlatSchedule` certificate interface and endpoint adapters. | A new uniform D7-even certificate family is not supplied here. |
| Composite/root-flat/local bridge/monodromy infrastructure | `Shared/*.lean`, `RoundComposite.lean`, `RoundComposite/ConcreteEndpoints.lean` | The shared root-flat lift, monodromy/rank-cycle lemmas, and graph-level composite endpoints build.  New D7/D5 propositions are intended to plug into these interfaces. | No new prime-odd or even certificate is created by the composite infrastructure alone. |

## Current Verification Snapshot

Lean builds rerun on 2026-05-02:

```text
lake build D7Odd.Handoff.TargetASeamQuotient D7Odd.Handoff.Additive4Plus2ConcreteGoal
=> Build completed successfully (8378 jobs).

lake build D7Odd.Handoff.Additive4Plus2TargetB D7Odd.Handoff
=> Build completed successfully (8384 jobs).

lake build D5Odd.EvenRouteE D5Odd.EvenRouteEM4 D7Odd.Even
=> Build completed successfully (8379 jobs).

lake build RoundComposite.ConcreteEndpoints
=> Build completed successfully (8375 jobs).
```

Program regressions rerun on 2026-05-02:

```text
python3 scripts/verify_d7_4plus2_rank_fingerprints.py \
  --json-out /tmp/d7_4plus2_rank_fingerprint_current.json
=> witnesses 3 all_ok True missing [] extra []

python3 scripts/verify_zero_set_k_cert.py \
  certs/d7_m9_zero_set_K_scalar_cert.json \
  --triangular-manifest certs/d7_m9_zero_set_K_triangular_obligations.json \
  --json-out /tmp/d7_m9_zero_set_K_scalar_triangular_full.json
=> m=9 scalar_ok=True triangular_ok=True table_ok=True expanded_valid=True full_ok=True
=> triangular_manifest_ok True mismatches []

python3 scripts/verify_4plus2_allN_bridge_cert.py \
  --cert-json certs/d7_m9_zero_set_K_full_bridge_cert.json
=> verified m=9 product_states=531441 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single

python3 scripts/verify_targetA_23_32_seam_quotient.py \
  --moduli 13,15,17,19,21,23,25,27,29,31,33,35,37,39,41 \
  --phi-max 200 \
  --manifest certs/d7_targetA_23_32_seam_quotient_manifest.json \
  --json-out /tmp/d7_targetA_23_32_seam_quotient_current.json
=> phi_all_ok=True, all_ok=True
=> manifest_ok True mismatches []

python3 scripts/summarize_d5_routeE_small_seam_blocks.py \
  --json-out /tmp/d5_routeE_small_seam_block_summary_current.json
=> cases 28 all_ok True return_sums_ok True

python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --json-out /tmp/d5_routeE_small_seam_family_scan_current.json
=> manifest_ok True mismatches []

python3 scripts/verify_d5_routeE_nonopen_bundle.py \
  /data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip \
  --json-out /tmp/d5_routeE_nonopen_bundle_check.json
=> cases 28 tsv_matches_repo True report_matches_tsv True python_recompute_all_ok True all_ok True

python3 scripts/verify_d5_even_routeE.py --mode section \
  --section-scan-moduli 6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60 \
  --section-scan-limit 1 \
  --full-scan-moduli 6,8,10,12,14,16,18,20 \
  --full-scan-limit 1 \
  --manifest certs/d5_routeE_open_port_manifest.json \
  --json-out /tmp/d5_routeE_open_port_manifest_verify.json
=> manifest_ok True mismatches []

python3 scripts/verify_d5_routeE_small_seam_rank_certs.py \
  --cert certs/d5_routeE_small_seam_rank_certs.json \
  --json-out /tmp/d5_routeE_small_seam_rank_cert_current.json
=> cases 28 all_ok True missing [] extra []
```

The D5 build replays existing `D5Odd.ReturnCycle` linter warnings.  They are
not new proof gaps for this audit, but they remain cleanup debt.

## Current Blocking Propositions

The sharpest remaining propositions are:

1. **D7 Target A, row family.**  Produce seven all-zero-set base row words for
   every odd `m >= 5`, prove column exact-cover, and prove the canonical
   folded base return admits a bijective rank into `ZMod (m^4)` stepping by
   `+1`.
2. **D7 Target A, `23/32` proof completion.**  Formalize the Q-hitting,
   Q-first-return, and length-sum obligations currently verified by
   `verify_targetA_23_32_seam_quotient.py`, and package the small moduli.
3. **D7 Target B'.**  Generalize the finite `m=9` zero-set-only scalar
   certificate, or replace it by a congruence-family `K_m(Z)`, then prove that
   the selected row schedule and `K_m(Z)` produce the triangular A3
   round-return equation and unit scalars needed by
   `A3TriangularScalarCertificate`.
4. **D5 even Route-E.**  Find count/slot families covering every even
   `m >= 6`; prove the induced `Theta_s` first-return equations and
   minimality; prove a uniform seam rank formula into `ZMod (m-1)`; and prove
   `sum tau = m^4`.
5. **D7 even.**  Keep the RootFlatSchedule route separate and supply a
   certificate family only on that track.

## Practical Next Checks

When another bundle arrives, the first comparison should ask whether it
supplies one of the missing propositions above rather than just another finite
cycle witness.  In particular:

- For D7 odd, look for row-family exact-cover formulas, explicit base/fiber
  rank formulas, or a uniform `K_m(Z)` scalar proof.
- For D5 even, look for residue-class count/slot families and symbolic
  one-dimensional small-seam proofs, not only additional finite moduli.
- For D7 even, reject anything that silently mixes into the D7 odd `4+2`
  bridge; it belongs behind the separate root-flat certificate interface.
