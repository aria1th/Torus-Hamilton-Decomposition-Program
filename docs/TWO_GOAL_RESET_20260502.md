# Two-Goal Reset

Date: 2026-05-02.

This note resets the active research goal after absorbing the latest D7
exceptional phase-splice and D5 Route-E branch-extraction bundles. It is a
planning target, not a completion claim.

The endpoint theorems stay as regressions. The live work has two proof
programs:

1. D7 odd: replace the already-closed direct endpoint by a structural
   `A7 ~= A5 x A3` explanation.
2. D5 even: replace the older global Route-E formula search by a finite
   residue-branch menu, with B20 as the first symbolic branch.

D7 even remains a separate RootFlatSchedule track and is not part of this
two-goal reset.

## Goal 1: D7 Odd Structural Proof

Prove the closed D7 odd torus/Cayley endpoint through the additive
`A7 ~= A5 x A3` decomposition.

The target is no longer just another finite D7 witness. The target is a
uniform bridge certificate with:

- an A5 base return of rank `m^4`;
- an A3 fiber return of rank `m^2`;
- compatibility data lowering through the existing `4+2` bridge interfaces.

Current state:

- The D7 odd torus/Cayley endpoint remains closed and should stay green.
- The `4+2` bridge plumbing is Lean-facing endpoint infrastructure, not the
  mathematical blocker.
- The good-class `23/32` A5 quotient arithmetic is closed in Lean for the
  expected congruence class, while Q-hitting, Q-first-return, length-sum, and
  small-modulus packaging remain to be formalized.
- The exceptional class `m = 10*t+7` is now separated into a five-lane
  phase-splice problem. The `00` correction block phase table has program
  verification, but not a Lean proof or a chosen uniform correction schedule.
- Target B' has the triangular A3 scalar interface and finite `m=9` evidence,
  but no uniform zero-set-only or congruence-family `K_m(Z)` theorem.

Reset target:

1. Prove the good-class A5 base package.
2. Prove the exceptional A5 five-lane splice package.
3. Assemble good and exceptional branches into seven all-zero-set A5 rows with
   exact column cover and folded rank step `m^4`.
4. Choose and prove the compatible A3 fiber family `K_m(Z)`, including scalar
   unit/carry and rank step `m^2`.
5. Lower the completed package through the existing D7 odd bridge to the
   torus/Cayley endpoint.

Definition of done:

- The good-class and exceptional A5 base branches together produce a uniform
  all-odd A5 rank step of size `m^4` in the concrete all-zero-set bridge
  interface.
- The A3 Target-B' family is compatible with that base branch and produces a
  scalar monodromy rank step of size `m^2`.
- The combined package fills `BridgeConcreteFullRankPackage` (or its current
  successor interface) for every odd `m >= 5`, leaving only the already-closed
  finite `m = 3` regression branch.

Blocking propositions:

- Lean Q-hitting and length-sum theorem for the good-class `23/32` branch.
- Lean `00` phase table and one-cycle correction schedule for
  `m = 10*t+7`.
- Seven-row all-zero-set exact-cover theorem.
- Uniform Target-B' `K_m(Z)` or congruence-family scalar theorem.

Near-term Lean/program work:

- Keep `TargetASeamQuotient` green while turning the Q-return formulas into
  the Q-hitting/length-sum package.
- Convert the exceptional `m = 10*t+7` phase-splice table into named Lean
  targets before attempting a monolithic proof.
- Use finite verifiers only to extract stable row schedules, zero-set cover
  identities, and scalar/carry formulas that can become Lean propositions.

## Goal 2: D5 Even Route-E Branch Menu

Prove the D5 even Route-E endpoint by a finite residue branch menu, beginning
with the extracted B20 branch.

This replaces the earlier single global count/drift target. The finite
small-seam table is evidence, not itself a uniform theorem.

Current state:

- The finite `m = 4` branch is closed in Lean.
- The non-open small-seam bundle gives validated finite witnesses for
  `m = 6,8,...,60`.
- The `Theta_s = {rho_s(0,a,0,0,-a) : a != 0}` seam is the proof-facing
  section for the all-large branch.
- The B20 branch, `m = 24*q+20`, has verifier support for the count vector,
  two-block seam map, pointwise return-time partition, and return-time sum.
- Lean now records the B20 arithmetic target in `RouteEB20`: the count sum and
  weighted return-time polynomial identity are closed, conditional on the
  extracted pointwise return-time distribution.
- Lean also records the expected B20 seam map as addition by `h+1` on
  `Fin (m-1)`, proves the two translation-block formulas, and proves this
  expected seam map is a single cycle.  The corresponding two-block
  cover/disjoint/translation obligations are packaged as `RouteEB20.seamBlocks`.
- Lean now names the remaining B20 trace proposition as
  `RouteEB20.ThetaTraceTarget`: concrete first-return equations, no-earlier
  returns, positive return times, and the branch return-time sum.  The
  adapter `RouteEB20.thetaPiecewiseCertificateOfTraceTarget` lowers this
  target to the existing `RouteEThetaPiecewiseTranslationCertificate`.
- Lean also records the verifier's six-value B20 pointwise return-time
  formula as `RouteEB20.returnTimeFormula`.  The sharper target
  `RouteEB20.ThetaPointwiseTraceTarget` uses that formula directly and lowers
  to `RouteEB20.ThetaTraceTarget`, with the final `m^4` sum discharged by
  `RouteEB20.returnTimeWeightedSum_eq_modulus_pow_four`.  The
  `RouteEB20.returnTimeFormula_*` lemmas name the pointwise partition cases.
- Lean now also names the B20 return-time interval package as
  `RouteEB20.returnTimeBlocks`, with `RouteEB20.returnTimeBlocks_cover`
  covering the nonzero seam by the extracted intervals.  This is a
  proof-facing organization of the same pointwise formula, not a trace proof.

Reset target:

1. Finish B20 as the first symbolic branch theorem.
2. Extract enough additional residue branches to cover every even `m >= 6`.
3. For each branch prove count/slot formula, `Theta` first-return equation,
   no-earlier-return minimality, seam rank or single-cycle theorem, and
   return-time sum `m^4`.
4. Lower the branch menu through the existing all-large Route-E adapters to
   the D5 Hamilton/Torus/Cayley endpoints.

Definition of done:

- The finite menu covers all even `m >= 6` by explicit residue predicates.
- Each menu item constructs the appropriate Route-E certificate target, not
  just a verifier witness.
- The `m = 4` finite branch plus the menu lower to the existing D5 even
  Hamilton, torus, and Cayley endpoints.

B20 first formal target:

```text
m = 24*q + 20
h = 12*q + 10
r = 4*q + 3
nu = (r,0,0,h+r,r)
```

Expected seam map:

```text
1 <= a <= h-2:      V(a) = a + h + 1 mod m
h-1 <= a <= m-1:    V(a) = a + h + 2 mod m
```

The Lean arithmetic and expected-map single-cycle targets are no longer the
blockers for B20. The remaining B20 blocker is to prove symbolically that the
Route-E trace has exactly this first-return map, no earlier return, and the
extracted pointwise return-time partition, preferably by constructing
`RouteEB20.ThetaPointwiseTraceTarget q`.  The named return-time blocks should
be used as the local case split for the pointwise partition proof.

Blocking propositions:

- B20 symbolic first-return and minimality proof.
- B20 pointwise return-time partition proof, feeding the existing Lean
  weighted-sum identity.
- Construction of `RouteEB20.ThetaPointwiseTraceTarget q`; its packaging
  through `RouteEB20.ThetaTraceTarget q` against the closed expected seam map
  is now handled by
  `RouteEB20.thetaPiecewiseCertificateOfTraceTarget`.
- A finite residue branch menu covering all even `m >= 6`.

Near-term Lean/program work:

- Finish the B20 symbolic trace proof before broadening the branch menu too
  aggressively.
- Use the `returnTimeBlocks` intervals as the proof skeleton for the B20
  pointwise return-time partition.
- Extract the next branch only when it has a stable count vector, seam map,
  return-time partition, and verifier coverage on several moduli.

## Operating Rule For New Bundles

Future bundles should be judged by whether they close one of the propositions
above. Additional finite witnesses are useful only when they identify a
uniform branch formula, a rank function, or a proof-ready recurrence that can
be moved into Lean.
