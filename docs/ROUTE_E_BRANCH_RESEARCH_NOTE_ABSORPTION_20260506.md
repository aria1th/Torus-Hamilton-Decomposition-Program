# Route-E branch research note absorption

Date: 2026-05-06

Package read:

- `/data/angel/repos/etc/RouteE/RouteE_branch_research_note_package_20260506.zip`

Extracted files:

- `RouteE_branch_research_note_B20_B16_R14e_20260506.md`
- `routeE_research_note_symbolic_checks.py`
- `routeE_research_note_symbolic_checks_output.txt`

## Status

The package is consistent with the current Route-E audit direction.  It does
not claim a concrete `RouteEAllPairSectionCertificate` for B20, B16, or R14e.
Instead it records branch-independent finite-map reductions and isolates the
remaining branch-specific first-return and no-early obligations.

The included symbolic output records:

```text
B20 insert: 240*q + 191 target 240*q + 191 True
B20 T03+T04: 10368*q**3 + 24426*q**2 + 19179*q + 5038
B20 time: True
B16 insert: 240*q + 151 target 240*q + 151 True
B16 time: True
R14e insert: 480*k + 131 target 480*k + 131 True
R14e time: True
```

The local rerun of `routeE_research_note_symbolic_checks.py` currently fails
because `sympy` is not installed in this checkout.  The recorded output is
therefore treated as package evidence, while low-risk arithmetic identities
that do not need `sympy` have been mirrored directly in Lean.

## Absorbed Lean Facts

B20:

- `RouteEB20.insertionBoundaryCountTarget`
- `RouteEB20.insertionBoundaryCountTarget_eq_boundary_card`
- `RouteEB20.insertionWeightedCountTarget`
- `RouteEB20.insertionWeightedCountTarget_eq_allPairRowCountTarget`

These formalize the note's B20 boundary-to-all-pair insertion distribution
counts.  The unweighted count matches `|B| = 3m - 2`; the weighted count matches
`|P| = 1 + 10(m - 1)` for `m = 24q + 20`.

B16:

- `RouteEB16.insertionBoundaryCountTarget`
- `RouteEB16.insertionBoundaryCountTarget_eq_boundary_card`
- `RouteEB16.insertionWeightedCountTarget`
- `RouteEB16.insertionWeightedCountTarget_eq_allPairRowCountTarget`

These formalize the note's B16 insertion distribution counts.  The unweighted
count matches `|B| = 3m - 2`; the weighted count matches
`|P| = 1 + 10(m - 1)` for `m = 24q + 16`.

R14e:

- The analogous insertion boundary count and weighted count targets were
  already present as `RouteER14e.insertionBoundaryCountTarget`,
  `RouteER14e.insertionBoundaryCountTarget_eq_boundary_card`,
  `RouteER14e.insertionWeightedCountTarget`, and
  `RouteER14e.insertionWeightedCountTarget_eq_allPairRowCountTarget`.

## Proof Direction

The note reinforces the intended Route-E proof chain:

```text
macro one-cycle
=> boundary one-cycle
=> all-pair one-cycle
=> root-flat one-cycle
=> D5(m) branch endpoint
```

This means future work should not try to prove all-pair transitivity by raw
enumeration when a boundary insertion proof is available.  The reusable Lean
surface for this is `RouteEAllPairBoundaryInsertionTarget`, whose
`sectionReturn_single` theorem already packages the boundary insertion lift.

## Branch Queue

B20 is the closest branch.  The boundary quotient one-cycle is already
Lean-closed, and the newly added insertion-count arithmetic confirms the
cardinality side of the boundary-to-all-pair lift.  Remaining B20 obligations:

- pointwise boundary insertion equations;
- no-intermediate-boundary for insertion legs;
- first-principles `03`, `04`, and `34` boundary clock/no-early derivations;
- residual-core first-return/no-early derivation for `14`, `23`, and `24`;
- finite `m = 20` table certificate;
- concrete `RouteEAllPairSectionCertificate` instance.

B16 remains proof-facing.  The macro length total and insertion count
arithmetic are now Lean-visible, but the concrete branch still needs:

- boundary quotient formula derived from zero-event congruences;
- macro-return equations and no-early proofs;
- pointwise insertion distribution and no-intermediate-boundary;
- label-wise or label-destination time mass derivation;
- finite `m = 16` certificate.

R14e remains proof-facing at the same structural level as B16.  Its insertion
arithmetic was already Lean-visible.  The concrete branch still needs:

- boundary quotient formula derived from zero-event congruences;
- macro-return equations and no-early proofs;
- pointwise insertion distribution and no-intermediate-boundary;
- label-wise or label-destination time mass derivation;
- finite `m = 14` certificate.

## Negative Controls

The note records three shortcuts that should not be promoted to theorem
statements:

- time exhaustion alone is not enough;
- symmetric unit choice `x = z` is not enough;
- a small macro section found after observing an all-pair cycle is only pattern
  evidence unless the return equations, no-early facts, and length sum are
  established directly.

The specific negative example recorded by the package is `m = 134`, `x = z =
23`: observed total time is correct, but the section map splits.

## Verification

Checked after the Lean absorption:

```bash
lake env lean D5Odd/EvenRouteE.lean
```
