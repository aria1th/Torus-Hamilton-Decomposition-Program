# D5 Even Route E Proof Progress

Date: 2026-05-06.

This note records the strongest proof progress currently extracted for the D5
even Route-E program.

## What Is Now Proved By Computation

The known embedded witnesses can be converted into prefix-root-flat layer
tables and checked by the generic nested first-return diagnostics.

Commands:

```bash
python3 scripts/export_d5_even_routeE_layers.py \
  --m 4 \
  --json-out /tmp/d5_routeE_layers_m4_20260506.json

python3 scripts/d5_routeE_nested_diagnostics.py \
  /tmp/d5_routeE_layers_m4_20260506.json
```

The same conversion was run for `m=6,8,10`.

Observed output shape:

```text
rf1_ok=True
rf2_ok=True
sign_product=-1 sign_target=-1 sign_ok=True
return_cycles=[m^4]
level cycles=[m^3], [m^2], [m], [1]
all nested time sums are correct
```

Concrete samples:

| `m` | witness type | nested result |
| ---: | --- | --- |
| 4 | finite `C/E/O` witness | all five colors pass |
| 6 | one-`Lambda_E` witness | color 0 passes; color symmetry gives the other colors |
| 8 | one-`Lambda_E` witness | color 0 passes; color symmetry gives the other colors |
| 10 | one-`Lambda_E` witness | color 0 passes; color symmetry gives the other colors |

This does not prove all even `m`, but it proves that the nested `Q4` viewpoint
is a real structure of the existing witnesses, not merely a proposed language.

## One-Lambda_E Reduction

For `m >= 6` in the embedded table, the witness has the form:

```text
constant C layers with count vector nu
one exceptional Lambda_E layer
cyclic color shifts
```

The full color return can therefore be studied as a single bulk translation
followed by the `Lambda_E` zero-mask rule.  This is exactly the setting of the
small-seam scripts and of the B20/B16/R14e branch packages.

Thus the current proof route should be:

```text
branch count formula
=> one-Lambda_E return formula
=> small-seam/all-pair first-return formula
=> nested Q4 first-return gates
=> root-flat RF3
=> D5 Hamilton decomposition
```

The last two arrows are now mechanically audited by
`d5_routeE_nested_diagnostics.py` once a concrete layer table is supplied.

## Local Defect Layer Is Finite Adjacent-Switch Data

The exceptional `Lambda_E` layer is controlled by the shifted zero mask.  In
prefix coordinates `(z1,z2,z3,z4)`, the five mask predicates are:

| bit | predicate |
| ---: | --- |
| 0 | `z4 = z3` |
| 1 | `z3 = z2` |
| 2 | `z2 = z1` |
| 3 | `z1 = 0` |
| 4 | `z4 = 0` |

Only 27 masks are reachable.  The five masks with exactly four zero bits are
impossible because four equalities force the fifth.  The reachable masks induce
26 distinct local stop-rank permutations.

The analyzer:

```bash
python3 scripts/analyze_d5_routeE_defect_layer.py
```

shows that every local permutation is a word in adjacent stop-rank switches
relative to the bulk row `(4,3,2,1,0)`.  The shortest words have length at most
`9`.

Examples:

```text
mask 01000, predicate z1=0:
  row=(3,4,2,1,0)
  word=3/4

mask 10000, predicate z4=0:
  row=(4,2,3,1,0)
  word=2/3

mask 00001, predicate z4=z3:
  row=(4,3,1,2,0)
  word=1/2

mask 00010, predicate z3=z2:
  row=(4,3,2,0,1)
  word=0/1
```

The full CSV-style table can be regenerated with:

```bash
python3 scripts/analyze_d5_routeE_defect_layer.py --csv \
  > /tmp/d5_routeE_defect_layer_20260506.csv
```

This is a partial proof of the adjacent-switch principle: the local defect
layer is built from adjacent stop-rank swaps.  What remains is to prove that
the resulting global return has a stable symbolic nested first-return formula
for a covering set of residue branches.

## B20 Trace Profile Diagnostic

The B20 trace-profile analyzer:

```bash
python3 scripts/analyze_d5_routeE_b20_trace_profiles.py \
  --moduli 20,44,68 \
  --json-out /tmp/d5_routeE_b20_profiles_20260506.json
```

shows that full shifted zero-mask profiles are not constant on the broad B20
source classes.  In contrast, the aggregate stop-rank count profile is constant
on each source class.  See
`docs/D5_EVEN_ROUTE_E_B20_TRACE_PROFILE_20260506.md`.

This changes the proof target: the symbolic B20 proof should track affine
hit-time sums for the zero-mask predicates and derive the stop-rank aggregate,
rather than trying to identify complete zero-mask words by return-time class.

The `m = 2` SAT witness remains only a smoke test for the full layered
encoding.  The actual Route-E even target is `m >= 4`; the one-`Lambda_E`
branch-formula target begins at `m >= 6`.

## What Is Disproved

The following sub-ansatzes should no longer be treated as viable proof routes:

1. **Stationary seam table.**  The old stationary SAT encoding is already
   `unsat` at `m=2`.  It is too narrow and should not be extrapolated.
2. **Fixed symmetric packet law.**  The candidate
   `m=48*k+38`, `nu=(11,m-23,0,11,0)` fails at `m=230` after four successful
   samples.
3. **Short hit streak promotion.**  Any branch law must survive a next-sample
   falsification check before formula fitting.

## Remaining Mathematical Blocker

The current blocker is not RF1/RF2/sign/nested-cycle checking.  Those are now
well-defined and pass known witnesses.

The real blocker is symbolic branch extraction:

```text
For a residue branch such as B20/B16/R14e,
prove the pointwise first-return map and no-earlier-return formula
for the one-Lambda_E bulk+defect return.
```

For B20 this is already isolated in Lean-facing language:

```text
counts:        (r, 0, 0, h+r, r), m = 24*q + 20
seam map:      two translation blocks
time formula:  six-value pointwise return-time partition
open theorem:  symbolic port-time/minimality proof
```

Thus the next proof step should not search a new high-level mechanism.  It
should attack the B20 symbolic trace theorem first, because B20 already has
the cleanest branch formula and a verified weighted time-sum identity.

## Current Status

Strongest honest statement:

```text
D5 even Route E is reduced to a finite branch-menu symbolic trace problem.

The existing witnesses satisfy the four-level nested root-flat certificate.
The local Lambda_E defect layer is finite adjacent-switch data.
The remaining open theorem is the symbolic first-return/minimality calculation
for enough residue branches to cover all even m >= 6.
```

This is significant progress, but it is not yet an all-even proof.
