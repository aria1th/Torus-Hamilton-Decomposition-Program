# A5 to A7 Current Proofs Bundle

Date: 2026-05-01.

Source files:

- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_v0_3.zip`
- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_note_v0_3.md`

This note records the update from the current-proofs bundle.  It is a
research-state update, not a completion certificate.

## Main Update

The local and structural parts of the `4+2` bridge should now be treated as
settled infrastructure:

- local `A7 ~= A5 x A3` bridge layer factorization;
- column exact-cover schedule criterion;
- skew-product monodromy criterion;
- triangular `A3` scalar primitiveity criterion;
- zero-set stratum reduction for Target B';
- one-`P` obstruction for directly lifting the mixed D5 odd schedule.

The new mathematical content is on Target A.  The `23/32` pass/fail pattern is
now explained by a seam quotient, not merely by finite cycle data.

## Seam Quotient

For `W = 23` or `W = 32`, let `Phi_W` be the first-return map on

```text
Sigma = {(0,a,b,0,-a-b) : a+b != 0}.
```

Define seam states

```text
B_i = (i,0),  A_j = (0,j),  1 <= i,j <= m-1,
Q = {B_i} union {A_j}.
```

For odd `m = 2h + 1`, `m >= 13`, the bundle gives a common `B`-chain

```text
B_i -> B_{i+1},  B_{m-1} -> A_1.
```

After collapsing the `B`-chain and the alternating `A`-line, both words are
controlled by the same map on `{1,...,h}`:

```text
phi_h(x) =
  x - 3  for 1 <= x <= 3,
  x - 8  for 4 <= x <= 5,
  x - 5  for 6 <= x <= h,
```

with residues represented in `{1,...,h}`.

The arithmetic theorem is:

```text
phi_h is one cycle  iff  h != 3 mod 5
                   iff  m != 2 mod 5.
```

When `h == 3 mod 5`, the quotient has five cycles.  This explains the bad
class for `23/32` structurally.

A Lean-friendly proof route is to use the inverse map.  In 1-based
coordinates, `phi_h^{-1}` is:

```text
x -> x + 5     for 1 <= x <= h-5,
h-4 -> 4,
h-3 -> 5,
h-2 -> 1,
h-1 -> 2,
h   -> 3.
```

Thus the inverse walks upward by `5` inside each residue class modulo `5`.
When it crosses the top five-point boundary, the residue class changes by

```text
3 - h mod 5.
```

Since `5` is prime, this boundary shift is transitive on the five residue
classes exactly when `h != 3 mod 5`.  If `h == 3 mod 5`, the shift is zero and
the five cycles are just the five residue classes, with lengths
`ceil(h/5),ceil(h/5),ceil(h/5),floor(h/5),floor(h/5)`.

## Remaining 23/32 Proof Obligations

The seam quotient removes the need to guess the `m == 2 mod 5` obstruction.
For `m >= 13`, the generic `23/32` primitive block theorem is now reduced to
two geometric lemmas plus the quotient arithmetic:

1. **Q-hitting:** every point of `Sigma` reaches `Q` under `Phi_W`;
2. **length sum:** `sum_{x in Sigma} ell_W(x) = m^4`.

Small odd moduli should be packaged separately:

- `m = 5,9,11`: primitive branch;
- `m = 7`: exceptional branch.

The exact-cover row schedule obligation remains separate from the primitive
block theorem.

## Verification Added

The new script

```text
scripts/verify_targetA_23_32_seam_quotient.py
```

checks the quotient as a finite regression:

- the arithmetic cycle theorem for `phi_h`;
- the inverse formula and the residue-boundary shift explanation;
- finite Q-hitting for the computed `Sigma` first-return table;
- the stated Q-first-return formulas for `23` and `32`;
- the length-sum identity in the same runs.

The broader local check used for this absorption was:

```bash
python3 scripts/verify_targetA_23_32_seam_quotient.py \
  --moduli 13,15,17,19,21,23,25,27,29,31,33,35,37,39,41 \
  --phi-max 200 \
  --json-out /tmp/targetA_23_32_seam_quotient_13_41.json
```

It reported `all_ok=True`.

The matching Lean-facing target is now:

```text
D7Odd/Handoff/TargetASeamQuotient.lean
```

It defines the quotient map `phi_h`, the inverse map, the good class
`h % 5 != 3`, and a `TargetASeamQuotientPackage` collecting the still-missing
formal obligations: the single-cycle arithmetic theorem, Q-hitting,
Q-first-return formulas, and the two length-sum identities.  The inverse-map
identities, bijectivity of `phi_h` for `h >= 6`, and the residue-shift unit
gate

```text
IsUnit (3 - h : ZMod 5) iff h % 5 != 3
```

are already proved in Lean.  This file is a proof interface, not a completed
Target-A theorem.  It also exposes branch lemmas for the inverse map: away
from the top boundary `phi_h^{-1}(x)=x+5`, while the top five points
`h-5,h-4,h-3,h-2,h-1` map to `3,4,0,1,2`.

## Updated Target-A Interpretation

Target A now has three layers:

1. prove the `23/32` primitive block theorem for `m != 2 mod 5` using
   Q-hitting, length sum, and the seam quotient arithmetic;
2. construct correction/splicing rows for `m == 2 mod 5`;
3. assemble seven primitive rows satisfying the column exact-cover constraint.

Target B' remains schedule-dependent: after a row schedule is fixed, solve the
zero-set-only or congruence-family `K_m(Z)` scalar unit problem for the `A3`
fiber.
