# A5 Exceptional Phase-Splice Bundle v0.4

Date: 2026-05-02.

Source bundle:

- `/data/angel/repos/etc/A5_exceptional_phase_splice_bundle_v0_4.zip`

This note records the D7 Target-A payload of the exceptional A5 phase-splice
bundle.  It is a research-state note, not a completed Target-A proof.

## Bundle Contents

The bundle contains:

- `A5_to_A7_exceptional_branch_flow_note_v0_4.md`: integrated flow note for
  the Target-A exceptional branch after the correction block was identified;
- `A5_exceptional_00_phase_offset_table_v0_2.md`: symbolic phase-offset table
  for the `00` correction block in the exceptional class;
- `compute_exceptional_00_phase_table.py`: phase-table reproduction script;
- `compute_exceptional_00_phase_table_m27_output.txt`: sample output for
  `m = 27`;
- prior context notes for the `23/32` seam quotient, failure-class pattern,
  candidate word probes, Sigma analysis, and the `m = 9` Target-B scalar
  certificate.

The reproduction script assumes the helper
`compute_A5_23_32_seam_quotient.py` is available at `/mnt/data`.  Locally,
that helper was copied from the bundle and the phase-table script was rerun
for `m = 17,27,37`, matching the stated lane behavior.

The repo now has a path-stable verifier for the same phase table:

```bash
python3 scripts/verify_targetA_exceptional_phase_splice.py \
  --moduli 17,27,37 \
  --json-out /tmp/d7_targetA_exceptional_phase_splice_17_37.json
```

It recomputes the actual `00` correction action from the A5 state dynamics and
checks it against the symbolic five-lane table for both `H = 23` and `H = 32`.
On the displayed moduli it reports `all_ok=True`.

## Main Finding

The `23/32` Target-A seam quotient already explains the good class:

```text
m = 2*h + 1,
phi_h is one cycle iff h % 5 != 3 iff m % 5 != 2.
```

The exceptional class is therefore

```text
m % 5 = 2,  m odd,
equivalently m = 10*t + 7, h = 5*t + 3.
```

In this class, the `23/32` quotient splits into five lanes, indexed by
`x mod 5`, with unequal lengths:

```text
L_1,L_2,L_3: length t+1
L_4,L_0:     length t
```

The new content is that the correction block

```text
C = 00
```

acts as a component-splice operator on these lanes.  On odd A-seam states
`A_(2*x-1)`, the raw block sends `x -> x+1` except at the all-zero boundary
`x = h`; that boundary is resolved by the next internal `H = 23` or `H = 32`
return.

## Phase Table

For `H = 23`, the correction map has the generic transitions:

```text
L_1(p) -> L_2(p)
L_2(p) -> L_3(p)
L_4(p) -> L_0(p)
L_0(0) -> L_1(t)
L_0(p) -> L_1(p), 1 <= p <= t-1
```

The third lane is:

```text
L_3(0) -> L_4(0)
L_3(1)=h -> L_1(0)
L_3(p) -> L_4(p-1), 2 <= p <= t.
```

For `H = 32`, the generic transitions are the same, but the all-zero boundary
resolves differently:

```text
L_3(1)=h -> L_2(1)
```

instead of `L_1(0)`.

Thus `00` is not a standalone primitive word.  It is a splice operator to be
inserted into a controlled row or row-family construction.

## What Was Ahead

The bundle is ahead of the current repo goal statement in its treatment of the
bad class.  It does not merely say that `23/32` fails when `m % 5 = 2`; it
reduces that failure to an explicit five-lane phase system and identifies the
first useful correction operator, `00`.

The repo is ahead on the formal arithmetic infrastructure for the good class:

- `D7Odd/Handoff/TargetASeamQuotient.lean` already proves the arithmetic
  criterion `phi_h` single-cycle iff `h % 5 != 3`;
- the bad-class five-component decomposition is already present in Lean as a
  residue-component cover;
- the Target-A endpoint interfaces already lower a completed base rank-step
  into the D7 bridge, torus, and Cayley endpoints.

The missing layer is the symbolic exceptional splice theorem.  The v0.4 bundle
now provides the right reduced object for that theorem, and
`scripts/verify_targetA_exceptional_phase_splice.py` pins the finite phase
table as a regression artifact.

## Goal Impact

D7 Target A should be split more sharply:

```text
Target A1, good class:
  use 23/32 for m % 5 != 2;
  finish Q-hitting, Q-first-return, and length-sum proofs;
  package small odd moduli separately.

Target A2, exceptional class:
  for m = 10*t + 7, use the five-lane system;
  formalize the 00 correction-block phase table;
  choose a correction word or row-family insertion schedule;
  prove the reduced lane map is one cycle;
  lift back through Q-hitting and length-sum/excursion coverage.

Target A3, assembly:
  combine the good and exceptional base branches into the seven-row
  all-zero-set exact-cover/rank-step package required by the 4+2 bridge.
```

Target B' remains schedule-dependent.  The `m = 9` zero-set-only scalar
certificate in the bundle is useful evidence, but a uniform `K_m(Z)` theorem
still depends on the final Target-A row schedule.

## Reachability Assessment

The good-class `23/32` branch is close to formalizable relative to the rest of
Target A: the quotient arithmetic is already in Lean, and the remaining pieces
are the geometric Q-hitting/length-sum proofs plus small-modulus packaging.

The exceptional branch is now plausible but not immediate.  It is no longer a
full `A5(m)` orbit search; it is a symbolic problem on five unequal lanes.
However, the crucial object is still missing: a correction word or row-family
insertion pattern whose reduced lane map is one cycle and whose lift preserves
the required excursion coverage and length sum.

The realistic next step is therefore to formalize or program-check the
five-lane splice system as a standalone reduced model, then search for a
symbolic correction schedule in that reduced model before attempting the full
Lean Target-A assembly.
