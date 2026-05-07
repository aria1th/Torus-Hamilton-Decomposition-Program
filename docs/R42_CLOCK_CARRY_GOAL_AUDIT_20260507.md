# R42 Clock-Carry Goal Audit

Date: 2026-05-07.

Goal:

```text
Explain or refute B42/R42 using the c-band clock-carry transducer program.
```

## Verdict

The one-piece R42 c-band threshold/residue carry refinement is refuted as a
branch promotion path.

The residue should now be split into two mod-96 sub-branches:

```text
R42-even: q = 2s,     m = 96s + 42, c = 12s + 5
R42-odd:  q = 2s + 1, m = 96s + 90, c = 12s + 11
```

R42-even remains a plausible depth-three carry candidate.  R42-odd is not
explained by the tested phase-shifted depth-three grammar.

This does not prove that every conceivable R42 transducer is impossible.  It
does prove that the current refinement chain should not be promoted:

```text
29-block / 69-edge projection
  -> c-band + u mod 6 atoms
  -> one/two/three threshold-residue carry corrections
  -> R42-odd phase-shifted depth-three test
```

The remaining R42 theorem obligations are still absent:

```text
closed pointwise first-return equations
symbolic no-early/minimality proof
Lean-facing endpoint theorem
```

## Evidence Chain

The audit artifact is:

```text
certs/routeE_r42_clock_carry_goal_audit.json
```

It checks the following concrete evidence.

1. R42 is naturally reparameterized as

   ```text
   c = 6*q + 5
   m = 8*c + 2
   x = z = c
   ```

2. The c-band support atoms cover the sampled qtime-missing supports, with
   116 atoms in each parity branch.

3. The first c-band qtime model fits all sampled slopes but leaves exactly
   9 bad qtime-intercept atoms in each parity branch.

4. A two-sample split initially suggested

   ```text
   8 one-feature atoms + 1 two-feature atom
   ```

   in each parity branch.

5. The larger stress test `q=6,8,10` and `q=7,9,11` refutes that split as a
   stable branch law:

   ```text
   7 one-feature atoms + 1 two-feature atom + 1 unresolved atom
   ```

6. The unresolved atom is

   ```text
   20->26|L1|B7:7|R0:0
   ```

   On even samples it is rescued by depth 3.  On odd samples it is not rescued
   by any tested threshold/residue feature set through depth 3.

7. The natural next R42-odd test also fails.  The artifact

   ```text
   certs/routeE_r42_odd_phase_shifted_carry.json
   ```

   checks one threshold/reversed-threshold carry together with phase-shifted
   gates

   ```text
   ±j + alpha*q + beta == 0 mod 5
   ±j + gamma*q + delta == 0 mod 6
   ```

   on the same unresolved atom.  It checks `302400` candidates and leaves
   `0` two-prime modular survivors.  The verifier artifact is

   ```text
   certs/routeE_r42_odd_phase_shifted_carry_verification.json
   ```

## Practical Consequence

Do not promote R42 as a single `m = 48q + 42` branch.  Keep R42-even as a
candidate depth-three carry branch, but treat R42-odd as open unless a new raw
zero-clock winner/carry state is introduced.

The next diagnostic entry point for that raw-state search is:

```text
scripts/summarize_routeE_r42_unresolved_atom_raw_trace.py
```

It dumps selector counts, zero-winner masks, and carry totals for the unresolved
atom.  It is a search artifact, not a proof checker.

The mathematical interpretation is:

```text
The 29-block/69-edge quotient is a real projection, but it is not the primitive
clock-carry object needed for the whole R42 residue.
```

Current completion status:

```text
tested_refinement_failed = true
r42_branch_closed = false
```
