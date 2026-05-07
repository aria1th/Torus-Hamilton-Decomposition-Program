# R42 Clock-Carry Goal Audit

Date: 2026-05-07.

Goal:

```text
Explain or refute B42/R42 using the c-band clock-carry transducer program.
```

## Verdict

The tested c-band threshold/residue carry refinement is refuted as a branch
promotion path.

This does not prove that every conceivable R42 transducer is impossible.  It
does prove that the current refinement chain should not be promoted:

```text
29-block / 69-edge projection
  -> c-band + u mod 6 atoms
  -> one/two/three threshold-residue carry corrections
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

## Practical Consequence

Do not continue blind atom splitting in this feature alphabet.  Either introduce
a genuinely new state variable from the raw zero-clock winner/carry dynamics,
or demote R42 from the near-term promotion queue.

The mathematical interpretation is:

```text
The 29-block/69-edge quotient is a real projection, but it is not the primitive
clock-carry object needed for a proof.
```

Current completion status:

```text
tested_refinement_failed = true
r42_branch_closed = false
```
