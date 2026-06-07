# H2 D5(4) Paper Realization Computed Audit - 2026-06-07

This note records the current Python-vs-paper audit for the H2 realization slot.
The reproducible check is:

```bash
python3 scripts/verify_d5m4_h2_realization.py
```

## Result

The abstract paper return maps are correct and already match Lean:

- `LowD5M4Seed.fullReturn` implements the five paper maps
  `R_hat_0..R_hat_4`.
- The script independently checks that all five are 256-cycles.

The remaining H2 gap is not cyclicity.  It is the final paper sentence:

> Start with the product of the terminal A2 layer word, the Y-coordinate row
> word, and the neutral Z-row. Insert the five local substitutions...

That sentence is still missing as an actual root-flat row schedule theorem.

## Negative Checks

The script confirms the following candidates cannot close the current
paper-faithful H2 handoff.

1. `terminalStdBaseRowAtState` read at `qCoord w`.

   This naive product row is Latin and RF2 before reset substitutions, but its
   four-layer returns are short cycles, not the paper `fullReturn` maps.  There
   is no common return-section conjugacy to `LowD5M4Seed.fullReturn`.

2. Naive rows plus separated first-lift/final-lift substitutions.

   All 16 choices of `(Y-layer, Z-layer)` fail RF2.

3. The color-anchored terminal sketch
   `terminalRowEquiv (omega (q - a_c)) c`.

   It is not RF1.  At `q = (0,0)` the row is `[1,2,2]`.

4. `EvenV11/D3EvenM4.lean`.

   This finite D3 base is a valid RF certificate, but it has no common conjugacy
   to the terminal paper returns `F_0,F_1,F_2`.  The obstruction is already
   visible from a conjugacy invariant: for the finite D3 base,
   `order(R0 o R2) = 63`, while the paper terminal returns satisfy
   `order(F0 o F2) = 33`.  It cannot be reused as the paper terminal A2 carrier
   for H2 without an additional bridge that changes the H2 target.

5. `archive/EvenV11/LowD5M4Finite.lean`.

   This generated D5(4) finite witness is RF-valid, but it has no common
   conjugacy to `LowD5M4Seed.fullReturn`.  It is a direct finite fallback, not the
   paper-faithful ribbon/run-collapse handoff currently exposed by
   `LowD5M4RibbonInterface`.

## Consequence

The current Lean direction is structurally correct:

- Keep `LowD5M4Seed.fullReturn` as the abstract paper return.
- Keep `LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput` as the
  H2 target.
- Do not use `seedRootEquiv`, `paperReturn`, `terminalStdBaseRowAtState`, or the
  generated finite blobs as the proof of this target.

But H2 cannot be closed by the existing terminal/product-row interpretations.
The next proof obligation is a genuine realization theorem for the terminal A2
layer word in the root-flat schedule, followed by the switching-ribbon transport
that produces the wild common reindexing `e`.

## Recommended Order

1. Prove or state a terminal A2 root-flat realization theorem:
   actual rows, RF1/RF2, and a common return-section reindexing to
   `TerminalA2LowMod.terminalReturn`.

2. Lift that theorem to the D5(4) product with the `Y` row and neutral `Z` row.

3. Apply the five Table D54 reset substitutions through the existing singleton
   or partial-exchange RF2 interface.

4. Use the switching-ribbon/cut-splice theorem to build the wild `e` and close
   `PhysicalRowsReturnMapConjGoal`.
