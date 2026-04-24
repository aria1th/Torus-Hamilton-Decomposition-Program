# D5 odd cleanup plan, 2026-04-24

## Current closed targets

Lean now has three closed D5 odd endpoints.

```lean
theorem D5_odd_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    HamiltonDecompositionD5 m
```

This is the internal root-flat/layer-schedule theorem.

```lean
theorem D5_odd_torus_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    TorusHamiltonDecompositionD5 m
```

This is the full torus layer-lift theorem in terms of color step maps on
`Vec5 m = (Fin 5 -> ZMod m)`.

```lean
theorem D5_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    CayleyHamiltonDecompositionD5 m
```

This is the explicit Cayley-edge wrapper: each edge has the form
`x -> x + e_i`, the five schedule colors partition outgoing directions at each
vertex, and each color step is a Hamilton cycle.

Verification command:

```bash
lake build D5Odd
```

Status at creation of this note: passed.

## Recommended cleanup order

1. Freeze the public theorem surface.

   Keep `D5_odd_unconditional` as the model-level theorem and
   `D5_odd_torus_unconditional` as the full-torus theorem.  Avoid renaming
   these unless there is a paper-facing naming decision, because the current
   names are already imported by `D5Odd.lean`.

2. The thin graph-title wrapper is now done.

   `TorusHamiltonDecompositionD5` is already mathematically the Cayley
   decomposition statement: for each vertex and color it selects one outgoing
   coordinate direction, `IsScheduleLatin` partitions the five outgoing
   directions, and each color step is one Hamilton cycle.

   `D5Odd/Cayley.lean` defines:

   ```lean
   structure CayleyEdge5 (m : Nat) [NeZero m] where
     src : Vertex5 m
     dir : Direction
     dst : Vertex5 m
     hdst : dst = src + e5 m dir
   ```

   It also proves that a `TorusHamiltonDecompositionD5 m` induces an edge
   partition into five Hamilton cycles:

   ```lean
   theorem D5_odd_cayley_unconditional {m : Nat} [NeZero m]
       (hodd : Odd m) (hm3 : 3 <= m) :
       CayleyHamiltonDecompositionD5 m
   ```

   The only further wrapper would be integration with a separate graph-library
   API, if the final paper statement must use one.

3. Keep `ReturnCycle.lean` intact for now.

   It is large, but it is the most proof-sensitive file.  Splitting it is a
   refactor, not a mathematical need.  Do it only after the final theorem
   surface is frozen and the paper-facing statement is stable.

4. If splitting later, split by proof layer.

   A low-risk eventual split is:

   - `D5Odd/CycleTools.lean`: generic single-cycle, rank, and semiconjugacy lemmas.
   - `D5Odd/RootTools.lean`: root translations, rotations, and vector arithmetic.
   - `D5Odd/Sigma.lean`: `sigmaVec`, `SigmaParam`, `nextSigma`, `orbitSigma`.
   - `D5Odd/NormalizedG.lean`: normalized return definitions and branch formulas.
   - `D5Odd/ReturnCycle.lean`: final return-cycle glue and exported theorems.

   This should be done one module at a time with `lake build D5Odd` after each
   move.

5. Archive stale handoff artifacts.

   The root contains many old `GPT55_D5_ODD_*.tar` handoff bundles and
   intermediate request/progress files.  Keep the latest audit and a final
   bundle, move older bundles into an `archive/` or `artifacts/` directory.

   Suggested files to keep visible:

   - `D5_ODD_PAPER_AUDIT_20260424.md`
   - `D5_ODD_CLEANUP_PLAN_20260424.md`
   - one final tarball containing `D5Odd/`, `D5Odd.lean`, and the audit docs

6. Do not chase linter warnings yet.

   The current warnings are mostly old flexible-tactic and unused-simp-arg
   warnings in `ReturnCycle.lean`.  They do not indicate proof gaps.  Cleaning
   them mechanically is lower value than freezing the final statement and
   packaging the theorem.

## Break conditions

- Stop if a refactor of `ReturnCycle.lean` creates non-mechanical proof
  failures.  Revert that refactor plan rather than spending proof time there.
- Stop before introducing a graph-library dependency unless the desired final
  graph theorem shape is specified.
- Stop before renaming public theorems if downstream documents or bundles have
  already referenced the current names.

## Best next move

Create one final delivery bundle containing the Lean files, audit, cleanup
plan, and project metadata.  If no graph-library API wrapper is required, the
D5 odd formalization is already in final mathematical shape.
