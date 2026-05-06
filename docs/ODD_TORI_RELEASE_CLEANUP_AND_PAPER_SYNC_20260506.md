# Odd Tori V75 Release Cleanup And Paper Sync

Date: 2026-05-06.

This note records the cleanup state after the V75 Lean endpoint closed.

## Lean Status

The current all-dimensional endpoint is closed in Lean:

```lean
RoundComposite.Concrete.odd_modulus_tori_all_dimensions_v75
RoundComposite.Concrete.oddModulusToriAllDimensionsGoal_v75
```

The endpoint proves the directed Cayley Hamilton decomposition for all
`d >= 2` and all odd `m >= 3`.

The proof route is:

```text
high modulus / prefix-count branch
+ small modulus / phase-split buffer reservoir successor branch
+ seed/product dispatcher
-> all dimensions
```

The high-modulus package is supplied by:

```lean
RoundComposite.Concrete.oddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal
```

## Manuscript Revisions

The paper should be updated around the following points.

1. State the final theorem with the same scope as the Lean endpoint:
   `d >= 2`, odd `m >= 3`, directed basis Cayley torus.

2. Present the proof as two main branches:
   high-modulus prefix-count closure for `m >= d`, and successor/base-tail
   closure for `m < d`.

3. Replace any remaining broad finite Hoffman/de Werra dependency language by
   the V75 local modular-trade/reservoir construction.  The broad ActiveHall
   theorem is historical context, not a dependency of the current endpoint.

4. Keep Appendix A aligned with the binary-layer signed trellis closure.  The
   unrestricted signed-column packing theorem is false; only the ordinary
   q>=2 seed closure is used.

5. Describe AI assistance in the disclosure section: OpenAI Codex 5.5
   (`xhigh`) and GPT-5.5 Pro (`xhigh`) were used autonomously for planning,
   Lean implementation, audit, and documentation.

## Historical Branch Quarantine

The following branches should remain available as research history and reusable
components, but should not be presented as the active proof path.

- Abstract ActiveHall/de Werra route:
  superseded by local modular-trade/reservoir scheduling in V75.

- D11 small-case raw certificate search:
  superseded by the all-dimensional successor branch.

- D5 even Route E:
  useful for a separate even-modulus or seam-analysis project, not used in the
  current odd-modulus theorem.

- D7/A5 exceptional bridge exploration:
  useful for historical insight and finite witness data, but no longer the
  main route.

Reusable material from those branches should be kept only when it supports the
current certificate calculus, local trade algebra, or finite verifier style.

## Release Checklist

Before updating the README release tag:

- `lake build RoundComposite` succeeds.
- Core Lean sources are free of `sorry`, `admit`, `axiom`, and `constant`.
- Build output is free of actionable linter warnings, except for intentionally
  suppressed proof-script style warnings in large arithmetic adapter files.
- README points to the closed V75 endpoint names.
- Unrelated dirty files are either committed separately or left out of the
  release commit.

The current README should keep the latest public stable tag until a new
GitHub release is actually created.
