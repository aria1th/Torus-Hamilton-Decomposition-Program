# GPT-5.5 Pro One-Shot Prompt: Odd-Modulus Tori Formalization

Date: 2026-05-04.

Use this prompt with the accompanying bundle
`odd_tori_gpt55_pro_oneshot_bundle_20260504.tar.gz`.

## Context

We are formalizing the all-dimensional odd-modulus torus Hamilton
decomposition theorem in Lean:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The Lean package exposes this as:

```lean
def RoundComposite.Concrete.OddModulusToriAllDimensionsGoal : Prop :=
  forall {d m : Nat}, 2 <= d -> Odd m -> 3 <= m ->
    Shared.CayleyHamiltonDecomposition d m
```

The structural dispatcher is already Lean-closed:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

It uses only the D2/D3/D5/D7 seeds, product closure, and the successor closure
`b -> 2*b + 1`.

Current verification status:

```text
lake build RoundComposite
```

passes on Lean `leanprover/lean4:v4.30.0-rc2` with mathlib tag
`v4.30.0-rc2`, SHA `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

Remote tag check on 2026-05-04:

```text
lean4 v4.30*: rc1, rc2
mathlib4 v4.30*: rc1, rc2
lean4 v4.30.0: no tag
mathlib4 v4.30.0: no tag
```

So there is no newer `v4.30.0` compatible tag to update to at this time.

The full local `.lake/packages/mathlib` is about 14GB and the source-only
`Mathlib/` tree is about 212MB, so the bundle includes a focused Mathlib source
subset plus `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Main Task

Analyze the bundled Lean and docs in one pass.  Please produce a Lean-facing
completion plan, and where feasible actual theorem statements/proof skeletons,
for closing the remaining hard fields below.  The desired output is not prose
only: it should be immediately actionable for implementing Lean proofs in this
repository.

Preferred final Lean endpoint:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

Lean now also splits `hLift` into the level-set half-slack bridge:

```lean
def PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal : Prop := ...
def PrefixCount.Qge2OrdinaryHalfSlackGoal : Prop := ...

theorem PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (hBridge : PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal)
    (hHalf : PrefixCount.Qge2OrdinaryHalfSlackGoal) :
    PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal
```

Thus the sharpest remaining fields are:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.Qge2OrdinaryHalfSlackGoal
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
```

Equivalent coarser replacements:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
OddSuccessorSmallModulusBaseTailGoal
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal
```

## Requested Output

Please return the following, in this order.

1. A completion audit: confirm whether the five sharp fields above are indeed
   sufficient for the final theorem, and identify any hidden extra Lean
   obligations you see in the files.

2. A proof route for
   `PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal`.  Treat it as a
   finite integral Hoffman/Rado-Edmonds style transportation theorem over
   signed columns with entries in `{-2,-1,1,2}` and prescribed column sum
   `-(c k)`.  Give Lean-friendly auxiliary theorem statements.

3. A proof route for
   `PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal`.  The previous GPT
   response says the plain indicator-cut-to-support theorem is false because
   the `c = 2` signed column has a one-unit defect at the middle level.  Use
   integer level-set decomposition plus the extra half-size slack.

4. A proof route for `PrefixCount.Qge2OrdinaryHalfSlackGoal`.  The target is
   the ordinary row-target inequality at `J.card = n / 2`.

5. A proof route for
   `OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`.  This is the
   geometry layer turning `ActiveHall.HallRealizationGoal` into the successor
   small-modulus base-tail/additive packet construction with `T = b + 1`.

6. A proof route for
   `ActiveHall.FiniteHoffman.CompatibleDeWerraGoal`, or a cleaner route to
   `RawExactEdgeColoringGoal`/`ExactEdgeColoringGoal`.  Prefer a standard
   finite Hoffman/de Werra edge-colouring theorem if it matches the bundled
   hypotheses exactly.

7. A Lean import and lemma checklist: list the Mathlib lemmas likely needed,
   by theorem name if possible, and say whether the bundled Mathlib subset
   appears sufficient or which extra Mathlib files should be added.

## Important Warnings

Do not target the false arbitrary packing theorem:

```lean
PrefixCount.Qge2SignedColumnPackingGoal
```

The repository has a Lean counterexample:

```lean
theorem PrefixCount.not_qge2SignedColumnPackingGoal :
    ¬ Qge2SignedColumnPackingGoal
```

The active q>=2 target is the ordinary-row theorem:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
```

and the ordinary-row half-slack is essential.

Please distinguish clearly between:

```text
proved in Lean already
mathematically plausible but needs Lean proof
possibly false or underspecified
```

When proposing Lean statements, keep names close to the existing namespace
style:

```lean
namespace RoundComposite
namespace PrefixCount
namespace ActiveHall
namespace FiniteHoffman
```

## Files To Read First

1. `docs/ODD_TORI_GPT55_PRO_ONESHOT_STATUS_20260504.md`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
3. `docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md`
4. `RoundComposite/PrefixCount.lean`
5. `RoundComposite/OddCore.lean`
6. `RoundComposite/ActiveHall.lean`
7. `RoundComposite/ConcreteEndpoints.lean`
8. `RoundComposite/SeedSemigroup.lean`
9. `Shared/*.lean`
10. `docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_RESPONSE_20260504.md`
11. `docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md`
12. `docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md`
13. `docs/GPT55_PRO_ACTIVE_HALL_EXACT_EDGE_COLORING_RESPONSE_20260504.md`

Then consult `mathlib_context/` inside the bundle as needed.
