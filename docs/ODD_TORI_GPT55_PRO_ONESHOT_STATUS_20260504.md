# Odd Tori GPT-5.5 Pro One-Shot Bundle Status

Date: 2026-05-04.

## Current Objective

Formalize the v4 closure theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The Lean-facing package goal is:

```lean
RoundComposite.Concrete.OddModulusToriAllDimensionsGoal
```

The closure dispatcher from D2/D3/D5/D7 seeds, product closure, and successor
closure is already Lean-closed in `RoundComposite/ConcreteEndpoints.lean`.

## Current Verification

The current working tree state after the q>=2 half-slack split satisfies:

```text
lake env lean RoundComposite/PrefixCount.lean
lake build RoundComposite
```

Both commands passed before this bundle was prepared.

Known unrelated dirty files at bundle preparation time:

```text
lake-manifest.json
scripts/d5_odd_paper_verify.py
Torus-Hamilton-Decomposition/
```

`lake-manifest.json` differs from HEAD only by the package name:

```diff
- "name": "D7Odd",
+ "name": "TorusHamiltonDecompositionProgram",
```

The current `lakefile.toml` already has:

```toml
name = "TorusHamiltonDecompositionProgram"
```

## Mathlib Status

Toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Project dependency:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0-rc2"
```

Manifest mathlib SHA:

```text
5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Remote tag check on 2026-05-04:

```text
lean4 v4.30*:      v4.30.0-rc1, v4.30.0-rc2
mathlib4 v4.30*:   v4.30.0-rc1, v4.30.0-rc2
lean4 v4.30.0:     absent
mathlib4 v4.30.0:  absent
```

Therefore no newer stable `v4.30.0` tag was available to update to.

The local full `.lake/packages/mathlib` directory is about 14GB, and
source-only `.lake/packages/mathlib/Mathlib` is about 212MB.  The bundle
therefore includes:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
mathlib_context/MATHLIB_VERSION.txt
mathlib_context/Mathlib subset:
  Mathlib/Data/Finset
  Mathlib/Data/Fintype
  Mathlib/Data/Fin
  Mathlib/Data/ZMod
  Mathlib/Data/Nat
  Mathlib/GroupTheory/Perm
  Mathlib/Logic/Function
  Mathlib/Dynamics/PeriodicPts
  Mathlib/Tactic
```

This is not a full vendored mathlib.  It is intended to give GPT-5.5 Pro local
source context for the most likely finite-combinatorics, `Finset`, `Fintype`,
`ZMod`, permutation cycle, and tactic APIs.

## Current Sharp Remaining Fields

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

## Recently Added Lean Split

`RoundComposite/PrefixCount.lean` now exposes:

```lean
def qge2UpperLevel {n : Nat} (u : Fin n -> Nat) (t : Nat) :
    Finset (Fin n)

def qge2HalfLevelPenalty (n : Nat) (u : Fin n -> Nat) (t : Nat) : Int

theorem qge2OrdinaryRowTarget_sum_eq_neg_columnSum ...

def Qge2IndicatorCutsHalfSlackToSupportGoal : Prop := ...
def Qge2OrdinaryHalfSlackGoal : Prop := ...

theorem ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (hBridge : Qge2IndicatorCutsHalfSlackToSupportGoal)
    (hHalf : Qge2OrdinaryHalfSlackGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal
```

This follows the completed GPT-5.5 Pro response saved at:

```text
docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_RESPONSE_20260504.md
```

## Bundle Contents

The generated tarball should include:

```text
docs/ODD_TORI_GPT55_PRO_ONESHOT_PROMPT_20260504.md
docs/ODD_TORI_GPT55_PRO_ONESHOT_STATUS_20260504.md
docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md
docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md
docs/GPT55_PRO_*_RESPONSE_20260504.md
docs/GPT55_PRO_*_REQUEST_20260504.md
RoundComposite/*.lean
Shared/*.lean
D5Odd/*.lean
D7Odd/*.lean
D7Odd/Handoff/*.lean
TorusD3Odd/*.lean
TorusD4/*.lean
RoundComposite.lean
Shared.lean
D5Odd.lean
D7Odd.lean
TorusD3Odd.lean
TorusD4.lean
lakefile.toml
lake-manifest.json
lean-toolchain
mathlib_context/
```

## Verification Commands For Re-Checking

```bash
lake env lean RoundComposite/PrefixCount.lean
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```
