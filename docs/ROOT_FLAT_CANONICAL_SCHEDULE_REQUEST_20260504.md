# Root-Flat Canonical Schedule Request

Date: 2026-05-04.

## Purpose

This is the standalone request for the second remaining field in the current
odd-modulus all-dimensional Lean goal.  The target is the canonical root-flat
schedule/return theorem used by the high-modulus prefix-count branch.

This request is independent of the q>=2 signed-column theorem and independent
of the small-modulus base-tail Hall branch.

## Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/PrefixCount.lean`
3. `Shared/RootFlat.lean`
4. `docs/ODD_TORI_CURRENT_GOAL_V3_1_20260504.md`
5. `docs/ODD_TORI_MINIMAL_BLOCKS_COMPLETION_AUDIT_20260504.md`
6. Optional legacy context: `docs/D11_ODD_WORKING_CERTIFICATE_NOTE_20260502.md`
7. Optional legacy helper list: `docs/D11_LEAN_HELPER_LEMMA_REQUESTS_20260502.md`

## Exact Lean Target

```lean
def RoundComposite.Concrete
  .PrefixCountRootFlatCanonicalScheduleCriterionGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d)
      {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) ->
    exists S : Shared.RootFlatSchedule
        (Fin d) (Fin d) (PrefixCountRootState d m) m,
      S.step = prefixCountRootStep d m /\
      S.rowLatin /\ S.layerBijective /\ S.returnsSingleCycle
```

Lean already proves the equivalence with the certificate-facing target:

```lean
theorem RoundComposite.Concrete
  .prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion :
    PrefixCountRootFlatCanonicalReturnGoal <->
      PrefixCountRootFlatCanonicalScheduleCriterionGoal
```

Therefore proving the schedule criterion is enough.

## Already Lean-Closed Infrastructure

The root-flat-to-torus lift is already done:

```lean
Shared.rootFlatLayeredDecomposition_of_schedule
Shared.RootFlatSchedule.fullStepsHamiltonian_of_return
RoundComposite.Concrete.standardCayleySolved_of_rootFlatLayered_standardStep
RoundComposite.Concrete.prefixCountGeometricCriterionGoal_of_rootFlatCanonical
```

The root state and step are already defined:

```lean
abbrev PrefixCountRootState (d m : Nat) :=
  Fin (d - 1) -> ZMod m

def prefixCountRootStep (d m : Nat) :
    Fin d -> PrefixCountRootState d m -> PrefixCountRootState d m :=
  fun i w j => if (i : Nat) = j then w j + 1 else w j
```

The layer count input is:

```lean
structure PrefixCount.LayerPermCounts (d m : Nat)
    (M : Matrix (Fin d) (Fin d) Nat) where
  layer : Fin m -> Equiv.Perm (Fin d)
  count_eq : forall i j : Fin d,
    (sum t : Fin m, if layer t i = j then 1 else 0) = M i j
```

The primitive hypotheses are supplied by:

```lean
C.Admissible m
```

after expanding `C.toMatrix hd2`.  In particular:

```lean
Nat.Coprime (C.zero i) m
IntCoprime ((C.step i k : Int) - (C.delta i : Int)) m
```

are the row-wise primitive conditions expected to drive the return map.

## Expected Canonical Rule

The D11 legacy certificate used the following pattern, and the general proof
should identify the dimension-generic version of it.

Let `q = d - 1`, root state `z : Fin q -> ZMod m`, and layer `t : ZMod m`.
The legacy stop-rank rule is:

```text
rho(t,z) = first rank rho in {1,...,q-1} with z_(rho-1) = t,
           or q if no such rank exists.
```

For `rho in {1,...,q}`, define the symbol permutation:

```text
lambda_rho(0) = 0
lambda_rho(1) = rho
lambda_rho(s) = s      if 2 <= s and rho < s
lambda_rho(s) = s - 1  if 2 <= s and s <= rho
```

The schedule should combine this state-dependent canonical permutation with
the layer permutation decomposition:

```text
symbol := (LayerPermCounts.layer t) color
direction/stop-rank := canonical lambda/rho applied to symbol
```

The exact direction indexing must match `prefixCountRootStep d m`.

## Required Proof Pieces

The proof should provide Lean-friendly versions of the following facts.

1. `lambda_rho` is a permutation of `Fin d`, for every valid `rho`.
2. The resulting `dir` map is row-Latin for every layer and root state.
3. For each fixed layer and color, the root-state map

   ```lean
   fun z => prefixCountRootStep d m (S.dir t z c) z
   ```

   is bijective.
4. For each color, the `m`-layer return map is a single cycle on
   `PrefixCountRootState d m`.
5. The single-cycle proof should use only the row counts supplied by
   `LayerPermCounts.count_eq` and the primitive conditions in `C.Admissible m`.

## Important Boundary

Do not use the simpler schedule

```lean
S.dir t z c := L.layer t c
```

with no state dependence.  Although it is row-Latin, its return is generally
just a translation on `(ZMod m)^(d-1)` and cannot provide the required single
cycle in higher rank.  The first-hit/canonical state dependence is essential.

Also avoid reproving the final torus Hamilton lift.  Once this target supplies
`S.step`, `S.rowLatin`, `S.layerBijective`, and `S.returnsSingleCycle`, the
existing `Shared.RootFlat` and `RoundComposite.OddCore` wrappers perform the
lift to `StandardCayleySolved d m`.

## Desired Output

The most useful answer would provide:

1. Exact Lean definitions for the generic `rho`, `lambda_rho`, and schedule.
2. A proof plan for row-Latin and layer-bijective properties.
3. A proof plan for the triangular return map and skew-cycle induction.
4. The smallest auxiliary lemmas that should be added before attempting the
   full `PrefixCountRootFlatCanonicalScheduleCriterionGoal`.
