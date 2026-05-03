# Odd-Modulus Tori Global Formalization Goal

Date: 2026-05-03.

This note resets the working goal after absorbing
`prefix_count_odd_tori_overhauled_v2_submission_bundle (1).zip` and the D2 seed
audit.  Route E is deferred to a later even-modulus goal.  A subsequent review
corrected the target: the theorem is not restricted to odd dimensions.  The
primary target is now the Lean formalization of the all-dimensional,
odd-modulus theorem.

The most recent compressed active-goal statement is recorded in
`docs/ODD_TORI_ACTIVE_GOAL_RESET_20260503.md`.  The key refinement is that the
D11 small branch and the general `d >= 13, m < d` branch should both be viewed
through one Hall-slack unit-packet base-tail lift theorem.  The general small
branch uses a uniform arithmetic witness for the Hall-slack inequality, now
Lean-closed as `seed_semigroup_base_available_with_hall_slack`.

## New Primary Goal

Formalize the following endpoint in Lean:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, prove the directed Hamilton decomposition of the equal-side
directed torus

```text
D_d(m) = Cay((ZMod m)^d, {e_0,...,e_{d-1}})
```

for every `d >= 2` and every odd `m >= 3`.

The one-dimensional case is a directed `m`-cycle and can be added as a trivial
wrapper later if the final statement wants `1 <= d` rather than `2 <= d`.

The proof should not proceed by dimension-by-dimension finite schedules.
The intended theorem shape is:

```text
finite seeds + two uniform odd-core branches + D2/product lifting machinery
--------------------------------------------------------------------------
all dimensions `d >= 2` and all odd moduli `m >= 3`
```

This is the main conceptual value of the v2 manuscript.

## Refined Goal Shape

The immediate target is not to formalize every construction detail at once.
First build a Lean-level global skeleton whose assumptions are exactly the
large mathematical blocks that remain to be filled.  The endpoint should then
be a short dispatcher theorem.

The cleanest structure is a two-stage endpoint:

1. prove an **odd-dimensional core theorem** for odd `d >= 3`;
2. prove the advertised **all-dimensional theorem** by repeatedly splitting
   off a factor `2` and using the already formalized `D2` seed plus the product
   lift.

This avoids forcing the prefix-count branch to support even dimensions if the
manuscript's natural count construction is still stated for odd `d`.

The current Lean-facing odd-core skeleton is implemented in
`RoundComposite/OddCore.lean`.  After integrating the D3 seed, it deliberately
leaves only three mathematical blocks as hypotheses:

- the high-modulus prefix-count branch for odd `d >= 13`, `m >= d`;
- the D11 small-modulus base-tail lift from the D5 seed, covering `m < 11`;
- the small-modulus base-tail lift from a solved seed-semigroup base for odd
  `d >= 13`, `m < d`.

Lean-facing branch interfaces:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCount
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {d m : Nat}, Odd d -> 5 <= d -> 3 <= m -> Odd m -> d <= m ->
    Solved d m

def RoundComposite.Concrete.OddCoreHighGE13
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {d m : Nat}, 13 <= d -> Odd d -> 3 <= m -> Odd m -> d <= m ->
    Solved d m

def RoundComposite.Concrete.OddCoreSmallGE13
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {d m : Nat}, 13 <= d -> Odd d -> 3 <= m -> Odd m -> m < d ->
    Solved d m

def RoundComposite.Concrete.D11SmallModulusLiftFromD5Base
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {m : Nat}, 3 <= m -> Odd m -> m < 11 ->
    Solved 5 m ->
    Solved 11 m

def RoundComposite.Concrete.OddCoreSmallModulusLiftOfBase
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {d m b : Nat},
    Odd d -> 13 <= d ->
    Odd m -> 3 <= m -> m < d ->
    Solved b m ->
    2 * b < d ∧ d <= 3 * b ->
    Solved d m
```

Odd-core dispatcher:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_odd_dimension_core_of_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 <= d) :
    OddUniformSolved StandardCayleySolved d
```

This dispatcher closes `d = 3,5,7,9,11` by seeds/composites and sends all odd
`d >= 13` to the two branch interfaces.  The D3, D5, and D7 seeds are wired
in; `d = 9` is obtained from `D3 * D3`.

All-dimensional wrapper:

```lean
theorem RoundComposite.Concrete.standard_cayley_odd_uniform_all_dimensions_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, Odd d -> 3 <= d ->
        RoundComposite.OddUniformSolved
          RoundComposite.Concrete.StandardCayleySolved d) :
    ∀ {d : Nat}, 2 <= d ->
      RoundComposite.OddUniformSolved
      RoundComposite.Concrete.StandardCayleySolved d
```

This wrapper is implemented in `RoundComposite/ConcreteEndpoints.lean`.  It
uses strong induction on `d`: if `d` is odd, call `hOddCore`; if `d` is even
and `d >= 2`, write `d = 2 * k`, solve `D2(m)`, solve `D_k(m^2)` by induction,
and apply the product lift.

The same reduction is also exposed under the final-goal naming:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_uniform_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, 3 <= d -> Odd d ->
        RoundComposite.OddUniformSolved
          RoundComposite.Concrete.StandardCayleySolved d)
    {d : Nat} (hd2 : 2 <= d) :
    RoundComposite.OddUniformSolved
      RoundComposite.Concrete.StandardCayleySolved d

theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_odd_core
    (hOddCore :
      ∀ {d : Nat}, 3 <= d -> Odd d ->
        RoundComposite.OddUniformSolved
          RoundComposite.Concrete.StandardCayleySolved d)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The combined branch dispatcher is also implemented:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_odd_core_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

This dispatcher is retained as a convenient intermediate skeleton.  A more
refined dispatcher now matches the manuscript proof spine more closely:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_refined_branches
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hD11Small : D11SmallModulusLiftFromD5Base StandardCayleySolved)
    (hSmallLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

For proof development, `RoundComposite/OddCore.lean` also exposes the three
remaining inputs in theorem-shaped, manuscript-facing names:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop
def RoundComposite.Concrete.D11SmallModulusFromD5BaseGoal : Prop
def RoundComposite.Concrete.OddCoreSmallModulusOfBaseGoal : Prop
def RoundComposite.Concrete.OddCoreSmallModulusOfUnitPacketsGoal : Prop

theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

This three-input endpoint is retained as a development adapter.  It is useful
for local work because it names the D11-small case and the general small case
separately, but it is no longer the preferred manuscript-facing goal boundary.
The older `hD11` and `hSmall` assumptions are derivable from these refined
branch interfaces.

A manuscript-facing compressed endpoint is now available:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Thus the preferred active boundary is:

- `OddCoreHighModulusPrefixCountGoal`;
- `OddCoreSmallModulusSlackPacketLiftGoal`.

The slack packet-lift theorem supplies the D11 small branch through a
Lean-checked `b = 5` Hall-slack adapter.  The general `d >= 13` small branch
uses the closed `OddCoreSmallBaseSlackWitnessGoal` to provide the chosen
seed-semigroup base, packet data, and Hall-slack inequality.

Therefore the adjusted goal is now exactly this: prove the final
all-dimensional odd-modulus theorem from two remaining uniform construction
theorems, not from a `d < 29` finite boundary table and not from a separate
D11-small branch theorem.

For the small-modulus branch, it is enough to prove the more Lean-ready packet
interface:

```lean
theorem RoundComposite.Concrete.oddCoreSmallModulusOfBaseGoal_of_unitPackets
    (hPacketLift : OddCoreSmallModulusOfUnitPacketsGoal) :
    OddCoreSmallModulusOfBaseGoal
```

This adapter constructs the unit-packet data from `2*b < d <= 3*b` using the
closed arithmetic lemmas in `RoundComposite/SeedSemigroup.lean`.  It remains
useful for the older non-slack endpoint.  The current v2 target should instead
prove the slack version above, because the Hall inequalities are part of the
actual base-tail theorem.

The small-branch hypothesis can already be reduced one step further.  The
seed-semigroup arithmetic is closed in `RoundComposite/SeedSemigroup.lean`:

```lean
inductive RoundComposite.SolvedBySeedSemigroup : Nat -> Prop

theorem RoundComposite.Concrete.seed_semigroup_base_available
    {d : Nat} (hdodd : Odd d) (hd13 : 13 <= d) :
    ∃ b : Nat,
      RoundComposite.SolvedBySeedSemigroup b ∧
      2 * b < d ∧ d <= 3 * b

theorem RoundComposite.Concrete.oddCoreSmallGE13_of_seed_semigroup_base
    (hLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved) :
    OddCoreSmallGE13 StandardCayleySolved
```

Thus the true small-modulus mathematical gap is now the base-tail lift
interface, in its current Lean-facing form
`OddCoreSmallModulusSlackPacketLiftGoal`, not the seed-base availability
arithmetic.

The final no-assumption theorem is obtained by replacing these parameters with
formalized proofs:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

## Proof Architecture

Use a five-tier proof stack.

1. **Seed tier.**  Uniform odd-modulus endpoints in dimensions `2,3,5,7`.
   D2, D3, D5, and D7 are repository-level Lean seeds.

2. **All-d wrapper tier.**  D2 plus product closure removes powers of `2`.
   Thus the hard construction only has to prove the odd-dimensional core.

3. **Multiplicative seed tier.**  Product/composite closure makes every odd
   dimension in the multiplicative semigroup generated by `{3,5,7}` available
   inside the odd core, while even base dimensions such as `6 = 2 * 3` remain
   available for base-tail witnesses through the D2 seed.

4. **High-modulus tier.**  The prefix-count count branch handles `m >= d` for
   odd `d`.
   It should produce a theorem whose public interface mentions only `d`, `m`,
   parity/size hypotheses, and `Shared.CayleyHamiltonDecomposition d m`.

5. **Small-modulus tier.**  The base-tail Hall-slack branch handles odd
   `d`, `m < d`, from a solved base dimension and explicit arithmetic
   witnesses.  The main proof should not use a `d < 29` finite boundary table.
   Instead, close `d <= 11` by seeds/composite/one base-tail case, use the
   already formalized seed-semigroup availability lemma for odd `d >= 13`, and
   prove the uniform base-tail lift interface.

This architecture is intentionally asymmetric: the global dispatcher should
know almost nothing about root-flat coordinates, signed transport, or active
Hall rounding.  Those details belong behind the two branch endpoints.

## Immediate Planning Decisions

- Do not formalize the finite boundary table before the base-tail public
  interface is fixed.  The table is audit/regression evidence, not the intended
  proof spine.
- Do not start the active Hall/Hoffman proof before the skeleton theorem says
  exactly what the Hall-slack branch must output.
- Do not broaden the prefix-count construction to even `d` unless the
  manuscript already supplies that proof.  Use the D2/product wrapper for even
  dimensions instead.
- Treat D7 as a seed, not as an active construction target for this goal.
- Treat Route E and even-modulus work as regression material only.
- The next Lean implementation target should be one of the two branch
  interfaces: prefix-count for `m >= d`, or base-tail Hall-slack for `m < d`.

## Deferred Goal

D5 even Route E is no longer part of the primary goal.  Keep its existing Lean
interfaces, verifiers, and documents as regression material, but do not let
Route E drive the current proof plan.

Deferred Route E work:

- finite residue branch menu for even `m >= 6`;
- B20 trace proof;
- all-even D5 endpoint;
- any D7-even reuse decisions.

These remain valuable, but they are not needed for the all-dimensional,
odd-modulus theorem.

## Seed Policy

Use these uniform seed dimensions.

`D2`:

- should be formalized directly in this repository;
- now lives in `Shared/D2Seed.lean`;
- also has literature support via Keating's 1985 two-generator Cayley digraph
  decomposition theorem;
- needed because even composite bases such as `6 = 2 * 3` remove low-modulus
  boundary cases like `(13,3)`.

`D3`:

- now lives in `Shared/D3Seed.lean`, adapted from the existing D3 odd
  formalization;
- is exported as `standard_cayley_odd_uniform_3`;
- feeds both the `d = 3` seed case and the `d = 9 = 3 * 3` composite case.

`D5`:

- already formalized here for all odd `m >= 3`;
- feeds the D11 corollary and other small-base lifts.

`D7`:

- already formalized here for all odd `m >= 3`;
- closes the small odd seed list and removes the last finite small-dimension
  gaps that would remain with only `D2,D3,D5`.

Seed consequence:

```text
seeds D2,D3,D5 only:
  small odd gaps left: (7,3), (7,5)

seeds D2,D3,D5,D7:
  no small odd seed gap remains
```

Since D7 is already a closed Lean endpoint in this repository, the pragmatic
formalization route should use it as a seed.

## Main Machinery to Formalize

### 1. D2 Seed

This is now formalized in `Shared/D2Seed.lean`.

Mathematical construction:

```text
s = x + y

color 0:
  horizontal if s = 0, vertical otherwise

color 1:
  complementary direction
```

Each step increments `s`.  The `m`-step return translates the horizontal
coordinate by `1` for one color and by `m - 1` for the other; both are units
modulo odd `m`.

Expected endpoint:

```lean
theorem Shared.D2.shared_cayley_uniform :
    ∀ {m : Nat}, 3 <= m -> Odd m ->
      Shared.CayleyHamiltonDecomposition 2 m

theorem RoundComposite.Concrete.standard_cayley_odd_uniform_2 :
    RoundComposite.OddUniformSolved
      RoundComposite.Concrete.StandardCayleySolved 2
```

### 2. D3 Seed

This is now integrated in `Shared/D3Seed.lean`, with the older D3 development
available through `TorusD3Odd`.

Expected endpoint:

```lean
theorem Shared.D3.shared_cayley_uniform :
    ∀ {m : Nat}, 3 <= m -> Odd m ->
      Shared.CayleyHamiltonDecomposition 3 m

theorem RoundComposite.Concrete.standard_cayley_odd_uniform_3 :
    RoundComposite.OddUniformSolved
      RoundComposite.Concrete.StandardCayleySolved 3
```

### 3. Seed Semigroup Closure

The repository already has composite/product infrastructure in
`RoundComposite` and `Shared.CayleyProduct`.  The new global proof should add
or reuse a theorem saying that the multiplicative semigroup generated by solved
seed dimensions is also solved uniformly in odd modulus.

Required seed set for the final theorem:

```text
{2,3,5,7}
```

### 4. Prefix-Count Count Branch

Formalize the v2 count branch:

```text
odd d >= 5, odd m >= d
--------------------------------
D_d(m) decomposable
```

Subtasks:

- root-flat certificate theorem in dimension `d`;
- prefix coordinates and one-layer Latin factorization;
- prefix-count primitiveity;
- prefix-admissible count matrix criterion;
- signed transportation branch for `q >= 2`;
- restricted `q = 1` branch;
- arithmetic branch cover for all odd `m >= d`.

### 5. Base-Tail Hall-Slack Branch

Formalize the v2 full-vertex base-tail theorem:

```text
m < d odd
D_b(m) decomposable
d = k_1 + ... + k_b
each m is a sum of k_j positive units mod m
T = d - b, T > b, m^b > m d T
--------------------------------
D_d(m) decomposable
```

Subtasks:

- full-vertex coordinate split
  `X x Q_(T-1) ~= (ZMod m)^d`;
- base-tail skew-product lift;
- extended prefix-count primitiveity for arbitrary threshold-symbol sequences
  of length divisible by `m`;
- cylinder decomposition of the base multigraph;
- active Hall criterion or a Lean-friendly equivalent;
- mixed-vertex slack;
- controlled residue rounding;
- universal residue table.

This is probably the heaviest formalization block.

### 6. Uniform Small-Base Arithmetic

After the count branch covers `m >= d` in the odd-dimensional core, only
`m < d` remains.  The revised proof spine should avoid a theorem-level
`d < 29` boundary.  Instead, use seed/composite dimensions generated by `D2`
and `D3` to provide a solved base uniformly.

This arithmetic lemma is now formalized in `RoundComposite/SeedSemigroup.lean`:

```lean
theorem RoundComposite.Concrete.seed_semigroup_base_available
    {d : Nat} (hdodd : Odd d) (hd13 : 13 <= d) :
    ∃ b : Nat,
      SolvedBySeedSemigroup b ∧
      2 * b < d ∧ d <= 3 * b
```

Here `SolvedBySeedSemigroup b` means `b` lies in the multiplicative semigroup
generated by the solved seed dimensions, with the practical construction using
`2` and `3` as the essential dense base source.

The proof uses the interval cover supplied by the two seed-semigroup families
`3 * 2^n` and `4 * 2^n`.  Every `d >= 13` has one of these bases in the
interval `(d/3, d/2)`.

The first high-modulus prefix-count foundation is also formalized in
`RoundComposite/PrefixCount.lean`.  It records the `Parts` and
`SignedPrefixCounts` certificate shapes, proves the signed values
`{-2,-1,1,2}` are primitive modulo every odd `m`, proves the bridge
`SignedPrefixCounts.toParts_admissible`, and closes the basic quotient/remainder
facts needed for `m = (d-1)q + r`.  `Parts.toMatrix`, `Parts.sum_cols_split`,
`MatrixAdmissible`, and `Parts.Admissible.toMatrixAdmissible` now bridge the
internal `{0, Delta, step}` representation to a dense `Fin d x Fin d` count
matrix with row sums, column sums, and primitive row conditions.
`LayerPermCounts` also records explicit layer permutations realizing a dense
count matrix and proves the resulting row and column sums automatically from
the count equations.  The same
module now defines
`QuotientTransport` and proves `QuotientTransport.toSigned_admissible`, so a
transport construction only has to produce the quotient/remainder fields.  It
also defines `MarginPlan`, `SignedMarginMatrix`, and
`MarginPlan.toTransport`, so the high-modulus construction can now be split
into three smaller obligations:

- construct row margins `zero`, `tau`, and `sigma`;
- construct a signed correction matrix with row sums `sigma` and zero column
  sums;
- prove the per-cell nonnegativity needed for the resulting natural counts.

The quotient/remainder case split for the same branch is also Lean-closed:
`quotient_remainder_count_branch` packages

```text
m = (d-1) * (m/(d-1)) + m%(d-1),
0 < m%(d-1) < d-1,
m/(d-1) = 1 or 2 <= m/(d-1).
```

This isolates the manuscript's `q = 1` versus `q >= 2` split from the actual
transport constructions.

`RoundComposite/SeedSemigroup.lean` also records the small-block arithmetic
needed by the base-tail theorem:

```lean
def RoundComposite.twoThreeBlockParts (b d : Nat) : List Nat

theorem RoundComposite.twoThreeBlockParts_spec
    {b d : Nat} (h : 2 * b < d ∧ d <= 3 * b) :
    (twoThreeBlockParts b d).length = b ∧
    (twoThreeBlockParts b d).sum = d ∧
    ∀ k, k ∈ twoThreeBlockParts b d → k = 2 ∨ k = 3

def RoundComposite.unitCarryPacket (m k : Nat) : List Nat

theorem RoundComposite.twoThreeBlockParts_unitCarryPacket_spec
    {b d m k : Nat}
    (hm3 : 3 <= m) (hodd : Odd m)
    (hbd : 2 * b < d ∧ d <= 3 * b)
    (hk : k ∈ twoThreeBlockParts b d) :
    (unitCarryPacket m k).length = k ∧
    (unitCarryPacket m k).sum = m ∧
    ∀ a, a ∈ unitCarryPacket m k →
      0 < a ∧ a < m ∧ Nat.Coprime a m

def RoundComposite.unitCarryPackets (m b d : Nat) : List (List Nat)

theorem RoundComposite.unitCarryPackets_spec
    {b d m : Nat} (hm3 : 3 <= m) (hodd : Odd m)
    (hbd : 2 * b < d ∧ d <= 3 * b) :
    (unitCarryPackets m b d).length = b ∧
    ((unitCarryPackets m b d).map List.length).sum = d ∧
    ∀ packet, packet ∈ unitCarryPackets m b d →
      packet.sum = m ∧
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m

structure RoundComposite.SmallBaseUnitPacketWitness (d m : Nat)

noncomputable def RoundComposite.Concrete.smallBaseUnitPacketWitness
    {d m : Nat} (hdodd : Odd d) (hd13 : 13 <= d)
    (hm3 : 3 <= m) (hmodd : Odd m) :
    SmallBaseUnitPacketWitness d m
```

Thus the range condition `2*b < d <= 3*b` has already been lowered to the
Lean-level statement that `d` is a sum of `b` blocks, each of size `2` or `3`,
and to the aggregate packet statement required by the base-tail lift: there are
`b` packets, the packet lengths sum to `d`, each packet sums to `m`, and every
packet entry is a positive unit modulo `m`.  The `SmallBaseUnitPacketWitness`
wrapper packages this with a seed-semigroup base and the proof that the chosen
base is solved by the existing D2/D3 product machinery.

The remaining public small-modulus branch is:

```lean
def RoundComposite.Concrete.OddCoreSmallModulusLiftOfBase
    (Solved : Nat -> Nat -> Prop) : Prop :=
  ∀ {d m b : Nat},
    Odd d -> 13 <= d ->
    Odd m -> 3 <= m -> m < d ->
    Solved b m ->
    2 * b < d ∧ d <= 3 * b ->
    Solved d m
```

Equivalently, in theorem-shaped manuscript language:

```lean
theorem odd_core_small_modulus_of_base
    {d m b : Nat}
    (hdodd : Odd d) (hd13 : 13 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) (hmd : m < d)
    (hbSolved : Shared.CayleyHamiltonDecomposition b m)
    (hbRange : 2 * b < d ∧ d <= 3 * b) :
    Shared.CayleyHamiltonDecomposition d m
```

The condition `2*b < d <= 3*b` gives `T = d-b > b` and a decomposition of `d`
into `b` parts of size `2` or `3`.  For odd `m`, those sizes are positive-unit
sums:

```text
2 = 1 + (m - 1)
3 = 1 + 1 + (m - 2)
```

The Hall-slack inequality should be proved uniformly inside the base-tail lift,
rather than by enumerating `d < 29`.

Small odd dimensions are handled separately:

```text
d = 3: D3 seed
d = 5: D5 seed
d = 7: D7 seed
d = 9: D3 * D3
d = 11: base-tail from b = 5
```

The exact all-dimensional boundary table remains recorded in
`docs/ODD_TORI_D_LT_29_BOUNDARY_WITNESSES_20260503.md`.  It enumerates all
`169` pairs `(d,m)` with `2 <= d < 29`, odd `m`, and `3 <= m < d`.  Its status
is now audit/regression evidence, not a dependency of the main proof spine.

In particular, `(13,3)` is not a leftover case; it is the first example of the
uniform small-base pattern, with `b = 6 = 2 * 3`.

## Suggested Lean Order

1. Keep `Shared/D2Seed.lean` as the closed D2 seed and regression-test it.
2. Keep `Shared/D3Seed.lean` as the closed D3 seed and regression-test it.
3. Keep the all-dimensional wrapper theorem
   `standard_cayley_odd_uniform_all_dimensions_of_odd_core` as the top-level
   reduction from all `d >= 2` to the odd-dimensional core.
4. Keep the Lean-facing odd-core skeleton theorem with branch hypotheses.
5. Package odd-uniform seeds `2,3,5,7`.
6. Reuse/prove multiplicative semigroup closure for the seed dimensions.
7. Keep the public interface for the odd-dimensional base-tail theorem.
8. Keep the public interface for the odd-dimensional prefix-count branch.
9. Keep the uniform small-base availability lemma
   `seed_semigroup_base_available` as the closed arithmetic input.
10. Package the small odd dimensions `d = 3,5,7,9,11`.
11. Fill the prefix-count count branch.
12. Fill the base-tail Hall-slack theorem, exposed through
   `OddCoreSmallModulusLiftOfBase`.
13. Replace odd-core skeleton assumptions by the proved branch endpoints.
14. Keep the `169`-pair all-dimensional table as an audit document only.
15. Prove the final `odd_modulus_tori_all_dimensions` endpoint.

## Open Blocks

The current hard blocks are no longer Route E branch extraction.  They are:

- signed transportation/count-branch formalization;
- active Hall/Hoffman realization and controlled rounding;
- base-tail Hall-slack arithmetic and rounding packaging behind
  `OddCoreSmallModulusLiftOfBase`.

Existing D5 and D7 formalized endpoints should be treated as stable seeds, not
as active research targets for this goal.
