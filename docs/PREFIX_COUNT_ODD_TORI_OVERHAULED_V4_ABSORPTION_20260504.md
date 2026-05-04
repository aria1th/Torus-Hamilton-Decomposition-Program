# Prefix-Count Odd Tori Overhauled v4 Absorption

Date: 2026-05-04.

Input files read:

- `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v4.pdf`
- `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v4_submission_bundle.zip`

The zip bundle contains:

```text
prefix_count_odd_tori_overhauled_v4.tex
prefix_count_odd_tori_overhauled_v4.pdf
prefix_count_odd_tori_overhauled_v4_README.md
prefix_count_odd_tori_overhauled_v4_checksums.txt
```

Checksum verification against the bundle checksum file passed for the TeX,
PDF, and README after extraction.

## Main Change

v4 reorganizes the manuscript around a dimension-closure theorem rather than
around a finite low-dimensional boundary.

The headline theorem is conditional on the uniform base dimensions
`3`, `5`, and `7`:

```text
If D_3(m), D_5(m), and D_7(m) are solved for every odd m >= 3,
then D_d(m) is solved for every d >= 2 and every odd m >= 3.
```

Together with the classical `D_2` case, the closure mechanisms are:

```text
product closure:
  a, b solved uniformly => a*b solved uniformly

successor closure:
  b solved uniformly and b >= 5 => 2*b + 1 solved uniformly
```

The old eventual theorem from dimensions `2` and `3`,
covering odd `d >= 29`, is retained as an independent corollary.  It is no
longer the main endpoint once `D_5` and `D_7` are imported.

## Consequence for Our Goal

The current Lean goal should pivot from the direct odd-core dispatcher

```text
odd d
  split into m >= d and m < d
  choose seed-semigroup base b for the small branch
```

to the simpler v4 closure dispatcher:

```text
base dimensions 2,3,5,7
+ product closure
+ successor closure b -> 2*b+1
--------------------------------
all dimensions d >= 2
```

The seed-semigroup interval machinery and the `d < 29` boundary table remain
useful audit/regression material, but they are not the shortest final proof
spine.

## Paper-Level Theorem Inventory

The main v4 theorem/proof blocks are:

1. Root-flat certificate theorem.

   A root-flat certificate with Latinness, layer bijections, and single-cycle
   color returns gives a directed Hamilton decomposition.

2. One-layer prefix factorization.

   The symbols

   ```text
   0, Delta, 2, ..., d-1
   ```

   give a permutation of the prefix labels at each layer and each one-layer map
   is bijective.

3. Prefix-count primitiveity.

   A word with counts `N_0, N_Delta, N_2, ..., N_{d-1}` is primitive if

   ```text
   gcd(N_0, m) = 1
   gcd(N_k - N_Delta, m) = 1 for 2 <= k <= d-1.
   ```

   The proof is the triangular skew-cycle induction.

4. Count matrix criterion.

   A prefix-admissible `d x d` count matrix gives the count-branch Hamilton
   decomposition.

5. Count branch for `m >= d`.

   v4 supplies symbolic constructions for both:

   ```text
   q >= 2: signed transportation core with entries in {±1, ±2}
   q = 1: direct Gale-Ryser plus matching correction
   ```

6. Base-tail lift.

   A base Hamilton cycle system plus active prefix-count symboling on the tail
   gives a full Hamilton decomposition.

7. Cylinder expansion.

   A solved base `D_b(m)` and unit packet decomposition of `m` expand the base
   multigraph into `d` Hamilton cycles.

8. Active Hall-slack realization.

   For the active-incidence graph, Hall/Hoffman cuts characterize symbol
   realizability.  A barycenter-plus-residue rounding argument with the
   universal residues `(u, -u, 0, ..., 0)` gives a feasible active symboling
   when

   ```text
   T = d - b > b
   m^b > m*d*T.
   ```

9. Base-tail Hall-slack theorem.

   If `D_b(m)` is solved, the unit-packet condition holds, and the two slack
   inequalities above hold, then `D_d(m)` is solved for `m < d`.

10. Successor closure.

    For `d = 2*b + 1` with `b >= 5`, use:

    ```text
    if m >= 2*b + 1: count branch
    if m < 2*b + 1: base-tail with T = b + 1 and packets 3,2,...,2
    ```

    The Hall-slack inequality is checked at `m = 3`:

    ```text
    3^b > 3*(2*b + 1)*(b + 1),
    ```

    true at `b = 5` and then increasing.

## Lean Mapping

Already Lean-closed or mostly present:

- `D2`, `D3`, `D5`, `D7` uniform odd-modulus seeds.
- Product/composite closure.
- Root-flat Cayley step compatibility and canonical-step lift infrastructure.
- Dense balanced matrix layer realization.
- Prefix-count transport interfaces and q=1 obstruction diagnostics.
- Seed-semigroup and Hall-slack arithmetic witnesses.
- Active-Hall finite interfaces, cut lemmas, residue compatibility, and
  one-symbol Hall token matching.

Still Lean-open after v4:

- The symbolic count branch as actual Lean constructors:
  q>=2 signed transportation and q=1 matching correction.
- The root-flat canonical return certificate from a prefix-admissible count
  matrix.
- The base-tail lift and active Hall-slack realization.
- The new short all-dimensional closure dispatcher using successor closure,
  rather than the older odd-core small-branch dispatcher.

## Recommended Goal Update

Replace the active top-level goal statement with the v4 closure version:

```text
Prove all d >= 2 and odd m >= 3 from:
  D2, D3, D5, D7 seeds,
  product closure,
  count branch m >= d,
  successor closure b -> 2*b+1.
```

At the Lean endpoint, the most useful new intermediate theorem is:

```lean
def OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Then prove a dispatcher:

```lean
theorem odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

using strong induction on `d`:

- `2,3,5,7` are seeds;
- `4,6,8,9,10` come from product closure and earlier induction;
- even `d` uses `2 * (d/2)`;
- odd `d >= 11` uses `d = 2*b + 1`, `b >= 5`, and the induction hypothesis
  for `b`.

This theorem makes the old `d < 29` boundary table and the general
seed-semigroup small branch nonessential for the final proof spine.

Update: this closure dispatcher is now Lean-closed as
`RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_357_and_successor`.
The remaining open theorem is the successor closure assumption it consumes.
The successor slack arithmetic used in the small branch is also Lean-closed as
`RoundComposite.successor_hall_slack`, and the broad slack-packet interface now
implies the narrow successor-small theorem via
`RoundComposite.Concrete.odd_successor_small_modulus_base_tail_of_slackPacketLift`.

## Risk / Formalization Notes

- v4 uses external classical inputs in paper form: Hoffman/Rado-Edmonds,
  Gale-Ryser, and ordinary matching arguments.  In Lean we should either
  formalize the exact finite lemmas needed or keep them as named theorem
  endpoints until a later pass.
- The Active Hall proof in v4 is stronger and more structured than the current
  `ActiveHall.HallRealizationGoal` placeholder.  The current file has useful
  cut lemmas but does not yet prove the Hoffman realization or controlled
  residue rounding theorem.
- The successor closure is the best next dispatcher-level Lean target because
  it reduces top-level proof complexity even before the hard construction
  endpoints are fully formalized.
