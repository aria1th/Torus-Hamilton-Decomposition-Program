# D11 Lean Helper Lemma Requests

Date: 2026-05-02.

Update 2026-05-03:

This request list is superseded in part by
`docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md`.  The large-branch
D11 coordinate/count lemmas remain useful, but the small-case checker section
for `m = 3,5,7,9` is no longer the preferred D11 route.  The v2 route asks
instead for the extended prefix-count theorem, the full-vertex base-tail lift,
cylinder decomposition, active Hall-slack realization, and the D11 corollary
from the uniform D5 theorem.

This note lists the Lean helper lemmas wanted for formalizing the D11 odd
certificate.  The mathematical status is recorded in
`docs/D11_ODD_WORKING_CERTIFICATE_NOTE_20260502.md`: the large branch
`m` odd, `m >= 11` is closed outside Lean; the small cases `m = 3,5,7,9`
need finite search certificates.

The main Lean objective is not to re-search the construction.  It is to
formalize the large-branch certificate and prepare a small certificate checker
for the four leftover moduli.

## A. Generic Finite Dynamics

These should preferably live in `Shared/` because D5, D7, D11, and future
base-tail certificates will reuse them.

1. `IsSingleCycleMap.skew_zmod_of_total_carry_unit`

```lean
P : B -> B
f : B -> ZMod m
T : B × ZMod m -> B × ZMod m
T (b,a) = (P b, a + f b)
sumCarry = Finset.univ.sum f
IsSingleCycleMap P
Nat.Coprime sumCarry.val m
--------------------------------
IsSingleCycleMap T
```

The exact statement can avoid `.val` by phrasing the unit condition as
`IsUnit sumCarry`.

2. `finite_self_comp_bijective_factors`

```lean
[Fintype α] [DecidableEq α]
Function.Bijective (f_n ∘ ... ∘ f_1)
------------------------------------
∀ i, Function.Bijective f_i
```

This is only needed if a proof wants to infer layer-map bijectivity from a
return composition.  In the D11 formalization it is better to prove layer
bijectivity directly, but this lemma closes a small written-proof gap.

3. `single_cycle_iter_return_fiber`

If `P` is a single cycle on `B`, then for the skew map above:

```lean
T^[Fintype.card B] (b,a) = (b, a + sumCarry)
```

This is the computational core of the skew-cycle lemma.

4. `full_layer_cycle_of_root_return`

For a map on `V = (ZMod m)^d` that increments the layer sum by `1` each step,
if the `m`-step return on the root-flat section is a single cycle, then the
full map is a single cycle on `V`.

This is the general version of the D11 Hamilton lift.

## B. D11 Coordinate Lemmas

These can live in a future `D11Odd/Basic.lean` or a D11 section of the
dimension-generic root-flat files.

5. `D11.rootVecOfPrefix_root`

Define

```lean
rootVecOfPrefix11 : (Fin 10 -> ZMod m) -> (Fin 11 -> ZMod m)
```

by the inverse formulas from the certificate.  Prove its coordinate sum is
zero.

6. `D11.rootPrefixCoord_left_right_inverse`

For

```lean
rootPrefixCoord11 : RootState11 m -> Fin 10 -> ZMod m
```

prove:

```lean
rootPrefixCoord11 (rootOfPrefix11 z) = z
rootOfPrefix11 (rootPrefixCoord11 w) = w
```

and package the equivalence

```lean
RootState11 m ≃ (Fin 10 -> ZMod m).
```

7. `D11.stopRank_direction_step`

For `lambda : Fin 11` and `dir = 10 - lambda`, prove that adding `e_dir` and
returning to the root-flat section changes prefix coordinates by:

```lean
z_j -> z_j - 1  iff j.val < lambda.val
z_j -> z_j      iff lambda.val <= j.val
```

This is the central coordinate computation.

8. `D11.layer_sum_increments`

For every direction `i : Fin 11`,

```lean
S (x + e_i) = S x + 1.
```

This feeds the full-layer lift.

## C. Canonical Layer Rule

9. `D11.lambdaRho_bijective`

For `rho in {1,...,10}`, define:

```lean
lambda_rho 0 = 0
lambda_rho 1 = rho
lambda_rho s = s      if 2 <= s and rho < s
lambda_rho s = s - 1  if 2 <= s and rho >= s
```

Prove `Function.Bijective (lambda_rho : Fin 11 -> Fin 11)`.

10. `D11.dirOfRho_bijective`

Since `dir(lambda) = 10 - lambda` is also a permutation, prove:

```lean
Function.Bijective (fun s => dir (lambda_rho s)).
```

11. `D11.canonical_selector_row_latin`

If every layer has a symbol permutation

```lean
sigma_t : Fin 11 ≃ Fin 11
```

then the selector

```lean
delta c x = dir (lambda_(rho(S x, z x)) (sigma_(S x) c))
```

satisfies:

```lean
∀ x, Function.Bijective (fun c => delta c x).
```

## D. Count Matrix and Schedule Lemmas

12. `D11.countMatrixSchedule_exists_of_valid`

Optional but mathematically clean:

```lean
row sums = m
column sums = m
--------------------------------
exists list of m layer permutations realizing the count matrix
```

This is the regular bipartite multigraph perfect-matching decomposition.
For the first D11 Lean pass, it is acceptable to skip this and use explicit
base layer lists plus `Block10`.

13. `D11.Block10_counts`

For the repeated ten-layer block:

```lean
beta_u(c) = 1 + ((c + u) mod 10) for c <= 9
beta_u(10) = 0
```

prove its count matrix:

```text
rows 0..9: [0,1,1,1,1,1,1,1,1,1,1]
row 10:   [10,0,0,0,0,0,0,0,0,0,0]
```

14. `D11.base_matrices_valid`

For `B1`, `B3`, `B7`, `B9`, `B5`, `B15`, prove:

```lean
row sums = base length
column sums = base length
explicit layer list realizes the matrix
```

This can be done by finite `native_decide` or generated proofs.

15. `D11.base_matrices_primitive`

For each base matrix and every row:

```lean
Nat.Coprime N_0 m
Nat.Coprime (Int.natAbs (N_k - N_1)) m
```

for `2 <= k <= 10`.

16. `D11.Block10_preserves_primitive_diffs`

Adding `h * Block10` preserves all `N_k - N_1` for `k >= 2`.

For colors `0,...,9`, all nonzero symbol counts increase by `h`.
For color `10`, only `N_0` increases by `10h`.

17. `D11.branch_primitive_arithmetic`

Prove the branch arithmetic:

```lean
gcd(m - 10, m) = gcd(10, m) = 1
```

for odd branches `m = 11+10h`, `13+10h`, `17+10h`, `19+10h`, and

```lean
gcd(m - 16, m) = gcd(16, m) = 1
```

for `m = 25+10h`.

18. `D11.odd_ge11_branch_cover`

Every odd `m >= 11` is in exactly one branch:

```text
11 + 10h
13 + 10h
15
17 + 10h
19 + 10h
25 + 10h
```

with `h >= 0`.

## E. Triangular Return Lemmas

These are the central proof obligations for the large branch.

19. `D11.return_head_translation`

For a fixed color word with counts `N_s`:

```lean
R^(1) z0 = z0 + N_0
```

20. `D11.return_triangular_skew`

For `1 <= r <= 9`, prove the first return on the first `r+1` coordinates has
the form:

```lean
R^(r+1) (u,a) = (R^(r) u, a + F_r u)
```

where `F_r` is independent of `a` and higher coordinates.

21. `D11.layer_debit_cases`

Formalize the case split for coordinate `z_r`:

```text
s = 0:       never changes
s = 1:       changes iff all lower coordinates != t
2 <= s <= r: never changes
s = r+1:     changes iff some lower coordinate = t
s >= r+2:    always changes
```

This lemma should be stated at one layer before summing over the return cycle.

22. `D11.carry_sum_count_controlled`

Assuming `R^(r)` is bijective or single-cycle, prove:

```lean
Finset.univ.sum F_r = (-1)^r * (N_{r+1} - N_1)
```

in `ZMod m`.

This is the corrected count-vector claim: the return map itself is not
count-determined, only the total skew carry is.

23. `D11.hit_count_mod`

For fixed `t`:

```lean
#{u : (ZMod m)^r | forall i<r, u_i != t} = (m-1)^r
#{u : (ZMod m)^r | exists i<r, u_i = t} = m^r - (m-1)^r
```

and modulo `m`:

```lean
(m-1)^r = (-1)^r
m^r - (m-1)^r = (-1)^(r+1)
```

These facts feed the carry sum.

24. `D11.primitive_row_single_cycle`

Combine head translation, triangular skew, carry sums, and the skew-cycle
lemma:

```lean
gcd(N_0,m)=1
gcd(N_k-N_1,m)=1 for 2 <= k <= 10
------------------------------------------------
R : (ZMod m)^10 -> (ZMod m)^10 is a single cycle
```

## F. Large-Branch Endpoint Lemmas

25. `D11.large_branch_root_return_single_cycle`

For every odd `m >= 11`, the chosen branch count matrix and any realized layer
schedule satisfying those counts give a single-cycle root-flat return for
every color.

26. `D11.large_branch_root_flat_certificate`

Package row-Latin, layer-bijective, and returns-single-cycle facts into a
D11 root-flat certificate.

27. `D11.large_branch_directed_positive_hamilton`

Lower the root-flat certificate to:

```lean
Shared.CayleyHamiltonDecomposition 11 m
```

or a D11-specific endpoint wrapper if one is introduced.

## G. Small-Case Certificate Checker

Legacy section.  These lemmas are still useful if a raw finite D11 certificate
is generated, but the v2 proof route replaces them with the full-vertex
base-tail Hall-slack formalization from the D5 input.

These are for `m = 3,5,7,9`.

28. `BaseSimplex.layer_bijective`

For arbitrary dimension `d` and base depth `b`, prove that base injectivity
plus `BaseSimplex` makes every base layer map a permutation.

29. `BaseTailCertificate.sound`

A checker theorem:

```lean
base injective
BaseSimplex
base return single cycles on (ZMod m)^b
tail carry units for r=b,...,q-1
------------------------------------------------
full root-flat return single cycles on (ZMod m)^q
```

30. `D11.small_raw_certificate_sound`

Specialize the base-tail certificate checker to:

```text
d = 11
m = 3,5,7,9
```

so that generated raw certificates can be imported and checked without
enumerating `(ZMod m)^10`.

## Suggested Order

1. Generic skew-cycle and full-layer lift lemmas.
2. D11 prefix coordinate equivalence and stop-rank step effect.
3. `lambda_rho`/selector row-Latin lemmas.
4. Finite count data for `Block10` and the six base matrices.
5. Triangular return and carry-sum lemmas.
6. Primitive row single-cycle theorem.
7. Large branch endpoint.
8. Base-tail checker and small raw certificates.
