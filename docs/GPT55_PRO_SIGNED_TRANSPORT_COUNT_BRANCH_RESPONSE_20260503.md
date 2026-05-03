# GPT-5.5 Pro Signed Transport Count Branch Response

Date: 2026-05-03.

Response id: `resp_02e89d0269448d6b0069f781f016888190bfe73ff01f394e06`.

Note: request prompt used the earlier odd-dimension wording; read this against the corrected goal `d >= 2`, odd `m >= 3`.

Below is a pragmatic Lean-facing design for the prefix-count branch.  I would separate the **geometric/root-flat criterion** from the **integer matrix construction** very aggressively.

---

## 1. Core representations and theorem statements

### Prefix symbols: use a “parts” representation internally

For construction proofs, avoid proving column-case splits in `Fin d` repeatedly.  Use:

```lean
namespace PrefixCount

open scoped BigOperators

/-- Counts for symbols `0, Δ, 2, ..., d-1`, row-indexed by colors `Fin d`. -/
structure Parts (d : ℕ) where
  zero  : Fin d -> ℕ
  delta : Fin d -> ℕ
  step  : Fin d -> Fin (d - 2) -> ℕ
```

Then define admissibility directly in this representation:

```lean
def IntCoprime (a : ℤ) (m : ℕ) : Prop :=
  Nat.Coprime a.natAbs m

structure Parts.Admissible {d : ℕ} (m : ℕ) (C : Parts d) : Prop where
  row_sum :
    ∀ i : Fin d,
      C.zero i + C.delta i + (∑ k : Fin (d - 2), C.step i k) = m

  col_zero :
    (∑ i : Fin d, C.zero i) = m

  col_delta :
    (∑ i : Fin d, C.delta i) = m

  col_step :
    ∀ k : Fin (d - 2), (∑ i : Fin d, C.step i k) = m

  prim_zero :
    ∀ i : Fin d, Nat.Coprime (C.zero i) m

  prim_step :
    ∀ i : Fin d,
    ∀ k : Fin (d - 2),
      IntCoprime ((C.step i k : ℤ) - (C.delta i : ℤ)) m
```

At the boundary with existing root-flat/layer infrastructure, convert to a dense matrix over `Fin d`.

```lean
def colZero {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩
def colDelta {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩
def colStep {d : ℕ} (hd : 2 ≤ d) (k : Fin (d - 2)) : Fin d :=
  ⟨k.val + 2, by omega⟩

def Parts.toMatrix {d : ℕ} (hd : 2 ≤ d) (C : Parts d) :
    Matrix (Fin d) (Fin d) ℕ :=
  -- define by cases on column `j : Fin d`;
  -- prove simp lemmas below.
  sorry

@[simp] theorem Parts.toMatrix_zero
    {d : ℕ} (hd : 2 ≤ d) (C : Parts d) (i : Fin d) :
    C.toMatrix hd i (colZero hd) = C.zero i := by
  sorry

@[simp] theorem Parts.toMatrix_delta
    {d : ℕ} (hd : 2 ≤ d) (C : Parts d) (i : Fin d) :
    C.toMatrix hd i (colDelta hd) = C.delta i := by
  sorry

@[simp] theorem Parts.toMatrix_step
    {d : ℕ} (hd : 2 ≤ d) (C : Parts d) (i : Fin d) (k : Fin (d - 2)) :
    C.toMatrix hd i (colStep hd k) = C.step i k := by
  sorry
```

Also prove one column-splitting lemma once:

```lean
theorem sum_cols_split
    {d : ℕ} (hd : 2 ≤ d) {α : Type*} [AddCommMonoid α]
    (f : Fin d -> α) :
    (∑ j : Fin d, f j)
      = f (colZero hd) + f (colDelta hd)
          + ∑ k : Fin (d - 2), f (colStep hd k) := by
  sorry
```

Then the matrix-style admissibility is just a derived wrapper.

```lean
structure MatrixAdmissible {d : ℕ} (hd : 2 ≤ d) (m : ℕ)
    (M : Matrix (Fin d) (Fin d) ℕ) : Prop where
  row_sum : ∀ i : Fin d, (∑ j : Fin d, M i j) = m
  col_sum : ∀ j : Fin d, (∑ i : Fin d, M i j) = m
  prim_zero :
    ∀ i : Fin d, Nat.Coprime (M i (colZero hd)) m
  prim_step :
    ∀ i : Fin d,
    ∀ k : Fin (d - 2),
      IntCoprime
        ((M i (colStep hd k) : ℤ) - (M i (colDelta hd) : ℤ)) m
```

```lean
theorem Parts.Admissible.toMatrixAdmissible
    {d m : ℕ} (hd : 2 ≤ d) {C : Parts d}
    (hC : C.Admissible m) :
    MatrixAdmissible hd m (C.toMatrix hd) := by
  -- Use `sum_cols_split` and the simp lemmas above.
  sorry
```

---

## 2. Prefix-count primitiveity theorem

This should be a thin wrapper around the existing root-flat/skew-product/single-cycle lemmas.

Statement in parts form:

```lean
/--
Prefix-count primitiveity for one color row.

For counts `N₀, NΔ, N₂, ..., N_{d-1}` summing to `m`, the corresponding
return map is a single cycle if
* `gcd N₀ m = 1`;
* `gcd (N_k - NΔ) m = 1` for every step symbol.
-/
theorem prefixCountPrimitiveity
    {d m : ℕ}
    (hd : 3 ≤ d)
    (hm : 0 < m)
    (N0 NDelta : ℕ)
    (Nstep : Fin (d - 2) -> ℕ)
    (hrow :
      N0 + NDelta + (∑ k : Fin (d - 2), Nstep k) = m)
    (h0 : Nat.Coprime N0 m)
    (hk :
      ∀ k : Fin (d - 2),
        IntCoprime ((Nstep k : ℤ) - (NDelta : ℤ)) m) :
    RootFlat.SingleCycle
      (RootFlat.prefixReturnMap d m N0 NDelta Nstep) := by
  -- Should only invoke existing root-flat/skew-product/single-cycle lemmas.
  sorry
```

Adjust `RootFlat.SingleCycle` and `RootFlat.prefixReturnMap` to the actual names in the repo.

---

## 3. Layer-permutation counts and count criterion

A count matrix gives a root-flat certificate once it is decomposed into layer permutations.

Use a certificate interface first:

```lean
structure LayerPermCounts (d m : ℕ)
    (M : Matrix (Fin d) (Fin d) ℕ) where
  layer : Fin m -> Equiv.Perm (Fin d)
  count_eq :
    ∀ i j : Fin d,
      (∑ t : Fin m, if layer t i = j then (1 : ℕ) else 0) = M i j
```

Then the count criterion:

```lean
theorem countMatrixCriterion
    {d m : ℕ}
    (hd : 3 ≤ d)
    (hm : 0 < m)
    {M : Matrix (Fin d) (Fin d) ℕ}
    (hM : MatrixAdmissible (by omega : 2 ≤ d) m M)
    (L : LayerPermCounts d m M) :
    Shared.CayleyHamiltonDecomposition d m := by
  -- Build the root-flat certificate from `L.layer`.
  -- For each color row, extract counts using `L.count_eq`.
  -- Invoke `prefixCountPrimitiveity`.
  -- Finish using existing root-flat certificate theorem.
  sorry
```

Convenience criterion directly from `Parts`:

```lean
theorem partsCountCriterion
    {d m : ℕ}
    (hd : 3 ≤ d)
    (hm : 0 < m)
    {C : Parts d}
    (hC : C.Admissible m)
    (L : LayerPermCounts d m (C.toMatrix (by omega : 2 ≤ d))) :
    Shared.CayleyHamiltonDecomposition d m := by
  exact countMatrixCriterion hd hm
    (Parts.Admissible.toMatrixAdmissible (by omega : 2 ≤ d) hC)
    L
```

If the repo already has a row/column-sum-to-layer-permutations theorem, wrap it as:

```lean
theorem exists_layerPermCounts_of_row_col_sums
    {d m : ℕ}
    {M : Matrix (Fin d) (Fin d) ℕ}
    (hrow : ∀ i : Fin d, (∑ j : Fin d, M i j) = m)
    (hcol : ∀ j : Fin d, (∑ i : Fin d, M i j) = m) :
    Nonempty (LayerPermCounts d m M) := by
  -- General regular bipartite multigraph edge-coloring / repeated Hall matching.
  sorry
```

If not already available, keep `LayerPermCounts` as an explicit field in the eventual certificate.

---

## 4. Signed-prefix certificates

The cleanest interface for the signed transportation construction is to make the primitive differences explicit.

```lean
def signedVals : Finset ℤ := {-2, -1, 1, 2}

def IsSignedVal (a : ℤ) : Prop :=
  a ∈ signedVals

theorem signedVal_coprime_of_odd
    {a : ℤ} {m : ℕ}
    (ha : IsSignedVal a)
    (hm : Odd m) :
    Nat.Coprime a.natAbs m := by
  -- Cases `a = ±1`, `a = ±2`.
  -- For `2`, use oddness of `m`.
  sorry
```

Signed count certificate:

```lean
/--
A signed prefix-count certificate.

`diff i k` is intended to be `N_{i,k} - N_{i,Δ}`.
-/
structure SignedPrefixCounts (d m : ℕ) where
  zero  : Fin d -> ℕ
  delta : Fin d -> ℕ
  diff  : Fin d -> Fin (d - 2) -> ℤ

  diff_signed :
    ∀ i k, IsSignedVal (diff i k)

  step_nonneg :
    ∀ i k, 0 ≤ (delta i : ℤ) + diff i k

  row_eq :
    ∀ i : Fin d,
      (zero i : ℤ)
        + (((d - 1 : ℕ) : ℤ) * (delta i : ℤ))
        + (∑ k : Fin (d - 2), diff i k)
        = (m : ℤ)

  col_zero :
    (∑ i : Fin d, zero i) = m

  col_delta :
    (∑ i : Fin d, delta i) = m

  diff_col_zero :
    ∀ k : Fin (d - 2), (∑ i : Fin d, diff i k) = 0

  prim_zero :
    ∀ i : Fin d, Nat.Coprime (zero i) m
```

Convert it to actual counts:

```lean
def SignedPrefixCounts.toParts {d m : ℕ}
    (S : SignedPrefixCounts d m) : Parts d where
  zero := S.zero
  delta := S.delta
  step := fun i k => Int.toNat ((S.delta i : ℤ) + S.diff i k)
```

Main conversion theorem:

```lean
theorem SignedPrefixCounts.toParts_admissible
    {d m : ℕ}
    (hm : Odd m)
    (S : SignedPrefixCounts d m) :
    S.toParts.Admissible m := by
  -- Row sums: cast to `ℤ`; use `S.row_eq`.
  -- Column step sums:
  --   ∑ i (delta i + diff i k) = m + 0.
  -- Primitive step:
  --   step - delta = diff, because of `step_nonneg`.
  --   Then use `signedVal_coprime_of_odd`.
  sorry
```

---

## 5. Quotient/remainder transportation data

This matches the manuscript decomposition `m = (d - 1) q + r`.

Use an auxiliary integer shift `tau`.  The intended formula is:

* `NΔ(i) = q - tau(i)`;
* `N_k(i) = NΔ(i) + eps(i,k)`;
* `N0(i) = r + (d - 1) tau(i) - ∑_k eps(i,k)`.

```lean
structure QuotientTransport (d m q r : ℕ) where
  zero : Fin d -> ℕ
  tau  : Fin d -> ℤ
  eps  : Fin d -> Fin (d - 2) -> ℤ

  eps_signed :
    ∀ i k, IsSignedVal (eps i k)

  eps_col_zero :
    ∀ k : Fin (d - 2), (∑ i : Fin d, eps i k) = 0

  tau_sum :
    (∑ i : Fin d, tau i) = (q : ℤ) - (r : ℤ)

  delta_nonneg :
    ∀ i : Fin d, 0 ≤ (q : ℤ) - tau i

  step_nonneg :
    ∀ i k, 0 ≤ (q : ℤ) - tau i + eps i k

  zero_eq :
    ∀ i : Fin d,
      (zero i : ℤ)
        = (r : ℤ)
          + (((d - 1 : ℕ) : ℤ) * tau i)
          - (∑ k : Fin (d - 2), eps i k)

  prim_zero :
    ∀ i : Fin d, Nat.Coprime (zero i) m
```

Conversion to `SignedPrefixCounts`:

```lean
def QuotientTransport.toSigned
    {d m q r : ℕ}
    (hmqr : m = (d - 1) * q + r)
    (T : QuotientTransport d m q r) :
    SignedPrefixCounts d m := by
  refine
  { zero := T.zero
    delta := fun i => Int.toNat ((q : ℤ) - T.tau i)
    diff := T.eps
    diff_signed := T.eps_signed
    step_nonneg := ?_
    row_eq := ?_
    col_zero := ?_
    col_delta := ?_
    diff_col_zero := T.eps_col_zero
    prim_zero := T.prim_zero }
  · exact T.step_nonneg
  · -- row_eq from `zero_eq`, `delta = q - tau`, and `hmqr`
    sorry
  · -- derive zero column sum using `zero_eq`, `tau_sum`, and `eps_col_zero`
    sorry
  · -- derive delta column sum using `tau_sum`
    sorry
```

This is the key algebraic bridge.  Once proved, both branches only need to produce a `QuotientTransport`.

---

## 6. Branch theorem statements

Let the final branch use canonical quotient/remainder.

```lean
theorem exists_transport_qge2
    {d m q r : ℕ}
    (hd_odd : Odd d)
    (hd5 : 5 ≤ d)
    (hm_odd : Odd m)
    (hmqr : m = (d - 1) * q + r)
    (hr : r < d - 1)
    (hrpos : 0 < r)
    (hq : 2 ≤ q) :
    Nonempty (QuotientTransport d m q r) := by
  -- Manuscript q ≥ 2 signed transportation branch.
  sorry
```

```lean
theorem exists_transport_qeq1
    {d m q r : ℕ}
    (hd_odd : Odd d)
    (hd5 : 5 ≤ d)
    (hm_odd : Odd m)
    (hmqr : m = (d - 1) * q + r)
    (hr : r < d - 1)
    (hrpos : 0 < r)
    (hq : q = 1) :
    Nonempty (QuotientTransport d m q r) := by
  -- Manuscript restricted q = 1 branch.
  sorry
```

Existence of an admissible prefix-count matrix:

```lean
theorem exists_admissibleParts_countBranch
    {d m : ℕ}
    (hd_odd : Odd d)
    (hm_odd : Odd m)
    (hd5 : 5 ≤ d)
    (hmd : d ≤ m) :
    ∃ C : Parts d, C.Admissible m := by
  let q := m / (d - 1)
  let r := m % (d - 1)

  have hd2 : 2 ≤ d := by omega
  have hden : 0 < d - 1 := by omega
  have hmqr : m = (d - 1) * q + r := by
    -- `Nat.div_add_mod`
    omega

  have hr : r < d - 1 := by
    exact Nat.mod_lt _ hden

  have hrpos : 0 < r := by
    -- since `d` odd, `d - 1` even, hence `(d - 1) * q` even;
    -- `m` odd forces `r` odd, hence nonzero.
    sorry

  have hqpos : 1 ≤ q := by
    -- from `d ≤ m` and `d - 1 ≤ m`
    sorry

  by_cases hq2 : 2 ≤ q
  · rcases exists_transport_qge2 hd_odd hd5 hm_odd hmqr hr hrpos hq2 with ⟨T⟩
    refine ⟨(T.toSigned hmqr).toParts, ?_⟩
    exact SignedPrefixCounts.toParts_admissible hm_odd (T.toSigned hmqr)
  · have hq1 : q = 1 := by omega
    rcases exists_transport_qeq1 hd_odd hd5 hm_odd hmqr hr hrpos hq1 with ⟨T⟩
    refine ⟨(T.toSigned hmqr).toParts, ?_⟩
    exact SignedPrefixCounts.toParts_admissible hm_odd (T.toSigned hmqr)
```

Final count-branch theorem:

```lean
theorem prefix_count_branch
    {d m : ℕ}
    (hd_odd : Odd d)
    (hm_odd : Odd m)
    (hd5 : 5 ≤ d)
    (hmd : d ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases exists_admissibleParts_countBranch hd_odd hm_odd hd5 hmd with ⟨C, hC⟩

  let hd2 : 2 ≤ d := by omega
  let M := C.toMatrix hd2

  have hM : MatrixAdmissible hd2 m M :=
    Parts.Admissible.toMatrixAdmissible hd2 hC

  rcases exists_layerPermCounts_of_row_col_sums
      hM.row_sum hM.col_sum with ⟨L⟩

  exact partsCountCriterion (by omega : 3 ≤ d) (by omega : 0 < m) hC L
```

If you do not yet want to prove `exists_layerPermCounts_of_row_col_sums`, replace the final theorem temporarily by a certificate theorem consuming `LayerPermCounts`.

---

## 7. Splitting the signed transportation proof

Introduce a margin plan and a signed margin matrix.  This isolates arithmetic from the combinatorics.

```lean
structure MarginPlan (d m q r : ℕ) where
  zero : Fin d -> ℕ
  tau  : Fin d -> ℤ
  sigma : Fin d -> ℤ

  sigma_def :
    ∀ i : Fin d,
      sigma i =
        (r : ℤ)
          + (((d - 1 : ℕ) : ℤ) * tau i)
          - (zero i : ℤ)

  tau_sum :
    (∑ i : Fin d, tau i) = (q : ℤ) - (r : ℤ)

  delta_nonneg :
    ∀ i : Fin d, 0 ≤ (q : ℤ) - tau i

  prim_zero :
    ∀ i : Fin d, Nat.Coprime (zero i) m
```

```lean
structure SignedMarginMatrix (d : ℕ) (sigma : Fin d -> ℤ) where
  eps : Fin d -> Fin (d - 2) -> ℤ

  eps_signed :
    ∀ i k, IsSignedVal (eps i k)

  row_sum :
    ∀ i : Fin d, (∑ k : Fin (d - 2), eps i k) = sigma i

  col_sum :
    ∀ k : Fin (d - 2), (∑ i : Fin d, eps i k) = 0
```

Combination theorem:

```lean
def MarginPlan.toTransport
    {d m q r : ℕ}
    (P : MarginPlan d m q r)
    (E : SignedMarginMatrix d P.sigma)
    (hstep :
      ∀ i k, 0 ≤ (q : ℤ) - P.tau i + E.eps i k) :
    QuotientTransport d m q r where
  zero := P.zero
  tau := P.tau
  eps := E.eps
  eps_signed := E.eps_signed
  eps_col_zero := E.col_sum
  tau_sum := P.tau_sum
  delta_nonneg := P.delta_nonneg
  step_nonneg := hstep
  zero_eq := by
    intro i
    rw [← P.sigma_def i, ← E.row_sum i]
  prim_zero := P.prim_zero
```

Then split q ≥ 2 as:

```lean
theorem qge2_marginPlan_exists
    {d m q r : ℕ}
    (hd_odd : Odd d) (hd5 : 5 ≤ d)
    (hm_odd : Odd m)
    (hmqr : m = (d - 1) * q + r)
    (hr : r < d - 1)
    (hrpos : 0 < r)
    (hq : 2 ≤ q) :
    ∃ P : MarginPlan d m q r, Qge2PlanBounds d q P := by
  -- Pure arithmetic/number theory from manuscript.
  sorry
```

```lean
theorem qge2_signedMarginMatrix_exists
    {d m q r : ℕ}
    {P : MarginPlan d m q r}
    (hP : Qge2PlanBounds d q P) :
    Nonempty (SignedMarginMatrix d P.sigma) := by
  -- The bounded signed transportation construction.
  sorry
```

```lean
theorem qge2_step_nonneg
    {d m q r : ℕ}
    {P : MarginPlan d m q r}
    {E : SignedMarginMatrix d P.sigma}
    (hP : Qge2PlanBounds d q P) :
    ∀ i k, 0 ≤ (q : ℤ) - P.tau i + E.eps i k := by
  -- Do not rely only on `q ≥ 2`; prove the actual per-cell condition.
  sorry
```

Then:

```lean
theorem exists_transport_qge2 ... :
    Nonempty (QuotientTransport d m q r) := by
  rcases qge2_marginPlan_exists ... with ⟨P, hP⟩
  rcases qge2_signedMarginMatrix_exists hP with ⟨E⟩
  exact ⟨P.toTransport E (qge2_step_nonneg hP)⟩
```

For q = 1, use an explicit matching/injection rather than Hall if possible.

Suggested q = 1 lemmas:

```lean
structure PMOneBase (d : ℕ) where
  B : Fin d -> Fin (d - 2) -> ℤ
  mem : ∀ i k, B i k = -1 ∨ B i k = 1
  row_sum : Fin d -> ℤ
  row_sum_eq : ∀ i, (∑ k, B i k) = row_sum i
  col_sum_eq : ∀ k, (∑ i, B i k) = -1
```

```lean
structure PlusOneMatching {d : ℕ} (B : Fin d -> Fin (d - 2) -> ℤ) where
  mate : Fin (d - 2) -> Fin d
  inj : Function.Injective mate
  pos : ∀ k, B (mate k) k = 1
```

Then define the upgraded matrix by cases:

```lean
def upgradeQeq1
    {d : ℕ}
    (B : Fin d -> Fin (d - 2) -> ℤ)
    (μ : PlusOneMatching B)
    (specialRow : Fin d)
    (specialCol : Fin (d - 2)) :
    Fin d -> Fin (d - 2) -> ℤ :=
  fun i k =>
    if i = μ.mate k then
      2
    else if i = specialRow ∧ k = specialCol then
      -2
    else
      B i k
```

Prove separately:

```lean
theorem upgradeQeq1_signed :
    ∀ i k, IsSignedVal (upgradeQeq1 B μ specialRow specialCol i k) := by
  sorry

theorem upgradeQeq1_col_sums :
    -- exact column sums after upgrades
    sorry

theorem upgradeQeq1_row_sums :
    -- row sums are base row sums plus indicator of matched columns
    -- minus the special correction
    sorry

theorem upgradeQeq1_nonneg :
    -- the single `-2` must be in a row with `delta ≥ 2`;
    -- every `-1` must be in a row with `delta ≥ 1`.
    sorry
```

This avoids formalizing Hall merely to choose the matched `+1` entries.

---

## 8. Hidden assumptions to check in the manuscript branch

These should be explicit fields/lemmas in Lean.

1. **Remainder positivity.**
   With `r = m % (d - 1)`, prove `0 < r`. This uses:
   * `Odd d`, hence `Even (d - 1)`;
   * `Odd m`;
   * `m = (d - 1) q + r`;
   * `r < d - 1`.

2. **Branch coverage.**
   From `d ≤ m` and `5 ≤ d`, prove `1 ≤ q`. Then `¬ 2 ≤ q` gives `q = 1`.

3. **q = 1 range.**
   If `q = 1`, prove `m = d - 1 + r` and therefore `d ≤ m ≤ 2*d - 3`.

4. **Zero-column primitiveity is separate.**
   Signed entries `±1, ±2` make `N_k - NΔ` primitive for odd `m`. They do **not** automatically imply `gcd(N0,m)=1`. The construction must prove `prim_zero`.

5. **Difference equality.**
   Ensure the actual counts satisfy
   ```lean
   (step i k : ℤ) - (delta i : ℤ) = eps i k
   ```
   not merely something congruent to it. Otherwise primitiveity proof changes.

6. **Nonnegativity is per cell.**
   For q = 1 especially:
   * if `delta i = 0`, then every `eps i k ≥ 0`;
   * if `delta i = 1`, then `eps i k = -2` is forbidden;
   * if `eps i k = -2`, the proof must show `2 ≤ delta i`.

7. **Column sums of signed differences.**
   Need exactly
   ```lean
   ∀ k, ∑ i, eps i k = 0
   ```
   so that step columns have sum `m`.

8. **Tau sum.**
   Need exactly
   ```lean
   ∑ i, tau i = q - r
   ```
   in `ℤ`. This is what forces both `delta` and `zero` column sums to be `m`.

9. **Nat/Int casts.**
   All row/column-sum proofs should be done in `ℤ` and then cast back to `ℕ` using nonnegativity.

10. **Oddness of m for `±2`.**
    `Nat.Coprime 2 m` requires `Odd m`.

11. **No duplicate/omitted symbols.**
    The `Fin (d - 2)` step symbols must correspond exactly to columns `2, ..., d - 1`.

12. **Layer decomposition.**
    Row and column sums are both needed. Total sum alone is insufficient.

---

## 9. Matching theorem avoidance

There are two matching-like points.

### q = 1 “matched +1 entries”

Avoid Hall. Build the base `±1` matrix so that an explicit injection works, for example a cyclic diagonal:

```lean
mate : Fin (d - 2) -> Fin d
```

with a simp lemma:

```lean
theorem base_pos_on_mate : ∀ k, B (mate k) k = 1
```

Then all upgrade proofs are finite-sum indicator lemmas.

### Decomposing counts into layer permutations

If the repo already has this, wrap it as `exists_layerPermCounts_of_row_col_sums`.

If not, do **not** mix a full Hall proof into the prefix-count branch. Use the certificate interface:

```lean
structure PrefixCountCertificate (d m : ℕ) where
  counts : Parts d
  admissible : counts.Admissible m
  layers : LayerPermCounts d m (counts.toMatrix (by omega))
```

and prove:

```lean
theorem PrefixCountCertificate.toCHD
    {d m : ℕ}
    (hd : 3 ≤ d)
    (hm : 0 < m)
    (Cert : PrefixCountCertificate d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  partsCountCriterion hd hm Cert.admissible Cert.layers
```

Later, either:
* prove the general row/column-sum layer theorem once, or
* strengthen the explicit count construction to output layers.

For Lean, explicit layers are best if the construction is naturally circulant/permutation-sum. Otherwise, a single isolated Hall-based theorem is preferable to scattering matching arguments through the branch.

---

## 10. Recommended file layout and implementation order

Suggested modules:

1. `PrefixCount/Parts.lean`
   * `Parts`
   * `colZero`, `colDelta`, `colStep`
   * `Parts.toMatrix`
   * `sum_cols_split`
   * `Parts.Admissible`
   * `MatrixAdmissible`
   * `Parts.Admissible.toMatrixAdmissible`

2. `PrefixCount/Primitiveity.lean`
   * `IntCoprime`
   * `prefixCountPrimitiveity`
   * imports existing root-flat/skew-product/single-cycle lemmas

3. `PrefixCount/LayerCounts.lean`
   * `LayerPermCounts`
   * `countMatrixCriterion`
   * `partsCountCriterion`
   * optional `exists_layerPermCounts_of_row_col_sums`

4. `PrefixCount/Signed/Core.lean`
   * `signedVals`, `IsSignedVal`
   * `signedVal_coprime_of_odd`
   * `SignedPrefixCounts`
   * `SignedPrefixCounts.toParts`
   * `SignedPrefixCounts.toParts_admissible`

5. `PrefixCount/Signed/Quotient.lean`
   * `QuotientTransport`
   * `QuotientTransport.toSigned`
   * `MarginPlan`
   * `SignedMarginMatrix`
   * `MarginPlan.toTransport`

6. `PrefixCount/Signed/Qge2.lean`
   * q ≥ 2 margin plan
   * signed transportation matrix construction
   * q ≥ 2 nonnegativity
   * `exists_transport_qge2`

7. `PrefixCount/Signed/Qeq1.lean`
   * restricted q = 1 base `±1` matrix
   * explicit matching/injection
   * upgrade lemmas
   * q = 1 nonnegativity
   * `exists_transport_qeq1`

8. `PrefixCount/CountBranch.lean`
   * quotient/remainder arithmetic lemmas
   * `exists_admissibleParts_countBranch`
   * `prefix_count_branch`

This order lets the Lean engineer validate the geometric criterion before tackling the manuscript’s signed transportation arithmetic.