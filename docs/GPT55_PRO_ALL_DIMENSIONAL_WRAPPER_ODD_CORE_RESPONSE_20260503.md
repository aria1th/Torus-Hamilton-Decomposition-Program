# GPT-5.5 Pro All-Dimensional Wrapper / Odd-Core Skeleton Response

Date: 2026-05-03.

Response id: `resp_0ec0fb435989d83b0069f7886079f48197b2220cf5e1dbd968`.

Below is the architecture I would implement. The key invariant is:

> dimension induction must prove `OddUniformSolved StandardCayleySolved d`, not a fixed-modulus pointwise statement.

This is what makes the product lift usable when the right factor is required at modulus `m^2`.

---

## 1. Odd-core branch interfaces

Put these in something like:

```lean
RoundComposite/Concrete/OddCore/Interfaces.lean
```

```lean
namespace RoundComposite.Concrete

def OddCoreHighGE5 (Solved : Nat -> Nat -> Prop) : Prop :=
  forall {d m : Nat},
    5 <= d -> Odd d ->
    3 <= m -> Odd m ->
    d <= m ->
    Solved d m

def OddCoreSmallGE5 (Solved : Nat -> Nat -> Prop) : Prop :=
  forall {d m : Nat},
    5 <= d -> Odd d ->
    3 <= m -> Odd m ->
    m < d ->
    Solved d m

def OddCoreHighGE9 (Solved : Nat -> Nat -> Prop) : Prop :=
  forall {d m : Nat},
    9 <= d -> Odd d ->
    3 <= m -> Odd m ->
    d <= m ->
    Solved d m

def OddCoreSmallGE9 (Solved : Nat -> Nat -> Prop) : Prop :=
  forall {d m : Nat},
    9 <= d -> Odd d ->
    3 <= m -> Odd m ->
    m < d ->
    Solved d m

theorem oddCoreHighGE9_of_oddCoreHighGE5
    {Solved : Nat -> Nat -> Prop}
    (h : OddCoreHighGE5 Solved) :
    OddCoreHighGE9 Solved := by
  intro d m hd9 hdodd hm3 hmodd hdm
  exact h (by omega) hdodd hm3 hmodd hdm

theorem oddCoreSmallGE9_of_oddCoreSmallGE5
    {Solved : Nat -> Nat -> Prop}
    (h : OddCoreSmallGE5 Solved) :
    OddCoreSmallGE9 Solved := by
  intro d m hd9 hdodd hm3 hmodd hmd
  exact h (by omega) hdodd hm3 hmodd hmd
```

Use the `GE9` dispatcher as the preferred public odd-core dispatcher, so that `D5` and `D7` remain explicit seeds.

```lean
private lemma nine_le_of_three_le_of_odd_ne_3_5_7
    {d : Nat} (hd3 : 3 <= d) (hdodd : Odd d)
    (h3 : d ≠ 3) (h5 : d ≠ 5) (h7 : d ≠ 7) :
    9 <= d := by
  rcases hdodd with ⟨k, hk⟩
  omega

theorem odd_dimension_core_uniform_of_seeded_ge9_interfaces
    {Solved : Nat -> Nat -> Prop}
    (hD3 : RoundComposite.OddUniformSolved Solved 3)
    (hD5 : RoundComposite.OddUniformSolved Solved 5)
    (hD7 : RoundComposite.OddUniformSolved Solved 7)
    (hHigh : OddCoreHighGE9 Solved)
    (hSmall : OddCoreSmallGE9 Solved)
    {d : Nat} (hd3 : 3 <= d) (hdodd : Odd d) :
    RoundComposite.OddUniformSolved Solved d := by
  intro m hm3 hmodd
  by_cases h3 : d = 3
  · subst d
    exact hD3 (m := m) hm3 hmodd
  by_cases h5 : d = 5
  · subst d
    exact hD5 (m := m) hm3 hmodd
  by_cases h7 : d = 7
  · subst d
    exact hD7 (m := m) hm3 hmodd

  have hd9 : 9 <= d :=
    nine_le_of_three_le_of_odd_ne_3_5_7 hd3 hdodd h3 h5 h7

  by_cases hdm : d <= m
  · exact hHigh hd9 hdodd hm3 hmodd hdm
  · exact hSmall hd9 hdodd hm3 hmodd (lt_of_not_ge hdm)

end RoundComposite.Concrete
```

The missing/branch theorem statements should then be:

```lean
namespace RoundComposite.Concrete

theorem standard_cayley_odd_uniform_3 :
    RoundComposite.OddUniformSolved StandardCayleySolved 3 := by
  -- D3 construction.
  -- To be supplied.
  sorry

theorem odd_core_high_modulus_prefix_count_ge5 :
    OddCoreHighGE5 StandardCayleySolved := by
  -- Prefix-count branch for odd d ≥ 5, m ≥ d.
  sorry

theorem odd_core_high_modulus_prefix_count_ge9 :
    OddCoreHighGE9 StandardCayleySolved :=
  oddCoreHighGE9_of_oddCoreHighGE5 odd_core_high_modulus_prefix_count_ge5

theorem odd_core_small_modulus_base_tail_ge9 :
    OddCoreSmallGE9 StandardCayleySolved := by
  -- Adapter around BaseTailLiftTheorem + finite boundary.
  -- This is the only small-modulus theorem imported by the odd-core dispatcher.
  sorry

theorem odd_modulus_tori_odd_dimension_core_of_branches
    {d : Nat} (hd3 : 3 <= d) (hdodd : Odd d) :
    RoundComposite.OddUniformSolved StandardCayleySolved d :=
  odd_dimension_core_uniform_of_seeded_ge9_interfaces
    standard_cayley_odd_uniform_3
    standard_cayley_odd_uniform_5
    standard_cayley_odd_uniform_7
    odd_core_high_modulus_prefix_count_ge9
    odd_core_small_modulus_base_tail_ge9
    hd3 hdodd

theorem odd_modulus_tori_odd_dimension_core
    {d m : Nat} (hd3 : 3 <= d) (hdodd : Odd d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m := by
  simpa [StandardCayleySolved] using
    (odd_modulus_tori_odd_dimension_core_of_branches
      (d := d) hd3 hdodd (m := m) hm3 hmodd)

end RoundComposite.Concrete
```

---

## 2. All-dimensional wrapper from odd core

Put this in a separate file, e.g.

```lean
RoundComposite/Concrete/AllDimensionsFromOddCore.lean
```

This file should **not** import the finite boundary machinery. It only needs product lifting, `D2`, and the odd-core theorem as a parameter.

```lean
namespace RoundComposite.Concrete

private lemma three_le_of_two_le_of_odd
    {d : Nat} (hd2 : 2 <= d) (hdodd : Odd d) :
    3 <= d := by
  rcases hdodd with ⟨k, hk⟩
  omega

private lemma odd_or_eq_two_mul (d : Nat) :
    Odd d ∨ ∃ k, d = 2 * k := by
  rcases Nat.even_or_odd d with hEven | hOdd
  · right
    rcases hEven with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · exact Or.inl hOdd

private lemma lt_two_mul_of_pos {k : Nat} (hk : 0 < k) :
    k < 2 * k := by
  omega

private lemma eq_one_or_two_le_of_two_le_two_mul
    {k : Nat} (h : 2 <= 2 * k) :
    k = 1 ∨ 2 <= k := by
  cases k with
  | zero =>
      omega
  | succ k =>
      cases k with
      | zero =>
          exact Or.inl rfl
      | succ k =>
          exact Or.inr (by omega)

theorem odd_uniform_cayley_two_mul
    {b : Nat} (hb : 0 < b)
    (hB : RoundComposite.OddUniformSolved StandardCayleySolved b) :
    RoundComposite.OddUniformSolved StandardCayleySolved (2 * b) :=
  odd_uniform_cayley_mul_of_standard
    (a := 2) (b := b)
    (by norm_num) hb
    standard_cayley_odd_uniform_2 hB

theorem odd_modulus_tori_all_dimensions_uniform_of_odd_core
    (hOddCore :
      forall {d : Nat}, 3 <= d -> Odd d ->
        RoundComposite.OddUniformSolved StandardCayleySolved d)
    {d : Nat} (hd2 : 2 <= d) :
    RoundComposite.OddUniformSolved StandardCayleySolved d := by
  revert hd2
  refine Nat.strong_induction_on d ?_
  intro d ih hd2

  rcases odd_or_eq_two_mul d with hdodd | ⟨k, hk⟩
  · exact hOddCore (three_le_of_two_le_of_odd hd2 hdodd) hdodd

  · subst d
    have hkpos : 0 < k := by omega

    rcases eq_one_or_two_le_of_two_le_two_mul (k := k) hd2 with hk1 | hk2
    · subst k
      simpa using
        (standard_cayley_odd_uniform_2 :
          RoundComposite.OddUniformSolved StandardCayleySolved 2)

    · have hklt : k < 2 * k := lt_two_mul_of_pos hkpos
      have hK :
          RoundComposite.OddUniformSolved StandardCayleySolved k :=
        ih k hklt hk2
      exact odd_uniform_cayley_two_mul hkpos hK

theorem odd_modulus_tori_all_dimensions_of_odd_core
    (hOddCore :
      forall {d : Nat}, 3 <= d -> Odd d ->
        RoundComposite.OddUniformSolved StandardCayleySolved d)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m := by
  simpa [StandardCayleySolved] using
    ((odd_modulus_tori_all_dimensions_uniform_of_odd_core
      hOddCore (d := d) hd2) (m := m) hm3 hmodd)

end RoundComposite.Concrete
```

Then, once the odd core exists:

```lean
namespace RoundComposite.Concrete

theorem odd_modulus_tori_all_dimensions_uniform
    {d : Nat} (hd2 : 2 <= d) :
    RoundComposite.OddUniformSolved StandardCayleySolved d :=
  odd_modulus_tori_all_dimensions_uniform_of_odd_core
    (fun {d} hd3 hdodd =>
      odd_modulus_tori_odd_dimension_core_of_branches
        (d := d) hd3 hdodd)
    (d := d) hd2

end RoundComposite.Concrete
```

And finally the requested top-level theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m := by
  simpa [RoundComposite.Concrete.StandardCayleySolved] using
    ((RoundComposite.Concrete.odd_modulus_tori_all_dimensions_uniform
      (d := d) hd2) (m := m) hm3 hmodd)
```

---

## 3. Why the wrapper must be uniform

Do **not** prove the all-dimensional theorem by induction at a fixed modulus `m`.

With the chosen split `d = 2 * k`, the product theorem is logically using:

```lean
D_2(m)  and  D_k(m^2)  ==>  D_(2*k)(m)
```

Therefore the induction hypothesis for `k` must solve `k` at every odd modulus, in particular at `m^2`. That is exactly why the induction predicate is:

```lean
RoundComposite.OddUniformSolved StandardCayleySolved d
```

The existing theorem

```lean
odd_uniform_cayley_mul_of_standard
```

already discharges the facts that `m^2` is odd and `3 <= m^2`. Do not manually use the pointwise product theorem unless you really want to prove those side facts yourself.

---

## 4. File/module plan

Recommended dependency graph:

```text
RoundComposite/Concrete/OddCore/Interfaces.lean
  - OddCoreHighGE5, OddCoreSmallGE5, GE9 variants
  - seeded odd-core dispatcher
  - no construction imports

RoundComposite/Concrete/OddCore/D3.lean
  - proves standard_cayley_odd_uniform_3

RoundComposite/Concrete/OddCore/PrefixCount.lean
  - proves odd_core_high_modulus_prefix_count_ge5
  - exports odd_core_high_modulus_prefix_count_ge9

RoundComposite/Concrete/OddCore/BaseTail.lean
  - proves odd_core_small_modulus_base_tail_ge9
  - finite boundary table is private/internal here

RoundComposite/Concrete/OddCore/Core.lean
  - imports D3, D5, D7, PrefixCount, BaseTail, Interfaces
  - proves odd_modulus_tori_odd_dimension_core_of_branches

RoundComposite/Concrete/AllDimensionsFromOddCore.lean
  - imports product lift + D2 seed
  - proves odd_modulus_tori_all_dimensions_uniform_of_odd_core

RoundComposite/Concrete/OddModulusAllDimensions.lean
  - imports OddCore/Core and AllDimensionsFromOddCore
  - proves final odd_modulus_tori_all_dimensions
```

Important: `AllDimensionsFromOddCore.lean` should not import `BaseTail.lean`. It only knows about an abstract odd-core theorem.

---

## 5. Avoiding premature finite-boundary formalization

Do **not** expose the finite boundary table to the odd-core dispatcher.

The only theorem `OddCore/Core.lean` should import from the base-tail side is:

```lean
theorem odd_core_small_modulus_base_tail_ge9 :
    RoundComposite.Concrete.OddCoreSmallGE9
      RoundComposite.Concrete.StandardCayleySolved
```

Internally, `BaseTail.lean` can later do:

1. call the stable `BaseTailLiftTheorem`;
2. define a private finite boundary `Finset`;
3. prove private boundary soundness;
4. prove private coverage;
5. combine them into `odd_core_small_modulus_base_tail_ge9`.

This keeps the public odd-core and all-dimensional wrappers stable while the finite table evolves.

---

## 6. D7 seed and no even-modulus Route E

Use the seeded `GE9` dispatcher. Then `D5` and `D7` are consumed directly:

```lean
standard_cayley_odd_uniform_5
standard_cayley_odd_uniform_7
```

The all-dimensional wrapper then proves, for example, dimension `14` as:

```text
D_14(m) from D_2(m) and D_7(m^2)
```

Since `m` is odd, `m^2` is odd, so the existing odd-modulus `D7` seed applies. No even-modulus Route E is needed or imported.

---

## 7. Strong induction is the right Lean architecture

A more number-theoretic architecture would factor

```text
d = 2^r * q
```

with `q` odd or `q = 1`. That is mathematically pretty but creates unnecessary Lean work around `Nat.factorization`, powers, associativity, and the pure-power-of-two case.

The strong-induction wrapper above is better for Lean:

- no prime factorization;
- no `Nat.div`/`Nat.mod` half arithmetic;
- no `D1` base case;
- pure powers of two bottom out at `D2`;
- product associativity is avoided because every even step uses exactly `d = 2 * k`.

This gives the desired “repeatedly split off a `D2` factor” proof while keeping the formal arithmetic minimal.