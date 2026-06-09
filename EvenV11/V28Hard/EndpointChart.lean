import EvenV11.EndpointCompletion

/-!
# Hard slot H6 (E1): parametric endpoint-successor chart

The endpoint step promotes dimension `b` to `d' = 2*b+1` (paper hypothesis
`4 ≤ b`).  The child has `2*b+1` successor coordinates in the cyclic order

  `Ω = (τ₀, τ₁, τ₂, p₁⁺, p₁⁻, p₂⁺, p₂⁻, …, p_{b−1}⁺, p_{b−1}⁻)`

indexed here by `Fin (2*b+1)`: position `i < 3` is `τᵢ`, position `3 + 2*j`
is `p_{j+1}⁺` and position `4 + 2*j` is `p_{j+1}⁻` (for `j : Fin (b-1)`).

The chart rows are encoded as permutations of the coordinate index set:

* `neutralRow` is the identity row `N`;
* `exchangeRow hb i` is `X_i = (τ_i ↔ p_{i+1}⁺)` for `i = 0, 1, 2` — the
  three exchanges need three distinct plus lanes `p₁⁺, p₂⁺, p₃⁺`, which is
  exactly where `4 ≤ b` enters;
* `resetRow hb` is `R = (p₁⁻ ↔ p₂⁻)`;
* `completionRow b h` is the cyclic shift `C_h : k ↦ k + h`.

`completionRow` is bridged to `EndpointCompletion.cyclicCompletionRow`
(which acts on `ZMod (2*b+1)`) through the canonical ring equivalence
`ZMod.finEquiv (2*b+1) : Fin (2*b+1) ≃+* ZMod (2*b+1)`, so the carry
machinery of `EvenV11.EndpointCompletion` applies verbatim.  The `b = 4`
instance is cross-checked against the paper chart by `decide` at the end of
the file, including the conventions
`endpointB4FirstCompletionTarget = 8 = minusIdx ⟨2,_⟩` (`p₃⁻`) and
`endpointB4FirstCompletionTail = 7 = plusIdx ⟨2,_⟩` (`p₃⁺`).
-/

namespace EvenV11
namespace V28Hard
namespace EndpointChart

variable {b : Nat}

/-! ## Successor-coordinate index helpers -/

/-- Index of the τ-slot `τ_i` among the `2*b+1` successor coordinates. -/
def tauIdx (hb : 1 ≤ b) (i : Fin 3) : Fin (2 * b + 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Index of the plus lane `p_{j+1}⁺` (position `3 + 2*j`, odd). -/
def plusIdx (j : Fin (b - 1)) : Fin (2 * b + 1) :=
  ⟨3 + 2 * j.val, by have := j.isLt; omega⟩

/-- Index of the minus lane `p_{j+1}⁻` (position `4 + 2*j`, even). -/
def minusIdx (j : Fin (b - 1)) : Fin (2 * b + 1) :=
  ⟨4 + 2 * j.val, by have := j.isLt; omega⟩

@[simp] theorem tauIdx_val (hb : 1 ≤ b) (i : Fin 3) :
    (tauIdx hb i).val = i.val := rfl

@[simp] theorem plusIdx_val (j : Fin (b - 1)) :
    (plusIdx j).val = 3 + 2 * j.val := rfl

@[simp] theorem minusIdx_val (j : Fin (b - 1)) :
    (minusIdx j).val = 4 + 2 * j.val := rfl

/-- The τ-slots are pairwise distinct. -/
theorem tauIdx_injective (hb : 1 ≤ b) :
    Function.Injective (tauIdx (b := b) hb) := by
  intro i i' h
  have hv := congrArg Fin.val h
  simp only [tauIdx_val] at hv
  exact Fin.ext hv

/-- The plus lanes are pairwise distinct. -/
theorem plusIdx_injective :
    Function.Injective (plusIdx (b := b)) := by
  intro j j' h
  have hv := congrArg Fin.val h
  simp only [plusIdx_val] at hv
  exact Fin.ext (by omega)

/-- The minus lanes are pairwise distinct. -/
theorem minusIdx_injective :
    Function.Injective (minusIdx (b := b)) := by
  intro j j' h
  have hv := congrArg Fin.val h
  simp only [minusIdx_val] at hv
  exact Fin.ext (by omega)

/-- τ-slots (`< 3`) never collide with plus lanes (`≥ 3`). -/
theorem tauIdx_ne_plusIdx (hb : 1 ≤ b) (i : Fin 3) (j : Fin (b - 1)) :
    tauIdx hb i ≠ plusIdx j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [tauIdx_val, plusIdx_val] at hv
  omega

/-- τ-slots (`< 3`) never collide with minus lanes (`≥ 4`). -/
theorem tauIdx_ne_minusIdx (hb : 1 ≤ b) (i : Fin 3) (j : Fin (b - 1)) :
    tauIdx hb i ≠ minusIdx j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [tauIdx_val, minusIdx_val] at hv
  omega

/-- Plus lanes (odd positions `3 + 2*j`) never collide with minus lanes
(even positions `4 + 2*j'`). -/
theorem plusIdx_ne_minusIdx (j j' : Fin (b - 1)) :
    plusIdx j ≠ minusIdx j' := by
  intro h
  have hv := congrArg Fin.val h
  simp only [plusIdx_val, minusIdx_val] at hv
  omega

/-- Classification of successor coordinates: every index is exactly one of a
τ-slot (`k < 3`), a plus lane (odd `k ≥ 3`), or a minus lane (even `k ≥ 4`).
Exclusivity is given by `tauIdx_ne_plusIdx`, `tauIdx_ne_minusIdx`,
`plusIdx_ne_minusIdx` and the three injectivity lemmas. -/
theorem coordIdx_classify (hb : 1 ≤ b) (k : Fin (2 * b + 1)) :
    (∃ i : Fin 3, k = tauIdx hb i) ∨
      (∃ j : Fin (b - 1), k = plusIdx j) ∨
      (∃ j : Fin (b - 1), k = minusIdx j) := by
  have hk := k.isLt
  rcases Nat.lt_or_ge k.val 3 with h3 | h3
  · exact Or.inl ⟨⟨k.val, h3⟩, Fin.ext rfl⟩
  · rcases Nat.even_or_odd k.val with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- even and `≥ 3`, hence `≥ 4`: a minus lane
      refine Or.inr (Or.inr ⟨⟨(k.val - 4) / 2, by omega⟩, Fin.ext ?_⟩)
      change k.val = 4 + 2 * ((k.val - 4) / 2)
      omega
    · -- odd and `≥ 3`: a plus lane
      refine Or.inr (Or.inl ⟨⟨(k.val - 3) / 2, by omega⟩, Fin.ext ?_⟩)
      change k.val = 3 + 2 * ((k.val - 3) / 2)
      omega

/-! ## Chart rows as permutations -/

/-- Neutral row `N`: the identity permutation (color `t_i` reads `τ_i`,
`d_j` reads `p_j⁺`, `μ_j` reads `p_j⁻`). -/
def neutralRow (b : Nat) : Equiv.Perm (Fin (2 * b + 1)) := 1

@[simp] theorem neutralRow_apply (k : Fin (2 * b + 1)) :
    neutralRow b k = k := rfl

/-- The neutral row is its own inverse. -/
theorem neutralRow_inv (b : Nat) : (neutralRow b)⁻¹ = neutralRow b :=
  inv_one

/-- The neutral row moves nothing. -/
theorem neutralRow_support (b : Nat) :
    (neutralRow b).support = ∅ :=
  Equiv.Perm.support_one

/-- The τ endpoint `τ_i` of the exchange row `X_i`. -/
def exchangeTauIdx (hb : 4 ≤ b) (i : Fin 3) : Fin (2 * b + 1) :=
  tauIdx (by omega) i

/-- The plus-lane endpoint `p_{i+1}⁺` of the exchange row `X_i`; this needs
three distinct plus lanes `p₁⁺, p₂⁺, p₃⁺`, i.e. `4 ≤ b`. -/
def exchangePlusIdx (hb : 4 ≤ b) (i : Fin 3) : Fin (2 * b + 1) :=
  plusIdx ⟨i.val, by have := i.isLt; omega⟩

@[simp] theorem exchangeTauIdx_val (hb : 4 ≤ b) (i : Fin 3) :
    (exchangeTauIdx hb i).val = i.val := rfl

@[simp] theorem exchangePlusIdx_val (hb : 4 ≤ b) (i : Fin 3) :
    (exchangePlusIdx hb i).val = 3 + 2 * i.val := rfl

/-- The two endpoints of an exchange row are distinct. -/
theorem exchangeTauIdx_ne_exchangePlusIdx (hb : 4 ≤ b) (i : Fin 3) :
    exchangeTauIdx hb i ≠ exchangePlusIdx hb i :=
  tauIdx_ne_plusIdx _ _ _

/-- Exchange row `X_i`: the transposition `τ_i ↔ p_{i+1}⁺`. -/
def exchangeRow (hb : 4 ≤ b) (i : Fin 3) :
    Equiv.Perm (Fin (2 * b + 1)) :=
  Equiv.swap (exchangeTauIdx hb i) (exchangePlusIdx hb i)

@[simp] theorem exchangeRow_apply_tau (hb : 4 ≤ b) (i : Fin 3) :
    exchangeRow hb i (exchangeTauIdx hb i) = exchangePlusIdx hb i :=
  Equiv.swap_apply_left _ _

@[simp] theorem exchangeRow_apply_plus (hb : 4 ≤ b) (i : Fin 3) :
    exchangeRow hb i (exchangePlusIdx hb i) = exchangeTauIdx hb i :=
  Equiv.swap_apply_right _ _

/-- `X_i` fixes every coordinate other than its two endpoints. -/
theorem exchangeRow_apply_of_ne (hb : 4 ≤ b) (i : Fin 3)
    {k : Fin (2 * b + 1)} (hτ : k ≠ exchangeTauIdx hb i)
    (hp : k ≠ exchangePlusIdx hb i) :
    exchangeRow hb i k = k :=
  Equiv.swap_apply_of_ne_of_ne hτ hp

/-- Moved-set characterization of the exchange row `X_i`. -/
theorem exchangeRow_apply_ne_self_iff (hb : 4 ≤ b) (i : Fin 3)
    (k : Fin (2 * b + 1)) :
    exchangeRow hb i k ≠ k ↔
      k = exchangeTauIdx hb i ∨ k = exchangePlusIdx hb i := by
  simp only [exchangeRow]
  rw [Equiv.swap_apply_ne_self_iff]
  exact and_iff_right (exchangeTauIdx_ne_exchangePlusIdx hb i)

/-- Each exchange row is its own inverse. -/
theorem exchangeRow_inv (hb : 4 ≤ b) (i : Fin 3) :
    (exchangeRow hb i)⁻¹ = exchangeRow hb i :=
  Equiv.swap_inv _ _

/-- The support of `X_i` is the pair `{τ_i, p_{i+1}⁺}`. -/
theorem exchangeRow_support (hb : 4 ≤ b) (i : Fin 3) :
    (exchangeRow hb i).support =
      {exchangeTauIdx hb i, exchangePlusIdx hb i} :=
  Equiv.Perm.support_swap (exchangeTauIdx_ne_exchangePlusIdx hb i)

/-- The first reset endpoint `p₁⁻` (position `4`). -/
def resetFirstIdx (hb : 4 ≤ b) : Fin (2 * b + 1) :=
  minusIdx ⟨0, by omega⟩

/-- The second reset endpoint `p₂⁻` (position `6`). -/
def resetSecondIdx (hb : 4 ≤ b) : Fin (2 * b + 1) :=
  minusIdx ⟨1, by omega⟩

@[simp] theorem resetFirstIdx_val (hb : 4 ≤ b) :
    (resetFirstIdx hb).val = 4 := rfl

@[simp] theorem resetSecondIdx_val (hb : 4 ≤ b) :
    (resetSecondIdx hb).val = 6 := rfl

/-- The two reset endpoints are distinct. -/
theorem resetFirstIdx_ne_resetSecondIdx (hb : 4 ≤ b) :
    resetFirstIdx hb ≠ resetSecondIdx hb := by
  intro h
  have hv := congrArg Fin.val h
  simp only [resetFirstIdx_val, resetSecondIdx_val] at hv
  omega

/-- Reset row `R`: the transposition `p₁⁻ ↔ p₂⁻`. -/
def resetRow (hb : 4 ≤ b) : Equiv.Perm (Fin (2 * b + 1)) :=
  Equiv.swap (resetFirstIdx hb) (resetSecondIdx hb)

@[simp] theorem resetRow_apply_first (hb : 4 ≤ b) :
    resetRow hb (resetFirstIdx hb) = resetSecondIdx hb :=
  Equiv.swap_apply_left _ _

@[simp] theorem resetRow_apply_second (hb : 4 ≤ b) :
    resetRow hb (resetSecondIdx hb) = resetFirstIdx hb :=
  Equiv.swap_apply_right _ _

/-- `R` fixes every coordinate other than `p₁⁻` and `p₂⁻`. -/
theorem resetRow_apply_of_ne (hb : 4 ≤ b) {k : Fin (2 * b + 1)}
    (h₁ : k ≠ resetFirstIdx hb) (h₂ : k ≠ resetSecondIdx hb) :
    resetRow hb k = k :=
  Equiv.swap_apply_of_ne_of_ne h₁ h₂

/-- Moved-set characterization of the reset row `R`. -/
theorem resetRow_apply_ne_self_iff (hb : 4 ≤ b) (k : Fin (2 * b + 1)) :
    resetRow hb k ≠ k ↔
      k = resetFirstIdx hb ∨ k = resetSecondIdx hb := by
  simp only [resetRow]
  rw [Equiv.swap_apply_ne_self_iff]
  exact and_iff_right (resetFirstIdx_ne_resetSecondIdx hb)

/-- The reset row is its own inverse. -/
theorem resetRow_inv (hb : 4 ≤ b) :
    (resetRow hb)⁻¹ = resetRow hb :=
  Equiv.swap_inv _ _

/-- The support of `R` is the pair `{p₁⁻, p₂⁻}`. -/
theorem resetRow_support (hb : 4 ≤ b) :
    (resetRow hb).support = {resetFirstIdx hb, resetSecondIdx hb} :=
  Equiv.Perm.support_swap (resetFirstIdx_ne_resetSecondIdx hb)

/-- Distinct exchange rows have disjoint supports. -/
theorem exchangeRow_support_disjoint (hb : 4 ≤ b) {i i' : Fin 3}
    (hii : i ≠ i') :
    Disjoint (exchangeRow hb i).support (exchangeRow hb i').support := by
  have hval : i.val ≠ i'.val := fun h => hii (Fin.ext h)
  have hi := i.isLt
  have hi' := i'.isLt
  rw [Finset.disjoint_left]
  intro k hk hk'
  rw [exchangeRow_support, Finset.mem_insert, Finset.mem_singleton] at hk hk'
  rcases hk with rfl | rfl <;> rcases hk' with h | h
  all_goals
    have hv := congrArg Fin.val h
    simp only [exchangeTauIdx_val, exchangePlusIdx_val] at hv
    omega

/-- Each exchange row has support disjoint from the reset row. -/
theorem exchangeRow_resetRow_support_disjoint (hb : 4 ≤ b) (i : Fin 3) :
    Disjoint (exchangeRow hb i).support (resetRow hb).support := by
  have hi := i.isLt
  rw [Finset.disjoint_left]
  intro k hk hk'
  rw [exchangeRow_support, Finset.mem_insert, Finset.mem_singleton] at hk
  rw [resetRow_support, Finset.mem_insert, Finset.mem_singleton] at hk'
  rcases hk with rfl | rfl <;> rcases hk' with h | h
  all_goals
    have hv := congrArg Fin.val h
    simp only [exchangeTauIdx_val, exchangePlusIdx_val, resetFirstIdx_val,
      resetSecondIdx_val] at hv
    omega

/-- Completion row `C_h`: the cyclic shift `k ↦ k + h` on the coordinate
indices, with the shift given in `ZMod (2*b+1)` to match
`EndpointCompletion.cyclicCompletionRow`.  (The paper requires
`h ≢ 0 mod 2*b+1` for an honest completion row; the permutation is defined
for every `h`, with `C_0 = N`.) -/
def completionRow (b : Nat) (h : ZMod (2 * b + 1)) :
    Equiv.Perm (Fin (2 * b + 1)) :=
  Equiv.addRight ((ZMod.finEquiv (2 * b + 1)).symm h)

@[simp] theorem completionRow_apply (b : Nat) (h : ZMod (2 * b + 1))
    (k : Fin (2 * b + 1)) :
    completionRow b h k = k + (ZMod.finEquiv (2 * b + 1)).symm h := by
  simp [completionRow]

/-- Bridge to `EvenV11.EndpointCompletion`: under the canonical ring
equivalence `Fin (2*b+1) ≃+* ZMod (2*b+1)`, the permutation
`completionRow b h` is exactly `cyclicCompletionRow h`, so the completion
carry certificates of `EndpointCompletion` apply to this chart row. -/
theorem completionRow_eq_cyclicCompletionRow (b : Nat)
    (h : ZMod (2 * b + 1)) (k : Fin (2 * b + 1)) :
    ZMod.finEquiv (2 * b + 1) (completionRow b h k) =
      EndpointCompletion.cyclicCompletionRow h
        (ZMod.finEquiv (2 * b + 1) k) := by
  simp [completionRow, EndpointCompletion.cyclicCompletionRow, map_add]

/-- The unit shift `C₁` is the base step `k ↦ k + 1` already used by the
endpoint-completion carry machinery (`finCompletionBaseStep`). -/
theorem completionRow_one_eq_finCompletionBaseStep (b : Nat)
    (k : Fin (2 * b + 1)) :
    completionRow b 1 k = EndpointCompletion.finCompletionBaseStep k := by
  simp [completionRow, EndpointCompletion.finCompletionBaseStep, map_one]

/-! ## Color naming layer

The `2*b+1` colors `(t₀, t₁, t₂, d₁, μ₁, …, d_{b−1}, μ_{b−1})` share the
index set `Fin (2*b+1)` with the coordinates, aligned so that the neutral
row `N` (the identity) lets `t_i` read `τ_i`, `d_j` read `p_j⁺`, and `μ_j`
read `p_j⁻`.  A chart row `σ` then sends the coordinate read by color `c`
to `σ c`. -/

/-- Color `t_i`: same index as the coordinate `τ_i`. -/
def colorT (hb : 1 ≤ b) (i : Fin 3) : Fin (2 * b + 1) := tauIdx hb i

/-- Color `d_{j+1}`: same index as the coordinate `p_{j+1}⁺`. -/
def colorD (j : Fin (b - 1)) : Fin (2 * b + 1) := plusIdx j

/-- Color `μ_{j+1}`: same index as the coordinate `p_{j+1}⁻`. -/
def colorMu (j : Fin (b - 1)) : Fin (2 * b + 1) := minusIdx j

/-- In the neutral row, color `t_i` reads coordinate `τ_i`. -/
theorem neutralRow_colorT (hb : 1 ≤ b) (i : Fin 3) :
    neutralRow b (colorT hb i) = tauIdx hb i := rfl

/-- In the neutral row, color `d_{j+1}` reads coordinate `p_{j+1}⁺`. -/
theorem neutralRow_colorD (j : Fin (b - 1)) :
    neutralRow b (colorD j) = plusIdx j := rfl

/-- In the neutral row, color `μ_{j+1}` reads coordinate `p_{j+1}⁻`. -/
theorem neutralRow_colorMu (j : Fin (b - 1)) :
    neutralRow b (colorMu j) = minusIdx j := rfl

/-! ## The `b = 4` instance against the paper chart

For `b = 4` there are nine coordinates, in order
`τ₀ τ₁ τ₂ p₁⁺ p₁⁻ p₂⁺ p₂⁻ p₃⁺ p₃⁻` (indices `0 … 8`), and the paper
displays six rows.  The table prints the row CONTENT per position, which is
the inverse reading of "index `k ↦ image`"; for the self-inverse rows
(`N`, `X₀`, `X₁`, `X₂`, `R`) both readings agree, and for `C₁` we state the
check in the `k ↦ k + 1` direction (the printed line `τ₁ τ₂ p₁⁺ … τ₀` is
its inverse reading: position `k` holds `Ω_{k+1}`). -/

/-- The nine images of a `b = 4` chart row, in coordinate order
`τ₀ τ₁ τ₂ p₁⁺ p₁⁻ p₂⁺ p₂⁻ p₃⁺ p₃⁻`. -/
def b4RowImages (σ : Equiv.Perm (Fin 9)) : List (Fin 9) :=
  (List.finRange 9).map σ

/-- Paper row `N`: the identity. -/
theorem b4_neutralRow_images :
    b4RowImages (neutralRow 4) = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide

/-- Paper row `X₀`: swap `τ₀ ↔ p₁⁺` (indices `0 ↔ 3`). -/
theorem b4_exchangeRow_zero_images :
    b4RowImages (exchangeRow (le_refl 4) 0) =
      [3, 1, 2, 0, 4, 5, 6, 7, 8] := by decide

/-- Paper row `X₁`: swap `τ₁ ↔ p₂⁺` (indices `1 ↔ 5`). -/
theorem b4_exchangeRow_one_images :
    b4RowImages (exchangeRow (le_refl 4) 1) =
      [0, 5, 2, 3, 4, 1, 6, 7, 8] := by decide

/-- Paper row `X₂`: swap `τ₂ ↔ p₃⁺` (indices `2 ↔ 7`). -/
theorem b4_exchangeRow_two_images :
    b4RowImages (exchangeRow (le_refl 4) 2) =
      [0, 1, 7, 3, 4, 5, 6, 2, 8] := by decide

/-- Paper row `R`: swap `p₁⁻ ↔ p₂⁻` (indices `4 ↔ 6`). -/
theorem b4_resetRow_images :
    b4RowImages (resetRow (le_refl 4)) =
      [0, 1, 2, 3, 6, 5, 4, 7, 8] := by decide

/-- Paper row `C₁`: the cyclic shift `k ↦ k + 1` (the printed table line is
the inverse reading; see the section comment). -/
theorem b4_completionRow_one_images :
    b4RowImages (completionRow 4 1) =
      [1, 2, 3, 4, 5, 6, 7, 8, 0] := by decide

/-- Index-convention bridge to `EvenV11.EndpointCompletion`: the `b = 4`
first-completion TARGET `8 : ZMod 9` is the minus lane `p₃⁻ = minusIdx ⟨2,_⟩`. -/
theorem b4_minusIdx_two_eq_completionTarget :
    ZMod.finEquiv 9 (minusIdx (b := 4) ⟨2, by omega⟩) =
      EndpointCompletion.endpointB4FirstCompletionTarget := by decide

/-- Index-convention bridge to `EvenV11.EndpointCompletion`: the `b = 4`
first-completion TAIL `7 : ZMod 9` is the plus lane `p₃⁺ = plusIdx ⟨2,_⟩`. -/
theorem b4_plusIdx_two_eq_completionTail :
    ZMod.finEquiv 9 (plusIdx (b := 4) ⟨2, by omega⟩) =
      EndpointCompletion.endpointB4FirstCompletionTail := by decide

end EndpointChart
end V28Hard
end EvenV11
