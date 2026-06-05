import Shared.TorusCayley

namespace EvenV11
namespace D3EvenRouteEGeSix

abbrev Vertex (m : Nat) := Shared.TorusVertex 3 m

def dirOfNat (n : Nat) : Shared.TorusDirection 3 :=
  ⟨n % 3, Nat.mod_lt n (by decide)⟩

inductive Word where
  | w012
  | w021
  | w102
  | w120
  | w201
  | w210
  deriving DecidableEq

namespace Word

def toTriple : Word → Nat × Nat × Nat
  | w012 => (0, 1, 2)
  | w021 => (0, 2, 1)
  | w102 => (1, 0, 2)
  | w120 => (1, 2, 0)
  | w201 => (2, 0, 1)
  | w210 => (2, 1, 0)

theorem toTriple_perm (w : Word) :
    w.toTriple = (0, 1, 2) ∨
    w.toTriple = (0, 2, 1) ∨
    w.toTriple = (1, 0, 2) ∨
    w.toTriple = (1, 2, 0) ∨
    w.toTriple = (2, 0, 1) ∨
    w.toTriple = (2, 1, 0) := by
  cases w <;> simp [toTriple]

end Word

def routeEWordCode (m : Nat) (x : Vertex m) : Word :=
  let i := (x 0).val
  let j := (x 1).val
  let k := (x 2).val
  let s := (i + j + k) % m
  if s = 1 then
    if i = 0 then Word.w102 else Word.w201
  else if s = 2 then
    if j = 0 then Word.w210 else Word.w012
  else if s = 0 then
    if m % 6 = 0 ∨ m % 6 = 2 then
      if i = m - 2 ∧ j = 1 ∧ k = 1 then Word.w012
      else if i = m - 2 ∧ j = 2 ∧ k = 0 then Word.w201
      else if i = 0 ∧ j = 0 ∧ k = 0 then Word.w102
      else if 1 <= i ∧ i <= m - 3 ∧ j = 1 ∧
          k = (m - 1 - i) % m then Word.w102
      else if i = m - 1 ∧ j = 2 ∧ k = m - 1 then Word.w102
      else if i = 0 ∧ j = 1 ∧ k = m - 1 then Word.w021
      else if 1 <= i ∧ i <= m - 3 ∧ j = (m - i) % m ∧
          k = 0 then Word.w021
      else if i = m - 1 ∧ j = 0 ∧ k = 1 then Word.w021
      else if i = 0 ∧ 2 <= j ∧ j <= m - 1 ∧
          k = (m - j) % m then Word.w210
      else if i = 1 ∧ j = 0 ∧ k = m - 1 then Word.w210
      else Word.w120
    else
      if i = 0 ∧ j = 0 ∧ k = 0 then Word.w102
      else if 2 <= i ∧ i <= m - 3 ∧ j = 1 ∧
          k = (m - 1 - i) % m then Word.w102
      else if i = m - 1 ∧ j = 2 ∧ k = m - 1 then Word.w102
      else if i = 0 ∧ j = 1 ∧ k = m - 1 then Word.w021
      else if 2 <= i ∧ i <= m - 3 ∧ j = (m - i) % m ∧
          k = 0 then Word.w021
      else if i = m - 1 ∧ j = 0 ∧ k = 1 then Word.w021
      else if i = 0 ∧ 2 <= j ∧ j <= m - 1 ∧
          k = (m - j) % m then Word.w210
      else if i = 1 ∧ j = 0 ∧ k = m - 1 then Word.w210
      else if i = 1 ∧ 2 <= j ∧ j <= m - 2 ∧
          k = (m - 1 - j) % m then Word.w210
      else if i = 2 ∧ j = 0 ∧ k = m - 2 then Word.w210
      else if i = 2 ∧ j = m - 1 ∧ k = m - 1 then Word.w210
      else if (i = 1 ∧ j = 1 ∧ k = m - 2) ∨
          (i = m - 2 ∧ j = 1 ∧ k = 1) then Word.w012
      else if (i = 1 ∧ j = m - 1 ∧ k = 0) ∨
          (i = m - 2 ∧ j = 2 ∧ k = 0) then Word.w201
      else Word.w120
  else
    Word.w012

def routeEWord (m : Nat) (x : Vertex m) : Nat × Nat × Nat :=
  (routeEWordCode m x).toTriple

def colorDir (m : Nat) :
    Shared.TorusColor 3 → Vertex m → Shared.TorusDirection 3
  | ⟨0, _⟩, x => dirOfNat (routeEWord m x).1
  | ⟨1, _⟩, x => dirOfNat (routeEWord m x).2.1
  | ⟨2, _⟩, x => dirOfNat (routeEWord m x).2.2
  | ⟨n + 3, h⟩, _ => by omega

theorem routeEWord_perm (m : Nat) (x : Vertex m) :
    routeEWord m x = (0, 1, 2) ∨
    routeEWord m x = (0, 2, 1) ∨
    routeEWord m x = (1, 0, 2) ∨
    routeEWord m x = (1, 2, 0) ∨
    routeEWord m x = (2, 0, 1) ∨
    routeEWord m x = (2, 1, 0) := by
  exact Word.toTriple_perm (routeEWordCode m x)

def sumLayer (m : Nat) (x : Vertex m) : ZMod m :=
  x 0 + x 1 + x 2

theorem routeEWordCode_eq_w012_of_sumLayer_val_ne_zero_one_two
    {m : Nat} [NeZero m] (x : Vertex m)
    (h0 : (sumLayer m x).val ≠ 0)
    (h1 : (sumLayer m x).val ≠ 1)
    (h2 : (sumLayer m x).val ≠ 2) :
    routeEWordCode m x = Word.w012 := by
  have hs :
      ((x 0).val + (x 1).val + (x 2).val) % m =
        (sumLayer m x).val := by
    simp [sumLayer, ZMod.val_add, Nat.add_mod]
  simp [routeEWordCode, hs, h0, h1, h2]

theorem routeEWordCode_eq_layer_one
    {m : Nat} [NeZero m] (x : Vertex m)
    (h1 : (sumLayer m x).val = 1) :
    routeEWordCode m x =
      if (x 0).val = 0 then Word.w102 else Word.w201 := by
  have hs :
      ((x 0).val + (x 1).val + (x 2).val) % m =
        (sumLayer m x).val := by
    simp [sumLayer, ZMod.val_add, Nat.add_mod]
  simp [routeEWordCode, hs, h1]

theorem routeEWordCode_eq_layer_two
    {m : Nat} [NeZero m] (x : Vertex m)
    (h2 : (sumLayer m x).val = 2) :
    routeEWordCode m x =
      if (x 1).val = 0 then Word.w210 else Word.w012 := by
  have hs :
      ((x 0).val + (x 1).val + (x 2).val) % m =
        (sumLayer m x).val := by
    simp [sumLayer, ZMod.val_add, Nat.add_mod]
  simp [routeEWordCode, hs, h2]

theorem even_mod_six_cases {m : Nat} (hm_even : Even m) :
    m % 6 = 0 ∨ m % 6 = 2 ∨ m % 6 = 4 := by
  rcases hm_even with ⟨k, rfl⟩
  omega

theorem even_mod_six_eq_four_of_not_zero_or_two
    {m : Nat} (hm_even : Even m)
    (hnot : ¬ (m % 6 = 0 ∨ m % 6 = 2)) :
    m % 6 = 4 := by
  rcases even_mod_six_cases hm_even with h0 | h2 | h4
  · exact False.elim (hnot (Or.inl h0))
  · exact False.elim (hnot (Or.inr h2))
  · exact h4

theorem not_mod_zero_or_two_of_mod_four
    {m : Nat} (h4 : m % 6 = 4) :
    ¬ (m % 6 = 0 ∨ m % 6 = 2) := by
  intro h
  rcases h with h0 | h2 <;> omega

theorem zeroLayerRoot_val_sum_mod
    {m : Nat} [NeZero m] (a b : ZMod m) :
    (a.val + b.val + (-a - b).val) % m = 0 := by
  rw [Nat.add_mod]
  rw [← ZMod.val_add]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt (-a - b))]
  rw [← ZMod.val_add (a + b) (-a - b)]
  simp

theorem colorDir_eq_zero_of_routeEWordCode_w012
    {m : Nat} {x : Vertex m}
    (h : routeEWordCode m x = Word.w012) :
    colorDir m (0 : Shared.TorusColor 3) x = (0 : Fin 3) := by
  simp [colorDir, routeEWord, h, Word.toTriple, dirOfNat]

theorem colorDir_eq_one_of_routeEWordCode_w012
    {m : Nat} {x : Vertex m}
    (h : routeEWordCode m x = Word.w012) :
    colorDir m (1 : Shared.TorusColor 3) x = (1 : Fin 3) := by
  simp [colorDir, routeEWord, h, Word.toTriple, dirOfNat]

theorem colorDir_eq_two_of_routeEWordCode_w012
    {m : Nat} {x : Vertex m}
    (h : routeEWordCode m x = Word.w012) :
    colorDir m (2 : Shared.TorusColor 3) x = (2 : Fin 3) := by
  simp [colorDir, routeEWord, h, Word.toTriple, dirOfNat]

theorem edgePartition (m : Nat) :
    Shared.IsCayleyEdgePartition (colorDir m) := by
  intro x i
  rcases routeEWord_perm m x with h | h | h | h | h | h
  · fin_cases i
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢

abbrev RootState (m : Nat) := ZMod m × ZMod m

def rootShiftSecondIfFirstZero (m : Nat) : RootState m ≃ RootState m where
  toFun w := if w.1.val = 0 then (w.1, w.2 + 1) else w
  invFun w := if w.1.val = 0 then (w.1, w.2 - 1) else w
  left_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : a.val = 0 <;> simp [h]
  right_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : a.val = 0 <;> simp [h]

def rootShiftSecondIfFirstNonzero (m : Nat) : RootState m ≃ RootState m where
  toFun w := if w.1.val = 0 then w else (w.1, w.2 + 1)
  invFun w := if w.1.val = 0 then w else (w.1, w.2 - 1)
  left_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : a.val = 0 <;> simp [h]
  right_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : a.val = 0 <;> simp [h]

def rootShiftFirstIfSecondZero (m : Nat) : RootState m ≃ RootState m where
  toFun w := if w.2.val = 0 then (w.1 + 1, w.2) else w
  invFun w := if w.2.val = 0 then (w.1 - 1, w.2) else w
  left_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : b.val = 0 <;> simp [h]
  right_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : b.val = 0 <;> simp [h]

def rootShiftFirstIfSecondNonzero (m : Nat) : RootState m ≃ RootState m where
  toFun w := if w.2.val = 0 then w else (w.1 + 1, w.2)
  invFun w := if w.2.val = 0 then w else (w.1 - 1, w.2)
  left_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : b.val = 0 <;> simp [h]
  right_inv := by
    intro w
    rcases w with ⟨a, b⟩
    by_cases h : b.val = 0 <;> simp [h]

def layerRootEquiv (m : Nat) :
    Vertex m ≃ ZMod m × RootState m where
  toFun x := (sumLayer m x, (x 0, x 1))
  invFun tw := fun i =>
    if i = (0 : Fin 3) then tw.2.1
    else if i = (1 : Fin 3) then tw.2.2
    else tw.1 - tw.2.1 - tw.2.2
  left_inv := by
    intro x
    funext i
    fin_cases i
    · simp
    · simp
    · simp [sumLayer]
      ring
  right_inv := by
    intro tw
    rcases tw with ⟨t, a, b⟩
    apply Prod.ext
    · simp [sumLayer]
    · apply Prod.ext <;> simp

@[simp] theorem layerRootEquiv_symm_sumLayer
    (m : Nat) (t : ZMod m) (w : RootState m) :
    sumLayer m ((layerRootEquiv m).symm (t, w)) = t := by
  have h := congrArg Prod.fst ((layerRootEquiv m).right_inv (t, w))
  simpa [layerRootEquiv] using h

theorem routeEWordCode_zeroLayer_of_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : m % 6 = 0 ∨ m % 6 = 2) (a b : ZMod m) :
    routeEWordCode m ((layerRootEquiv m).symm ((0 : ZMod m), (a, b))) =
      if a.val = m - 2 ∧ b.val = 1 ∧ (-a - b).val = 1 then Word.w012
      else if a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0 then Word.w201
      else if a = 0 ∧ b = 0 ∧ -a - b = 0 then Word.w102
      else if 1 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then Word.w102
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then Word.w102
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then Word.w021
      else if 1 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then Word.w021
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then Word.w021
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then Word.w210
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then Word.w210
      else Word.w120 := by
  have hs := zeroLayerRoot_val_sum_mod (m := m) a b
  simp [routeEWordCode, layerRootEquiv, hs, hmod]

theorem routeEWordCode_zeroLayer_of_not_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : ¬ (m % 6 = 0 ∨ m % 6 = 2)) (a b : ZMod m) :
    routeEWordCode m ((layerRootEquiv m).symm ((0 : ZMod m), (a, b))) =
      if a = 0 ∧ b = 0 ∧ -a - b = 0 then Word.w102
      else if 2 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then Word.w102
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then Word.w102
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then Word.w021
      else if 2 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then Word.w021
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then Word.w021
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then Word.w210
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then Word.w210
      else if a.val = 1 ∧ 2 <= b.val ∧ b.val <= m - 2 ∧
          (-a - b).val = (m - 1 - b.val) % m then Word.w210
      else if a.val = 2 ∧ b = 0 ∧
          (-a - b).val = m - 2 then Word.w210
      else if a.val = 2 ∧ b.val = m - 1 ∧
          (-a - b).val = m - 1 then Word.w210
      else if (a.val = 1 ∧ b.val = 1 ∧
            (-a - b).val = m - 2) ∨
          (a.val = m - 2 ∧ b.val = 1 ∧
            (-a - b).val = 1) then Word.w012
      else if (a.val = 1 ∧ b.val = m - 1 ∧ -a - b = 0) ∨
          (a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0) then Word.w201
      else Word.w120 := by
  have hs := zeroLayerRoot_val_sum_mod (m := m) a b
  simp [routeEWordCode, layerRootEquiv, hs, hmod]

theorem sumLayer_add_torusBasis
    (m : Nat) (x : Vertex m) (i : Fin 3) :
    sumLayer m (x + Shared.torusBasis 3 m i) = sumLayer m x + 1 := by
  fin_cases i <;> simp [sumLayer, Shared.torusBasis, Pi.add_apply] <;> ring

theorem sumLayer_cayleyColorStep
    (m : Nat) (c : Shared.TorusColor 3) (x : Vertex m) :
    sumLayer m (Shared.cayleyColorStep (colorDir m) c x) =
      sumLayer m x + 1 := by
  exact sumLayer_add_torusBasis m x (colorDir m c x)

def wordColorRootStep (m : Nat) (w : Word)
    (c : Shared.TorusColor 3) (r : RootState m) : RootState m :=
  match w with
  | Word.w012 =>
      match c with
      | ⟨0, _⟩ => (r.1 + 1, r.2)
      | ⟨1, _⟩ => (r.1, r.2 + 1)
      | ⟨2, _⟩ => r
      | ⟨n + 3, h⟩ => by omega
  | Word.w021 =>
      match c with
      | ⟨0, _⟩ => (r.1 + 1, r.2)
      | ⟨1, _⟩ => r
      | ⟨2, _⟩ => (r.1, r.2 + 1)
      | ⟨n + 3, h⟩ => by omega
  | Word.w102 =>
      match c with
      | ⟨0, _⟩ => (r.1, r.2 + 1)
      | ⟨1, _⟩ => (r.1 + 1, r.2)
      | ⟨2, _⟩ => r
      | ⟨n + 3, h⟩ => by omega
  | Word.w120 =>
      match c with
      | ⟨0, _⟩ => (r.1, r.2 + 1)
      | ⟨1, _⟩ => r
      | ⟨2, _⟩ => (r.1 + 1, r.2)
      | ⟨n + 3, h⟩ => by omega
  | Word.w201 =>
      match c with
      | ⟨0, _⟩ => r
      | ⟨1, _⟩ => (r.1 + 1, r.2)
      | ⟨2, _⟩ => (r.1, r.2 + 1)
      | ⟨n + 3, h⟩ => by omega
  | Word.w210 =>
      match c with
      | ⟨0, _⟩ => r
      | ⟨1, _⟩ => (r.1, r.2 + 1)
      | ⟨2, _⟩ => (r.1 + 1, r.2)
      | ⟨n + 3, h⟩ => by omega

def routeELayerMap (m : Nat)
    (t : ZMod m) (c : Shared.TorusColor 3) (w : RootState m) :
    RootState m :=
  ((layerRootEquiv m)
    (Shared.cayleyColorStep (colorDir m) c
      ((layerRootEquiv m).symm (t, w)))).2

theorem routeELayerMap_zeroLayer_eq_wordColorRootStep
    {m : Nat} [NeZero m] (c : Shared.TorusColor 3) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) c (a, b) =
      wordColorRootStep m
        (routeEWordCode m
          ((layerRootEquiv m).symm ((0 : ZMod m), (a, b))))
        c (a, b) := by
  have hsymm :
      (layerRootEquiv m).symm ((0 : ZMod m), (a, b)) =
        (fun i => if i = (0 : Fin 3) then a
          else if i = (1 : Fin 3) then b else -a - b) := by
    funext i
    fin_cases i <;> simp [layerRootEquiv]
  rw [hsymm]
  rcases hcode :
      routeEWordCode m
        (fun i => if i = (0 : Fin 3) then a
          else if i = (1 : Fin 3) then b else -a - b) <;>
    fin_cases c <;>
    simp [routeELayerMap, wordColorRootStep, colorDir, routeEWord,
      hcode, Word.toTriple, dirOfNat, Shared.cayleyColorStep,
      Shared.torusBasis, layerRootEquiv]

theorem routeELayerMap_zeroLayer_eq_wordColorRootStep_of_code
    {m : Nat} [NeZero m] {c : Shared.TorusColor 3} {a b : ZMod m}
    {w : Word}
    (hcode :
      routeEWordCode m
        ((layerRootEquiv m).symm ((0 : ZMod m), (a, b))) = w) :
    routeELayerMap m (0 : ZMod m) c (a, b) =
      wordColorRootStep m w c (a, b) := by
  rw [routeELayerMap_zeroLayer_eq_wordColorRootStep, hcode]

theorem routeELayerMap_zeroLayer_of_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : m % 6 = 0 ∨ m % 6 = 2)
    (c : Shared.TorusColor 3) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) c (a, b) =
      wordColorRootStep m
        (if a.val = m - 2 ∧ b.val = 1 ∧ (-a - b).val = 1 then Word.w012
        else if a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0 then Word.w201
        else if a = 0 ∧ b = 0 ∧ -a - b = 0 then Word.w102
        else if 1 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
            (-a - b).val = (m - 1 - a.val) % m then Word.w102
        else if a.val = m - 1 ∧ b.val = 2 ∧
            (-a - b).val = m - 1 then Word.w102
        else if a = 0 ∧ b.val = 1 ∧
            (-a - b).val = m - 1 then Word.w021
        else if 1 <= a.val ∧ a.val <= m - 3 ∧
            b.val = (m - a.val) % m ∧ -a - b = 0 then Word.w021
        else if a.val = m - 1 ∧ b = 0 ∧
            (-a - b).val = 1 then Word.w021
        else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
            (-a - b).val = (m - b.val) % m then Word.w210
        else if a.val = 1 ∧ b = 0 ∧
            (-a - b).val = m - 1 then Word.w210
        else Word.w120) c (a, b) := by
  exact routeELayerMap_zeroLayer_eq_wordColorRootStep_of_code
    (routeEWordCode_zeroLayer_of_mod_zero_or_two hmod a b)

theorem routeELayerMap_zeroLayer_of_not_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : ¬ (m % 6 = 0 ∨ m % 6 = 2))
    (c : Shared.TorusColor 3) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) c (a, b) =
      wordColorRootStep m
        (if a = 0 ∧ b = 0 ∧ -a - b = 0 then Word.w102
        else if 2 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
            (-a - b).val = (m - 1 - a.val) % m then Word.w102
        else if a.val = m - 1 ∧ b.val = 2 ∧
            (-a - b).val = m - 1 then Word.w102
        else if a = 0 ∧ b.val = 1 ∧
            (-a - b).val = m - 1 then Word.w021
        else if 2 <= a.val ∧ a.val <= m - 3 ∧
            b.val = (m - a.val) % m ∧ -a - b = 0 then Word.w021
        else if a.val = m - 1 ∧ b = 0 ∧
            (-a - b).val = 1 then Word.w021
        else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
            (-a - b).val = (m - b.val) % m then Word.w210
        else if a.val = 1 ∧ b = 0 ∧
            (-a - b).val = m - 1 then Word.w210
        else if a.val = 1 ∧ 2 <= b.val ∧ b.val <= m - 2 ∧
            (-a - b).val = (m - 1 - b.val) % m then Word.w210
        else if a.val = 2 ∧ b = 0 ∧
            (-a - b).val = m - 2 then Word.w210
        else if a.val = 2 ∧ b.val = m - 1 ∧
            (-a - b).val = m - 1 then Word.w210
        else if (a.val = 1 ∧ b.val = 1 ∧
              (-a - b).val = m - 2) ∨
            (a.val = m - 2 ∧ b.val = 1 ∧
              (-a - b).val = 1) then Word.w012
        else if (a.val = 1 ∧ b.val = m - 1 ∧ -a - b = 0) ∨
            (a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0) then Word.w201
        else Word.w120) c (a, b) := by
  exact routeELayerMap_zeroLayer_eq_wordColorRootStep_of_code
    (routeEWordCode_zeroLayer_of_not_mod_zero_or_two hmod a b)

set_option maxHeartbeats 1000000 in
-- Splitting the zero-layer Route-E word table into a colour-0 map table
-- expands ten nested decidable branches.
theorem routeELayerMap_zeroLayer_color_zero_of_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : m % 6 = 0 ∨ m % 6 = 2) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) (0 : Shared.TorusColor 3) (a, b) =
      if a.val = m - 2 ∧ b.val = 1 ∧ (-a - b).val = 1 then
        (a + 1, b)
      else if a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0 then
        (a, b)
      else if a = 0 ∧ b = 0 ∧ -a - b = 0 then
        (a, b + 1)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then
        (a, b + 1)
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then
        (a, b + 1)
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then
        (a + 1, b)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then
        (a + 1, b)
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then
        (a + 1, b)
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then
        (a, b)
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then
        (a, b)
      else
        (a, b + 1) := by
  rw [routeELayerMap_zeroLayer_of_mod_zero_or_two hmod]
  simp only [wordColorRootStep]
  split_ifs <;> rfl

set_option maxHeartbeats 1000000 in
-- Splitting the zero-layer Route-E word table into a colour-1 map table
-- expands ten nested decidable branches.
theorem routeELayerMap_zeroLayer_color_one_of_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : m % 6 = 0 ∨ m % 6 = 2) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) (1 : Shared.TorusColor 3) (a, b) =
      if a.val = m - 2 ∧ b.val = 1 ∧ (-a - b).val = 1 then
        (a, b + 1)
      else if a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0 then
        (a + 1, b)
      else if a = 0 ∧ b = 0 ∧ -a - b = 0 then
        (a + 1, b)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then
        (a + 1, b)
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then
        (a + 1, b)
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then
        (a, b)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then
        (a, b)
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then
        (a, b)
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then
        (a, b + 1)
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then
        (a, b + 1)
      else
        (a, b) := by
  rw [routeELayerMap_zeroLayer_of_mod_zero_or_two hmod]
  simp only [wordColorRootStep]
  split_ifs <;> rfl

set_option maxHeartbeats 1000000 in
-- Splitting the zero-layer Route-E word table into a colour-2 map table
-- expands ten nested decidable branches.
theorem routeELayerMap_zeroLayer_color_two_of_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : m % 6 = 0 ∨ m % 6 = 2) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) (2 : Shared.TorusColor 3) (a, b) =
      if a.val = m - 2 ∧ b.val = 1 ∧ (-a - b).val = 1 then
        (a, b)
      else if a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0 then
        (a, b + 1)
      else if a = 0 ∧ b = 0 ∧ -a - b = 0 then
        (a, b)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then
        (a, b)
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then
        (a, b)
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then
        (a, b + 1)
      else if 1 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then
        (a, b + 1)
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then
        (a, b + 1)
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then
        (a + 1, b)
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then
        (a + 1, b)
      else
        (a + 1, b) := by
  rw [routeELayerMap_zeroLayer_of_mod_zero_or_two hmod]
  simp only [wordColorRootStep]
  split_ifs <;> rfl

private theorem apply_word_ite {α : Sort*} (f : Word -> α)
    (p : Prop) [Decidable p] (x y : Word) :
    f (if p then x else y) = if p then f x else f y := by
  by_cases hp : p <;> simp [hp]

set_option maxHeartbeats 1000000 in
-- Splitting the zero-layer Route-E word table into the colour-2 map table
-- for the remaining even residue class expands fourteen decidable branches.
theorem routeELayerMap_zeroLayer_color_two_of_not_mod_zero_or_two
    {m : Nat} [NeZero m]
    (hmod : ¬ (m % 6 = 0 ∨ m % 6 = 2)) (a b : ZMod m) :
    routeELayerMap m (0 : ZMod m) (2 : Shared.TorusColor 3) (a, b) =
      if a = 0 ∧ b = 0 ∧ -a - b = 0 then
        (a, b)
      else if 2 <= a.val ∧ a.val <= m - 3 ∧ b.val = 1 ∧
          (-a - b).val = (m - 1 - a.val) % m then
        (a, b)
      else if a.val = m - 1 ∧ b.val = 2 ∧
          (-a - b).val = m - 1 then
        (a, b)
      else if a = 0 ∧ b.val = 1 ∧
          (-a - b).val = m - 1 then
        (a, b + 1)
      else if 2 <= a.val ∧ a.val <= m - 3 ∧
          b.val = (m - a.val) % m ∧ -a - b = 0 then
        (a, b + 1)
      else if a.val = m - 1 ∧ b = 0 ∧
          (-a - b).val = 1 then
        (a, b + 1)
      else if a = 0 ∧ 2 <= b.val ∧ b.val <= m - 1 ∧
          (-a - b).val = (m - b.val) % m then
        (a + 1, b)
      else if a.val = 1 ∧ b = 0 ∧
          (-a - b).val = m - 1 then
        (a + 1, b)
      else if a.val = 1 ∧ 2 <= b.val ∧ b.val <= m - 2 ∧
          (-a - b).val = (m - 1 - b.val) % m then
        (a + 1, b)
      else if a.val = 2 ∧ b = 0 ∧
          (-a - b).val = m - 2 then
        (a + 1, b)
      else if a.val = 2 ∧ b.val = m - 1 ∧
          (-a - b).val = m - 1 then
        (a + 1, b)
      else if (a.val = 1 ∧ b.val = 1 ∧
            (-a - b).val = m - 2) ∨
          (a.val = m - 2 ∧ b.val = 1 ∧
            (-a - b).val = 1) then
        (a, b)
      else if (a.val = 1 ∧ b.val = m - 1 ∧ -a - b = 0) ∨
          (a.val = m - 2 ∧ b.val = 2 ∧ -a - b = 0) then
        (a, b + 1)
      else
        (a + 1, b) := by
  rw [routeELayerMap_zeroLayer_of_not_mod_zero_or_two hmod]
  repeat rw [apply_word_ite
    (fun w => wordColorRootStep m w (2 : Shared.TorusColor 3) (a, b))]
  simp [wordColorRootStep]

theorem routeELayerMap_zero_of_layer_val_ne_zero_one_two
    {m : Nat} [NeZero m] {t : ZMod m} (w : RootState m)
    (h0 : t.val ≠ 0) (h1 : t.val ≠ 1) (h2 : t.val ≠ 2) :
    routeELayerMap m t (0 : Shared.TorusColor 3) w = (w.1 + 1, w.2) := by
  let x : Vertex m := (layerRootEquiv m).symm (t, w)
  have hcode : routeEWordCode m x = Word.w012 := by
    apply routeEWordCode_eq_w012_of_sumLayer_val_ne_zero_one_two
    · simpa [x] using h0
    · simpa [x] using h1
    · simpa [x] using h2
  have hdir : colorDir m (0 : Shared.TorusColor 3) x = (0 : Fin 3) :=
    colorDir_eq_zero_of_routeEWordCode_w012 hcode
  rcases w with ⟨a, b⟩
  change colorDir m (0 : Shared.TorusColor 3)
      (fun i => if i = 0 then a else if i = 1 then b else t - a - b) =
        (0 : Fin 3) at hdir
  simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
    layerRootEquiv]

theorem routeELayerMap_one_of_layer_val_ne_zero_one_two
    {m : Nat} [NeZero m] {t : ZMod m} (w : RootState m)
    (h0 : t.val ≠ 0) (h1 : t.val ≠ 1) (h2 : t.val ≠ 2) :
    routeELayerMap m t (1 : Shared.TorusColor 3) w = (w.1, w.2 + 1) := by
  let x : Vertex m := (layerRootEquiv m).symm (t, w)
  have hcode : routeEWordCode m x = Word.w012 := by
    apply routeEWordCode_eq_w012_of_sumLayer_val_ne_zero_one_two
    · simpa [x] using h0
    · simpa [x] using h1
    · simpa [x] using h2
  have hdir : colorDir m (1 : Shared.TorusColor 3) x = (1 : Fin 3) :=
    colorDir_eq_one_of_routeEWordCode_w012 hcode
  rcases w with ⟨a, b⟩
  change colorDir m (1 : Shared.TorusColor 3)
      (fun i => if i = 0 then a else if i = 1 then b else t - a - b) =
        (1 : Fin 3) at hdir
  simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
    layerRootEquiv]

theorem routeELayerMap_two_of_layer_val_ne_zero_one_two
    {m : Nat} [NeZero m] {t : ZMod m} (w : RootState m)
    (h0 : t.val ≠ 0) (h1 : t.val ≠ 1) (h2 : t.val ≠ 2) :
    routeELayerMap m t (2 : Shared.TorusColor 3) w = w := by
  let x : Vertex m := (layerRootEquiv m).symm (t, w)
  have hcode : routeEWordCode m x = Word.w012 := by
    apply routeEWordCode_eq_w012_of_sumLayer_val_ne_zero_one_two
    · simpa [x] using h0
    · simpa [x] using h1
    · simpa [x] using h2
  have hdir : colorDir m (2 : Shared.TorusColor 3) x = (2 : Fin 3) :=
    colorDir_eq_two_of_routeEWordCode_w012 hcode
  rcases w with ⟨a, b⟩
  change colorDir m (2 : Shared.TorusColor 3)
      (fun i => if i = 0 then a else if i = 1 then b else t - a - b) =
        (2 : Fin 3) at hdir
  simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
    layerRootEquiv]

theorem routeELayerMap_bijective_of_layer_val_ne_zero_one_two
    {m : Nat} [NeZero m] {t : ZMod m}
    (h0 : t.val ≠ 0) (h1 : t.val ≠ 1) (h2 : t.val ≠ 2)
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap m t c) := by
  fin_cases c
  · convert
      (Equiv.prodCongr
        (Equiv.addRight (1 : ZMod m)) (Equiv.refl (ZMod m))).bijective
      using 1
    funext w
    exact routeELayerMap_zero_of_layer_val_ne_zero_one_two w h0 h1 h2
  · convert
      (Equiv.prodCongr
        (Equiv.refl (ZMod m)) (Equiv.addRight (1 : ZMod m))).bijective
      using 1
    funext w
    exact routeELayerMap_one_of_layer_val_ne_zero_one_two w h0 h1 h2
  · convert (Equiv.refl (RootState m)).bijective using 1
    funext w
    exact routeELayerMap_two_of_layer_val_ne_zero_one_two w h0 h1 h2

theorem routeELayerMap_color_zero_of_layer_one
    {m : Nat} [NeZero m] (hm2 : 2 <= m) (w : RootState m) :
    routeELayerMap m (1 : ZMod m) (0 : Shared.TorusColor 3) w =
      if w.1.val = 0 then (w.1, w.2 + 1) else w := by
  let x : Vertex m := (layerRootEquiv m).symm ((1 : ZMod m), w)
  have hsum : (sumLayer m x).val = 1 := by
    simp [x, ZMod.val_one'' (by omega : m ≠ 1)]
  have hcode :
      routeEWordCode m x =
        if (x 0).val = 0 then Word.w102 else Word.w201 :=
    routeEWordCode_eq_layer_one x hsum
  rcases w with ⟨a, b⟩
  by_cases h : a.val = 0
  · have hx0 : (x 0).val = 0 := by
      simpa [x] using h
    have hdir : colorDir m (0 : Shared.TorusColor 3) x = (1 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx0, Word.toTriple, dirOfNat]
    change colorDir m (0 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (1 : ZMod m) - a - b) = (1 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]
  · have hx0 : (x 0).val ≠ 0 := by
      simpa [x] using h
    have hdir : colorDir m (0 : Shared.TorusColor 3) x = (2 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx0, Word.toTriple, dirOfNat]
    change colorDir m (0 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (1 : ZMod m) - a - b) = (2 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]

theorem routeELayerMap_color_one_of_layer_one
    {m : Nat} [NeZero m] (hm2 : 2 <= m) (w : RootState m) :
    routeELayerMap m (1 : ZMod m) (1 : Shared.TorusColor 3) w =
      (w.1 + 1, w.2) := by
  let x : Vertex m := (layerRootEquiv m).symm ((1 : ZMod m), w)
  have hsum : (sumLayer m x).val = 1 := by
    simp [x, ZMod.val_one'' (by omega : m ≠ 1)]
  have hcode :
      routeEWordCode m x =
        if (x 0).val = 0 then Word.w102 else Word.w201 :=
    routeEWordCode_eq_layer_one x hsum
  have hdir : colorDir m (1 : Shared.TorusColor 3) x = (0 : Fin 3) := by
    by_cases h : (x 0).val = 0 <;>
      simp [colorDir, routeEWord, hcode, h, Word.toTriple, dirOfNat]
  rcases w with ⟨a, b⟩
  change colorDir m (1 : Shared.TorusColor 3)
      (fun i => if i = 0 then a else if i = 1 then b else
        (1 : ZMod m) - a - b) = (0 : Fin 3) at hdir
  simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
    layerRootEquiv]

theorem routeELayerMap_color_one_bijective_of_layer_one
    {m : Nat} [NeZero m] (hm2 : 2 <= m) :
    Function.Bijective
      (routeELayerMap m (1 : ZMod m) (1 : Shared.TorusColor 3)) := by
  convert
    (Equiv.prodCongr
      (Equiv.addRight (1 : ZMod m)) (Equiv.refl (ZMod m))).bijective
    using 1
  funext w
  exact routeELayerMap_color_one_of_layer_one hm2 w

theorem routeELayerMap_color_two_of_layer_one
    {m : Nat} [NeZero m] (hm2 : 2 <= m) (w : RootState m) :
    routeELayerMap m (1 : ZMod m) (2 : Shared.TorusColor 3) w =
      if w.1.val = 0 then w else (w.1, w.2 + 1) := by
  let x : Vertex m := (layerRootEquiv m).symm ((1 : ZMod m), w)
  have hsum : (sumLayer m x).val = 1 := by
    simp [x, ZMod.val_one'' (by omega : m ≠ 1)]
  have hcode :
      routeEWordCode m x =
        if (x 0).val = 0 then Word.w102 else Word.w201 :=
    routeEWordCode_eq_layer_one x hsum
  rcases w with ⟨a, b⟩
  by_cases h : a.val = 0
  · have hx0 : (x 0).val = 0 := by
      simpa [x] using h
    have hdir : colorDir m (2 : Shared.TorusColor 3) x = (2 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx0, Word.toTriple, dirOfNat]
    change colorDir m (2 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (1 : ZMod m) - a - b) = (2 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]
  · have hx0 : (x 0).val ≠ 0 := by
      simpa [x] using h
    have hdir : colorDir m (2 : Shared.TorusColor 3) x = (1 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx0, Word.toTriple, dirOfNat]
    change colorDir m (2 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (1 : ZMod m) - a - b) = (1 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]

theorem routeELayerMap_bijective_of_layer_one
    {m : Nat} [NeZero m] (hm2 : 2 <= m)
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap m (1 : ZMod m) c) := by
  fin_cases c
  · convert (rootShiftSecondIfFirstZero m).bijective using 1
    funext w
    exact routeELayerMap_color_zero_of_layer_one hm2 w
  · exact routeELayerMap_color_one_bijective_of_layer_one hm2
  · convert (rootShiftSecondIfFirstNonzero m).bijective using 1
    funext w
    exact routeELayerMap_color_two_of_layer_one hm2 w

theorem routeELayerMap_color_zero_of_layer_two
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerMap m (2 : ZMod m) (0 : Shared.TorusColor 3) w =
      if w.2.val = 0 then w else (w.1 + 1, w.2) := by
  let x : Vertex m := (layerRootEquiv m).symm ((2 : ZMod m), w)
  have htwo : (2 : ZMod m).val = 2 := by
    exact ZMod.val_natCast_of_lt (n := m) (a := 2) (by omega : 2 < m)
  have hsum : (sumLayer m x).val = 2 := by
    simp [x, htwo]
  have hcode :
      routeEWordCode m x =
        if (x 1).val = 0 then Word.w210 else Word.w012 :=
    routeEWordCode_eq_layer_two x hsum
  rcases w with ⟨a, b⟩
  by_cases h : b.val = 0
  · have hx1 : (x 1).val = 0 := by
      simpa [x] using h
    have hdir : colorDir m (0 : Shared.TorusColor 3) x = (2 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx1, Word.toTriple, dirOfNat]
    change colorDir m (0 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (2 : ZMod m) - a - b) = (2 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]
  · have hx1 : (x 1).val ≠ 0 := by
      simpa [x] using h
    have hdir : colorDir m (0 : Shared.TorusColor 3) x = (0 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx1, Word.toTriple, dirOfNat]
    change colorDir m (0 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (2 : ZMod m) - a - b) = (0 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]

theorem routeELayerMap_color_one_of_layer_two
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerMap m (2 : ZMod m) (1 : Shared.TorusColor 3) w =
      (w.1, w.2 + 1) := by
  let x : Vertex m := (layerRootEquiv m).symm ((2 : ZMod m), w)
  have htwo : (2 : ZMod m).val = 2 := by
    exact ZMod.val_natCast_of_lt (n := m) (a := 2) (by omega : 2 < m)
  have hsum : (sumLayer m x).val = 2 := by
    simp [x, htwo]
  have hcode :
      routeEWordCode m x =
        if (x 1).val = 0 then Word.w210 else Word.w012 :=
    routeEWordCode_eq_layer_two x hsum
  have hdir : colorDir m (1 : Shared.TorusColor 3) x = (1 : Fin 3) := by
    by_cases h : (x 1).val = 0 <;>
      simp [colorDir, routeEWord, hcode, h, Word.toTriple, dirOfNat]
  rcases w with ⟨a, b⟩
  change colorDir m (1 : Shared.TorusColor 3)
      (fun i => if i = 0 then a else if i = 1 then b else
        (2 : ZMod m) - a - b) = (1 : Fin 3) at hdir
  simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
    layerRootEquiv]

theorem routeELayerMap_color_one_bijective_of_layer_two
    {m : Nat} [NeZero m] (hm3 : 3 <= m) :
    Function.Bijective
      (routeELayerMap m (2 : ZMod m) (1 : Shared.TorusColor 3)) := by
  convert
    (Equiv.prodCongr
      (Equiv.refl (ZMod m)) (Equiv.addRight (1 : ZMod m))).bijective
    using 1
  funext w
  exact routeELayerMap_color_one_of_layer_two hm3 w

theorem routeELayerMap_color_two_of_layer_two
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerMap m (2 : ZMod m) (2 : Shared.TorusColor 3) w =
      if w.2.val = 0 then (w.1 + 1, w.2) else w := by
  let x : Vertex m := (layerRootEquiv m).symm ((2 : ZMod m), w)
  have htwo : (2 : ZMod m).val = 2 := by
    exact ZMod.val_natCast_of_lt (n := m) (a := 2) (by omega : 2 < m)
  have hsum : (sumLayer m x).val = 2 := by
    simp [x, htwo]
  have hcode :
      routeEWordCode m x =
        if (x 1).val = 0 then Word.w210 else Word.w012 :=
    routeEWordCode_eq_layer_two x hsum
  rcases w with ⟨a, b⟩
  by_cases h : b.val = 0
  · have hx1 : (x 1).val = 0 := by
      simpa [x] using h
    have hdir : colorDir m (2 : Shared.TorusColor 3) x = (0 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx1, Word.toTriple, dirOfNat]
    change colorDir m (2 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (2 : ZMod m) - a - b) = (0 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]
  · have hx1 : (x 1).val ≠ 0 := by
      simpa [x] using h
    have hdir : colorDir m (2 : Shared.TorusColor 3) x = (2 : Fin 3) := by
      simp [colorDir, routeEWord, hcode, hx1, Word.toTriple, dirOfNat]
    change colorDir m (2 : Shared.TorusColor 3)
        (fun i => if i = 0 then a else if i = 1 then b else
          (2 : ZMod m) - a - b) = (2 : Fin 3) at hdir
    simp [routeELayerMap, Shared.cayleyColorStep, hdir, Shared.torusBasis,
      layerRootEquiv, h]

theorem routeELayerMap_bijective_of_layer_two
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap m (2 : ZMod m) c) := by
  fin_cases c
  · convert (rootShiftFirstIfSecondNonzero m).bijective using 1
    funext w
    exact routeELayerMap_color_zero_of_layer_two hm3 w
  · exact routeELayerMap_color_one_bijective_of_layer_two hm3
  · convert (rootShiftFirstIfSecondZero m).bijective using 1
    funext w
    exact routeELayerMap_color_two_of_layer_two hm3 w

theorem routeELayerMap_bijective_of_layer_val_ne_zero
    {m : Nat} [NeZero m] (hm3 : 3 <= m) {t : ZMod m}
    (h0 : t.val ≠ 0) (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap m t c) := by
  by_cases h1 : t.val = 1
  · have ht : t = (1 : ZMod m) := by
      calc
        t = (t.val : ZMod m) := (ZMod.natCast_zmod_val t).symm
        _ = (1 : ZMod m) := by simp [h1]
    subst t
    exact routeELayerMap_bijective_of_layer_one (by omega : 2 <= m) c
  · by_cases h2 : t.val = 2
    · have ht : t = (2 : ZMod m) := by
        calc
          t = (t.val : ZMod m) := (ZMod.natCast_zmod_val t).symm
          _ = (2 : ZMod m) := by simp [h2]
      subst t
      exact routeELayerMap_bijective_of_layer_two hm3 c
    · exact routeELayerMap_bijective_of_layer_val_ne_zero_one_two
        h0 h1 h2 c

theorem routeELayerMap_bijective_of_zero_layer
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c)) :
    ∀ c : Shared.TorusColor 3, ∀ t : ZMod m,
      Function.Bijective (routeELayerMap m t c) := by
  intro c t
  by_cases h0 : t.val = 0
  · have ht : t = (0 : ZMod m) := by
      calc
        t = (t.val : ZMod m) := (ZMod.natCast_zmod_val t).symm
        _ = (0 : ZMod m) := by simp [h0]
    subst t
    exact hZero c
  · exact routeELayerMap_bijective_of_layer_val_ne_zero hm3 h0 c

theorem routeELayerMap_zero_layer_bijective_of_even_mod_cases
    {m : Nat} [NeZero m] (hm_even : Even m)
    (hZeroOrTwo :
      (m % 6 = 0 ∨ m % 6 = 2) ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hFour :
      m % 6 = 4 ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c)) :
    ∀ c : Shared.TorusColor 3,
      Function.Bijective (routeELayerMap m (0 : ZMod m) c) := by
  rcases even_mod_six_cases hm_even with h0 | h2 | h4
  · exact hZeroOrTwo (Or.inl h0)
  · exact hZeroOrTwo (Or.inr h2)
  · exact hFour h4

theorem routeELayerMap_zero_layer_bijective_m6
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap 6 (0 : ZMod 6) c) := by
  fin_cases c <;> decide

theorem routeELayerMap_bijective_m6
    (c : Shared.TorusColor 3) (t : ZMod 6) :
    Function.Bijective (routeELayerMap 6 t c) :=
  routeELayerMap_bijective_of_zero_layer
    (m := 6) (by norm_num) routeELayerMap_zero_layer_bijective_m6 c t

set_option maxRecDepth 10000 in
theorem routeELayerMap_zero_layer_bijective_m8
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap 8 (0 : ZMod 8) c) := by
  fin_cases c <;> decide

theorem routeELayerMap_bijective_m8
    (c : Shared.TorusColor 3) (t : ZMod 8) :
    Function.Bijective (routeELayerMap 8 t c) :=
  routeELayerMap_bijective_of_zero_layer
    (m := 8) (by norm_num) routeELayerMap_zero_layer_bijective_m8 c t

set_option maxRecDepth 10000 in
theorem routeELayerMap_zero_layer_bijective_m10
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap 10 (0 : ZMod 10) c) := by
  fin_cases c <;> decide

theorem routeELayerMap_bijective_m10
    (c : Shared.TorusColor 3) (t : ZMod 10) :
    Function.Bijective (routeELayerMap 10 t c) :=
  routeELayerMap_bijective_of_zero_layer
    (m := 10) (by norm_num) routeELayerMap_zero_layer_bijective_m10 c t

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
-- The generated zero-layer check expands over the 12x12 root-state space.
theorem routeELayerMap_zero_layer_bijective_m12
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeELayerMap 12 (0 : ZMod 12) c) := by
  fin_cases c <;> decide

theorem routeELayerMap_bijective_m12
    (c : Shared.TorusColor 3) (t : ZMod 12) :
    Function.Bijective (routeELayerMap 12 t c) :=
  routeELayerMap_bijective_of_zero_layer
    (m := 12) (by norm_num) routeELayerMap_zero_layer_bijective_m12 c t

theorem routeELayerMap_zero_layer_bijective_of_even_ge_six_tail
    {m : Nat} [NeZero m] (hm_even : Even m) (hm6 : 6 <= m)
    (hTail :
      14 <= m ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c)) :
    ∀ c : Shared.TorusColor 3,
      Function.Bijective (routeELayerMap m (0 : ZMod m) c) := by
  by_cases h6eq : m = 6
  · subst m
    exact routeELayerMap_zero_layer_bijective_m6
  · by_cases h8eq : m = 8
    · subst m
      exact routeELayerMap_zero_layer_bijective_m8
    · by_cases h10eq : m = 10
      · subst m
        exact routeELayerMap_zero_layer_bijective_m10
      · by_cases h12eq : m = 12
        · subst m
          exact routeELayerMap_zero_layer_bijective_m12
        · exact hTail (by
            rcases hm_even with ⟨k, rfl⟩
            omega)

theorem layerRootEquiv_cayleyColorStep
    (m : Nat) (t : ZMod m) (c : Shared.TorusColor 3)
    (w : RootState m) :
    (layerRootEquiv m)
      (Shared.cayleyColorStep (colorDir m) c
        ((layerRootEquiv m).symm (t, w))) =
      (t + 1, routeELayerMap m t c w) := by
  apply Prod.ext
  · change
      sumLayer m
        (Shared.cayleyColorStep (colorDir m) c
          ((layerRootEquiv m).symm (t, w))) = t + 1
    rw [sumLayer_cayleyColorStep]
    simp
  · rfl

def routeELayerPrefixMap (m : Nat) (c : Shared.TorusColor 3) :
    Nat -> RootState m -> RootState m
  | 0 => fun w => w
  | k + 1 => fun w =>
      routeELayerMap m (k : ZMod m) c
        (routeELayerPrefixMap m c k w)

def routeEReturnMap (m : Nat) (c : Shared.TorusColor 3) :
    RootState m -> RootState m :=
  routeELayerPrefixMap m c m

def routeEFullStep (m : Nat) (c : Shared.TorusColor 3) :
    ZMod m × RootState m -> ZMod m × RootState m :=
  fun tw => (tw.1 + 1, routeELayerMap m tw.1 c tw.2)

theorem layerRootEquiv_cayleyColorStep_fullStep
    (m : Nat) (c : Shared.TorusColor 3) (tw : ZMod m × RootState m) :
    (layerRootEquiv m)
      (Shared.cayleyColorStep (colorDir m) c
        ((layerRootEquiv m).symm tw)) =
      routeEFullStep m c tw := by
  rcases tw with ⟨t, w⟩
  exact layerRootEquiv_cayleyColorStep m t c w

theorem layerRootEquiv_cayleyColorStep_any
    (m : Nat) (c : Shared.TorusColor 3) (x : Vertex m) :
    (layerRootEquiv m)
      (Shared.cayleyColorStep (colorDir m) c x) =
      routeEFullStep m c ((layerRootEquiv m) x) := by
  simpa using
    layerRootEquiv_cayleyColorStep_fullStep
      m c ((layerRootEquiv m) x)

theorem routeEFullStep_bijective
    (m : Nat) (c : Shared.TorusColor 3)
    (hLayer :
      ∀ t : ZMod m, Function.Bijective (routeELayerMap m t c)) :
    Function.Bijective (routeEFullStep m c) := by
  constructor
  · intro x y hxy
    rcases x with ⟨tx, wx⟩
    rcases y with ⟨ty, wy⟩
    have ht : tx + 1 = ty + 1 := congrArg Prod.fst hxy
    have ht' : tx = ty := add_right_cancel ht
    subst ty
    have hw :
        routeELayerMap m tx c wx =
          routeELayerMap m tx c wy := by
      simpa [routeEFullStep] using congrArg Prod.snd hxy
    exact Prod.ext rfl ((hLayer tx).1 hw)
  · intro y
    rcases y with ⟨t', w'⟩
    let t : ZMod m := t' - 1
    rcases (hLayer t).2 w' with ⟨w, hw⟩
    refine ⟨(t, w), ?_⟩
    apply Prod.ext
    · simp [routeEFullStep, t]
    · simp [routeEFullStep, t, hw]

theorem routeELayerPrefixMap_bijective
    (m : Nat) (c : Shared.TorusColor 3)
    (hLayer :
      ∀ t : ZMod m, Function.Bijective (routeELayerMap m t c)) :
    ∀ k : Nat, Function.Bijective (routeELayerPrefixMap m c k)
  | 0 => by
      constructor
      · intro x y hxy
        simpa [routeELayerPrefixMap] using hxy
      · intro y
        exact ⟨y, by simp [routeELayerPrefixMap]⟩
  | k + 1 => by
    simpa [routeELayerPrefixMap, Function.comp_def] using
        (hLayer (k : ZMod m)).comp
          (routeELayerPrefixMap_bijective m c hLayer k)

theorem routeELayerPrefixMap_bijective_of_zero_layer
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (c : Shared.TorusColor 3) (k : Nat) :
    Function.Bijective (routeELayerPrefixMap m c k) :=
  routeELayerPrefixMap_bijective m c
    ((routeELayerMap_bijective_of_zero_layer hm3 hZero) c) k

theorem routeEReturnMap_bijective_of_zero_layer
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeEReturnMap m c) := by
  simpa [routeEReturnMap] using
    routeELayerPrefixMap_bijective_of_zero_layer hm3 hZero c m

theorem routeEReturnMap_bijective_m6
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeEReturnMap 6 c) :=
  routeEReturnMap_bijective_of_zero_layer
    (m := 6) (by norm_num) routeELayerMap_zero_layer_bijective_m6 c

theorem routeEReturnMap_bijective_m8
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeEReturnMap 8 c) :=
  routeEReturnMap_bijective_of_zero_layer
    (m := 8) (by norm_num) routeELayerMap_zero_layer_bijective_m8 c

theorem routeEReturnMap_bijective_m10
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeEReturnMap 10 c) :=
  routeEReturnMap_bijective_of_zero_layer
    (m := 10) (by norm_num) routeELayerMap_zero_layer_bijective_m10 c

theorem routeEReturnMap_bijective_m12
    (c : Shared.TorusColor 3) :
    Function.Bijective (routeEReturnMap 12 c) :=
  routeEReturnMap_bijective_of_zero_layer
    (m := 12) (by norm_num) routeELayerMap_zero_layer_bijective_m12 c

def routeEPrefix3ZeroModel (m : Nat) (w : RootState m) : RootState m :=
  let z := routeELayerMap m (0 : ZMod m) (0 : Shared.TorusColor 3) w
  let v := if z.1.val = 0 then (z.1, z.2 + 1) else z
  if v.2.val = 0 then v else (v.1 + 1, v.2)

def routeEPrefix3OneModel (m : Nat) (w : RootState m) : RootState m :=
  let z := routeELayerMap m (0 : ZMod m) (1 : Shared.TorusColor 3) w
  (z.1 + 1, z.2 + 1)

def routeEPrefix3TwoModel (m : Nat) (w : RootState m) : RootState m :=
  let z := routeELayerMap m (0 : ZMod m) (2 : Shared.TorusColor 3) w
  let v := if z.1.val = 0 then z else (z.1, z.2 + 1)
  if v.2.val = 0 then (v.1 + 1, v.2) else v

theorem routeELayerPrefixMap_three_zero_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerPrefixMap m (0 : Shared.TorusColor 3) 3 w =
      routeEPrefix3ZeroModel m w := by
  simp only [routeELayerPrefixMap]
  rw [show ((0 : Nat) : ZMod m) = (0 : ZMod m) by norm_num]
  rw [show ((1 : Nat) : ZMod m) = (1 : ZMod m) by norm_num]
  rw [show ((2 : Nat) : ZMod m) = (2 : ZMod m) by norm_num]
  rw [routeELayerMap_color_zero_of_layer_one
    (by omega : 2 <= m)
    (routeELayerMap m (0 : ZMod m) (0 : Shared.TorusColor 3) w)]
  rw [routeELayerMap_color_zero_of_layer_two hm3]
  simp [routeEPrefix3ZeroModel]

theorem routeELayerPrefixMap_three_one_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerPrefixMap m (1 : Shared.TorusColor 3) 3 w =
      routeEPrefix3OneModel m w := by
  simp only [routeELayerPrefixMap]
  rw [show ((0 : Nat) : ZMod m) = (0 : ZMod m) by norm_num]
  rw [show ((1 : Nat) : ZMod m) = (1 : ZMod m) by norm_num]
  rw [show ((2 : Nat) : ZMod m) = (2 : ZMod m) by norm_num]
  rw [routeELayerMap_color_one_of_layer_one
    (by omega : 2 <= m)
    (routeELayerMap m (0 : ZMod m) (1 : Shared.TorusColor 3) w)]
  rw [routeELayerMap_color_one_of_layer_two hm3]
  simp [routeEPrefix3OneModel]

theorem routeELayerPrefixMap_three_two_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeELayerPrefixMap m (2 : Shared.TorusColor 3) 3 w =
      routeEPrefix3TwoModel m w := by
  simp only [routeELayerPrefixMap]
  rw [show ((0 : Nat) : ZMod m) = (0 : ZMod m) by norm_num]
  rw [show ((1 : Nat) : ZMod m) = (1 : ZMod m) by norm_num]
  rw [show ((2 : Nat) : ZMod m) = (2 : ZMod m) by norm_num]
  rw [routeELayerMap_color_two_of_layer_one
    (by omega : 2 <= m)
    (routeELayerMap m (0 : ZMod m) (2 : Shared.TorusColor 3) w)]
  rw [routeELayerMap_color_two_of_layer_two hm3]
  simp [routeEPrefix3TwoModel]

def routeEReturnZeroModel (m : Nat) (w : RootState m) : RootState m :=
  let u := routeEPrefix3ZeroModel m w
  (u.1 + ((m - 3 : Nat) : ZMod m), u.2)

def routeEReturnOneModel (m : Nat) (w : RootState m) : RootState m :=
  let u := routeEPrefix3OneModel m w
  (u.1, u.2 + ((m - 3 : Nat) : ZMod m))

def routeEReturnTwoModel (m : Nat) (w : RootState m) : RootState m :=
  routeEPrefix3TwoModel m w

/--
Finite-head rank coordinates for the three closed Route-E return models.
These tables close the first representative `m = 6, 8, 10, 12` moduli;
the remaining all-even proof still needs the symbolic rank/cycle lift.
-/
def routeEReturnZeroModelRank_m6 (w : RootState 6) : ZMod 36 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 36)
  | 0, 1 => (30 : ZMod 36)
  | 0, 2 => (24 : ZMod 36)
  | 0, 3 => (3 : ZMod 36)
  | 0, 4 => (19 : ZMod 36)
  | 0, 5 => (13 : ZMod 36)
  | 1, 0 => (21 : ZMod 36)
  | 1, 1 => (15 : ZMod 36)
  | 1, 2 => (9 : ZMod 36)
  | 1, 3 => (33 : ZMod 36)
  | 1, 4 => (27 : ZMod 36)
  | 1, 5 => (12 : ZMod 36)
  | 2, 0 => (29 : ZMod 36)
  | 2, 1 => (23 : ZMod 36)
  | 2, 2 => (2 : ZMod 36)
  | 2, 3 => (18 : ZMod 36)
  | 2, 4 => (26 : ZMod 36)
  | 2, 5 => (5 : ZMod 36)
  | 3, 0 => (14 : ZMod 36)
  | 3, 1 => (8 : ZMod 36)
  | 3, 2 => (32 : ZMod 36)
  | 3, 3 => (17 : ZMod 36)
  | 3, 4 => (11 : ZMod 36)
  | 3, 5 => (35 : ZMod 36)
  | 4, 0 => (22 : ZMod 36)
  | 4, 1 => (7 : ZMod 36)
  | 4, 2 => (1 : ZMod 36)
  | 4, 3 => (25 : ZMod 36)
  | 4, 4 => (4 : ZMod 36)
  | 4, 5 => (20 : ZMod 36)
  | 5, 0 => (6 : ZMod 36)
  | 5, 1 => (31 : ZMod 36)
  | 5, 2 => (16 : ZMod 36)
  | 5, 3 => (10 : ZMod 36)
  | 5, 4 => (34 : ZMod 36)
  | 5, 5 => (28 : ZMod 36)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m6_bijective :
    Function.Bijective routeEReturnZeroModelRank_m6 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m6_step :
    ∀ w : RootState 6,
      routeEReturnZeroModelRank_m6 (routeEReturnZeroModel 6 w) =
        routeEReturnZeroModelRank_m6 w + 1 := by
  decide

theorem routeEReturnZeroModel_singleCycle_m6 :
    Shared.IsSingleCycleMap (routeEReturnZeroModel 6) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnZeroModel 6)
    routeEReturnZeroModelRank_m6
    routeEReturnZeroModelRank_m6_bijective
    routeEReturnZeroModelRank_m6_step

def routeEReturnOneModelRank_m6 (w : RootState 6) : ZMod 36 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 36)
  | 0, 1 => (26 : ZMod 36)
  | 0, 2 => (5 : ZMod 36)
  | 0, 3 => (31 : ZMod 36)
  | 0, 4 => (21 : ZMod 36)
  | 0, 5 => (10 : ZMod 36)
  | 1, 0 => (16 : ZMod 36)
  | 1, 1 => (6 : ZMod 36)
  | 1, 2 => (32 : ZMod 36)
  | 1, 3 => (22 : ZMod 36)
  | 1, 4 => (11 : ZMod 36)
  | 1, 5 => (27 : ZMod 36)
  | 2, 0 => (33 : ZMod 36)
  | 2, 1 => (23 : ZMod 36)
  | 2, 2 => (12 : ZMod 36)
  | 2, 3 => (28 : ZMod 36)
  | 2, 4 => (1 : ZMod 36)
  | 2, 5 => (17 : ZMod 36)
  | 3, 0 => (13 : ZMod 36)
  | 3, 1 => (29 : ZMod 36)
  | 3, 2 => (2 : ZMod 36)
  | 3, 3 => (18 : ZMod 36)
  | 3, 4 => (34 : ZMod 36)
  | 3, 5 => (7 : ZMod 36)
  | 4, 0 => (3 : ZMod 36)
  | 4, 1 => (19 : ZMod 36)
  | 4, 2 => (35 : ZMod 36)
  | 4, 3 => (8 : ZMod 36)
  | 4, 4 => (14 : ZMod 36)
  | 4, 5 => (24 : ZMod 36)
  | 5, 0 => (20 : ZMod 36)
  | 5, 1 => (9 : ZMod 36)
  | 5, 2 => (15 : ZMod 36)
  | 5, 3 => (25 : ZMod 36)
  | 5, 4 => (4 : ZMod 36)
  | 5, 5 => (30 : ZMod 36)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m6_bijective :
    Function.Bijective routeEReturnOneModelRank_m6 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m6_step :
    ∀ w : RootState 6,
      routeEReturnOneModelRank_m6 (routeEReturnOneModel 6 w) =
        routeEReturnOneModelRank_m6 w + 1 := by
  decide

theorem routeEReturnOneModel_singleCycle_m6 :
    Shared.IsSingleCycleMap (routeEReturnOneModel 6) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnOneModel 6)
    routeEReturnOneModelRank_m6
    routeEReturnOneModelRank_m6_bijective
    routeEReturnOneModelRank_m6_step

def routeEReturnTwoModelRank_m6 (w : RootState 6) : ZMod 36 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 36)
  | 0, 1 => (14 : ZMod 36)
  | 0, 2 => (15 : ZMod 36)
  | 0, 3 => (9 : ZMod 36)
  | 0, 4 => (29 : ZMod 36)
  | 0, 5 => (23 : ZMod 36)
  | 1, 0 => (1 : ZMod 36)
  | 1, 1 => (31 : ZMod 36)
  | 1, 2 => (32 : ZMod 36)
  | 1, 3 => (16 : ZMod 36)
  | 1, 4 => (10 : ZMod 36)
  | 1, 5 => (30 : ZMod 36)
  | 2, 0 => (24 : ZMod 36)
  | 2, 1 => (2 : ZMod 36)
  | 2, 2 => (3 : ZMod 36)
  | 2, 3 => (33 : ZMod 36)
  | 2, 4 => (17 : ZMod 36)
  | 2, 5 => (11 : ZMod 36)
  | 3, 0 => (18 : ZMod 36)
  | 3, 1 => (25 : ZMod 36)
  | 3, 2 => (26 : ZMod 36)
  | 3, 3 => (4 : ZMod 36)
  | 3, 4 => (34 : ZMod 36)
  | 3, 5 => (5 : ZMod 36)
  | 4, 0 => (12 : ZMod 36)
  | 4, 1 => (19 : ZMod 36)
  | 4, 2 => (20 : ZMod 36)
  | 4, 3 => (27 : ZMod 36)
  | 4, 4 => (21 : ZMod 36)
  | 4, 5 => (35 : ZMod 36)
  | 5, 0 => (6 : ZMod 36)
  | 5, 1 => (13 : ZMod 36)
  | 5, 2 => (7 : ZMod 36)
  | 5, 3 => (8 : ZMod 36)
  | 5, 4 => (28 : ZMod 36)
  | 5, 5 => (22 : ZMod 36)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m6_bijective :
    Function.Bijective routeEReturnTwoModelRank_m6 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m6_step :
    ∀ w : RootState 6,
      routeEReturnTwoModelRank_m6 (routeEReturnTwoModel 6 w) =
        routeEReturnTwoModelRank_m6 w + 1 := by
  decide

theorem routeEReturnTwoModel_singleCycle_m6 :
    Shared.IsSingleCycleMap (routeEReturnTwoModel 6) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnTwoModel 6)
    routeEReturnTwoModelRank_m6
    routeEReturnTwoModelRank_m6_bijective
    routeEReturnTwoModelRank_m6_step

def routeEReturnZeroModelRank_m8 (w : RootState 8) : ZMod 64 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 64)
  | 0, 1 => (56 : ZMod 64)
  | 0, 2 => (48 : ZMod 64)
  | 0, 3 => (40 : ZMod 64)
  | 0, 4 => (4 : ZMod 64)
  | 0, 5 => (33 : ZMod 64)
  | 0, 6 => (25 : ZMod 64)
  | 0, 7 => (17 : ZMod 64)
  | 1, 0 => (36 : ZMod 64)
  | 1, 1 => (28 : ZMod 64)
  | 1, 2 => (20 : ZMod 64)
  | 1, 3 => (12 : ZMod 64)
  | 1, 4 => (60 : ZMod 64)
  | 1, 5 => (52 : ZMod 64)
  | 1, 6 => (44 : ZMod 64)
  | 1, 7 => (16 : ZMod 64)
  | 2, 0 => (55 : ZMod 64)
  | 2, 1 => (47 : ZMod 64)
  | 2, 2 => (39 : ZMod 64)
  | 2, 3 => (3 : ZMod 64)
  | 2, 4 => (32 : ZMod 64)
  | 2, 5 => (24 : ZMod 64)
  | 2, 6 => (43 : ZMod 64)
  | 2, 7 => (7 : ZMod 64)
  | 3, 0 => (27 : ZMod 64)
  | 3, 1 => (19 : ZMod 64)
  | 3, 2 => (11 : ZMod 64)
  | 3, 3 => (59 : ZMod 64)
  | 3, 4 => (51 : ZMod 64)
  | 3, 5 => (23 : ZMod 64)
  | 3, 6 => (15 : ZMod 64)
  | 3, 7 => (63 : ZMod 64)
  | 4, 0 => (46 : ZMod 64)
  | 4, 1 => (38 : ZMod 64)
  | 4, 2 => (2 : ZMod 64)
  | 4, 3 => (31 : ZMod 64)
  | 4, 4 => (50 : ZMod 64)
  | 4, 5 => (42 : ZMod 64)
  | 4, 6 => (6 : ZMod 64)
  | 4, 7 => (35 : ZMod 64)
  | 5, 0 => (18 : ZMod 64)
  | 5, 1 => (10 : ZMod 64)
  | 5, 2 => (58 : ZMod 64)
  | 5, 3 => (30 : ZMod 64)
  | 5, 4 => (22 : ZMod 64)
  | 5, 5 => (14 : ZMod 64)
  | 5, 6 => (62 : ZMod 64)
  | 5, 7 => (54 : ZMod 64)
  | 6, 0 => (37 : ZMod 64)
  | 6, 1 => (9 : ZMod 64)
  | 6, 2 => (1 : ZMod 64)
  | 6, 3 => (49 : ZMod 64)
  | 6, 4 => (41 : ZMod 64)
  | 6, 5 => (5 : ZMod 64)
  | 6, 6 => (34 : ZMod 64)
  | 6, 7 => (26 : ZMod 64)
  | 7, 0 => (8 : ZMod 64)
  | 7, 1 => (57 : ZMod 64)
  | 7, 2 => (29 : ZMod 64)
  | 7, 3 => (21 : ZMod 64)
  | 7, 4 => (13 : ZMod 64)
  | 7, 5 => (61 : ZMod 64)
  | 7, 6 => (53 : ZMod 64)
  | 7, 7 => (45 : ZMod 64)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m8_bijective :
    Function.Bijective routeEReturnZeroModelRank_m8 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m8_step :
    ∀ w : RootState 8,
      routeEReturnZeroModelRank_m8 (routeEReturnZeroModel 8 w) =
        routeEReturnZeroModelRank_m8 w + 1 := by
  decide

theorem routeEReturnZeroModel_singleCycle_m8 :
    Shared.IsSingleCycleMap (routeEReturnZeroModel 8) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnZeroModel 8)
    routeEReturnZeroModelRank_m8
    routeEReturnZeroModelRank_m8_bijective
    routeEReturnZeroModelRank_m8_step

def routeEReturnOneModelRank_m8 (w : RootState 8) : ZMod 64 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 64)
  | 0, 1 => (21 : ZMod 64)
  | 0, 2 => (7 : ZMod 64)
  | 0, 3 => (28 : ZMod 64)
  | 0, 4 => (36 : ZMod 64)
  | 0, 5 => (57 : ZMod 64)
  | 0, 6 => (14 : ZMod 64)
  | 0, 7 => (43 : ZMod 64)
  | 1, 0 => (51 : ZMod 64)
  | 1, 1 => (8 : ZMod 64)
  | 1, 2 => (29 : ZMod 64)
  | 1, 3 => (37 : ZMod 64)
  | 1, 4 => (58 : ZMod 64)
  | 1, 5 => (15 : ZMod 64)
  | 1, 6 => (44 : ZMod 64)
  | 1, 7 => (22 : ZMod 64)
  | 2, 0 => (30 : ZMod 64)
  | 2, 1 => (38 : ZMod 64)
  | 2, 2 => (59 : ZMod 64)
  | 2, 3 => (16 : ZMod 64)
  | 2, 4 => (45 : ZMod 64)
  | 2, 5 => (23 : ZMod 64)
  | 2, 6 => (1 : ZMod 64)
  | 2, 7 => (52 : ZMod 64)
  | 3, 0 => (60 : ZMod 64)
  | 3, 1 => (17 : ZMod 64)
  | 3, 2 => (46 : ZMod 64)
  | 3, 3 => (24 : ZMod 64)
  | 3, 4 => (2 : ZMod 64)
  | 3, 5 => (53 : ZMod 64)
  | 3, 6 => (31 : ZMod 64)
  | 3, 7 => (9 : ZMod 64)
  | 4, 0 => (47 : ZMod 64)
  | 4, 1 => (25 : ZMod 64)
  | 4, 2 => (3 : ZMod 64)
  | 4, 3 => (54 : ZMod 64)
  | 4, 4 => (32 : ZMod 64)
  | 4, 5 => (10 : ZMod 64)
  | 4, 6 => (61 : ZMod 64)
  | 4, 7 => (39 : ZMod 64)
  | 5, 0 => (4 : ZMod 64)
  | 5, 1 => (55 : ZMod 64)
  | 5, 2 => (33 : ZMod 64)
  | 5, 3 => (11 : ZMod 64)
  | 5, 4 => (62 : ZMod 64)
  | 5, 5 => (40 : ZMod 64)
  | 5, 6 => (48 : ZMod 64)
  | 5, 7 => (18 : ZMod 64)
  | 6, 0 => (34 : ZMod 64)
  | 6, 1 => (12 : ZMod 64)
  | 6, 2 => (63 : ZMod 64)
  | 6, 3 => (41 : ZMod 64)
  | 6, 4 => (49 : ZMod 64)
  | 6, 5 => (19 : ZMod 64)
  | 6, 6 => (5 : ZMod 64)
  | 6, 7 => (26 : ZMod 64)
  | 7, 0 => (13 : ZMod 64)
  | 7, 1 => (42 : ZMod 64)
  | 7, 2 => (50 : ZMod 64)
  | 7, 3 => (20 : ZMod 64)
  | 7, 4 => (6 : ZMod 64)
  | 7, 5 => (27 : ZMod 64)
  | 7, 6 => (35 : ZMod 64)
  | 7, 7 => (56 : ZMod 64)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m8_bijective :
    Function.Bijective routeEReturnOneModelRank_m8 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m8_step :
    ∀ w : RootState 8,
      routeEReturnOneModelRank_m8 (routeEReturnOneModel 8 w) =
        routeEReturnOneModelRank_m8 w + 1 := by
  decide

theorem routeEReturnOneModel_singleCycle_m8 :
    Shared.IsSingleCycleMap (routeEReturnOneModel 8) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnOneModel 8)
    routeEReturnOneModelRank_m8
    routeEReturnOneModelRank_m8_bijective
    routeEReturnOneModelRank_m8_step

def routeEReturnTwoModelRank_m8 (w : RootState 8) : ZMod 64 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 64)
  | 0, 1 => (18 : ZMod 64)
  | 0, 2 => (19 : ZMod 64)
  | 0, 3 => (11 : ZMod 64)
  | 0, 4 => (37 : ZMod 64)
  | 0, 5 => (29 : ZMod 64)
  | 0, 6 => (55 : ZMod 64)
  | 0, 7 => (47 : ZMod 64)
  | 1, 0 => (1 : ZMod 64)
  | 1, 1 => (57 : ZMod 64)
  | 1, 2 => (58 : ZMod 64)
  | 1, 3 => (20 : ZMod 64)
  | 1, 4 => (12 : ZMod 64)
  | 1, 5 => (38 : ZMod 64)
  | 1, 6 => (30 : ZMod 64)
  | 1, 7 => (56 : ZMod 64)
  | 2, 0 => (48 : ZMod 64)
  | 2, 1 => (2 : ZMod 64)
  | 2, 2 => (3 : ZMod 64)
  | 2, 3 => (59 : ZMod 64)
  | 2, 4 => (21 : ZMod 64)
  | 2, 5 => (13 : ZMod 64)
  | 2, 6 => (39 : ZMod 64)
  | 2, 7 => (31 : ZMod 64)
  | 3, 0 => (40 : ZMod 64)
  | 3, 1 => (49 : ZMod 64)
  | 3, 2 => (50 : ZMod 64)
  | 3, 3 => (4 : ZMod 64)
  | 3, 4 => (60 : ZMod 64)
  | 3, 5 => (22 : ZMod 64)
  | 3, 6 => (14 : ZMod 64)
  | 3, 7 => (23 : ZMod 64)
  | 4, 0 => (32 : ZMod 64)
  | 4, 1 => (41 : ZMod 64)
  | 4, 2 => (42 : ZMod 64)
  | 4, 3 => (51 : ZMod 64)
  | 4, 4 => (5 : ZMod 64)
  | 4, 5 => (61 : ZMod 64)
  | 4, 6 => (6 : ZMod 64)
  | 4, 7 => (15 : ZMod 64)
  | 5, 0 => (24 : ZMod 64)
  | 5, 1 => (33 : ZMod 64)
  | 5, 2 => (34 : ZMod 64)
  | 5, 3 => (43 : ZMod 64)
  | 5, 4 => (52 : ZMod 64)
  | 5, 5 => (44 : ZMod 64)
  | 5, 6 => (62 : ZMod 64)
  | 5, 7 => (7 : ZMod 64)
  | 6, 0 => (16 : ZMod 64)
  | 6, 1 => (25 : ZMod 64)
  | 6, 2 => (26 : ZMod 64)
  | 6, 3 => (35 : ZMod 64)
  | 6, 4 => (27 : ZMod 64)
  | 6, 5 => (53 : ZMod 64)
  | 6, 6 => (45 : ZMod 64)
  | 6, 7 => (63 : ZMod 64)
  | 7, 0 => (8 : ZMod 64)
  | 7, 1 => (17 : ZMod 64)
  | 7, 2 => (9 : ZMod 64)
  | 7, 3 => (10 : ZMod 64)
  | 7, 4 => (36 : ZMod 64)
  | 7, 5 => (28 : ZMod 64)
  | 7, 6 => (54 : ZMod 64)
  | 7, 7 => (46 : ZMod 64)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m8_bijective :
    Function.Bijective routeEReturnTwoModelRank_m8 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m8_step :
    ∀ w : RootState 8,
      routeEReturnTwoModelRank_m8 (routeEReturnTwoModel 8 w) =
        routeEReturnTwoModelRank_m8 w + 1 := by
  decide

theorem routeEReturnTwoModel_singleCycle_m8 :
    Shared.IsSingleCycleMap (routeEReturnTwoModel 8) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnTwoModel 8)
    routeEReturnTwoModelRank_m8
    routeEReturnTwoModelRank_m8_bijective
    routeEReturnTwoModelRank_m8_step

def routeEReturnZeroModelRank_m10 (w : RootState 10) : ZMod 100 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 100)
  | 0, 1 => (25 : ZMod 100)
  | 0, 2 => (90 : ZMod 100)
  | 0, 3 => (40 : ZMod 100)
  | 0, 4 => (80 : ZMod 100)
  | 0, 5 => (5 : ZMod 100)
  | 0, 6 => (71 : ZMod 100)
  | 0, 7 => (20 : ZMod 100)
  | 0, 8 => (61 : ZMod 100)
  | 0, 9 => (10 : ZMod 100)
  | 1, 0 => (75 : ZMod 100)
  | 1, 1 => (24 : ZMod 100)
  | 1, 2 => (65 : ZMod 100)
  | 1, 3 => (14 : ZMod 100)
  | 1, 4 => (55 : ZMod 100)
  | 1, 5 => (30 : ZMod 100)
  | 1, 6 => (95 : ZMod 100)
  | 1, 7 => (45 : ZMod 100)
  | 1, 8 => (85 : ZMod 100)
  | 1, 9 => (35 : ZMod 100)
  | 2, 0 => (49 : ZMod 100)
  | 2, 1 => (89 : ZMod 100)
  | 2, 2 => (39 : ZMod 100)
  | 2, 3 => (79 : ZMod 100)
  | 2, 4 => (4 : ZMod 100)
  | 2, 5 => (70 : ZMod 100)
  | 2, 6 => (19 : ZMod 100)
  | 2, 7 => (60 : ZMod 100)
  | 2, 8 => (84 : ZMod 100)
  | 2, 9 => (9 : ZMod 100)
  | 3, 0 => (23 : ZMod 100)
  | 3, 1 => (64 : ZMod 100)
  | 3, 2 => (13 : ZMod 100)
  | 3, 3 => (54 : ZMod 100)
  | 3, 4 => (29 : ZMod 100)
  | 3, 5 => (94 : ZMod 100)
  | 3, 6 => (44 : ZMod 100)
  | 3, 7 => (59 : ZMod 100)
  | 3, 8 => (34 : ZMod 100)
  | 3, 9 => (99 : ZMod 100)
  | 4, 0 => (88 : ZMod 100)
  | 4, 1 => (38 : ZMod 100)
  | 4, 2 => (78 : ZMod 100)
  | 4, 3 => (3 : ZMod 100)
  | 4, 4 => (69 : ZMod 100)
  | 4, 5 => (18 : ZMod 100)
  | 4, 6 => (43 : ZMod 100)
  | 4, 7 => (83 : ZMod 100)
  | 4, 8 => (8 : ZMod 100)
  | 4, 9 => (74 : ZMod 100)
  | 5, 0 => (63 : ZMod 100)
  | 5, 1 => (12 : ZMod 100)
  | 5, 2 => (53 : ZMod 100)
  | 5, 3 => (28 : ZMod 100)
  | 5, 4 => (93 : ZMod 100)
  | 5, 5 => (17 : ZMod 100)
  | 5, 6 => (58 : ZMod 100)
  | 5, 7 => (33 : ZMod 100)
  | 5, 8 => (98 : ZMod 100)
  | 5, 9 => (48 : ZMod 100)
  | 6, 0 => (37 : ZMod 100)
  | 6, 1 => (77 : ZMod 100)
  | 6, 2 => (2 : ZMod 100)
  | 6, 3 => (68 : ZMod 100)
  | 6, 4 => (92 : ZMod 100)
  | 6, 5 => (42 : ZMod 100)
  | 6, 6 => (82 : ZMod 100)
  | 6, 7 => (7 : ZMod 100)
  | 6, 8 => (73 : ZMod 100)
  | 6, 9 => (22 : ZMod 100)
  | 7, 0 => (11 : ZMod 100)
  | 7, 1 => (52 : ZMod 100)
  | 7, 2 => (27 : ZMod 100)
  | 7, 3 => (67 : ZMod 100)
  | 7, 4 => (16 : ZMod 100)
  | 7, 5 => (57 : ZMod 100)
  | 7, 6 => (32 : ZMod 100)
  | 7, 7 => (97 : ZMod 100)
  | 7, 8 => (47 : ZMod 100)
  | 7, 9 => (87 : ZMod 100)
  | 8, 0 => (76 : ZMod 100)
  | 8, 1 => (51 : ZMod 100)
  | 8, 2 => (1 : ZMod 100)
  | 8, 3 => (91 : ZMod 100)
  | 8, 4 => (41 : ZMod 100)
  | 8, 5 => (81 : ZMod 100)
  | 8, 6 => (6 : ZMod 100)
  | 8, 7 => (72 : ZMod 100)
  | 8, 8 => (21 : ZMod 100)
  | 8, 9 => (62 : ZMod 100)
  | 9, 0 => (50 : ZMod 100)
  | 9, 1 => (26 : ZMod 100)
  | 9, 2 => (66 : ZMod 100)
  | 9, 3 => (15 : ZMod 100)
  | 9, 4 => (56 : ZMod 100)
  | 9, 5 => (31 : ZMod 100)
  | 9, 6 => (96 : ZMod 100)
  | 9, 7 => (46 : ZMod 100)
  | 9, 8 => (86 : ZMod 100)
  | 9, 9 => (36 : ZMod 100)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m10_bijective :
    Function.Bijective routeEReturnZeroModelRank_m10 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnZeroModelRank_m10_step :
    ∀ w : RootState 10,
      routeEReturnZeroModelRank_m10 (routeEReturnZeroModel 10 w) =
        routeEReturnZeroModelRank_m10 w + 1 := by
  decide

theorem routeEReturnZeroModel_singleCycle_m10 :
    Shared.IsSingleCycleMap (routeEReturnZeroModel 10) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnZeroModel 10)
    routeEReturnZeroModelRank_m10
    routeEReturnZeroModelRank_m10_bijective
    routeEReturnZeroModelRank_m10_step

def routeEReturnOneModelRank_m10 (w : RootState 10) : ZMod 100 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 100)
  | 0, 1 => (27 : ZMod 100)
  | 0, 2 => (9 : ZMod 100)
  | 0, 3 => (53 : ZMod 100)
  | 0, 4 => (81 : ZMod 100)
  | 0, 5 => (35 : ZMod 100)
  | 0, 6 => (91 : ZMod 100)
  | 0, 7 => (18 : ZMod 100)
  | 0, 8 => (62 : ZMod 100)
  | 0, 9 => (44 : ZMod 100)
  | 1, 0 => (72 : ZMod 100)
  | 1, 1 => (10 : ZMod 100)
  | 1, 2 => (54 : ZMod 100)
  | 1, 3 => (82 : ZMod 100)
  | 1, 4 => (36 : ZMod 100)
  | 1, 5 => (92 : ZMod 100)
  | 1, 6 => (19 : ZMod 100)
  | 1, 7 => (63 : ZMod 100)
  | 1, 8 => (45 : ZMod 100)
  | 1, 9 => (28 : ZMod 100)
  | 2, 0 => (11 : ZMod 100)
  | 2, 1 => (55 : ZMod 100)
  | 2, 2 => (83 : ZMod 100)
  | 2, 3 => (37 : ZMod 100)
  | 2, 4 => (93 : ZMod 100)
  | 2, 5 => (20 : ZMod 100)
  | 2, 6 => (64 : ZMod 100)
  | 2, 7 => (46 : ZMod 100)
  | 2, 8 => (1 : ZMod 100)
  | 2, 9 => (73 : ZMod 100)
  | 3, 0 => (84 : ZMod 100)
  | 3, 1 => (38 : ZMod 100)
  | 3, 2 => (94 : ZMod 100)
  | 3, 3 => (21 : ZMod 100)
  | 3, 4 => (65 : ZMod 100)
  | 3, 5 => (47 : ZMod 100)
  | 3, 6 => (2 : ZMod 100)
  | 3, 7 => (29 : ZMod 100)
  | 3, 8 => (74 : ZMod 100)
  | 3, 9 => (12 : ZMod 100)
  | 4, 0 => (95 : ZMod 100)
  | 4, 1 => (22 : ZMod 100)
  | 4, 2 => (66 : ZMod 100)
  | 4, 3 => (48 : ZMod 100)
  | 4, 4 => (3 : ZMod 100)
  | 4, 5 => (30 : ZMod 100)
  | 4, 6 => (75 : ZMod 100)
  | 4, 7 => (13 : ZMod 100)
  | 4, 8 => (85 : ZMod 100)
  | 4, 9 => (56 : ZMod 100)
  | 5, 0 => (67 : ZMod 100)
  | 5, 1 => (49 : ZMod 100)
  | 5, 2 => (4 : ZMod 100)
  | 5, 3 => (31 : ZMod 100)
  | 5, 4 => (76 : ZMod 100)
  | 5, 5 => (14 : ZMod 100)
  | 5, 6 => (86 : ZMod 100)
  | 5, 7 => (57 : ZMod 100)
  | 5, 8 => (96 : ZMod 100)
  | 5, 9 => (39 : ZMod 100)
  | 6, 0 => (5 : ZMod 100)
  | 6, 1 => (32 : ZMod 100)
  | 6, 2 => (77 : ZMod 100)
  | 6, 3 => (15 : ZMod 100)
  | 6, 4 => (87 : ZMod 100)
  | 6, 5 => (58 : ZMod 100)
  | 6, 6 => (97 : ZMod 100)
  | 6, 7 => (40 : ZMod 100)
  | 6, 8 => (68 : ZMod 100)
  | 6, 9 => (23 : ZMod 100)
  | 7, 0 => (78 : ZMod 100)
  | 7, 1 => (16 : ZMod 100)
  | 7, 2 => (88 : ZMod 100)
  | 7, 3 => (59 : ZMod 100)
  | 7, 4 => (98 : ZMod 100)
  | 7, 5 => (41 : ZMod 100)
  | 7, 6 => (69 : ZMod 100)
  | 7, 7 => (24 : ZMod 100)
  | 7, 8 => (6 : ZMod 100)
  | 7, 9 => (50 : ZMod 100)
  | 8, 0 => (89 : ZMod 100)
  | 8, 1 => (60 : ZMod 100)
  | 8, 2 => (99 : ZMod 100)
  | 8, 3 => (42 : ZMod 100)
  | 8, 4 => (70 : ZMod 100)
  | 8, 5 => (25 : ZMod 100)
  | 8, 6 => (7 : ZMod 100)
  | 8, 7 => (51 : ZMod 100)
  | 8, 8 => (79 : ZMod 100)
  | 8, 9 => (33 : ZMod 100)
  | 9, 0 => (61 : ZMod 100)
  | 9, 1 => (43 : ZMod 100)
  | 9, 2 => (71 : ZMod 100)
  | 9, 3 => (26 : ZMod 100)
  | 9, 4 => (8 : ZMod 100)
  | 9, 5 => (52 : ZMod 100)
  | 9, 6 => (80 : ZMod 100)
  | 9, 7 => (34 : ZMod 100)
  | 9, 8 => (90 : ZMod 100)
  | 9, 9 => (17 : ZMod 100)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m10_bijective :
    Function.Bijective routeEReturnOneModelRank_m10 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnOneModelRank_m10_step :
    ∀ w : RootState 10,
      routeEReturnOneModelRank_m10 (routeEReturnOneModel 10 w) =
        routeEReturnOneModelRank_m10 w + 1 := by
  decide

theorem routeEReturnOneModel_singleCycle_m10 :
    Shared.IsSingleCycleMap (routeEReturnOneModel 10) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnOneModel 10)
    routeEReturnOneModelRank_m10
    routeEReturnOneModelRank_m10_bijective
    routeEReturnOneModelRank_m10_step

def routeEReturnTwoModelRank_m10 (w : RootState 10) : ZMod 100 :=
  match w.1.val, w.2.val with
  | 0, 0 => (0 : ZMod 100)
  | 0, 1 => (22 : ZMod 100)
  | 0, 2 => (23 : ZMod 100)
  | 0, 3 => (13 : ZMod 100)
  | 0, 4 => (45 : ZMod 100)
  | 0, 5 => (35 : ZMod 100)
  | 0, 6 => (67 : ZMod 100)
  | 0, 7 => (57 : ZMod 100)
  | 0, 8 => (89 : ZMod 100)
  | 0, 9 => (79 : ZMod 100)
  | 1, 0 => (1 : ZMod 100)
  | 1, 1 => (91 : ZMod 100)
  | 1, 2 => (92 : ZMod 100)
  | 1, 3 => (24 : ZMod 100)
  | 1, 4 => (14 : ZMod 100)
  | 1, 5 => (46 : ZMod 100)
  | 1, 6 => (36 : ZMod 100)
  | 1, 7 => (68 : ZMod 100)
  | 1, 8 => (58 : ZMod 100)
  | 1, 9 => (90 : ZMod 100)
  | 2, 0 => (80 : ZMod 100)
  | 2, 1 => (2 : ZMod 100)
  | 2, 2 => (3 : ZMod 100)
  | 2, 3 => (93 : ZMod 100)
  | 2, 4 => (25 : ZMod 100)
  | 2, 5 => (15 : ZMod 100)
  | 2, 6 => (47 : ZMod 100)
  | 2, 7 => (37 : ZMod 100)
  | 2, 8 => (69 : ZMod 100)
  | 2, 9 => (59 : ZMod 100)
  | 3, 0 => (70 : ZMod 100)
  | 3, 1 => (81 : ZMod 100)
  | 3, 2 => (82 : ZMod 100)
  | 3, 3 => (4 : ZMod 100)
  | 3, 4 => (94 : ZMod 100)
  | 3, 5 => (26 : ZMod 100)
  | 3, 6 => (16 : ZMod 100)
  | 3, 7 => (48 : ZMod 100)
  | 3, 8 => (38 : ZMod 100)
  | 3, 9 => (49 : ZMod 100)
  | 4, 0 => (60 : ZMod 100)
  | 4, 1 => (71 : ZMod 100)
  | 4, 2 => (72 : ZMod 100)
  | 4, 3 => (83 : ZMod 100)
  | 4, 4 => (5 : ZMod 100)
  | 4, 5 => (95 : ZMod 100)
  | 4, 6 => (27 : ZMod 100)
  | 4, 7 => (17 : ZMod 100)
  | 4, 8 => (28 : ZMod 100)
  | 4, 9 => (39 : ZMod 100)
  | 5, 0 => (50 : ZMod 100)
  | 5, 1 => (61 : ZMod 100)
  | 5, 2 => (62 : ZMod 100)
  | 5, 3 => (73 : ZMod 100)
  | 5, 4 => (84 : ZMod 100)
  | 5, 5 => (6 : ZMod 100)
  | 5, 6 => (96 : ZMod 100)
  | 5, 7 => (7 : ZMod 100)
  | 5, 8 => (18 : ZMod 100)
  | 5, 9 => (29 : ZMod 100)
  | 6, 0 => (40 : ZMod 100)
  | 6, 1 => (51 : ZMod 100)
  | 6, 2 => (52 : ZMod 100)
  | 6, 3 => (63 : ZMod 100)
  | 6, 4 => (74 : ZMod 100)
  | 6, 5 => (85 : ZMod 100)
  | 6, 6 => (75 : ZMod 100)
  | 6, 7 => (97 : ZMod 100)
  | 6, 8 => (8 : ZMod 100)
  | 6, 9 => (19 : ZMod 100)
  | 7, 0 => (30 : ZMod 100)
  | 7, 1 => (41 : ZMod 100)
  | 7, 2 => (42 : ZMod 100)
  | 7, 3 => (53 : ZMod 100)
  | 7, 4 => (64 : ZMod 100)
  | 7, 5 => (54 : ZMod 100)
  | 7, 6 => (86 : ZMod 100)
  | 7, 7 => (76 : ZMod 100)
  | 7, 8 => (98 : ZMod 100)
  | 7, 9 => (9 : ZMod 100)
  | 8, 0 => (20 : ZMod 100)
  | 8, 1 => (31 : ZMod 100)
  | 8, 2 => (32 : ZMod 100)
  | 8, 3 => (43 : ZMod 100)
  | 8, 4 => (33 : ZMod 100)
  | 8, 5 => (65 : ZMod 100)
  | 8, 6 => (55 : ZMod 100)
  | 8, 7 => (87 : ZMod 100)
  | 8, 8 => (77 : ZMod 100)
  | 8, 9 => (99 : ZMod 100)
  | 9, 0 => (10 : ZMod 100)
  | 9, 1 => (21 : ZMod 100)
  | 9, 2 => (11 : ZMod 100)
  | 9, 3 => (12 : ZMod 100)
  | 9, 4 => (44 : ZMod 100)
  | 9, 5 => (34 : ZMod 100)
  | 9, 6 => (66 : ZMod 100)
  | 9, 7 => (56 : ZMod 100)
  | 9, 8 => (88 : ZMod 100)
  | 9, 9 => (78 : ZMod 100)
  | _, _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m10_bijective :
    Function.Bijective routeEReturnTwoModelRank_m10 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Generated finite rank-table checks expand over up to 100 root states.
theorem routeEReturnTwoModelRank_m10_step :
    ∀ w : RootState 10,
      routeEReturnTwoModelRank_m10 (routeEReturnTwoModel 10 w) =
        routeEReturnTwoModelRank_m10 w + 1 := by
  decide

theorem routeEReturnTwoModel_singleCycle_m10 :
    Shared.IsSingleCycleMap (routeEReturnTwoModel 10) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnTwoModel 10)
    routeEReturnTwoModelRank_m10
    routeEReturnTwoModelRank_m10_bijective
    routeEReturnTwoModelRank_m10_step

def routeEReturnModelRankSearch_m12
    (step : RootState 12 -> RootState 12) :
    Nat -> Nat -> RootState 12 -> RootState 12 -> ZMod 144
  | 0, _k, _cur, _w => 0
  | n + 1, k, cur, w =>
      if w = cur then (k : ZMod 144)
      else routeEReturnModelRankSearch_m12 step n (k + 1) (step cur) w

def routeEReturnZeroModelRank_m12 (w : RootState 12) : ZMod 144 :=
  routeEReturnModelRankSearch_m12
    (routeEReturnZeroModel 12) 144 0 ((0 : ZMod 12), (0 : ZMod 12)) w

def routeEReturnOneModelRank_m12 (w : RootState 12) : ZMod 144 :=
  routeEReturnModelRankSearch_m12
    (routeEReturnOneModel 12) 144 0 ((0 : ZMod 12), (0 : ZMod 12)) w

def routeEReturnTwoModelRank_m12 (w : RootState 12) : ZMod 144 :=
  routeEReturnModelRankSearch_m12
    (routeEReturnTwoModel 12) 144 0 ((0 : ZMod 12), (0 : ZMod 12)) w

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnZeroModelRank_m12_bijective :
    Function.Bijective routeEReturnZeroModelRank_m12 := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnZeroModelRank_m12_step :
    ∀ w : RootState 12,
      routeEReturnZeroModelRank_m12 (routeEReturnZeroModel 12 w) =
        routeEReturnZeroModelRank_m12 w + 1 := by
  decide

theorem routeEReturnZeroModel_singleCycle_m12 :
    Shared.IsSingleCycleMap (routeEReturnZeroModel 12) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnZeroModel 12)
    routeEReturnZeroModelRank_m12
    routeEReturnZeroModelRank_m12_bijective
    routeEReturnZeroModelRank_m12_step

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnOneModelRank_m12_bijective :
    Function.Bijective routeEReturnOneModelRank_m12 := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnOneModelRank_m12_step :
    ∀ w : RootState 12,
      routeEReturnOneModelRank_m12 (routeEReturnOneModel 12 w) =
        routeEReturnOneModelRank_m12 w + 1 := by
  decide

theorem routeEReturnOneModel_singleCycle_m12 :
    Shared.IsSingleCycleMap (routeEReturnOneModel 12) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnOneModel 12)
    routeEReturnOneModelRank_m12
    routeEReturnOneModelRank_m12_bijective
    routeEReturnOneModelRank_m12_step

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnTwoModelRank_m12_bijective :
    Function.Bijective routeEReturnTwoModelRank_m12 := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- The orbit-search rank check expands over the 12x12 root-state space.
theorem routeEReturnTwoModelRank_m12_step :
    ∀ w : RootState 12,
      routeEReturnTwoModelRank_m12 (routeEReturnTwoModel 12 w) =
        routeEReturnTwoModelRank_m12 w + 1 := by
  decide

theorem routeEReturnTwoModel_singleCycle_m12 :
    Shared.IsSingleCycleMap (routeEReturnTwoModel 12) :=
  Shared.single_cycle_of_zmod_rank (routeEReturnTwoModel 12)
    routeEReturnTwoModelRank_m12
    routeEReturnTwoModelRank_m12_bijective
    routeEReturnTwoModelRank_m12_step


theorem routeELayerPrefixMap_tail_zero
    {m : Nat} [NeZero m] :
    ∀ k : Nat, ∀ (_hkm : k + 3 <= m) (w : RootState m),
      routeELayerPrefixMap m (0 : Shared.TorusColor 3) (k + 3) w =
        let u := routeELayerPrefixMap m (0 : Shared.TorusColor 3) 3 w
        (u.1 + (k : ZMod m), u.2)
  | 0, _hkm, w => by
      simp [routeELayerPrefixMap]
  | k + 1, _hkm, w => by
      have hkprev : k + 3 <= m := by omega
      have hklt : k + 3 < m := by omega
      have hval : ((k + 3 : Nat) : ZMod m).val = k + 3 := by
        exact ZMod.val_natCast_of_lt (n := m) (a := k + 3) hklt
      rw [show k + 1 + 3 = (k + 3) + 1 by omega]
      change
        routeELayerMap m ((k + 3 : Nat) : ZMod m)
            (0 : Shared.TorusColor 3)
            (routeELayerPrefixMap m (0 : Shared.TorusColor 3) (k + 3) w) =
          let u := routeELayerPrefixMap m (0 : Shared.TorusColor 3) 3 w
          (u.1 + ((k + 1 : Nat) : ZMod m), u.2)
      rw [routeELayerPrefixMap_tail_zero k hkprev w]
      rw [routeELayerMap_zero_of_layer_val_ne_zero_one_two]
      · simp [Nat.cast_add]
        ring
      · rw [hval]
        omega
      · rw [hval]
        omega
      · rw [hval]
        omega

theorem routeELayerPrefixMap_tail_one
    {m : Nat} [NeZero m] :
    ∀ k : Nat, ∀ (_hkm : k + 3 <= m) (w : RootState m),
      routeELayerPrefixMap m (1 : Shared.TorusColor 3) (k + 3) w =
        let u := routeELayerPrefixMap m (1 : Shared.TorusColor 3) 3 w
        (u.1, u.2 + (k : ZMod m))
  | 0, _hkm, w => by
      simp [routeELayerPrefixMap]
  | k + 1, _hkm, w => by
      have hkprev : k + 3 <= m := by omega
      have hklt : k + 3 < m := by omega
      have hval : ((k + 3 : Nat) : ZMod m).val = k + 3 := by
        exact ZMod.val_natCast_of_lt (n := m) (a := k + 3) hklt
      rw [show k + 1 + 3 = (k + 3) + 1 by omega]
      change
        routeELayerMap m ((k + 3 : Nat) : ZMod m)
            (1 : Shared.TorusColor 3)
            (routeELayerPrefixMap m (1 : Shared.TorusColor 3) (k + 3) w) =
          let u := routeELayerPrefixMap m (1 : Shared.TorusColor 3) 3 w
          (u.1, u.2 + ((k + 1 : Nat) : ZMod m))
      rw [routeELayerPrefixMap_tail_one k hkprev w]
      rw [routeELayerMap_one_of_layer_val_ne_zero_one_two]
      · simp [Nat.cast_add]
        ring
      · rw [hval]
        omega
      · rw [hval]
        omega
      · rw [hval]
        omega

theorem routeELayerPrefixMap_tail_two
    {m : Nat} [NeZero m] :
    ∀ k : Nat, ∀ (_hkm : k + 3 <= m) (w : RootState m),
      routeELayerPrefixMap m (2 : Shared.TorusColor 3) (k + 3) w =
        routeELayerPrefixMap m (2 : Shared.TorusColor 3) 3 w
  | 0, _hkm, w => by
      simp [routeELayerPrefixMap]
  | k + 1, _hkm, w => by
      have hkprev : k + 3 <= m := by omega
      have hklt : k + 3 < m := by omega
      have hval : ((k + 3 : Nat) : ZMod m).val = k + 3 := by
        exact ZMod.val_natCast_of_lt (n := m) (a := k + 3) hklt
      rw [show k + 1 + 3 = (k + 3) + 1 by omega]
      change
        routeELayerMap m ((k + 3 : Nat) : ZMod m)
            (2 : Shared.TorusColor 3)
            (routeELayerPrefixMap m (2 : Shared.TorusColor 3) (k + 3) w) =
          routeELayerPrefixMap m (2 : Shared.TorusColor 3) 3 w
      rw [routeELayerPrefixMap_tail_two k hkprev w]
      rw [routeELayerMap_two_of_layer_val_ne_zero_one_two]
      · rw [hval]
        omega
      · rw [hval]
        omega
      · rw [hval]
        omega

theorem routeEReturnMap_zero_eq_tail
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (0 : Shared.TorusColor 3) w =
      let u := routeELayerPrefixMap m (0 : Shared.TorusColor 3) 3 w
      (u.1 + ((m - 3 : Nat) : ZMod m), u.2) := by
  have hsum : (m - 3) + 3 = m := by omega
  simpa [routeEReturnMap, hsum] using
    routeELayerPrefixMap_tail_zero (m := m) (m - 3) (by omega) w

theorem routeEReturnMap_zero_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (0 : Shared.TorusColor 3) w =
      routeEReturnZeroModel m w := by
  rw [routeEReturnMap_zero_eq_tail hm3 w]
  rw [routeELayerPrefixMap_three_zero_eq_model hm3 w]
  rfl

theorem routeEReturnMap_one_eq_tail
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (1 : Shared.TorusColor 3) w =
      let u := routeELayerPrefixMap m (1 : Shared.TorusColor 3) 3 w
      (u.1, u.2 + ((m - 3 : Nat) : ZMod m)) := by
  have hsum : (m - 3) + 3 = m := by omega
  simpa [routeEReturnMap, hsum] using
    routeELayerPrefixMap_tail_one (m := m) (m - 3) (by omega) w

theorem routeEReturnMap_one_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (1 : Shared.TorusColor 3) w =
      routeEReturnOneModel m w := by
  rw [routeEReturnMap_one_eq_tail hm3 w]
  rw [routeELayerPrefixMap_three_one_eq_model hm3 w]
  rfl

theorem routeEReturnMap_two_eq_tail
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (2 : Shared.TorusColor 3) w =
      routeELayerPrefixMap m (2 : Shared.TorusColor 3) 3 w := by
  have hsum : (m - 3) + 3 = m := by omega
  simpa [routeEReturnMap, hsum] using
    routeELayerPrefixMap_tail_two (m := m) (m - 3) (by omega) w

theorem routeEReturnMap_two_eq_model
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (w : RootState m) :
    routeEReturnMap m (2 : Shared.TorusColor 3) w =
      routeEReturnTwoModel m w := by
  rw [routeEReturnMap_two_eq_tail hm3 w]
  rw [routeELayerPrefixMap_three_two_eq_model hm3 w]
  rfl

theorem routeEReturnMap_singleCycle_of_models
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (hZero : Shared.IsSingleCycleMap (routeEReturnZeroModel m))
    (hOne : Shared.IsSingleCycleMap (routeEReturnOneModel m))
    (hTwo : Shared.IsSingleCycleMap (routeEReturnTwoModel m)) :
    ∀ c : Shared.TorusColor 3,
      Shared.IsSingleCycleMap (routeEReturnMap m c) := by
  intro c
  fin_cases c
  · convert hZero using 1
    funext w
    exact routeEReturnMap_zero_eq_model hm3 w
  · convert hOne using 1
    funext w
    exact routeEReturnMap_one_eq_model hm3 w
  · convert hTwo using 1
    funext w
    exact routeEReturnMap_two_eq_model hm3 w

theorem routeEReturnMap_singleCycle_m6
    (c : Shared.TorusColor 3) :
    Shared.IsSingleCycleMap (routeEReturnMap 6 c) :=
  routeEReturnMap_singleCycle_of_models
    (m := 6) (by norm_num)
    routeEReturnZeroModel_singleCycle_m6
    routeEReturnOneModel_singleCycle_m6
    routeEReturnTwoModel_singleCycle_m6 c

theorem routeEReturnMap_singleCycle_m8
    (c : Shared.TorusColor 3) :
    Shared.IsSingleCycleMap (routeEReturnMap 8 c) :=
  routeEReturnMap_singleCycle_of_models
    (m := 8) (by norm_num)
    routeEReturnZeroModel_singleCycle_m8
    routeEReturnOneModel_singleCycle_m8
    routeEReturnTwoModel_singleCycle_m8 c

theorem routeEReturnMap_singleCycle_m10
    (c : Shared.TorusColor 3) :
    Shared.IsSingleCycleMap (routeEReturnMap 10 c) :=
  routeEReturnMap_singleCycle_of_models
    (m := 10) (by norm_num)
    routeEReturnZeroModel_singleCycle_m10
    routeEReturnOneModel_singleCycle_m10
    routeEReturnTwoModel_singleCycle_m10 c

theorem routeEReturnMap_singleCycle_m12
    (c : Shared.TorusColor 3) :
    Shared.IsSingleCycleMap (routeEReturnMap 12 c) :=
  routeEReturnMap_singleCycle_of_models
    (m := 12) (by norm_num)
    routeEReturnZeroModel_singleCycle_m12
    routeEReturnOneModel_singleCycle_m12
    routeEReturnTwoModel_singleCycle_m12 c

theorem routeEReturnZeroModel_singleCycle_of_even_ge_six_tail
    {m : Nat} [NeZero m] (hm_even : Even m) (_hm6 : 6 <= m)
    (hTail :
      14 <= m -> Shared.IsSingleCycleMap (routeEReturnZeroModel m)) :
    Shared.IsSingleCycleMap (routeEReturnZeroModel m) := by
  by_cases h6eq : m = 6
  · subst m
    exact routeEReturnZeroModel_singleCycle_m6
  · by_cases h8eq : m = 8
    · subst m
      exact routeEReturnZeroModel_singleCycle_m8
    · by_cases h10eq : m = 10
      · subst m
        exact routeEReturnZeroModel_singleCycle_m10
      · by_cases h12eq : m = 12
        · subst m
          exact routeEReturnZeroModel_singleCycle_m12
        · exact hTail (by
            rcases hm_even with ⟨k, rfl⟩
            omega)

theorem routeEReturnOneModel_singleCycle_of_even_ge_six_tail
    {m : Nat} [NeZero m] (hm_even : Even m) (_hm6 : 6 <= m)
    (hTail :
      14 <= m -> Shared.IsSingleCycleMap (routeEReturnOneModel m)) :
    Shared.IsSingleCycleMap (routeEReturnOneModel m) := by
  by_cases h6eq : m = 6
  · subst m
    exact routeEReturnOneModel_singleCycle_m6
  · by_cases h8eq : m = 8
    · subst m
      exact routeEReturnOneModel_singleCycle_m8
    · by_cases h10eq : m = 10
      · subst m
        exact routeEReturnOneModel_singleCycle_m10
      · by_cases h12eq : m = 12
        · subst m
          exact routeEReturnOneModel_singleCycle_m12
        · exact hTail (by
            rcases hm_even with ⟨k, rfl⟩
            omega)

theorem routeEReturnTwoModel_singleCycle_of_even_ge_six_tail
    {m : Nat} [NeZero m] (hm_even : Even m) (_hm6 : 6 <= m)
    (hTail :
      14 <= m -> Shared.IsSingleCycleMap (routeEReturnTwoModel m)) :
    Shared.IsSingleCycleMap (routeEReturnTwoModel m) := by
  by_cases h6eq : m = 6
  · subst m
    exact routeEReturnTwoModel_singleCycle_m6
  · by_cases h8eq : m = 8
    · subst m
      exact routeEReturnTwoModel_singleCycle_m8
    · by_cases h10eq : m = 10
      · subst m
        exact routeEReturnTwoModel_singleCycle_m10
      · by_cases h12eq : m = 12
        · subst m
          exact routeEReturnTwoModel_singleCycle_m12
        · exact hTail (by
            rcases hm_even with ⟨k, rfl⟩
            omega)

theorem cayleyColorStep_bijective_of_routeELayer
    (m : Nat) (c : Shared.TorusColor 3)
    (hLayer :
      ∀ t : ZMod m, Function.Bijective (routeELayerMap m t c)) :
    Function.Bijective (Shared.cayleyColorStep (colorDir m) c) := by
  let e := layerRootEquiv m
  have hFull : Function.Bijective (routeEFullStep m c) :=
    routeEFullStep_bijective m c hLayer
  constructor
  · intro x y hxy
    apply e.injective
    apply hFull.1
    simpa [e, layerRootEquiv_cayleyColorStep_any] using
      congrArg e hxy
  · intro y
    rcases hFull.2 (e y) with ⟨tw, htw⟩
    refine ⟨e.symm tw, ?_⟩
    apply e.injective
    simpa [e, layerRootEquiv_cayleyColorStep_fullStep] using htw

theorem layerRootEquiv_colorStep_iterate_zero
    (m : Nat) (c : Shared.TorusColor 3) :
    ∀ k : Nat, ∀ w : RootState m,
      (layerRootEquiv m)
        ((Shared.cayleyColorStep (colorDir m) c)^[k]
          ((layerRootEquiv m).symm (0, w))) =
        ((k : ZMod m), routeELayerPrefixMap m c k w)
  | 0, w => by
      simp [routeELayerPrefixMap]
  | k + 1, w => by
      rw [Function.iterate_succ_apply']
      have hprev :
          ((Shared.cayleyColorStep (colorDir m) c)^[k])
              ((layerRootEquiv m).symm (0, w)) =
            (layerRootEquiv m).symm
              ((k : ZMod m), routeELayerPrefixMap m c k w) := by
        apply (layerRootEquiv m).injective
        simpa using layerRootEquiv_colorStep_iterate_zero m c k w
      rw [hprev]
      rw [layerRootEquiv_cayleyColorStep]
      simp [routeELayerPrefixMap, Nat.cast_add]

theorem layerRootEquiv_colorStep_iterate_period_zero
    (m : Nat) [NeZero m] (c : Shared.TorusColor 3) (w : RootState m) :
    (layerRootEquiv m)
      ((Shared.cayleyColorStep (colorDir m) c)^[m]
        ((layerRootEquiv m).symm (0, w))) =
      (0, routeEReturnMap m c w) := by
  simpa [routeEReturnMap] using
    layerRootEquiv_colorStep_iterate_zero m c m w

theorem colorStep_iterate_period_base
    (m : Nat) [NeZero m] (c : Shared.TorusColor 3) (w : RootState m) :
    ((Shared.cayleyColorStep (colorDir m) c)^[m])
        ((layerRootEquiv m).symm (0, w)) =
      (layerRootEquiv m).symm (0, routeEReturnMap m c w) := by
  apply (layerRootEquiv m).injective
  rw [layerRootEquiv_colorStep_iterate_period_zero]
  simp

theorem colorStep_cover_from_root
    (m : Nat) [NeZero m] (c : Shared.TorusColor 3)
    (hLayer :
      ∀ t : ZMod m, Function.Bijective (routeELayerMap m t c)) :
    ∀ x : Vertex m, ∃ w : RootState m, ∃ k : Nat,
      k < m ∧
        ((Shared.cayleyColorStep (colorDir m) c)^[k])
          ((layerRootEquiv m).symm (0, w)) = x := by
  intro x
  let tw := (layerRootEquiv m) x
  let k : Nat := tw.1.val
  have hPrefix :
      Function.Bijective (routeELayerPrefixMap m c k) :=
    routeELayerPrefixMap_bijective m c hLayer k
  rcases hPrefix.2 tw.2 with ⟨w0, hw0⟩
  refine ⟨w0, k, ZMod.val_lt tw.1, ?_⟩
  apply (layerRootEquiv m).injective
  rw [layerRootEquiv_colorStep_iterate_zero]
  have hk : (k : ZMod m) = tw.1 := ZMod.natCast_zmod_val tw.1
  simp [tw, k, hk, hw0]

theorem colorHamiltonian_of_returnMap_singleCycle
    {m : Nat} [NeZero m]
    (hLayer :
      ∀ c : Shared.TorusColor 3, ∀ t : ZMod m,
        Function.Bijective (routeELayerMap m t c))
    (hReturn :
      ∀ c : Shared.TorusColor 3,
        Shared.IsSingleCycleMap (routeEReturnMap m c)) :
    Shared.IsCayleyColorHamiltonian (colorDir m) := by
  intro c
  exact Shared.single_cycle_of_periodic_return_cover
    (S := Shared.cayleyColorStep (colorDir m) c)
    (base := fun w : RootState m => (layerRootEquiv m).symm (0, w))
    (R := routeEReturnMap m c)
    (period := m)
    (cayleyColorStep_bijective_of_routeELayer m c (hLayer c))
    (colorStep_iterate_period_base m c)
    (hReturn c)
    (colorStep_cover_from_root m c (hLayer c))

theorem colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
    {m : Nat} [NeZero m] (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hReturn :
      ∀ c : Shared.TorusColor 3,
        Shared.IsSingleCycleMap (routeEReturnMap m c)) :
    Shared.IsCayleyColorHamiltonian (colorDir m) :=
  colorHamiltonian_of_returnMap_singleCycle
    (routeELayerMap_bijective_of_zero_layer hm3 hZero)
    hReturn

theorem colorHamiltonian_m6 :
    Shared.IsCayleyColorHamiltonian (colorDir 6) :=
  colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
    (m := 6) (by norm_num)
    routeELayerMap_zero_layer_bijective_m6
    routeEReturnMap_singleCycle_m6

theorem colorHamiltonian_m8 :
    Shared.IsCayleyColorHamiltonian (colorDir 8) :=
  colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
    (m := 8) (by norm_num)
    routeELayerMap_zero_layer_bijective_m8
    routeEReturnMap_singleCycle_m8

theorem colorHamiltonian_m10 :
    Shared.IsCayleyColorHamiltonian (colorDir 10) :=
  colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
    (m := 10) (by norm_num)
    routeELayerMap_zero_layer_bijective_m10
    routeEReturnMap_singleCycle_m10

def cayleyDecompositionOfHamiltonian {m : Nat}
    (hHamiltonian : Shared.IsCayleyColorHamiltonian (colorDir m)) :
    Shared.CayleyDecomposition 3 m where
  colorDir := colorDir m
  edgePartition := edgePartition m
  colorHamiltonian := hHamiltonian

theorem ordinary_of_hamiltonian {m : Nat}
    (hHamiltonian : Shared.IsCayleyColorHamiltonian (colorDir m)) :
    Shared.CayleyHamiltonDecomposition 3 m :=
  ⟨cayleyDecompositionOfHamiltonian hHamiltonian⟩

theorem ordinary_three_m6 :
    Shared.CayleyHamiltonDecomposition 3 6 :=
  ordinary_of_hamiltonian colorHamiltonian_m6

theorem ordinary_three_m8 :
    Shared.CayleyHamiltonDecomposition 3 8 :=
  ordinary_of_hamiltonian colorHamiltonian_m8

theorem ordinary_three_m10 :
    Shared.CayleyHamiltonDecomposition 3 10 :=
  ordinary_of_hamiltonian colorHamiltonian_m10

theorem ordinary_three_ge_six_of_routeE_hamiltonian
    (hHamiltonian :
      ∀ {m : Nat}, Even m -> 6 <= m ->
        Shared.IsCayleyColorHamiltonian (colorDir m)) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  intro m hm_even hm6
  exact ordinary_of_hamiltonian (hHamiltonian hm_even hm6)

theorem ordinary_three_ge_six_of_routeE_return_maps
    (hLayer :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3, ∀ t : ZMod m,
          Function.Bijective (routeELayerMap m t c))
    (hReturn :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3,
          Shared.IsSingleCycleMap (routeEReturnMap m c)) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  intro m hm_even hm6
  haveI : NeZero m := ⟨by omega⟩
  exact ordinary_of_hamiltonian
    (colorHamiltonian_of_returnMap_singleCycle
      (hLayer hm_even hm6) (hReturn hm_even hm6))

theorem ordinary_three_ge_six_of_routeE_zero_layer_return_maps
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hReturn :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3,
          Shared.IsSingleCycleMap (routeEReturnMap m c)) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  intro m hm_even hm6
  haveI : NeZero m := ⟨by omega⟩
  exact ordinary_of_hamiltonian
    (colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
      (by omega : 3 <= m) (hZero hm_even hm6) (hReturn hm_even hm6))

theorem ordinary_three_ge_six_of_routeE_zero_layer_return_models
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hReturnZero :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        Shared.IsSingleCycleMap (routeEReturnZeroModel m))
    (hReturnOne :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        Shared.IsSingleCycleMap (routeEReturnOneModel m))
    (hReturnTwo :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        Shared.IsSingleCycleMap (routeEReturnTwoModel m)) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  apply ordinary_three_ge_six_of_routeE_zero_layer_return_maps hZero
  intro m _ hm_even hm6
  exact routeEReturnMap_singleCycle_of_models
    (m := m) (by omega : 3 <= m)
    (hReturnZero hm_even hm6)
    (hReturnOne hm_even hm6)
    (hReturnTwo hm_even hm6)

/--
Rank-coordinate package for the three closed Route-E D3 return models.

This is the proof-facing boundary used by the round14 writeup: each colour
return is cyclic once it has a bijective rank coordinate whose return step is
`+1`.
-/
structure RouteEReturnModelRankPackage (m : Nat) [NeZero m] where
  N : Nat
  N_neZero : NeZero N
  rankZero : RootState m -> ZMod N
  rankZero_bijective : Function.Bijective rankZero
  rankZero_step :
    ∀ w : RootState m,
      rankZero (routeEReturnZeroModel m w) = rankZero w + 1
  rankOne : RootState m -> ZMod N
  rankOne_bijective : Function.Bijective rankOne
  rankOne_step :
    ∀ w : RootState m,
      rankOne (routeEReturnOneModel m w) = rankOne w + 1
  rankTwo : RootState m -> ZMod N
  rankTwo_bijective : Function.Bijective rankTwo
  rankTwo_step :
    ∀ w : RootState m,
      rankTwo (routeEReturnTwoModel m w) = rankTwo w + 1

namespace RouteEReturnModelRankPackage

theorem zero_singleCycle
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m) :
    Shared.IsSingleCycleMap (routeEReturnZeroModel m) := by
  haveI : NeZero pkg.N := pkg.N_neZero
  exact Shared.single_cycle_of_zmod_rank
    (routeEReturnZeroModel m) pkg.rankZero
    pkg.rankZero_bijective pkg.rankZero_step

theorem one_singleCycle
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m) :
    Shared.IsSingleCycleMap (routeEReturnOneModel m) := by
  haveI : NeZero pkg.N := pkg.N_neZero
  exact Shared.single_cycle_of_zmod_rank
    (routeEReturnOneModel m) pkg.rankOne
    pkg.rankOne_bijective pkg.rankOne_step

theorem two_singleCycle
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m) :
    Shared.IsSingleCycleMap (routeEReturnTwoModel m) := by
  haveI : NeZero pkg.N := pkg.N_neZero
  exact Shared.single_cycle_of_zmod_rank
    (routeEReturnTwoModel m) pkg.rankTwo
    pkg.rankTwo_bijective pkg.rankTwo_step

theorem returnMap_singleCycle
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m)
    (hm3 : 3 <= m) :
    ∀ c : Shared.TorusColor 3,
      Shared.IsSingleCycleMap (routeEReturnMap m c) :=
  routeEReturnMap_singleCycle_of_models
    (m := m) hm3
    (zero_singleCycle pkg)
    (one_singleCycle pkg)
    (two_singleCycle pkg)

theorem colorHamiltonian_of_zero_layer
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m)
    (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c)) :
    Shared.IsCayleyColorHamiltonian (colorDir m) :=
  colorHamiltonian_of_zero_layer_and_returnMap_singleCycle
    hm3 hZero (returnMap_singleCycle pkg hm3)

theorem ordinary_three_of_zero_layer
    {m : Nat} [NeZero m] (pkg : RouteEReturnModelRankPackage m)
    (hm3 : 3 <= m)
    (hZero :
      ∀ c : Shared.TorusColor 3,
        Function.Bijective (routeELayerMap m (0 : ZMod m) c)) :
    Shared.CayleyHamiltonDecomposition 3 m :=
  ordinary_of_hamiltonian
    (colorHamiltonian_of_zero_layer pkg hm3 hZero)

end RouteEReturnModelRankPackage

def routeEReturnModelRankPackageOfEvenModCases
    {m : Nat} [NeZero m] (hm_even : Even m)
    (hZeroOrTwo :
      (m % 6 = 0 ∨ m % 6 = 2) ->
        RouteEReturnModelRankPackage m)
    (hFour :
      m % 6 = 4 ->
        RouteEReturnModelRankPackage m) :
    RouteEReturnModelRankPackage m :=
  if h02 : m % 6 = 0 ∨ m % 6 = 2 then
    hZeroOrTwo h02
  else
    hFour (even_mod_six_eq_four_of_not_zero_or_two hm_even h02)

def routeEReturnModelRankPackage_m6 : RouteEReturnModelRankPackage 6 where
  N := 36
  N_neZero := ⟨by norm_num⟩
  rankZero := routeEReturnZeroModelRank_m6
  rankZero_bijective := routeEReturnZeroModelRank_m6_bijective
  rankZero_step := routeEReturnZeroModelRank_m6_step
  rankOne := routeEReturnOneModelRank_m6
  rankOne_bijective := routeEReturnOneModelRank_m6_bijective
  rankOne_step := routeEReturnOneModelRank_m6_step
  rankTwo := routeEReturnTwoModelRank_m6
  rankTwo_bijective := routeEReturnTwoModelRank_m6_bijective
  rankTwo_step := routeEReturnTwoModelRank_m6_step

def routeEReturnModelRankPackage_m8 : RouteEReturnModelRankPackage 8 where
  N := 64
  N_neZero := ⟨by norm_num⟩
  rankZero := routeEReturnZeroModelRank_m8
  rankZero_bijective := routeEReturnZeroModelRank_m8_bijective
  rankZero_step := routeEReturnZeroModelRank_m8_step
  rankOne := routeEReturnOneModelRank_m8
  rankOne_bijective := routeEReturnOneModelRank_m8_bijective
  rankOne_step := routeEReturnOneModelRank_m8_step
  rankTwo := routeEReturnTwoModelRank_m8
  rankTwo_bijective := routeEReturnTwoModelRank_m8_bijective
  rankTwo_step := routeEReturnTwoModelRank_m8_step

def routeEReturnModelRankPackage_m10 : RouteEReturnModelRankPackage 10 where
  N := 100
  N_neZero := ⟨by norm_num⟩
  rankZero := routeEReturnZeroModelRank_m10
  rankZero_bijective := routeEReturnZeroModelRank_m10_bijective
  rankZero_step := routeEReturnZeroModelRank_m10_step
  rankOne := routeEReturnOneModelRank_m10
  rankOne_bijective := routeEReturnOneModelRank_m10_bijective
  rankOne_step := routeEReturnOneModelRank_m10_step
  rankTwo := routeEReturnTwoModelRank_m10
  rankTwo_bijective := routeEReturnTwoModelRank_m10_bijective
  rankTwo_step := routeEReturnTwoModelRank_m10_step

def routeEReturnModelRankPackage_m12 : RouteEReturnModelRankPackage 12 where
  N := 144
  N_neZero := ⟨by norm_num⟩
  rankZero := routeEReturnZeroModelRank_m12
  rankZero_bijective := routeEReturnZeroModelRank_m12_bijective
  rankZero_step := routeEReturnZeroModelRank_m12_step
  rankOne := routeEReturnOneModelRank_m12
  rankOne_bijective := routeEReturnOneModelRank_m12_bijective
  rankOne_step := routeEReturnOneModelRank_m12_step
  rankTwo := routeEReturnTwoModelRank_m12
  rankTwo_bijective := routeEReturnTwoModelRank_m12_bijective
  rankTwo_step := routeEReturnTwoModelRank_m12_step

def routeEReturnModelRankPackageOfEvenGeSixTail
    {m : Nat} [NeZero m] (hm_even : Even m) (hm6 : 6 <= m)
    (hTail : 14 <= m -> RouteEReturnModelRankPackage m) :
    RouteEReturnModelRankPackage m := by
  by_cases h6eq : m = 6
  · subst m
    exact routeEReturnModelRankPackage_m6
  · by_cases h8eq : m = 8
    · subst m
      exact routeEReturnModelRankPackage_m8
    · by_cases h10eq : m = 10
      · subst m
        exact routeEReturnModelRankPackage_m10
      · by_cases h12eq : m = 12
        · subst m
          exact routeEReturnModelRankPackage_m12
        · exact hTail (by
            rcases hm_even with ⟨k, rfl⟩
            omega)

theorem ordinary_three_ge_six_of_routeE_zero_layer_return_rank_package
    (hZero :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hRank :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        RouteEReturnModelRankPackage m) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  intro m hm_even hm6
  haveI : NeZero m := ⟨by omega⟩
  exact RouteEReturnModelRankPackage.ordinary_three_of_zero_layer
    (hRank hm_even hm6) (by omega : 3 <= m)
    (hZero hm_even hm6)

theorem ordinary_three_ge_six_of_routeE_residue_rank_packages
    (hZeroOrTwo :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        (m % 6 = 0 ∨ m % 6 = 2) ->
          ∀ c : Shared.TorusColor 3,
            Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hZeroFour :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        m % 6 = 4 ->
          ∀ c : Shared.TorusColor 3,
            Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hRankOrTwo :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        (m % 6 = 0 ∨ m % 6 = 2) ->
          RouteEReturnModelRankPackage m)
    (hRankFour :
      ∀ {m : Nat} [NeZero m], Even m -> 6 <= m ->
        m % 6 = 4 ->
          RouteEReturnModelRankPackage m) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  apply ordinary_three_ge_six_of_routeE_zero_layer_return_rank_package
  · intro m _ hm_even hm6
    exact routeELayerMap_zero_layer_bijective_of_even_mod_cases
      hm_even (hZeroOrTwo hm_even hm6) (hZeroFour hm_even hm6)
  · intro m _ hm_even hm6
    exact routeEReturnModelRankPackageOfEvenModCases
      hm_even (hRankOrTwo hm_even hm6) (hRankFour hm_even hm6)

theorem ordinary_three_ge_six_of_routeE_tail_rank_package
    (hZeroTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        ∀ c : Shared.TorusColor 3,
          Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hRankTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        RouteEReturnModelRankPackage m) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  apply ordinary_three_ge_six_of_routeE_zero_layer_return_rank_package
  · intro m _ hm_even hm6
    exact routeELayerMap_zero_layer_bijective_of_even_ge_six_tail
      hm_even hm6 (hZeroTail hm_even)
  · intro m _ hm_even hm6
    exact routeEReturnModelRankPackageOfEvenGeSixTail
      hm_even hm6 (hRankTail hm_even)

theorem ordinary_three_ge_six_of_routeE_tail_residue_rank_packages
    (hZeroOrTwoTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        (m % 6 = 0 ∨ m % 6 = 2) ->
          ∀ c : Shared.TorusColor 3,
            Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hZeroFourTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        m % 6 = 4 ->
          ∀ c : Shared.TorusColor 3,
            Function.Bijective (routeELayerMap m (0 : ZMod m) c))
    (hRankOrTwoTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        (m % 6 = 0 ∨ m % 6 = 2) ->
          RouteEReturnModelRankPackage m)
    (hRankFourTail :
      ∀ {m : Nat} [NeZero m], Even m -> 14 <= m ->
        m % 6 = 4 ->
          RouteEReturnModelRankPackage m) :
    ∀ {m : Nat}, Even m -> 6 <= m ->
      Shared.CayleyHamiltonDecomposition 3 m := by
  apply ordinary_three_ge_six_of_routeE_tail_rank_package
  · intro m _ hm_even hm14
    exact routeELayerMap_zero_layer_bijective_of_even_mod_cases
      hm_even (hZeroOrTwoTail hm_even hm14) (hZeroFourTail hm_even hm14)
  · intro m _ hm_even hm14
    exact routeEReturnModelRankPackageOfEvenModCases
      hm_even (hRankOrTwoTail hm_even hm14) (hRankFourTail hm_even hm14)

end D3EvenRouteEGeSix
end EvenV11
