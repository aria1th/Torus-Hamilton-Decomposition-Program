import D7Odd.Handoff.CanonicalBridge

set_option linter.style.nativeDecide false
set_option linter.style.longLine false

namespace D7Odd
namespace Handoff

abbrev Rho6 := {r : Fin 7 // 1 ≤ r.val}

def rootPrefixCoord {m : Nat} (w : RootState7 m) : Fin 6 → ZMod m
  | 0 => -(w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5)
  | 1 => -(w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4)
  | 2 => -(w.1 0 + w.1 1 + w.1 2 + w.1 3)
  | 3 => -(w.1 0 + w.1 1 + w.1 2)
  | 4 => -(w.1 0 + w.1 1)
  | 5 => -(w.1 0)

def rootVecOfPrefix {m : Nat} (z : Fin 6 → ZMod m) : Vec7 m
  | 0 => -z 5
  | 1 => z 5 - z 4
  | 2 => z 4 - z 3
  | 3 => z 3 - z 2
  | 4 => z 2 - z 1
  | 5 => z 1 - z 0
  | 6 => z 0

theorem root_rootVecOfPrefix {m : Nat} (z : Fin 6 → ZMod m) :
    Root7 m (rootVecOfPrefix z) := by
  unfold Root7 sum7 rootVecOfPrefix
  rw [Fin.sum_univ_seven]
  ring

def rootOfPrefix {m : Nat} (z : Fin 6 → ZMod m) : RootState7 m :=
  ⟨rootVecOfPrefix z, root_rootVecOfPrefix z⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rootPrefixCoord_rootOfPrefix {m : Nat} (z : Fin 6 → ZMod m) :
    rootPrefixCoord (rootOfPrefix z) = z := by
  funext k
  fin_cases k <;> simp [rootPrefixCoord, rootOfPrefix, rootVecOfPrefix] <;> ring

set_option linter.flexible false in
theorem rootOfPrefix_rootPrefixCoord {m : Nat} (w : RootState7 m) :
    rootOfPrefix (rootPrefixCoord w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
  · simp [rootOfPrefix, rootVecOfPrefix, rootPrefixCoord]
    rw [rootSix_six_coord w]
    ring

theorem rootPrefixCoord_bijective {m : Nat} :
    Function.Bijective (rootPrefixCoord : RootState7 m → Fin 6 → ZMod m) :=
  bijective_of_inverse rootPrefixCoord rootOfPrefix
    rootOfPrefix_rootPrefixCoord rootPrefixCoord_rootOfPrefix

theorem rootOfPrefix_bijective {m : Nat} :
    Function.Bijective (rootOfPrefix : (Fin 6 → ZMod m) → RootState7 m) :=
  bijective_of_inverse rootOfPrefix rootPrefixCoord
    rootPrefixCoord_rootOfPrefix rootOfPrefix_rootPrefixCoord

def prefixHead {m : Nat} (z : Fin 6 → ZMod m) : ZMod m :=
  z 0

def prefixTail {m : Nat} (z : Fin 6 → ZMod m) : Fin 5 → ZMod m :=
  fun i => z ⟨i.val + 1, by omega⟩

def prefixOfHeadTail {m : Nat} (x : ZMod m) (tail : Fin 5 → ZMod m) :
    Fin 6 → ZMod m
  | 0 => x
  | 1 => tail 0
  | 2 => tail 1
  | 3 => tail 2
  | 4 => tail 3
  | 5 => tail 4

@[simp] theorem prefixHead_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 5 → ZMod m) :
    prefixHead (prefixOfHeadTail x tail) = x := by
  rfl

@[simp] theorem prefixTail_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 5 → ZMod m) :
    prefixTail (prefixOfHeadTail x tail) = tail := by
  funext i
  fin_cases i <;> rfl

theorem prefixOfHeadTail_head_tail {m : Nat} (z : Fin 6 → ZMod m) :
    prefixOfHeadTail (prefixHead z) (prefixTail z) = z := by
  funext i
  fin_cases i <;> rfl

def prefixSplitEquiv (m : Nat) : (Fin 6 → ZMod m) ≃ ZMod m × (Fin 5 → ZMod m) where
  toFun z := (prefixHead z, prefixTail z)
  invFun p := prefixOfHeadTail p.1 p.2
  left_inv := prefixOfHeadTail_head_tail
  right_inv := by
    intro p
    cases p
    simp

def prefixFiberBase {m : Nat} (b : ZMod m) (tail : Fin 5 → ZMod m) :
    Fin 6 → ZMod m :=
  prefixOfHeadTail b tail

def prefixPair {m : Nat} (z : Fin 6 → ZMod m) : ZMod m × ZMod m :=
  (z 0, z 1)

def prefixPairBase {m : Nat} (p : ZMod m × ZMod m) : Fin 6 → ZMod m
  | 0 => p.1
  | 1 => p.2
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

def prefixTriple {m : Nat} (z : Fin 6 → ZMod m) :
    ZMod m × ZMod m × ZMod m :=
  (z 0, z 1, z 2)

def prefixTripleBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m) : Fin 6 → ZMod m
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2
  | 3 => 0
  | 4 => 0
  | 5 => 0

def prefixTriplePair {m : Nat}
    (p : ZMod m × ZMod m × ZMod m) : ZMod m × ZMod m :=
  (p.1, p.2.1)

def prefixQuad {m : Nat} (z : Fin 6 → ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m :=
  (z 0, z 1, z 2, z 3)

def prefixQuadBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m) : Fin 6 → ZMod m
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | 3 => p.2.2.2
  | 4 => 0
  | 5 => 0

def prefixQuadTriple {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m :=
  (p.1, p.2.1, p.2.2.1)

def prefixQuint {m : Nat} (z : Fin 6 → ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m × ZMod m :=
  (z 0, z 1, z 2, z 3, z 4)

def prefixQuintBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) : Fin 6 → ZMod m
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | 3 => p.2.2.2.1
  | 4 => p.2.2.2.2
  | 5 => 0

def prefixQuintQuad {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m :=
  (p.1, p.2.1, p.2.2.1, p.2.2.2.1)

@[simp] theorem prefixPair_pairBase {m : Nat} (p : ZMod m × ZMod m) :
    prefixPair (prefixPairBase p) = p := by
  cases p
  rfl

@[simp] theorem prefixTriple_tripleBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m) :
    prefixTriple (prefixTripleBase p) = p := by
  rcases p with ⟨x, y, z⟩
  rfl

@[simp] theorem prefixQuad_quadBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuad (prefixQuadBase p) = p := by
  rcases p with ⟨w, x, y, z⟩
  rfl

@[simp] theorem prefixQuint_quintBase {m : Nat}
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuint (prefixQuintBase p) = p := by
  rcases p with ⟨v, w, x, y, z⟩
  rfl

@[simp] theorem prefixFiberBase_head {m : Nat}
    (b : ZMod m) (tail : Fin 5 → ZMod m) :
    prefixHead (prefixFiberBase b tail) = b := by
  rfl

theorem prefixFiberBase_surj {m : Nat} (b : ZMod m) :
    ∀ z : Fin 6 → ZMod m, prefixHead z = b → ∃ tail : Fin 5 → ZMod m,
      prefixFiberBase b tail = z := by
  intro z hz
  refine ⟨prefixTail z, ?_⟩
  unfold prefixFiberBase
  rw [← hz]
  exact prefixOfHeadTail_head_tail z

def prefixRho {m : Nat} (t : ZMod m) (z : Fin 6 → ZMod m) : Rho6 :=
  if z 0 = t then ⟨1, by decide⟩
  else if z 1 = t then ⟨2, by decide⟩
  else if z 2 = t then ⟨3, by decide⟩
  else if z 3 = t then ⟨4, by decide⟩
  else if z 4 = t then ⟨5, by decide⟩
  else ⟨6, by decide⟩

theorem sub_one_ne_sub_one {m : Nat} {a b : ZMod m} (h : a ≠ b) :
    a - 1 ≠ b - 1 := by
  intro hsub
  have hc := congrArg (fun x : ZMod m => x + 1) hsub
  exact h (by simpa using hc)

theorem add_one_ne_of_ne_sub_one {m : Nat} {a b : ZMod m} (h : a ≠ b - 1) :
    a + 1 ≠ b := by
  intro hadd
  have hc := congrArg (fun x : ZMod m => x - 1) hadd
  exact h (by simpa using hc)

theorem add_one_eq_iff_eq_sub_one {m : Nat} {a b : ZMod m} :
    a + 1 = b ↔ a = b - 1 := by
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    rw [h]
    ring

set_option linter.flexible false in
theorem exists_fin6_lt_one_eq {m : Nat} (z : Fin 6 → ZMod m) (a : ZMod m) :
    (∃ k : Fin 6, k.val < 1 ∧ z k = a) ↔ z 0 = a := by
  constructor
  · rintro ⟨k, hk, hz⟩
    fin_cases k <;> simp at hk hz ⊢
    exact hz
  · intro h
    exact ⟨0, by decide, h⟩

set_option linter.flexible false in
theorem exists_fin6_lt_two_eq {m : Nat} (z : Fin 6 → ZMod m) (a : ZMod m) :
    (∃ k : Fin 6, k.val < 2 ∧ z k = a) ↔ z 0 = a ∨ z 1 = a := by
  constructor
  · rintro ⟨k, hk, hz⟩
    fin_cases k <;> simp at hk hz ⊢
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩

set_option linter.flexible false in
theorem exists_fin6_lt_three_eq {m : Nat} (z : Fin 6 → ZMod m) (a : ZMod m) :
    (∃ k : Fin 6, k.val < 3 ∧ z k = a) ↔
      z 0 = a ∨ z 1 = a ∨ z 2 = a := by
  constructor
  · rintro ⟨k, hk, hz⟩
    fin_cases k <;> simp at hk hz ⊢
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)
  · rintro (h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩

set_option linter.flexible false in
theorem exists_fin6_lt_four_eq {m : Nat} (z : Fin 6 → ZMod m) (a : ZMod m) :
    (∃ k : Fin 6, k.val < 4 ∧ z k = a) ↔
      z 0 = a ∨ z 1 = a ∨ z 2 = a ∨ z 3 = a := by
  constructor
  · rintro ⟨k, hk, hz⟩
    fin_cases k <;> simp at hk hz ⊢
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  · rintro (h | h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩

set_option linter.flexible false in
theorem exists_fin6_lt_five_eq {m : Nat} (z : Fin 6 → ZMod m) (a : ZMod m) :
    (∃ k : Fin 6, k.val < 5 ∧ z k = a) ↔
      z 0 = a ∨ z 1 = a ∨ z 2 = a ∨ z 3 = a ∨ z 4 = a := by
  constructor
  · rintro ⟨k, hk, hz⟩
    fin_cases k <;> simp at hk hz ⊢
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))
  · rintro (h | h | h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨4, by decide, h⟩

set_option linter.unusedSimpArgs false in
theorem prefixRho_lt_three_iff_exists_lt_two {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    (prefixRho t z).1.val < 3 ↔ ∃ k : Fin 6, k.val < 2 ∧ z k = t := by
  unfold prefixRho
  by_cases h0 : z 0 = t
  · rw [exists_fin6_lt_two_eq]
    simp [h0]
  · by_cases h1 : z 1 = t
    · rw [exists_fin6_lt_two_eq]
      simp [h0, h1]
    · rw [exists_fin6_lt_two_eq]
      by_cases h2 : z 2 = t
      · simp [h0, h1, h2]
      · by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4]
          · simp [h0, h1, h2, h3, h4]

set_option linter.unusedSimpArgs false in
theorem prefixRho_lt_four_iff_exists_lt_three {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    (prefixRho t z).1.val < 4 ↔ ∃ k : Fin 6, k.val < 3 ∧ z k = t := by
  unfold prefixRho
  by_cases h0 : z 0 = t
  · rw [exists_fin6_lt_three_eq]
    simp [h0]
  · by_cases h1 : z 1 = t
    · rw [exists_fin6_lt_three_eq]
      simp [h0, h1]
    · by_cases h2 : z 2 = t
      · rw [exists_fin6_lt_three_eq]
        simp [h0, h1, h2]
      · rw [exists_fin6_lt_three_eq]
        by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4]
          · simp [h0, h1, h2, h3, h4]

set_option linter.unusedSimpArgs false in
theorem prefixRho_lt_five_iff_exists_lt_four {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    (prefixRho t z).1.val < 5 ↔ ∃ k : Fin 6, k.val < 4 ∧ z k = t := by
  unfold prefixRho
  by_cases h0 : z 0 = t
  · rw [exists_fin6_lt_four_eq]
    simp [h0]
  · by_cases h1 : z 1 = t
    · rw [exists_fin6_lt_four_eq]
      simp [h0, h1]
    · by_cases h2 : z 2 = t
      · rw [exists_fin6_lt_four_eq]
        simp [h0, h1, h2]
      · by_cases h3 : z 3 = t
        · rw [exists_fin6_lt_four_eq]
          simp [h0, h1, h2, h3]
        · rw [exists_fin6_lt_four_eq]
          by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4]
          · simp [h0, h1, h2, h3, h4]

set_option linter.unusedSimpArgs false in
theorem prefixRho_lt_six_iff_exists_lt_five {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    (prefixRho t z).1.val < 6 ↔ ∃ k : Fin 6, k.val < 5 ∧ z k = t := by
  unfold prefixRho
  rw [exists_fin6_lt_five_eq]
  by_cases h0 : z 0 = t
  · simp [h0]
  · by_cases h1 : z 1 = t
    · simp [h0, h1]
    · by_cases h2 : z 2 = t
      · simp [h0, h1, h2]
      · by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4]
          · simp [h0, h1, h2, h3, h4]

theorem prefixRho_eq_one_iff {m : Nat} (t : ZMod m) (z : Fin 6 → ZMod m) :
    (prefixRho t z).1 = (1 : Fin 7) ↔ z 0 = t := by
  unfold prefixRho
  by_cases h0 : z 0 = t
  · simp [h0]
  · by_cases h1 : z 1 = t
    · simp [h0, h1]
    · by_cases h2 : z 2 = t
      · simp [h0, h1, h2]
      · by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4]
          · simp [h0, h1, h2, h3, h4]


def canonicalRho {m : Nat} (t : ZMod m) (w : RootState7 m) : Rho6 :=
  prefixRho t (rootPrefixCoord w)

def prefixLabelToDirection (r : Fin 7) : Direction :=
  ⟨6 - r.val, by omega⟩

def prefixLabelStep {m : Nat} (r : Fin 7) (z : Fin 6 → ZMod m) : Fin 6 → ZMod m :=
  fun k => z k - if k.val < r.val then 1 else 0

def prefixLabelUnstep {m : Nat} (r : Fin 7) (z : Fin 6 → ZMod m) : Fin 6 → ZMod m :=
  fun k => z k + if k.val < r.val then 1 else 0

theorem rootPrefixCoord_addQRoot_prefixLabel {m : Nat}
    (r : Fin 7) (w : RootState7 m) :
    rootPrefixCoord (addQRoot m (prefixLabelToDirection r) w) =
      prefixLabelStep r (rootPrefixCoord w) := by
  funext k
  fin_cases r <;> fin_cases k <;>
    simp [prefixLabelStep, prefixLabelToDirection, rootPrefixCoord,
      addQRoot, addQ, q7, e7] <;> ring

theorem rootPrefixCoord_subQRoot_prefixLabel {m : Nat}
    (r : Fin 7) (w : RootState7 m) :
    rootPrefixCoord (subQRoot m (prefixLabelToDirection r) w) =
      prefixLabelUnstep r (rootPrefixCoord w) := by
  funext k
  fin_cases r <;> fin_cases k <;>
    simp [prefixLabelUnstep, prefixLabelToDirection, rootPrefixCoord,
      subQRoot, subQ, q7, e7] <;> ring

theorem exists_fin6_lt_two_step_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 2 ≤ r.val) :
    (∃ k : Fin 6, k.val < 2 ∧ prefixLabelStep r z k = t - 1) ↔
      ∃ k : Fin 6, k.val < 2 ∧ z k = t := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_two_eq, exists_fin6_lt_two_eq]
    simp [prefixLabelStep]

theorem exists_fin6_lt_three_step_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 3 ≤ r.val) :
    (∃ k : Fin 6, k.val < 3 ∧ prefixLabelStep r z k = t - 1) ↔
      ∃ k : Fin 6, k.val < 3 ∧ z k = t := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_three_eq, exists_fin6_lt_three_eq]
    simp [prefixLabelStep]

theorem exists_fin6_lt_four_step_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 4 ≤ r.val) :
    (∃ k : Fin 6, k.val < 4 ∧ prefixLabelStep r z k = t - 1) ↔
      ∃ k : Fin 6, k.val < 4 ∧ z k = t := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_four_eq, exists_fin6_lt_four_eq]
    simp [prefixLabelStep]

theorem exists_fin6_lt_five_step_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 5 ≤ r.val) :
    (∃ k : Fin 6, k.val < 5 ∧ prefixLabelStep r z k = t - 1) ↔
      ∃ k : Fin 6, k.val < 5 ∧ z k = t := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_five_eq, exists_fin6_lt_five_eq]
    simp [prefixLabelStep]

theorem exists_fin6_lt_two_unstep_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 2 ≤ r.val) :
    (∃ k : Fin 6, k.val < 2 ∧ prefixLabelUnstep r z k = t) ↔
      ∃ k : Fin 6, k.val < 2 ∧ z k = t - 1 := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_two_eq, exists_fin6_lt_two_eq]
    simp [prefixLabelUnstep, add_one_eq_iff_eq_sub_one]

theorem exists_fin6_lt_three_unstep_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 3 ≤ r.val) :
    (∃ k : Fin 6, k.val < 3 ∧ prefixLabelUnstep r z k = t) ↔
      ∃ k : Fin 6, k.val < 3 ∧ z k = t - 1 := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_three_eq, exists_fin6_lt_three_eq]
    simp [prefixLabelUnstep, add_one_eq_iff_eq_sub_one]

theorem exists_fin6_lt_four_unstep_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 4 ≤ r.val) :
    (∃ k : Fin 6, k.val < 4 ∧ prefixLabelUnstep r z k = t) ↔
      ∃ k : Fin 6, k.val < 4 ∧ z k = t - 1 := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_four_eq, exists_fin6_lt_four_eq]
    simp [prefixLabelUnstep, add_one_eq_iff_eq_sub_one]

theorem exists_fin6_lt_five_unstep_eq {m : Nat} (z : Fin 6 → ZMod m)
    (t : ZMod m) (r : Fin 7) (hr : 5 ≤ r.val) :
    (∃ k : Fin 6, k.val < 5 ∧ prefixLabelUnstep r z k = t) ↔
      ∃ k : Fin 6, k.val < 5 ∧ z k = t - 1 := by
  fin_cases r <;> norm_num at hr
  all_goals
    rw [exists_fin6_lt_five_eq, exists_fin6_lt_five_eq]
    simp [prefixLabelUnstep, add_one_eq_iff_eq_sub_one]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem prefixLabelUnstep_step {m : Nat}
    (r : Fin 7) (z : Fin 6 → ZMod m) :
    prefixLabelUnstep r (prefixLabelStep r z) = z := by
  funext k
  fin_cases r <;> fin_cases k <;>
    simp [prefixLabelUnstep, prefixLabelStep] <;> ring

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem prefixLabelStep_unstep {m : Nat}
    (r : Fin 7) (z : Fin 6 → ZMod m) :
    prefixLabelStep r (prefixLabelUnstep r z) = z := by
  funext k
  fin_cases r <;> fin_cases k <;>
    simp [prefixLabelUnstep, prefixLabelStep] <;> ring

theorem prefixRho_after_step_self {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    prefixRho (t - 1) (prefixLabelStep (prefixRho t z).1 z) = prefixRho t z := by
  unfold prefixRho
  by_cases h0 : z 0 = t
  · simp [h0, prefixLabelStep]
  · have h0' : z 0 - 1 ≠ t - 1 := sub_one_ne_sub_one h0
    by_cases h1 : z 1 = t
    · simp [h0, h1, h0', prefixLabelStep]
    · have h1' : z 1 - 1 ≠ t - 1 := sub_one_ne_sub_one h1
      by_cases h2 : z 2 = t
      · simp [h0, h1, h2, h0', h1', prefixLabelStep]
      · have h2' : z 2 - 1 ≠ t - 1 := sub_one_ne_sub_one h2
        by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3, h0', h1', h2', prefixLabelStep]
        · have h3' : z 3 - 1 ≠ t - 1 := sub_one_ne_sub_one h3
          by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4, h0', h1', h2', h3', prefixLabelStep]
          · have h4' : z 4 - 1 ≠ t - 1 := sub_one_ne_sub_one h4
            simp [h0, h1, h2, h3, h4, h0', h1', h2', h3', h4',
              prefixLabelStep]

theorem prefixRho_after_unstep_self {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    prefixRho t (prefixLabelUnstep (prefixRho (t - 1) z).1 z) =
      prefixRho (t - 1) z := by
  unfold prefixRho
  by_cases h0 : z 0 = t - 1
  · simp [h0, prefixLabelUnstep]
  · have h0' : z 0 + 1 ≠ t := add_one_ne_of_ne_sub_one h0
    by_cases h1 : z 1 = t - 1
    · simp [h0, h1, h0', prefixLabelUnstep]
    · have h1' : z 1 + 1 ≠ t := add_one_ne_of_ne_sub_one h1
      by_cases h2 : z 2 = t - 1
      · simp [h0, h1, h2, h0', h1', prefixLabelUnstep]
      · have h2' : z 2 + 1 ≠ t := add_one_ne_of_ne_sub_one h2
        by_cases h3 : z 3 = t - 1
        · simp [h0, h1, h2, h3, h0', h1', h2', prefixLabelUnstep]
        · have h3' : z 3 + 1 ≠ t := add_one_ne_of_ne_sub_one h3
          by_cases h4 : z 4 = t - 1
          · simp [h0, h1, h2, h3, h4, h0', h1', h2', h3',
              prefixLabelUnstep]
          · have h4' : z 4 + 1 ≠ t := add_one_ne_of_ne_sub_one h4
            simp [h0, h1, h2, h3, h4, h0', h1', h2', h3', h4',
              prefixLabelUnstep]

def canonicalPrefixLabelOfRho (rho : Rho6) (sym : CanonSym) : Fin 7 :=
  if sym = 0 then 0
  else if sym = 1 then rho.1
  else if rho.1.val < sym.val then sym
  else ⟨sym.val - 1, by omega⟩

def canonicalDirOfRho (rho : Rho6) (sym : CanonSym) : Direction :=
  prefixLabelToDirection (canonicalPrefixLabelOfRho rho sym)

def canonicalLayerDir {m : Nat} (t : ZMod m) (w : RootState7 m)
    (sym : CanonSym) : Direction :=
  canonicalDirOfRho (canonicalRho t w) sym

def canonicalPrefixMap {m : Nat} (t : ZMod m) (sym : CanonSym) :
    (Fin 6 → ZMod m) → (Fin 6 → ZMod m) :=
  fun z => prefixLabelStep (canonicalPrefixLabelOfRho (prefixRho t z) sym) z

def canonicalPrefixInvLabel {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) : Fin 7 :=
  if sym = 0 then 0
  else if sym = 1 then (prefixRho (t - 1) z).1
  else if ∃ k : Fin 6, k.val < sym.val - 1 ∧ z k = t - 1 then sym
  else ⟨sym.val - 1, by omega⟩

def canonicalPrefixInvMap {m : Nat} (t : ZMod m) (sym : CanonSym) :
    (Fin 6 → ZMod m) → (Fin 6 → ZMod m) :=
  fun z => prefixLabelUnstep (canonicalPrefixInvLabel t sym z) z

@[simp] theorem canonicalPrefixMap_zero {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t 0 z = z := by
  funext k
  fin_cases k <;> simp [canonicalPrefixMap, canonicalPrefixLabelOfRho,
    prefixLabelStep]

@[simp] theorem canonicalPrefixInvMap_zero {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixInvMap t 0 z = z := by
  funext k
  fin_cases k <;> simp [canonicalPrefixInvMap, canonicalPrefixInvLabel,
    prefixLabelUnstep]

theorem canonicalPrefixLayerInverse_zero {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 0 (canonicalPrefixMap t 0 z) = z) ∧
      (∀ z, canonicalPrefixMap t 0 (canonicalPrefixInvMap t 0 z) = z) := by
  simp

theorem canonicalPrefixLayerInverse_delta {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 1 (canonicalPrefixMap t 1 z) = z) ∧
      (∀ z, canonicalPrefixMap t 1 (canonicalPrefixInvMap t 1 z) = z) := by
  constructor
  · intro z
    simp [canonicalPrefixInvMap, canonicalPrefixMap, canonicalPrefixInvLabel,
      canonicalPrefixLabelOfRho, prefixRho_after_step_self, prefixLabelUnstep_step]
  · intro z
    simp [canonicalPrefixInvMap, canonicalPrefixMap, canonicalPrefixInvLabel,
      canonicalPrefixLabelOfRho, prefixRho_after_unstep_self, prefixLabelStep_unstep]

theorem canonicalPrefixInvLabel_after_map_two {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixInvLabel t 2 (canonicalPrefixMap t 2 z) =
      canonicalPrefixLabelOfRho (prefixRho t z) 2 := by
  unfold canonicalPrefixInvLabel canonicalPrefixMap canonicalPrefixLabelOfRho prefixRho
  by_cases h0 : z 0 = t
  · simp [h0, prefixLabelStep]
  · have h0' : z 0 - 1 ≠ t - 1 := sub_one_ne_sub_one h0
    by_cases h1 : z 1 = t
    · simp [h0, h1, h0', prefixLabelStep]
    · by_cases h2 : z 2 = t
      · simp [h0, h1, h2, h0', prefixLabelStep]
      · by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3, h0', prefixLabelStep]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4, h0', prefixLabelStep]
          · simp [h0, h1, h2, h3, h4, h0', prefixLabelStep]

theorem canonicalPrefixLabel_after_inv_two {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixLabelOfRho (prefixRho t (canonicalPrefixInvMap t 2 z)) 2 =
      canonicalPrefixInvLabel t 2 z := by
  unfold canonicalPrefixInvMap canonicalPrefixInvLabel canonicalPrefixLabelOfRho prefixRho
  by_cases h0 : z 0 = t - 1
  · simp [h0, prefixLabelUnstep]
  · have h0' : z 0 + 1 ≠ t := add_one_ne_of_ne_sub_one h0
    by_cases h1 : z 1 = t
    · simp [h0, h1, h0', prefixLabelUnstep]
    · by_cases h2 : z 2 = t
      · simp [h0, h1, h2, h0', prefixLabelUnstep]
      · by_cases h3 : z 3 = t
        · simp [h0, h1, h2, h3, h0', prefixLabelUnstep]
        · by_cases h4 : z 4 = t
          · simp [h0, h1, h2, h3, h4, h0', prefixLabelUnstep]
          · simp [h0, h1, h2, h3, h4, h0', prefixLabelUnstep]

theorem canonicalPrefixLayerInverse_two {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 2 (canonicalPrefixMap t 2 z) = z) ∧
      (∀ z, canonicalPrefixMap t 2 (canonicalPrefixInvMap t 2 z) = z) := by
  constructor
  · intro z
    rw [show canonicalPrefixInvMap t 2 (canonicalPrefixMap t 2 z) =
        prefixLabelUnstep (canonicalPrefixLabelOfRho (prefixRho t z) 2)
          (canonicalPrefixMap t 2 z) by
      simp [canonicalPrefixInvMap, canonicalPrefixInvLabel_after_map_two]]
    simp [canonicalPrefixMap, prefixLabelUnstep_step]
  · intro z
    rw [show canonicalPrefixMap t 2 (canonicalPrefixInvMap t 2 z) =
        prefixLabelStep (canonicalPrefixInvLabel t 2 z)
          (canonicalPrefixInvMap t 2 z) by
      simp [canonicalPrefixMap, canonicalPrefixLabel_after_inv_two]]
    simp [canonicalPrefixInvMap, prefixLabelStep_unstep]


theorem canonicalPrefixInvLabel_after_map_three {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixInvLabel t 3 (canonicalPrefixMap t 3 z) =
      canonicalPrefixLabelOfRho (prefixRho t z) 3 := by
  change (if ∃ k : Fin 6, k.val < 2 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7)) z k = t - 1
      then (3 : Fin 7) else (2 : Fin 7)) =
    (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 2 ∧ z k = t
  · have hr := (prefixRho_lt_three_iff_exists_lt_two t z).2 h
    have hs : ∃ k : Fin 6, k.val < 2 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7)) z k = t - 1 :=
      (exists_fin6_lt_two_step_eq z t (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 3 <;> simp [hr'])).mpr h
    rw [if_pos hs, if_pos hr]
  · have hr := mt (prefixRho_lt_three_iff_exists_lt_two t z).1 h
    have hs : ¬ ∃ k : Fin 6, k.val < 2 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7)) z k = t - 1 := by
      intro hs
      exact h ((exists_fin6_lt_two_step_eq z t (if (prefixRho t z).1.val < 3 then (3 : Fin 7) else (2 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 3 <;> simp [hr'])).mp hs)
    rw [if_neg hs, if_neg hr]

theorem canonicalPrefixLabel_after_inv_three {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixLabelOfRho (prefixRho t (canonicalPrefixInvMap t 3 z)) 3 =
      canonicalPrefixInvLabel t 3 z := by
  change (if (prefixRho t (prefixLabelUnstep (if ∃ k : Fin 6, k.val < 2 ∧ z k = t - 1 then (3 : Fin 7) else (2 : Fin 7)) z)).1.val < 3
      then (3 : Fin 7) else (2 : Fin 7)) =
    (if ∃ k : Fin 6, k.val < 2 ∧ z k = t - 1 then (3 : Fin 7) else (2 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 2 ∧ z k = t - 1
  · have hs : ∃ k : Fin 6, k.val < 2 ∧ prefixLabelUnstep (3 : Fin 7) z k = t :=
      (exists_fin6_lt_two_unstep_eq z t (3 : Fin 7) (by decide)).mpr h
    have hr : (prefixRho t (prefixLabelUnstep (3 : Fin 7) z)).1.val < 3 :=
      (prefixRho_lt_three_iff_exists_lt_two t (prefixLabelUnstep (3 : Fin 7) z)).2 hs
    rw [if_pos h, if_pos hr]
  · have hs : ¬ ∃ k : Fin 6, k.val < 2 ∧ prefixLabelUnstep (2 : Fin 7) z k = t := by
      intro hs
      exact h ((exists_fin6_lt_two_unstep_eq z t (2 : Fin 7) (by decide)).mp hs)
    have hr : ¬ (prefixRho t (prefixLabelUnstep (2 : Fin 7) z)).1.val < 3 := by
      intro hr
      exact hs ((prefixRho_lt_three_iff_exists_lt_two t (prefixLabelUnstep (2 : Fin 7) z)).1 hr)
    rw [if_neg h, if_neg hr]

theorem canonicalPrefixLayerInverse_three {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 3 (canonicalPrefixMap t 3 z) = z) ∧
      (∀ z, canonicalPrefixMap t 3 (canonicalPrefixInvMap t 3 z) = z) := by
  constructor
  · intro z
    rw [show canonicalPrefixInvMap t 3 (canonicalPrefixMap t 3 z) =
        prefixLabelUnstep (canonicalPrefixLabelOfRho (prefixRho t z) 3)
          (canonicalPrefixMap t 3 z) by
      simp [canonicalPrefixInvMap, canonicalPrefixInvLabel_after_map_three]]
    simp [canonicalPrefixMap, prefixLabelUnstep_step]
  · intro z
    rw [show canonicalPrefixMap t 3 (canonicalPrefixInvMap t 3 z) =
        prefixLabelStep (canonicalPrefixInvLabel t 3 z)
          (canonicalPrefixInvMap t 3 z) by
      simp [canonicalPrefixMap, canonicalPrefixLabel_after_inv_three]]
    simp [canonicalPrefixInvMap, prefixLabelStep_unstep]


theorem canonicalPrefixInvLabel_after_map_four {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixInvLabel t 4 (canonicalPrefixMap t 4 z) =
      canonicalPrefixLabelOfRho (prefixRho t z) 4 := by
  change (if ∃ k : Fin 6, k.val < 3 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7)) z k = t - 1
      then (4 : Fin 7) else (3 : Fin 7)) =
    (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 3 ∧ z k = t
  · have hr := (prefixRho_lt_four_iff_exists_lt_three t z).2 h
    have hs : ∃ k : Fin 6, k.val < 3 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7)) z k = t - 1 :=
      (exists_fin6_lt_three_step_eq z t (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 4 <;> simp [hr'])).mpr h
    rw [if_pos hs, if_pos hr]
  · have hr := mt (prefixRho_lt_four_iff_exists_lt_three t z).1 h
    have hs : ¬ ∃ k : Fin 6, k.val < 3 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7)) z k = t - 1 := by
      intro hs
      exact h ((exists_fin6_lt_three_step_eq z t (if (prefixRho t z).1.val < 4 then (4 : Fin 7) else (3 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 4 <;> simp [hr'])).mp hs)
    rw [if_neg hs, if_neg hr]

theorem canonicalPrefixLabel_after_inv_four {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixLabelOfRho (prefixRho t (canonicalPrefixInvMap t 4 z)) 4 =
      canonicalPrefixInvLabel t 4 z := by
  change (if (prefixRho t (prefixLabelUnstep (if ∃ k : Fin 6, k.val < 3 ∧ z k = t - 1 then (4 : Fin 7) else (3 : Fin 7)) z)).1.val < 4
      then (4 : Fin 7) else (3 : Fin 7)) =
    (if ∃ k : Fin 6, k.val < 3 ∧ z k = t - 1 then (4 : Fin 7) else (3 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 3 ∧ z k = t - 1
  · have hs : ∃ k : Fin 6, k.val < 3 ∧ prefixLabelUnstep (4 : Fin 7) z k = t :=
      (exists_fin6_lt_three_unstep_eq z t (4 : Fin 7) (by decide)).mpr h
    have hr : (prefixRho t (prefixLabelUnstep (4 : Fin 7) z)).1.val < 4 :=
      (prefixRho_lt_four_iff_exists_lt_three t (prefixLabelUnstep (4 : Fin 7) z)).2 hs
    rw [if_pos h, if_pos hr]
  · have hs : ¬ ∃ k : Fin 6, k.val < 3 ∧ prefixLabelUnstep (3 : Fin 7) z k = t := by
      intro hs
      exact h ((exists_fin6_lt_three_unstep_eq z t (3 : Fin 7) (by decide)).mp hs)
    have hr : ¬ (prefixRho t (prefixLabelUnstep (3 : Fin 7) z)).1.val < 4 := by
      intro hr
      exact hs ((prefixRho_lt_four_iff_exists_lt_three t (prefixLabelUnstep (3 : Fin 7) z)).1 hr)
    rw [if_neg h, if_neg hr]

theorem canonicalPrefixLayerInverse_four {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 4 (canonicalPrefixMap t 4 z) = z) ∧
      (∀ z, canonicalPrefixMap t 4 (canonicalPrefixInvMap t 4 z) = z) := by
  constructor
  · intro z
    rw [show canonicalPrefixInvMap t 4 (canonicalPrefixMap t 4 z) =
        prefixLabelUnstep (canonicalPrefixLabelOfRho (prefixRho t z) 4)
          (canonicalPrefixMap t 4 z) by
      simp [canonicalPrefixInvMap, canonicalPrefixInvLabel_after_map_four]]
    simp [canonicalPrefixMap, prefixLabelUnstep_step]
  · intro z
    rw [show canonicalPrefixMap t 4 (canonicalPrefixInvMap t 4 z) =
        prefixLabelStep (canonicalPrefixInvLabel t 4 z)
          (canonicalPrefixInvMap t 4 z) by
      simp [canonicalPrefixMap, canonicalPrefixLabel_after_inv_four]]
    simp [canonicalPrefixInvMap, prefixLabelStep_unstep]


theorem canonicalPrefixInvLabel_after_map_five {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixInvLabel t 5 (canonicalPrefixMap t 5 z) =
      canonicalPrefixLabelOfRho (prefixRho t z) 5 := by
  change (if ∃ k : Fin 6, k.val < 4 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7)) z k = t - 1
      then (5 : Fin 7) else (4 : Fin 7)) =
    (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 4 ∧ z k = t
  · have hr := (prefixRho_lt_five_iff_exists_lt_four t z).2 h
    have hs : ∃ k : Fin 6, k.val < 4 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7)) z k = t - 1 :=
      (exists_fin6_lt_four_step_eq z t (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 5 <;> simp [hr'])).mpr h
    rw [if_pos hs, if_pos hr]
  · have hr := mt (prefixRho_lt_five_iff_exists_lt_four t z).1 h
    have hs : ¬ ∃ k : Fin 6, k.val < 4 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7)) z k = t - 1 := by
      intro hs
      exact h ((exists_fin6_lt_four_step_eq z t (if (prefixRho t z).1.val < 5 then (5 : Fin 7) else (4 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 5 <;> simp [hr'])).mp hs)
    rw [if_neg hs, if_neg hr]

theorem canonicalPrefixLabel_after_inv_five {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixLabelOfRho (prefixRho t (canonicalPrefixInvMap t 5 z)) 5 =
      canonicalPrefixInvLabel t 5 z := by
  change (if (prefixRho t (prefixLabelUnstep (if ∃ k : Fin 6, k.val < 4 ∧ z k = t - 1 then (5 : Fin 7) else (4 : Fin 7)) z)).1.val < 5
      then (5 : Fin 7) else (4 : Fin 7)) =
    (if ∃ k : Fin 6, k.val < 4 ∧ z k = t - 1 then (5 : Fin 7) else (4 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 4 ∧ z k = t - 1
  · have hs : ∃ k : Fin 6, k.val < 4 ∧ prefixLabelUnstep (5 : Fin 7) z k = t :=
      (exists_fin6_lt_four_unstep_eq z t (5 : Fin 7) (by decide)).mpr h
    have hr : (prefixRho t (prefixLabelUnstep (5 : Fin 7) z)).1.val < 5 :=
      (prefixRho_lt_five_iff_exists_lt_four t (prefixLabelUnstep (5 : Fin 7) z)).2 hs
    rw [if_pos h, if_pos hr]
  · have hs : ¬ ∃ k : Fin 6, k.val < 4 ∧ prefixLabelUnstep (4 : Fin 7) z k = t := by
      intro hs
      exact h ((exists_fin6_lt_four_unstep_eq z t (4 : Fin 7) (by decide)).mp hs)
    have hr : ¬ (prefixRho t (prefixLabelUnstep (4 : Fin 7) z)).1.val < 5 := by
      intro hr
      exact hs ((prefixRho_lt_five_iff_exists_lt_four t (prefixLabelUnstep (4 : Fin 7) z)).1 hr)
    rw [if_neg h, if_neg hr]

theorem canonicalPrefixLayerInverse_five {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 5 (canonicalPrefixMap t 5 z) = z) ∧
      (∀ z, canonicalPrefixMap t 5 (canonicalPrefixInvMap t 5 z) = z) := by
  constructor
  · intro z
    rw [show canonicalPrefixInvMap t 5 (canonicalPrefixMap t 5 z) =
        prefixLabelUnstep (canonicalPrefixLabelOfRho (prefixRho t z) 5)
          (canonicalPrefixMap t 5 z) by
      simp [canonicalPrefixInvMap, canonicalPrefixInvLabel_after_map_five]]
    simp [canonicalPrefixMap, prefixLabelUnstep_step]
  · intro z
    rw [show canonicalPrefixMap t 5 (canonicalPrefixInvMap t 5 z) =
        prefixLabelStep (canonicalPrefixInvLabel t 5 z)
          (canonicalPrefixInvMap t 5 z) by
      simp [canonicalPrefixMap, canonicalPrefixLabel_after_inv_five]]
    simp [canonicalPrefixInvMap, prefixLabelStep_unstep]


theorem canonicalPrefixInvLabel_after_map_six {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixInvLabel t 6 (canonicalPrefixMap t 6 z) =
      canonicalPrefixLabelOfRho (prefixRho t z) 6 := by
  change (if ∃ k : Fin 6, k.val < 5 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7)) z k = t - 1
      then (6 : Fin 7) else (5 : Fin 7)) =
    (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 5 ∧ z k = t
  · have hr := (prefixRho_lt_six_iff_exists_lt_five t z).2 h
    have hs : ∃ k : Fin 6, k.val < 5 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7)) z k = t - 1 :=
      (exists_fin6_lt_five_step_eq z t (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 6 <;> simp [hr'])).mpr h
    rw [if_pos hs, if_pos hr]
  · have hr := mt (prefixRho_lt_six_iff_exists_lt_five t z).1 h
    have hs : ¬ ∃ k : Fin 6, k.val < 5 ∧
        prefixLabelStep (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7)) z k = t - 1 := by
      intro hs
      exact h ((exists_fin6_lt_five_step_eq z t (if (prefixRho t z).1.val < 6 then (6 : Fin 7) else (5 : Fin 7)) (by
        by_cases hr' : (prefixRho t z).1.val < 6 <;> simp [hr'])).mp hs)
    rw [if_neg hs, if_neg hr]

theorem canonicalPrefixLabel_after_inv_six {m : Nat} [NeZero m]
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    canonicalPrefixLabelOfRho (prefixRho t (canonicalPrefixInvMap t 6 z)) 6 =
      canonicalPrefixInvLabel t 6 z := by
  change (if (prefixRho t (prefixLabelUnstep (if ∃ k : Fin 6, k.val < 5 ∧ z k = t - 1 then (6 : Fin 7) else (5 : Fin 7)) z)).1.val < 6
      then (6 : Fin 7) else (5 : Fin 7)) =
    (if ∃ k : Fin 6, k.val < 5 ∧ z k = t - 1 then (6 : Fin 7) else (5 : Fin 7))
  by_cases h : ∃ k : Fin 6, k.val < 5 ∧ z k = t - 1
  · have hs : ∃ k : Fin 6, k.val < 5 ∧ prefixLabelUnstep (6 : Fin 7) z k = t :=
      (exists_fin6_lt_five_unstep_eq z t (6 : Fin 7) (by decide)).mpr h
    have hr : (prefixRho t (prefixLabelUnstep (6 : Fin 7) z)).1.val < 6 :=
      (prefixRho_lt_six_iff_exists_lt_five t (prefixLabelUnstep (6 : Fin 7) z)).2 hs
    rw [if_pos h, if_pos hr]
  · have hs : ¬ ∃ k : Fin 6, k.val < 5 ∧ prefixLabelUnstep (5 : Fin 7) z k = t := by
      intro hs
      exact h ((exists_fin6_lt_five_unstep_eq z t (5 : Fin 7) (by decide)).mp hs)
    have hr : ¬ (prefixRho t (prefixLabelUnstep (5 : Fin 7) z)).1.val < 6 := by
      intro hr
      exact hs ((prefixRho_lt_six_iff_exists_lt_five t (prefixLabelUnstep (5 : Fin 7) z)).1 hr)
    rw [if_neg h, if_neg hr]

theorem canonicalPrefixLayerInverse_six {m : Nat} [NeZero m] (t : ZMod m) :
    (∀ z, canonicalPrefixInvMap t 6 (canonicalPrefixMap t 6 z) = z) ∧
      (∀ z, canonicalPrefixMap t 6 (canonicalPrefixInvMap t 6 z) = z) := by
  constructor
  · intro z
    rw [show canonicalPrefixInvMap t 6 (canonicalPrefixMap t 6 z) =
        prefixLabelUnstep (canonicalPrefixLabelOfRho (prefixRho t z) 6)
          (canonicalPrefixMap t 6 z) by
      simp [canonicalPrefixInvMap, canonicalPrefixInvLabel_after_map_six]]
    simp [canonicalPrefixMap, prefixLabelUnstep_step]
  · intro z
    rw [show canonicalPrefixMap t 6 (canonicalPrefixInvMap t 6 z) =
        prefixLabelStep (canonicalPrefixInvLabel t 6 z)
          (canonicalPrefixInvMap t 6 z) by
      simp [canonicalPrefixMap, canonicalPrefixLabel_after_inv_six]]
    simp [canonicalPrefixInvMap, prefixLabelStep_unstep]

theorem canonicalDirOfRho_bijective (rho : Rho6) :
    Function.Bijective (canonicalDirOfRho rho) := by
  rcases rho with ⟨rho, hrho⟩
  fin_cases rho
  · norm_num at hrho
  · change Function.Bijective (canonicalDirOfRho (⟨1, by decide⟩ : Rho6))
    native_decide
  · change Function.Bijective (canonicalDirOfRho (⟨2, by decide⟩ : Rho6))
    native_decide
  · change Function.Bijective (canonicalDirOfRho (⟨3, by decide⟩ : Rho6))
    native_decide
  · change Function.Bijective (canonicalDirOfRho (⟨4, by decide⟩ : Rho6))
    native_decide
  · change Function.Bijective (canonicalDirOfRho (⟨5, by decide⟩ : Rho6))
    native_decide
  · change Function.Bijective (canonicalDirOfRho (⟨6, by decide⟩ : Rho6))
    native_decide

theorem canonicalLayerDir_bijective {m : Nat} (t : ZMod m) (w : RootState7 m) :
    Function.Bijective (canonicalLayerDir t w) :=
  canonicalDirOfRho_bijective (canonicalRho t w)

def countMatrixScheduleAt {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (t : ZMod m) : SymbolPerm7 :=
  P.schedule.get ⟨t.val, by
    simpa [P.length_eq] using ZMod.val_lt t⟩

theorem countMatrixScheduleAt_latin {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (t : ZMod m) :
    Function.Bijective (countMatrixScheduleAt P t) := by
  have hmem := List.get_mem P.schedule ⟨t.val, by
    simpa [P.length_eq] using ZMod.val_lt t⟩
  exact (List.forall_iff_forall_mem.mp (by simpa [scheduleListLatin] using P.latin))
    (countMatrixScheduleAt P t) hmem

def canonicalRootFlatSchedule {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) : RootFlatSchedule m where
  dir := fun t w c => canonicalLayerDir t w ((countMatrixScheduleAt P t) c)

theorem canonicalRootFlatSchedule_rowLatin {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) :
    (canonicalRootFlatSchedule P).rowLatin := by
  intro t w
  simpa [canonicalRootFlatSchedule] using
    Function.Bijective.comp
      (canonicalLayerDir_bijective t w)
      (countMatrixScheduleAt_latin P t)

def canonicalLayerMap {m : Nat} (t : ZMod m) (sym : CanonSym) :
    RootState7 m → RootState7 m :=
  fun w => addQRoot m (canonicalLayerDir t w sym) w

def canonicalLayerInv {m : Nat} (t : ZMod m) (sym : CanonSym) :
    RootState7 m → RootState7 m :=
  fun w => subQRoot m (prefixLabelToDirection
    (canonicalPrefixInvLabel t sym (rootPrefixCoord w))) w

theorem rootPrefixCoord_canonicalLayerMap {m : Nat}
    (t : ZMod m) (sym : CanonSym) (w : RootState7 m) :
    rootPrefixCoord (canonicalLayerMap t sym w) =
      canonicalPrefixMap t sym (rootPrefixCoord w) := by
  simp [canonicalLayerMap, canonicalPrefixMap, canonicalLayerDir, canonicalRho,
    canonicalDirOfRho, rootPrefixCoord_addQRoot_prefixLabel]

theorem rootOfPrefix_canonicalPrefixMap {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) :
    rootOfPrefix (canonicalPrefixMap t sym z) =
      canonicalLayerMap t sym (rootOfPrefix z) := by
  apply rootPrefixCoord_bijective.1
  rw [rootPrefixCoord_rootOfPrefix, rootPrefixCoord_canonicalLayerMap,
    rootPrefixCoord_rootOfPrefix]

theorem rootPrefixCoord_canonicalLayerInv {m : Nat}
    (t : ZMod m) (sym : CanonSym) (w : RootState7 m) :
    rootPrefixCoord (canonicalLayerInv t sym w) =
      canonicalPrefixInvMap t sym (rootPrefixCoord w) := by
  simp [canonicalLayerInv, canonicalPrefixInvMap,
    rootPrefixCoord_subQRoot_prefixLabel]

theorem rootOfPrefix_canonicalPrefixInvMap {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) :
    rootOfPrefix (canonicalPrefixInvMap t sym z) =
      canonicalLayerInv t sym (rootOfPrefix z) := by
  apply rootPrefixCoord_bijective.1
  rw [rootPrefixCoord_rootOfPrefix, rootPrefixCoord_canonicalLayerInv,
    rootPrefixCoord_rootOfPrefix]

def CanonicalPrefixLayerBijectiveTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (t : ZMod m) (sym : CanonSym),
    Function.Bijective (canonicalPrefixMap t sym)

def CanonicalPrefixLayerInverseTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (t : ZMod m) (sym : CanonSym),
    (∀ z, canonicalPrefixInvMap t sym (canonicalPrefixMap t sym z) = z) ∧
      (∀ z, canonicalPrefixMap t sym (canonicalPrefixInvMap t sym z) = z)

theorem canonicalPrefixLayerInverse : CanonicalPrefixLayerInverseTheorem := by
  intro m _ t sym
  fin_cases sym
  · exact canonicalPrefixLayerInverse_zero t
  · exact canonicalPrefixLayerInverse_delta t
  · exact canonicalPrefixLayerInverse_two t
  · exact canonicalPrefixLayerInverse_three t
  · exact canonicalPrefixLayerInverse_four t
  · exact canonicalPrefixLayerInverse_five t
  · exact canonicalPrefixLayerInverse_six t


theorem canonicalPrefixLayerBijective_of_inverse
    (hinv : CanonicalPrefixLayerInverseTheorem) :
    CanonicalPrefixLayerBijectiveTheorem := by
  intro m _ t sym
  exact bijective_of_inverse (canonicalPrefixMap t sym) (canonicalPrefixInvMap t sym)
    (hinv t sym).1 (hinv t sym).2

def CanonicalLayerBijectiveTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (t : ZMod m) (sym : CanonSym),
    Function.Bijective (canonicalLayerMap t sym)

theorem canonicalLayerBijective_of_prefix
    (hprefix : CanonicalPrefixLayerBijectiveTheorem) :
    CanonicalLayerBijectiveTheorem := by
  intro m _ t sym
  exact bijective_of_bijective_semiconj
    (f := canonicalPrefixMap t sym)
    (g := canonicalLayerMap t sym)
    (φ := rootOfPrefix)
    rootOfPrefix_bijective
    (rootOfPrefix_canonicalPrefixMap t sym)
    (hprefix t sym)

theorem canonicalLayerBijective_of_prefix_inverse
    (hinv : CanonicalPrefixLayerInverseTheorem) :
    CanonicalLayerBijectiveTheorem :=
  canonicalLayerBijective_of_prefix
    (canonicalPrefixLayerBijective_of_inverse hinv)

theorem canonicalLayerBijective : CanonicalLayerBijectiveTheorem :=
  canonicalLayerBijective_of_prefix_inverse canonicalPrefixLayerInverse

def CanonicalReturnSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) →
      (canonicalRootFlatSchedule P).returnsSingleCycle

def canonicalPrefixScheduleReturn {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) :
    (Fin 6 → ZMod m) → (Fin 6 → ZMod m) :=
  fun z => (List.range m).foldl
    (fun x (t : Nat) =>
      canonicalPrefixMap (t : ZMod m) ((countMatrixScheduleAt P (t : ZMod m)) c) x)
    z

def canonicalPrefixWordAt {m : Nat} (W : List CanonSym) (t : ZMod m) : CanonSym :=
  if h : t.val < W.length then W.get ⟨t.val, h⟩ else 0

def canonicalPrefixWordReturn {m : Nat} [NeZero m] (W : List CanonSym) :
    (Fin 6 → ZMod m) → (Fin 6 → ZMod m) :=
  fun z => (List.range m).foldl
    (fun x (t : Nat) =>
      canonicalPrefixMap (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m)) x)
    z

theorem foldl_eq_of_forall_mem {α β : Type*} (L : List β) (f g : α → β → α)
    (h : ∀ x b, b ∈ L → f x b = g x b) :
    ∀ x, L.foldl f x = L.foldl g x := by
  induction L with
  | nil =>
      intro x
      rfl
  | cons b L ih =>
      intro x
      rw [List.foldl_cons, List.foldl_cons]
      rw [h x b (by simp)]
      exact ih (by
        intro y b' hb'
        exact h y b' (by simp [hb'])) (g x b)

theorem canonicalPrefixWordAt_schedule {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) (t : Nat) (ht : t < m) :
    canonicalPrefixWordAt (canonicalWord P.schedule c) (t : ZMod m) =
      (countMatrixScheduleAt P (t : ZMod m)) c := by
  simp [canonicalPrefixWordAt, countMatrixScheduleAt, canonicalWord,
    ZMod.val_natCast_of_lt ht, P.length_eq, ht]

theorem canonicalPrefixScheduleReturn_eq_word {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) :
    canonicalPrefixScheduleReturn P c =
      canonicalPrefixWordReturn (canonicalWord P.schedule c) := by
  funext z
  unfold canonicalPrefixScheduleReturn canonicalPrefixWordReturn
  apply foldl_eq_of_forall_mem
  intro x t ht
  rw [canonicalPrefixWordAt_schedule P c t (List.mem_range.mp ht)]

theorem canonicalPrefixMap_coord {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) (k : Fin 6) :
    canonicalPrefixMap t sym z k =
      z k - if k.val < (canonicalPrefixLabelOfRho (prefixRho t z) sym).val then 1 else 0 := by
  rfl

theorem canonicalPrefixMap_coord_zero {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 0 = z 0 - if sym = 0 then 0 else 1 := by
  have hpos : 0 < (prefixRho t z).1.val := by
    have h := (prefixRho t z).2
    omega
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep]
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, hpos]
  · by_cases h : (prefixRho t z).1.val < (2 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (3 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (4 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (5 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (6 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]

theorem canonicalPrefixMap_coord_one {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 1 =
      z 1 -
        if sym = 0 then 0
        else if sym = 1 then if z 0 = t then 0 else 1
        else if sym = 2 then if z 0 = t then 1 else 0
        else 1 := by
  have hρ := prefixRho_eq_one_iff t z
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep]
  · by_cases h0 : z 0 = t
    · have hr : (prefixRho t z).1 = (1 : Fin 7) := hρ.2 h0
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h0, hr]
    · have hr : (prefixRho t z).1 ≠ (1 : Fin 7) := fun h => h0 (hρ.1 h)
      have hval : ¬ (prefixRho t z).1.val ≤ 1 := by
        intro hle
        have hge := (prefixRho t z).2
        have heq : (prefixRho t z).1.val = 1 := by omega
        exact hr (Fin.ext heq)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h0, hval]
  · by_cases h0 : z 0 = t
    · have hr : (prefixRho t z).1 = (1 : Fin 7) := hρ.2 h0
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h0, hr]
    · have hr : (prefixRho t z).1 ≠ (1 : Fin 7) := fun h => h0 (hρ.1 h)
      have hval : ¬ (prefixRho t z).1.val < 2 := by
        intro hlt
        have hge := (prefixRho t z).2
        have heq : (prefixRho t z).1.val = 1 := by omega
        exact hr (Fin.ext heq)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h0, hval]
  · by_cases h : (prefixRho t z).1.val < (3 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (4 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (5 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]
  · by_cases h : (prefixRho t z).1.val < (6 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep, h]

def canonicalPrefixCoordOneDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  if sym = 0 then 0
  else if sym = 1 then if z 0 = t then 0 else 1
  else if sym = 2 then if z 0 = t then 1 else 0
  else 1

theorem canonicalPrefixMap_coord_one_debit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 1 =
      z 1 - canonicalPrefixCoordOneDebit t sym z := by
  simpa [canonicalPrefixCoordOneDebit] using canonicalPrefixMap_coord_one t sym z

theorem canonicalPrefixCoordOneDebit_eq_of_coord_zero_eq {m : Nat}
    {t : ZMod m} {sym : CanonSym} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) :
    canonicalPrefixCoordOneDebit t sym z' =
      canonicalPrefixCoordOneDebit t sym z := by
  simp [canonicalPrefixCoordOneDebit, h0]

theorem canonicalPrefixMap_coord_zero_eq_of_coord_zero_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) :
    canonicalPrefixMap t sym z' 0 = canonicalPrefixMap t sym z 0 := by
  rw [canonicalPrefixMap_coord_zero, canonicalPrefixMap_coord_zero, h0]

theorem canonicalPrefixMap_coord_one_add_of_coord_zero_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (d : ZMod m) (h0 : z' 0 = z 0) (h1 : z' 1 = z 1 + d) :
    canonicalPrefixMap t sym z' 1 =
      canonicalPrefixMap t sym z 1 + d := by
  rw [canonicalPrefixMap_coord_one_debit, canonicalPrefixMap_coord_one_debit]
  rw [canonicalPrefixCoordOneDebit_eq_of_coord_zero_eq h0, h1]
  ring

def canonicalPrefixCoordTwoHit {m : Nat} (t : ZMod m) (z : Fin 6 → ZMod m) : Prop :=
  ∃ k : Fin 6, k.val < 2 ∧ z k = t

theorem canonicalPrefixCoordTwoHit_iff {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixCoordTwoHit t z ↔ z 0 = t ∨ z 1 = t := by
  simpa [canonicalPrefixCoordTwoHit] using exists_fin6_lt_two_eq z t

instance canonicalPrefixCoordTwoHit_decidable {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    Decidable (canonicalPrefixCoordTwoHit t z) := by
  unfold canonicalPrefixCoordTwoHit
  infer_instance

def canonicalPrefixCoordTwoDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  if sym = 0 then 0
  else if sym = 1 then if canonicalPrefixCoordTwoHit t z then 0 else 1
  else if sym = 2 then 0
  else if sym = 3 then if canonicalPrefixCoordTwoHit t z then 1 else 0
  else 1

theorem canonicalPrefixMap_coord_two {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 2 =
      z 2 - canonicalPrefixCoordTwoDebit t sym z := by
  have hρ := prefixRho_lt_three_iff_exists_lt_two t z
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
      canonicalPrefixCoordTwoDebit]
  · by_cases hhit : canonicalPrefixCoordTwoHit t z
    · have hr : (prefixRho t z).1.val < 3 := hρ.2 hhit
      have hnot : ¬ 2 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, hhit, hnot]
    · have hr : ¬ (prefixRho t z).1.val < 3 := fun h => hhit (hρ.1 h)
      have hgt : 2 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, hhit, hgt]
  · by_cases h : (prefixRho t z).1.val < (2 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, h]
  · by_cases hhit : canonicalPrefixCoordTwoHit t z
    · have hr : (prefixRho t z).1.val < 3 := hρ.2 hhit
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, hhit, hr]
    · have hr : ¬ (prefixRho t z).1.val < 3 := fun h => hhit (hρ.1 h)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, hhit, hr]
  · by_cases h : (prefixRho t z).1.val < (4 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, h]
  · by_cases h : (prefixRho t z).1.val < (5 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, h]
  · by_cases h : (prefixRho t z).1.val < (6 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordTwoDebit, h]

theorem canonicalPrefixCoordTwoHit_iff_of_coord_zero_one_eq {m : Nat}
    {t : ZMod m} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) :
    canonicalPrefixCoordTwoHit t z' ↔ canonicalPrefixCoordTwoHit t z := by
  simp [canonicalPrefixCoordTwoHit_iff, h0, h1]

theorem canonicalPrefixCoordTwoDebit_eq_of_coord_zero_one_eq {m : Nat}
    {t : ZMod m} {sym : CanonSym} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) :
    canonicalPrefixCoordTwoDebit t sym z' =
      canonicalPrefixCoordTwoDebit t sym z := by
  have hhit := canonicalPrefixCoordTwoHit_iff_of_coord_zero_one_eq
    (t := t) h0 h1
  by_cases hz' : canonicalPrefixCoordTwoHit t z'
  · have hz : canonicalPrefixCoordTwoHit t z := hhit.mp hz'
    simp [canonicalPrefixCoordTwoDebit, hz', hz]
  · have hz : ¬ canonicalPrefixCoordTwoHit t z := fun h => hz' (hhit.mpr h)
    simp [canonicalPrefixCoordTwoDebit, hz', hz]

theorem canonicalPrefixMap_coord_two_add_of_coord_zero_one_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (d : ZMod m) (h0 : z' 0 = z 0) (h1 : z' 1 = z 1)
    (h2 : z' 2 = z 2 + d) :
    canonicalPrefixMap t sym z' 2 =
      canonicalPrefixMap t sym z 2 + d := by
  rw [canonicalPrefixMap_coord_two, canonicalPrefixMap_coord_two]
  rw [canonicalPrefixCoordTwoDebit_eq_of_coord_zero_one_eq h0 h1, h2]
  ring

def canonicalPrefixCoordThreeHit {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) : Prop :=
  ∃ k : Fin 6, k.val < 3 ∧ z k = t

theorem canonicalPrefixCoordThreeHit_iff {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixCoordThreeHit t z ↔
      z 0 = t ∨ z 1 = t ∨ z 2 = t := by
  simpa [canonicalPrefixCoordThreeHit] using exists_fin6_lt_three_eq z t

instance canonicalPrefixCoordThreeHit_decidable {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    Decidable (canonicalPrefixCoordThreeHit t z) := by
  unfold canonicalPrefixCoordThreeHit
  infer_instance

def canonicalPrefixCoordThreeDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  if sym = 0 then 0
  else if sym = 1 then if canonicalPrefixCoordThreeHit t z then 0 else 1
  else if sym = 2 then 0
  else if sym = 3 then 0
  else if sym = 4 then if canonicalPrefixCoordThreeHit t z then 1 else 0
  else 1

theorem canonicalPrefixMap_coord_three {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 3 =
      z 3 - canonicalPrefixCoordThreeDebit t sym z := by
  have hρ := prefixRho_lt_four_iff_exists_lt_three t z
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
      canonicalPrefixCoordThreeDebit]
  · by_cases hhit : canonicalPrefixCoordThreeHit t z
    · have hr : (prefixRho t z).1.val < 4 := hρ.2 hhit
      have hnot : ¬ 3 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, hhit, hnot]
    · have hr : ¬ (prefixRho t z).1.val < 4 := fun h => hhit (hρ.1 h)
      have hgt : 3 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, hhit, hgt]
  · by_cases h : (prefixRho t z).1.val < (2 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, h]
  · by_cases h : (prefixRho t z).1.val < (3 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, h]
  · by_cases hhit : canonicalPrefixCoordThreeHit t z
    · have hr : (prefixRho t z).1.val < 4 := hρ.2 hhit
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, hhit, hr]
    · have hr : ¬ (prefixRho t z).1.val < 4 := fun h => hhit (hρ.1 h)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, hhit, hr]
  · by_cases h : (prefixRho t z).1.val < (5 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, h]
  · by_cases h : (prefixRho t z).1.val < (6 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordThreeDebit, h]

theorem canonicalPrefixCoordThreeHit_iff_of_coord_zero_one_two_eq {m : Nat}
    {t : ZMod m} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2) :
    canonicalPrefixCoordThreeHit t z' ↔ canonicalPrefixCoordThreeHit t z := by
  simp [canonicalPrefixCoordThreeHit_iff, h0, h1, h2]

theorem canonicalPrefixCoordThreeDebit_eq_of_coord_zero_one_two_eq {m : Nat}
    {t : ZMod m} {sym : CanonSym} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2) :
    canonicalPrefixCoordThreeDebit t sym z' =
      canonicalPrefixCoordThreeDebit t sym z := by
  have hhit := canonicalPrefixCoordThreeHit_iff_of_coord_zero_one_two_eq
    (t := t) h0 h1 h2
  by_cases hz' : canonicalPrefixCoordThreeHit t z'
  · have hz : canonicalPrefixCoordThreeHit t z := hhit.mp hz'
    simp [canonicalPrefixCoordThreeDebit, hz', hz]
  · have hz : ¬ canonicalPrefixCoordThreeHit t z := fun h => hz' (hhit.mpr h)
    simp [canonicalPrefixCoordThreeDebit, hz', hz]

theorem canonicalPrefixMap_coord_three_add_of_coord_zero_one_two_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (d : ZMod m) (h0 : z' 0 = z 0) (h1 : z' 1 = z 1)
    (h2 : z' 2 = z 2) (h3 : z' 3 = z 3 + d) :
    canonicalPrefixMap t sym z' 3 =
      canonicalPrefixMap t sym z 3 + d := by
  rw [canonicalPrefixMap_coord_three, canonicalPrefixMap_coord_three]
  rw [canonicalPrefixCoordThreeDebit_eq_of_coord_zero_one_two_eq h0 h1 h2, h3]
  ring

def canonicalPrefixCoordFourHit {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) : Prop :=
  ∃ k : Fin 6, k.val < 4 ∧ z k = t

theorem canonicalPrefixCoordFourHit_iff {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixCoordFourHit t z ↔
      z 0 = t ∨ z 1 = t ∨ z 2 = t ∨ z 3 = t := by
  simpa [canonicalPrefixCoordFourHit] using exists_fin6_lt_four_eq z t

instance canonicalPrefixCoordFourHit_decidable {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    Decidable (canonicalPrefixCoordFourHit t z) := by
  unfold canonicalPrefixCoordFourHit
  infer_instance

def canonicalPrefixCoordFourDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  if sym = 0 then 0
  else if sym = 1 then if canonicalPrefixCoordFourHit t z then 0 else 1
  else if sym = 2 then 0
  else if sym = 3 then 0
  else if sym = 4 then 0
  else if sym = 5 then if canonicalPrefixCoordFourHit t z then 1 else 0
  else 1

theorem canonicalPrefixMap_coord_four {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 4 =
      z 4 - canonicalPrefixCoordFourDebit t sym z := by
  have hρ := prefixRho_lt_five_iff_exists_lt_four t z
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
      canonicalPrefixCoordFourDebit]
  · by_cases hhit : canonicalPrefixCoordFourHit t z
    · have hr : (prefixRho t z).1.val < 5 := hρ.2 hhit
      have hnot : ¬ 4 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, hhit, hnot]
    · have hr : ¬ (prefixRho t z).1.val < 5 := fun h => hhit (hρ.1 h)
      have hgt : 4 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, hhit, hgt]
  · by_cases h : (prefixRho t z).1.val < (2 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, h]
  · by_cases h : (prefixRho t z).1.val < (3 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, h]
  · by_cases h : (prefixRho t z).1.val < (4 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, h]
  · by_cases hhit : canonicalPrefixCoordFourHit t z
    · have hr : (prefixRho t z).1.val < 5 := hρ.2 hhit
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, hhit, hr]
    · have hr : ¬ (prefixRho t z).1.val < 5 := fun h => hhit (hρ.1 h)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, hhit, hr]
  · by_cases h : (prefixRho t z).1.val < (6 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFourDebit, h]

theorem canonicalPrefixCoordFourHit_iff_of_coord_zero_one_two_three_eq {m : Nat}
    {t : ZMod m} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) :
    canonicalPrefixCoordFourHit t z' ↔ canonicalPrefixCoordFourHit t z := by
  simp [canonicalPrefixCoordFourHit_iff, h0, h1, h2, h3]

theorem canonicalPrefixCoordFourDebit_eq_of_coord_zero_one_two_three_eq {m : Nat}
    {t : ZMod m} {sym : CanonSym} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) :
    canonicalPrefixCoordFourDebit t sym z' =
      canonicalPrefixCoordFourDebit t sym z := by
  have hhit := canonicalPrefixCoordFourHit_iff_of_coord_zero_one_two_three_eq
    (t := t) h0 h1 h2 h3
  by_cases hz' : canonicalPrefixCoordFourHit t z'
  · have hz : canonicalPrefixCoordFourHit t z := hhit.mp hz'
    simp [canonicalPrefixCoordFourDebit, hz', hz]
  · have hz : ¬ canonicalPrefixCoordFourHit t z := fun h => hz' (hhit.mpr h)
    simp [canonicalPrefixCoordFourDebit, hz', hz]

theorem canonicalPrefixMap_coord_four_add_of_coord_zero_one_two_three_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (d : ZMod m) (h0 : z' 0 = z 0) (h1 : z' 1 = z 1)
    (h2 : z' 2 = z 2) (h3 : z' 3 = z 3) (h4 : z' 4 = z 4 + d) :
    canonicalPrefixMap t sym z' 4 =
      canonicalPrefixMap t sym z 4 + d := by
  rw [canonicalPrefixMap_coord_four, canonicalPrefixMap_coord_four]
  rw [canonicalPrefixCoordFourDebit_eq_of_coord_zero_one_two_three_eq h0 h1 h2 h3, h4]
  ring

def canonicalPrefixCoordFiveHit {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) : Prop :=
  ∃ k : Fin 6, k.val < 5 ∧ z k = t

theorem canonicalPrefixCoordFiveHit_iff {m : Nat} (t : ZMod m)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixCoordFiveHit t z ↔
      z 0 = t ∨ z 1 = t ∨ z 2 = t ∨ z 3 = t ∨ z 4 = t := by
  simpa [canonicalPrefixCoordFiveHit] using exists_fin6_lt_five_eq z t

instance canonicalPrefixCoordFiveHit_decidable {m : Nat}
    (t : ZMod m) (z : Fin 6 → ZMod m) :
    Decidable (canonicalPrefixCoordFiveHit t z) := by
  unfold canonicalPrefixCoordFiveHit
  infer_instance

def canonicalPrefixCoordFiveDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  if sym = 0 then 0
  else if sym = 1 then if canonicalPrefixCoordFiveHit t z then 0 else 1
  else if sym = 2 then 0
  else if sym = 3 then 0
  else if sym = 4 then 0
  else if sym = 5 then 0
  else if canonicalPrefixCoordFiveHit t z then 1 else 0

theorem canonicalPrefixMap_coord_five {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixMap t sym z 5 =
      z 5 - canonicalPrefixCoordFiveDebit t sym z := by
  have hρ := prefixRho_lt_six_iff_exists_lt_five t z
  fin_cases sym
  · simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
      canonicalPrefixCoordFiveDebit]
  · by_cases hhit : canonicalPrefixCoordFiveHit t z
    · have hr : (prefixRho t z).1.val < 6 := hρ.2 hhit
      have hnot : ¬ 5 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, hhit, hnot]
    · have hr : ¬ (prefixRho t z).1.val < 6 := fun h => hhit (hρ.1 h)
      have hgt : 5 < (prefixRho t z).1.val := by omega
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, hhit, hgt]
  · by_cases h : (prefixRho t z).1.val < (2 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, h]
  · by_cases h : (prefixRho t z).1.val < (3 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, h]
  · by_cases h : (prefixRho t z).1.val < (4 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, h]
  · by_cases h : (prefixRho t z).1.val < (5 : Nat) <;>
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, h]
  · by_cases hhit : canonicalPrefixCoordFiveHit t z
    · have hr : (prefixRho t z).1.val < 6 := hρ.2 hhit
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, hhit, hr]
    · have hr : ¬ (prefixRho t z).1.val < 6 := fun h => hhit (hρ.1 h)
      simp [canonicalPrefixMap, canonicalPrefixLabelOfRho, prefixLabelStep,
        canonicalPrefixCoordFiveDebit, hhit, hr]

theorem canonicalPrefixCoordFiveHit_iff_of_coord_zero_one_two_three_four_eq {m : Nat}
    {t : ZMod m} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) (h4 : z' 4 = z 4) :
    canonicalPrefixCoordFiveHit t z' ↔ canonicalPrefixCoordFiveHit t z := by
  simp [canonicalPrefixCoordFiveHit_iff, h0, h1, h2, h3, h4]

theorem canonicalPrefixCoordFiveDebit_eq_of_coord_zero_one_two_three_four_eq {m : Nat}
    {t : ZMod m} {sym : CanonSym} {z z' : Fin 6 → ZMod m}
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) (h4 : z' 4 = z 4) :
    canonicalPrefixCoordFiveDebit t sym z' =
      canonicalPrefixCoordFiveDebit t sym z := by
  have hhit := canonicalPrefixCoordFiveHit_iff_of_coord_zero_one_two_three_four_eq
    (t := t) h0 h1 h2 h3 h4
  by_cases hz' : canonicalPrefixCoordFiveHit t z'
  · have hz : canonicalPrefixCoordFiveHit t z := hhit.mp hz'
    simp [canonicalPrefixCoordFiveDebit, hz', hz]
  · have hz : ¬ canonicalPrefixCoordFiveHit t z := fun h => hz' (hhit.mpr h)
    simp [canonicalPrefixCoordFiveDebit, hz', hz]

theorem canonicalPrefixMap_coord_five_add_of_coord_zero_one_two_three_four_eq {m : Nat}
    (t : ZMod m) (sym : CanonSym) {z z' : Fin 6 → ZMod m}
    (d : ZMod m) (h0 : z' 0 = z 0) (h1 : z' 1 = z 1)
    (h2 : z' 2 = z 2) (h3 : z' 3 = z 3) (h4 : z' 4 = z 4)
    (h5 : z' 5 = z 5 + d) :
    canonicalPrefixMap t sym z' 5 =
      canonicalPrefixMap t sym z 5 + d := by
  rw [canonicalPrefixMap_coord_five, canonicalPrefixMap_coord_five]
  rw [canonicalPrefixCoordFiveDebit_eq_of_coord_zero_one_two_three_four_eq
    h0 h1 h2 h3 h4, h5]
  ring

def canonicalPrefixWordPrefixState {m : Nat}
    (W : List CanonSym) (n : Nat) (z : Fin 6 → ZMod m) : Fin 6 → ZMod m :=
  (List.range n).foldl
    (fun x (t : Nat) =>
      canonicalPrefixMap (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m)) x)
    z

theorem canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
    {m : Nat} (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 + d →
        canonicalPrefixWordPrefixState W n z' 0 =
          canonicalPrefixWordPrefixState W n z 0 ∧
        canonicalPrefixWordPrefixState W n z' 1 =
          canonicalPrefixWordPrefixState W n z 1 + d
  | 0, z, z', d, h0, h1 => by
      simp [canonicalPrefixWordPrefixState, h0, h1]
  | n + 1, z, z', d, h0, h1 => by
      simp only [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have ih :=
        canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
          W n z z' d h0 h1
      constructor
      · simpa [canonicalPrefixWordPrefixState] using
          canonicalPrefixMap_coord_zero_eq_of_coord_zero_eq
            (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) ih.1
      · simpa [canonicalPrefixWordPrefixState] using
          canonicalPrefixMap_coord_one_add_of_coord_zero_eq
            (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) d ih.1 ih.2

theorem canonicalPrefixWordReturn_coord_zero_one_add_of_coord_zero_eq
    {m : Nat} [NeZero m] (W : List CanonSym)
    {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1 + d) :
      canonicalPrefixWordReturn (m := m) W z' 0 =
        canonicalPrefixWordReturn (m := m) W z 0 ∧
      canonicalPrefixWordReturn (m := m) W z' 1 =
        canonicalPrefixWordReturn (m := m) W z 1 + d := by
  change
      canonicalPrefixWordPrefixState W m z' 0 =
        canonicalPrefixWordPrefixState W m z 0 ∧
      canonicalPrefixWordPrefixState W m z' 1 =
        canonicalPrefixWordPrefixState W m z 1 + d
  exact canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
    W m z z' d h0 h1

theorem canonicalPrefixWordReturn_iter_coord_zero_one_add_of_coord_zero_eq
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 + d →
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 0 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 0 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 1 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 + d
  | 0, z, z', d, h0, h1 => by
      simp [h0, h1]
  | n + 1, z, z', d, h0, h1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have ih := canonicalPrefixWordReturn_iter_coord_zero_one_add_of_coord_zero_eq
        W n z z' d h0 h1
      exact canonicalPrefixWordReturn_coord_zero_one_add_of_coord_zero_eq W d ih.1 ih.2

theorem canonicalPrefixWordPrefixState_after_return_iter_coord_zero_one_add
    {m : Nat} [NeZero m] (W : List CanonSym)
    (j t : Nat) {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1 + d) :
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 0 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 1 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 1 + d := by
  have hiter :=
    canonicalPrefixWordReturn_iter_coord_zero_one_add_of_coord_zero_eq
      W j z z' d h0 h1
  exact canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
    W t _ _ d hiter.1 hiter.2

theorem canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
    {m : Nat} (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 + d →
        canonicalPrefixWordPrefixState W n z' 0 =
          canonicalPrefixWordPrefixState W n z 0 ∧
        canonicalPrefixWordPrefixState W n z' 1 =
          canonicalPrefixWordPrefixState W n z 1 ∧
        canonicalPrefixWordPrefixState W n z' 2 =
          canonicalPrefixWordPrefixState W n z 2 + d
  | 0, z, z', d, h0, h1, h2 => by
      simp [canonicalPrefixWordPrefixState, h0, h1, h2]
  | n + 1, z, z', d, h0, h1, h2 => by
      simp only [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have ih :=
        canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
          W n z z' d h0 h1 h2
      constructor
      · simpa [canonicalPrefixWordPrefixState] using
          canonicalPrefixMap_coord_zero_eq_of_coord_zero_eq
            (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) ih.1
      · constructor
        · simpa [canonicalPrefixWordPrefixState] using
            canonicalPrefixMap_coord_one_add_of_coord_zero_eq
              (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
              ih.1 (by rw [ih.2.1]; ring)
        · simpa [canonicalPrefixWordPrefixState] using
            canonicalPrefixMap_coord_two_add_of_coord_zero_one_eq
              (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) d
              ih.1 ih.2.1 ih.2.2

theorem canonicalPrefixWordReturn_coord_zero_one_two_add_of_coord_zero_one_eq
    {m : Nat} [NeZero m] (W : List CanonSym)
    {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2 + d) :
      canonicalPrefixWordReturn (m := m) W z' 0 =
        canonicalPrefixWordReturn (m := m) W z 0 ∧
      canonicalPrefixWordReturn (m := m) W z' 1 =
        canonicalPrefixWordReturn (m := m) W z 1 ∧
      canonicalPrefixWordReturn (m := m) W z' 2 =
        canonicalPrefixWordReturn (m := m) W z 2 + d := by
  change
      canonicalPrefixWordPrefixState W m z' 0 =
        canonicalPrefixWordPrefixState W m z 0 ∧
      canonicalPrefixWordPrefixState W m z' 1 =
        canonicalPrefixWordPrefixState W m z 1 ∧
      canonicalPrefixWordPrefixState W m z' 2 =
        canonicalPrefixWordPrefixState W m z 2 + d
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
    W m z z' d h0 h1 h2

theorem canonicalPrefixWordReturn_iter_coord_zero_one_two_add_of_coord_zero_one_eq
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 + d →
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 0 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 0 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 1 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 2 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 2 + d
  | 0, z, z', d, h0, h1, h2 => by
      simp [h0, h1, h2]
  | n + 1, z, z', d, h0, h1, h2 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have ih := canonicalPrefixWordReturn_iter_coord_zero_one_two_add_of_coord_zero_one_eq
        W n z z' d h0 h1 h2
      exact canonicalPrefixWordReturn_coord_zero_one_two_add_of_coord_zero_one_eq
        W d ih.1 ih.2.1 ih.2.2

theorem canonicalPrefixWordPrefixState_after_return_iter_coord_zero_one_two_add
    {m : Nat} [NeZero m] (W : List CanonSym)
    (j t : Nat) {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2 + d) :
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 0 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 1 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 1 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 2 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 2 + d := by
  have hiter :=
    canonicalPrefixWordReturn_iter_coord_zero_one_two_add_of_coord_zero_one_eq
      W j z z' d h0 h1 h2
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
    W t _ _ d hiter.1 hiter.2.1 hiter.2.2

theorem canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
    {m : Nat} (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 → z' 3 = z 3 + d →
        canonicalPrefixWordPrefixState W n z' 0 =
          canonicalPrefixWordPrefixState W n z 0 ∧
        canonicalPrefixWordPrefixState W n z' 1 =
          canonicalPrefixWordPrefixState W n z 1 ∧
        canonicalPrefixWordPrefixState W n z' 2 =
          canonicalPrefixWordPrefixState W n z 2 ∧
        canonicalPrefixWordPrefixState W n z' 3 =
          canonicalPrefixWordPrefixState W n z 3 + d
  | 0, z, z', d, h0, h1, h2, h3 => by
      simp [canonicalPrefixWordPrefixState, h0, h1, h2, h3]
  | n + 1, z, z', d, h0, h1, h2, h3 => by
      simp only [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have ih :=
        canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
          W n z z' d h0 h1 h2 h3
      constructor
      · simpa [canonicalPrefixWordPrefixState] using
          canonicalPrefixMap_coord_zero_eq_of_coord_zero_eq
            (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) ih.1
      · constructor
        · simpa [canonicalPrefixWordPrefixState] using
            canonicalPrefixMap_coord_one_add_of_coord_zero_eq
              (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
              ih.1 (by rw [ih.2.1]; ring)
        · constructor
          · simpa [canonicalPrefixWordPrefixState] using
              canonicalPrefixMap_coord_two_add_of_coord_zero_one_eq
                (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
                ih.1 ih.2.1 (by rw [ih.2.2.1]; ring)
          · simpa [canonicalPrefixWordPrefixState] using
              canonicalPrefixMap_coord_three_add_of_coord_zero_one_two_eq
                (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) d
                ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

theorem canonicalPrefixWordReturn_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
    {m : Nat} [NeZero m] (W : List CanonSym)
    {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3 + d) :
      canonicalPrefixWordReturn (m := m) W z' 0 =
        canonicalPrefixWordReturn (m := m) W z 0 ∧
      canonicalPrefixWordReturn (m := m) W z' 1 =
        canonicalPrefixWordReturn (m := m) W z 1 ∧
      canonicalPrefixWordReturn (m := m) W z' 2 =
        canonicalPrefixWordReturn (m := m) W z 2 ∧
      canonicalPrefixWordReturn (m := m) W z' 3 =
        canonicalPrefixWordReturn (m := m) W z 3 + d := by
  change
      canonicalPrefixWordPrefixState W m z' 0 =
        canonicalPrefixWordPrefixState W m z 0 ∧
      canonicalPrefixWordPrefixState W m z' 1 =
        canonicalPrefixWordPrefixState W m z 1 ∧
      canonicalPrefixWordPrefixState W m z' 2 =
        canonicalPrefixWordPrefixState W m z 2 ∧
      canonicalPrefixWordPrefixState W m z' 3 =
        canonicalPrefixWordPrefixState W m z 3 + d
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
    W m z z' d h0 h1 h2 h3

theorem canonicalPrefixWordReturn_iter_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 → z' 3 = z 3 + d →
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 0 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 0 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 1 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 2 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 2 ∧
        ((canonicalPrefixWordReturn (m := m) W)^[n] z') 3 =
          ((canonicalPrefixWordReturn (m := m) W)^[n] z) 3 + d
  | 0, z, z', d, h0, h1, h2, h3 => by
      simp [h0, h1, h2, h3]
  | n + 1, z, z', d, h0, h1, h2, h3 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have ih :=
        canonicalPrefixWordReturn_iter_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
          W n z z' d h0 h1 h2 h3
      exact canonicalPrefixWordReturn_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
        W d ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

theorem canonicalPrefixWordPrefixState_after_return_iter_coord_zero_one_two_three_add
    {m : Nat} [NeZero m] (W : List CanonSym)
    (j t : Nat) {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3 + d) :
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 0 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 1 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 1 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 2 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 2 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 3 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 3 + d := by
  have hiter :=
    canonicalPrefixWordReturn_iter_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
      W j z z' d h0 h1 h2 h3
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
    W t _ _ d hiter.1 hiter.2.1 hiter.2.2.1 hiter.2.2.2

theorem canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
    {m : Nat} (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 → z' 3 = z 3 →
        z' 4 = z 4 + d →
          canonicalPrefixWordPrefixState W n z' 0 =
            canonicalPrefixWordPrefixState W n z 0 ∧
          canonicalPrefixWordPrefixState W n z' 1 =
            canonicalPrefixWordPrefixState W n z 1 ∧
          canonicalPrefixWordPrefixState W n z' 2 =
            canonicalPrefixWordPrefixState W n z 2 ∧
          canonicalPrefixWordPrefixState W n z' 3 =
            canonicalPrefixWordPrefixState W n z 3 ∧
          canonicalPrefixWordPrefixState W n z' 4 =
            canonicalPrefixWordPrefixState W n z 4 + d
  | 0, z, z', d, h0, h1, h2, h3, h4 => by
      simp [canonicalPrefixWordPrefixState, h0, h1, h2, h3, h4]
  | n + 1, z, z', d, h0, h1, h2, h3, h4 => by
      simp only [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have ih :=
        canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
          W n z z' d h0 h1 h2 h3 h4
      constructor
      · simpa [canonicalPrefixWordPrefixState] using
          canonicalPrefixMap_coord_zero_eq_of_coord_zero_eq
            (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) ih.1
      · constructor
        · simpa [canonicalPrefixWordPrefixState] using
            canonicalPrefixMap_coord_one_add_of_coord_zero_eq
              (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
              ih.1 (by rw [ih.2.1]; ring)
        · constructor
          · simpa [canonicalPrefixWordPrefixState] using
              canonicalPrefixMap_coord_two_add_of_coord_zero_one_eq
                (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
                ih.1 ih.2.1 (by rw [ih.2.2.1]; ring)
          · constructor
            · simpa [canonicalPrefixWordPrefixState] using
                canonicalPrefixMap_coord_three_add_of_coord_zero_one_two_eq
                  (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) (0 : ZMod m)
                  ih.1 ih.2.1 ih.2.2.1 (by rw [ih.2.2.2.1]; ring)
            · simpa [canonicalPrefixWordPrefixState] using
                canonicalPrefixMap_coord_four_add_of_coord_zero_one_two_three_eq
                  (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m)) d
                  ih.1 ih.2.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2

theorem canonicalPrefixWordReturn_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
    {m : Nat} [NeZero m] (W : List CanonSym)
    {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) (h4 : z' 4 = z 4 + d) :
      canonicalPrefixWordReturn (m := m) W z' 0 =
        canonicalPrefixWordReturn (m := m) W z 0 ∧
      canonicalPrefixWordReturn (m := m) W z' 1 =
        canonicalPrefixWordReturn (m := m) W z 1 ∧
      canonicalPrefixWordReturn (m := m) W z' 2 =
        canonicalPrefixWordReturn (m := m) W z 2 ∧
      canonicalPrefixWordReturn (m := m) W z' 3 =
        canonicalPrefixWordReturn (m := m) W z 3 ∧
      canonicalPrefixWordReturn (m := m) W z' 4 =
        canonicalPrefixWordReturn (m := m) W z 4 + d := by
  change
      canonicalPrefixWordPrefixState W m z' 0 =
        canonicalPrefixWordPrefixState W m z 0 ∧
      canonicalPrefixWordPrefixState W m z' 1 =
        canonicalPrefixWordPrefixState W m z 1 ∧
      canonicalPrefixWordPrefixState W m z' 2 =
        canonicalPrefixWordPrefixState W m z 2 ∧
      canonicalPrefixWordPrefixState W m z' 3 =
        canonicalPrefixWordPrefixState W m z 3 ∧
      canonicalPrefixWordPrefixState W m z' 4 =
        canonicalPrefixWordPrefixState W m z 4 + d
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
    W m z z' d h0 h1 h2 h3 h4

theorem canonicalPrefixWordReturn_iter_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z z' : Fin 6 → ZMod m, ∀ d : ZMod m,
      z' 0 = z 0 → z' 1 = z 1 → z' 2 = z 2 → z' 3 = z 3 →
        z' 4 = z 4 + d →
          ((canonicalPrefixWordReturn (m := m) W)^[n] z') 0 =
            ((canonicalPrefixWordReturn (m := m) W)^[n] z) 0 ∧
          ((canonicalPrefixWordReturn (m := m) W)^[n] z') 1 =
            ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 ∧
          ((canonicalPrefixWordReturn (m := m) W)^[n] z') 2 =
            ((canonicalPrefixWordReturn (m := m) W)^[n] z) 2 ∧
          ((canonicalPrefixWordReturn (m := m) W)^[n] z') 3 =
            ((canonicalPrefixWordReturn (m := m) W)^[n] z) 3 ∧
          ((canonicalPrefixWordReturn (m := m) W)^[n] z') 4 =
            ((canonicalPrefixWordReturn (m := m) W)^[n] z) 4 + d
  | 0, z, z', d, h0, h1, h2, h3, h4 => by
      simp [h0, h1, h2, h3, h4]
  | n + 1, z, z', d, h0, h1, h2, h3, h4 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have ih :=
        canonicalPrefixWordReturn_iter_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
          W n z z' d h0 h1 h2 h3 h4
      exact canonicalPrefixWordReturn_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
        W d ih.1 ih.2.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2

theorem canonicalPrefixWordPrefixState_after_return_iter_coord_zero_one_two_three_four_add
    {m : Nat} [NeZero m] (W : List CanonSym)
    (j t : Nat) {z z' : Fin 6 → ZMod m} (d : ZMod m)
    (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2)
    (h3 : z' 3 = z 3) (h4 : z' 4 = z 4 + d) :
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 0 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 1 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 1 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 2 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 2 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 3 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 3 ∧
      canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z') 4 =
        canonicalPrefixWordPrefixState W t
          ((canonicalPrefixWordReturn (m := m) W)^[j] z) 4 + d := by
  have hiter :=
    canonicalPrefixWordReturn_iter_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
      W j z z' d h0 h1 h2 h3 h4
  exact canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
    W t _ _ d hiter.1 hiter.2.1 hiter.2.2.1 hiter.2.2.2.1 hiter.2.2.2.2

def canonicalPrefixWordPairPrefix {m : Nat}
    (W : List CanonSym) (t : Nat) (p : ZMod m × ZMod m) : ZMod m × ZMod m :=
  prefixPair (canonicalPrefixWordPrefixState W t (prefixPairBase p))

def canonicalPrefixWordPairReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m) : ZMod m × ZMod m :=
  prefixPair (canonicalPrefixWordReturn (m := m) W (prefixPairBase p))

def canonicalPrefixWordTriplePrefix {m : Nat}
    (W : List CanonSym) (t : Nat) (p : ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m :=
  prefixTriple (canonicalPrefixWordPrefixState W t (prefixTripleBase p))

def canonicalPrefixWordTripleReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m :=
  prefixTriple (canonicalPrefixWordReturn (m := m) W (prefixTripleBase p))

def canonicalPrefixWordQuadPrefix {m : Nat}
    (W : List CanonSym) (t : Nat)
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m :=
  prefixQuad (canonicalPrefixWordPrefixState W t (prefixQuadBase p))

def canonicalPrefixWordQuadReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m :=
  prefixQuad (canonicalPrefixWordReturn (m := m) W (prefixQuadBase p))

def canonicalPrefixWordQuintPrefix {m : Nat}
    (W : List CanonSym) (t : Nat)
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m × ZMod m :=
  prefixQuint (canonicalPrefixWordPrefixState W t (prefixQuintBase p))

def canonicalPrefixWordQuintReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m × ZMod m × ZMod m :=
  prefixQuint (canonicalPrefixWordReturn (m := m) W (prefixQuintBase p))

theorem canonicalPrefixWordPairPrefix_apply_eq_of_pair {m : Nat}
    (W : List CanonSym) (t : Nat) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordPairPrefix W t (prefixPair z) =
      prefixPair (canonicalPrefixWordPrefixState W t z) := by
  apply Prod.ext
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
      W t z (prefixPairBase (prefixPair z)) (0 : ZMod m) (by rfl)
        (by change z 1 = z 1 + (0 : ZMod m); ring)
    exact h.1
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
      W t z (prefixPairBase (prefixPair z)) (0 : ZMod m) (by rfl)
        (by change z 1 = z 1 + (0 : ZMod m); ring)
    simpa using h.2

theorem canonicalPrefixWordPairReturn_apply_eq_of_pair {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordPairReturn W (prefixPair z) =
      prefixPair (canonicalPrefixWordReturn (m := m) W z) := by
  change canonicalPrefixWordPairPrefix W m (prefixPair z) =
      prefixPair (canonicalPrefixWordPrefixState W m z)
  exact canonicalPrefixWordPairPrefix_apply_eq_of_pair W m z

theorem canonicalPrefixWordPairReturn_iter_apply_eq_of_pair
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      (canonicalPrefixWordPairReturn W)^[n] (prefixPair z) =
        prefixPair ((canonicalPrefixWordReturn (m := m) W)^[n] z)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordPairReturn_iter_apply_eq_of_pair W n z]
      rw [canonicalPrefixWordPairReturn_apply_eq_of_pair W]

theorem canonicalPrefixWordTriplePrefix_apply_eq_of_triple {m : Nat}
    (W : List CanonSym) (t : Nat) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordTriplePrefix W t (prefixTriple z) =
      prefixTriple (canonicalPrefixWordPrefixState W t z) := by
  apply Prod.ext
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
      W t z (prefixTripleBase (prefixTriple z)) (0 : ZMod m) (by rfl)
        (by rfl) (by change z 2 = z 2 + (0 : ZMod m); ring)
    exact h.1
  · apply Prod.ext
    · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
        W t z (prefixTripleBase (prefixTriple z)) (0 : ZMod m) (by rfl)
          (by rfl) (by change z 2 = z 2 + (0 : ZMod m); ring)
      exact h.2.1
    · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
        W t z (prefixTripleBase (prefixTriple z)) (0 : ZMod m) (by rfl)
          (by rfl) (by change z 2 = z 2 + (0 : ZMod m); ring)
      simpa using h.2.2

theorem canonicalPrefixWordTripleReturn_apply_eq_of_triple {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordTripleReturn W (prefixTriple z) =
      prefixTriple (canonicalPrefixWordReturn (m := m) W z) := by
  change canonicalPrefixWordTriplePrefix W m (prefixTriple z) =
      prefixTriple (canonicalPrefixWordPrefixState W m z)
  exact canonicalPrefixWordTriplePrefix_apply_eq_of_triple W m z

theorem canonicalPrefixWordTripleReturn_iter_apply_eq_of_triple
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      (canonicalPrefixWordTripleReturn W)^[n] (prefixTriple z) =
        prefixTriple ((canonicalPrefixWordReturn (m := m) W)^[n] z)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordTripleReturn_iter_apply_eq_of_triple W n z]
      rw [canonicalPrefixWordTripleReturn_apply_eq_of_triple W]

theorem canonicalPrefixWordTriplePrefix_pair {m : Nat}
    (W : List CanonSym) (t : Nat) (p : ZMod m × ZMod m × ZMod m) :
    prefixTriplePair (canonicalPrefixWordTriplePrefix W t p) =
      canonicalPrefixWordPairPrefix W t (prefixTriplePair p) := by
  rcases p with ⟨p0, p1, p2⟩
  apply Prod.ext
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
      W t (prefixPairBase (p0, p1)) (prefixTripleBase (p0, p1, p2)) (0 : ZMod m)
      (by rfl) (by change p1 = p1 + (0 : ZMod m); ring)
    simpa [prefixTriplePair, canonicalPrefixWordTriplePrefix,
      canonicalPrefixWordPairPrefix, prefixTriple, prefixPair] using h.1
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
      W t (prefixPairBase (p0, p1)) (prefixTripleBase (p0, p1, p2)) (0 : ZMod m)
      (by rfl) (by change p1 = p1 + (0 : ZMod m); ring)
    simpa [prefixTriplePair, canonicalPrefixWordTriplePrefix,
      canonicalPrefixWordPairPrefix, prefixTriple, prefixPair] using h.2

theorem canonicalPrefixWordTripleReturn_pair {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m × ZMod m) :
    prefixTriplePair (canonicalPrefixWordTripleReturn W p) =
      canonicalPrefixWordPairReturn W (prefixTriplePair p) := by
  change prefixTriplePair (canonicalPrefixWordTriplePrefix W m p) =
    canonicalPrefixWordPairPrefix W m (prefixTriplePair p)
  exact canonicalPrefixWordTriplePrefix_pair W m p

theorem canonicalPrefixWordTripleReturn_pair_iter
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m,
      prefixTriplePair ((canonicalPrefixWordTripleReturn W)^[n] p) =
        (canonicalPrefixWordPairReturn W)^[n] (prefixTriplePair p)
  | 0, p => by simp [prefixTriplePair]
  | n + 1, p => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordTripleReturn_pair]
      rw [canonicalPrefixWordTripleReturn_pair_iter W n]

theorem canonicalPrefixWordQuadPrefix_apply_eq_of_quad {m : Nat}
    (W : List CanonSym) (t : Nat) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordQuadPrefix W t (prefixQuad z) =
      prefixQuad (canonicalPrefixWordPrefixState W t z) := by
  apply Prod.ext
  · have h :=
      canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
        W t z (prefixQuadBase (prefixQuad z)) (0 : ZMod m) (by rfl)
        (by rfl) (by rfl) (by change z 3 = z 3 + (0 : ZMod m); ring)
    exact h.1
  · apply Prod.ext
    · have h :=
        canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
          W t z (prefixQuadBase (prefixQuad z)) (0 : ZMod m) (by rfl)
          (by rfl) (by rfl) (by change z 3 = z 3 + (0 : ZMod m); ring)
      exact h.2.1
    · apply Prod.ext
      · have h :=
          canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
            W t z (prefixQuadBase (prefixQuad z)) (0 : ZMod m) (by rfl)
            (by rfl) (by rfl) (by change z 3 = z 3 + (0 : ZMod m); ring)
        exact h.2.2.1
      · have h :=
          canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
            W t z (prefixQuadBase (prefixQuad z)) (0 : ZMod m) (by rfl)
            (by rfl) (by rfl) (by change z 3 = z 3 + (0 : ZMod m); ring)
        simpa using h.2.2.2

theorem canonicalPrefixWordQuadReturn_apply_eq_of_quad {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordQuadReturn W (prefixQuad z) =
      prefixQuad (canonicalPrefixWordReturn (m := m) W z) := by
  change canonicalPrefixWordQuadPrefix W m (prefixQuad z) =
      prefixQuad (canonicalPrefixWordPrefixState W m z)
  exact canonicalPrefixWordQuadPrefix_apply_eq_of_quad W m z

theorem canonicalPrefixWordQuadReturn_iter_apply_eq_of_quad
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      (canonicalPrefixWordQuadReturn W)^[n] (prefixQuad z) =
        prefixQuad ((canonicalPrefixWordReturn (m := m) W)^[n] z)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordQuadReturn_iter_apply_eq_of_quad W n z]
      rw [canonicalPrefixWordQuadReturn_apply_eq_of_quad W]

theorem canonicalPrefixWordQuadPrefix_triple {m : Nat}
    (W : List CanonSym) (t : Nat)
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuadTriple (canonicalPrefixWordQuadPrefix W t p) =
      canonicalPrefixWordTriplePrefix W t (prefixQuadTriple p) := by
  rcases p with ⟨p0, p1, p2, p3⟩
  apply Prod.ext
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
      W t (prefixTripleBase (p0, p1, p2)) (prefixQuadBase (p0, p1, p2, p3))
      (0 : ZMod m) (by rfl) (by rfl)
      (by change p2 = p2 + (0 : ZMod m); ring)
    simpa [prefixQuadTriple, canonicalPrefixWordQuadPrefix,
      canonicalPrefixWordTriplePrefix, prefixQuad, prefixTriple] using h.1
  · apply Prod.ext
    · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
        W t (prefixTripleBase (p0, p1, p2)) (prefixQuadBase (p0, p1, p2, p3))
        (0 : ZMod m) (by rfl) (by rfl)
        (by change p2 = p2 + (0 : ZMod m); ring)
      simpa [prefixQuadTriple, canonicalPrefixWordQuadPrefix,
        canonicalPrefixWordTriplePrefix, prefixQuad, prefixTriple] using h.2.1
    · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
        W t (prefixTripleBase (p0, p1, p2)) (prefixQuadBase (p0, p1, p2, p3))
        (0 : ZMod m) (by rfl) (by rfl)
        (by change p2 = p2 + (0 : ZMod m); ring)
      simpa [prefixQuadTriple, canonicalPrefixWordQuadPrefix,
        canonicalPrefixWordTriplePrefix, prefixQuad, prefixTriple] using h.2.2

theorem canonicalPrefixWordQuadReturn_triple {m : Nat} [NeZero m]
    (W : List CanonSym) (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuadTriple (canonicalPrefixWordQuadReturn W p) =
      canonicalPrefixWordTripleReturn W (prefixQuadTriple p) := by
  change prefixQuadTriple (canonicalPrefixWordQuadPrefix W m p) =
    canonicalPrefixWordTriplePrefix W m (prefixQuadTriple p)
  exact canonicalPrefixWordQuadPrefix_triple W m p

theorem canonicalPrefixWordQuadReturn_triple_iter
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m × ZMod m,
      prefixQuadTriple ((canonicalPrefixWordQuadReturn W)^[n] p) =
        (canonicalPrefixWordTripleReturn W)^[n] (prefixQuadTriple p)
  | 0, p => by simp [prefixQuadTriple]
  | n + 1, p => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordQuadReturn_triple]
      rw [canonicalPrefixWordQuadReturn_triple_iter W n]

theorem canonicalPrefixWordQuintPrefix_apply_eq_of_quint {m : Nat}
    (W : List CanonSym) (t : Nat) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordQuintPrefix W t (prefixQuint z) =
      prefixQuint (canonicalPrefixWordPrefixState W t z) := by
  apply Prod.ext
  · have h :=
      canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
        W t z (prefixQuintBase (prefixQuint z)) (0 : ZMod m) (by rfl)
        (by rfl) (by rfl) (by rfl) (by change z 4 = z 4 + (0 : ZMod m); ring)
    exact h.1
  · apply Prod.ext
    · have h :=
        canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
          W t z (prefixQuintBase (prefixQuint z)) (0 : ZMod m) (by rfl)
          (by rfl) (by rfl) (by rfl) (by change z 4 = z 4 + (0 : ZMod m); ring)
      exact h.2.1
    · apply Prod.ext
      · have h :=
          canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
            W t z (prefixQuintBase (prefixQuint z)) (0 : ZMod m) (by rfl)
            (by rfl) (by rfl) (by rfl) (by change z 4 = z 4 + (0 : ZMod m); ring)
        exact h.2.2.1
      · apply Prod.ext
        · have h :=
            canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
              W t z (prefixQuintBase (prefixQuint z)) (0 : ZMod m) (by rfl)
              (by rfl) (by rfl) (by rfl) (by change z 4 = z 4 + (0 : ZMod m); ring)
          exact h.2.2.2.1
        · have h :=
            canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
              W t z (prefixQuintBase (prefixQuint z)) (0 : ZMod m) (by rfl)
              (by rfl) (by rfl) (by rfl) (by change z 4 = z 4 + (0 : ZMod m); ring)
          simpa using h.2.2.2.2

theorem canonicalPrefixWordQuintReturn_apply_eq_of_quint {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordQuintReturn W (prefixQuint z) =
      prefixQuint (canonicalPrefixWordReturn (m := m) W z) := by
  change canonicalPrefixWordQuintPrefix W m (prefixQuint z) =
      prefixQuint (canonicalPrefixWordPrefixState W m z)
  exact canonicalPrefixWordQuintPrefix_apply_eq_of_quint W m z

theorem canonicalPrefixWordQuintReturn_iter_apply_eq_of_quint
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      (canonicalPrefixWordQuintReturn W)^[n] (prefixQuint z) =
        prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[n] z)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordQuintReturn_iter_apply_eq_of_quint W n z]
      rw [canonicalPrefixWordQuintReturn_apply_eq_of_quint W]

theorem canonicalPrefixWordQuintPrefix_quad {m : Nat}
    (W : List CanonSym) (t : Nat)
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuintQuad (canonicalPrefixWordQuintPrefix W t p) =
      canonicalPrefixWordQuadPrefix W t (prefixQuintQuad p) := by
  rcases p with ⟨p0, p1, p2, p3, p4⟩
  apply Prod.ext
  · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
      W t (prefixQuadBase (p0, p1, p2, p3))
        (prefixQuintBase (p0, p1, p2, p3, p4)) (0 : ZMod m)
      (by rfl) (by rfl) (by rfl)
      (by change p3 = p3 + (0 : ZMod m); ring)
    simpa [prefixQuintQuad, canonicalPrefixWordQuintPrefix,
      canonicalPrefixWordQuadPrefix, prefixQuint, prefixQuad] using h.1
  · apply Prod.ext
    · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
        W t (prefixQuadBase (p0, p1, p2, p3))
          (prefixQuintBase (p0, p1, p2, p3, p4)) (0 : ZMod m)
        (by rfl) (by rfl) (by rfl)
        (by change p3 = p3 + (0 : ZMod m); ring)
      simpa [prefixQuintQuad, canonicalPrefixWordQuintPrefix,
        canonicalPrefixWordQuadPrefix, prefixQuint, prefixQuad] using h.2.1
    · apply Prod.ext
      · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
          W t (prefixQuadBase (p0, p1, p2, p3))
            (prefixQuintBase (p0, p1, p2, p3, p4)) (0 : ZMod m)
          (by rfl) (by rfl) (by rfl)
          (by change p3 = p3 + (0 : ZMod m); ring)
        simpa [prefixQuintQuad, canonicalPrefixWordQuintPrefix,
          canonicalPrefixWordQuadPrefix, prefixQuint, prefixQuad] using h.2.2.1
      · have h := canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
          W t (prefixQuadBase (p0, p1, p2, p3))
            (prefixQuintBase (p0, p1, p2, p3, p4)) (0 : ZMod m)
          (by rfl) (by rfl) (by rfl)
          (by change p3 = p3 + (0 : ZMod m); ring)
        simpa [prefixQuintQuad, canonicalPrefixWordQuintPrefix,
          canonicalPrefixWordQuadPrefix, prefixQuint, prefixQuad] using h.2.2.2

theorem canonicalPrefixWordQuintReturn_quad {m : Nat} [NeZero m]
    (W : List CanonSym)
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    prefixQuintQuad (canonicalPrefixWordQuintReturn W p) =
      canonicalPrefixWordQuadReturn W (prefixQuintQuad p) := by
  change prefixQuintQuad (canonicalPrefixWordQuintPrefix W m p) =
    canonicalPrefixWordQuadPrefix W m (prefixQuintQuad p)
  exact canonicalPrefixWordQuintPrefix_quad W m p

theorem canonicalPrefixWordQuintReturn_quad_iter
    {m : Nat} [NeZero m] (W : List CanonSym) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m,
      prefixQuintQuad ((canonicalPrefixWordQuintReturn W)^[n] p) =
        (canonicalPrefixWordQuadReturn W)^[n] (prefixQuintQuad p)
  | 0, p => by simp [prefixQuintQuad]
  | n + 1, p => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [canonicalPrefixWordQuintReturn_quad]
      rw [canonicalPrefixWordQuintReturn_quad_iter W n]

def canonicalPrefixWordLayerDebitTwo {m : Nat}
    (W : List CanonSym) (z : Fin 6 → ZMod m) (t : Nat) : ZMod m :=
  canonicalPrefixCoordTwoDebit (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))
    (canonicalPrefixWordPrefixState W t z)

theorem canonicalPrefixWordPrefixState_coord_two {m : Nat}
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      canonicalPrefixWordPrefixState W n z 2 =
        z 2 - ((List.range n).map
          (fun t : Nat => canonicalPrefixWordLayerDebitTwo W z t)).sum
  | 0, z => by
      simp [canonicalPrefixWordPrefixState]
  | n + 1, z => by
      rw [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        canonicalPrefixMap (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m))
          (canonicalPrefixWordPrefixState W n z) 2 =
        z 2 - ((List.range n ++ [n]).map
          (fun t : Nat => canonicalPrefixWordLayerDebitTwo W z t)).sum
      rw [canonicalPrefixMap_coord_two]
      rw [canonicalPrefixWordPrefixState_coord_two W n z]
      rw [List.map_append, List.sum_append]
      simp [canonicalPrefixWordLayerDebitTwo]
      ring

theorem canonicalPrefixWordReturn_coord_two_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 2 =
      z 2 - ((List.range m).map
        (fun t : Nat => canonicalPrefixWordLayerDebitTwo W z t)).sum := by
  change canonicalPrefixWordPrefixState W m z 2 =
    z 2 - ((List.range m).map
      (fun t : Nat => canonicalPrefixWordLayerDebitTwo W z t)).sum
  exact canonicalPrefixWordPrefixState_coord_two W m z

def canonicalPrefixWordReturnDebitTwo {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  ((List.range m).map (fun t : Nat => canonicalPrefixWordLayerDebitTwo W z t)).sum

def canonicalPrefixWordReturnIterDebitTwo {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (n : Nat) : ZMod m :=
  ((List.range n).map
    (fun j : Nat =>
      canonicalPrefixWordReturnDebitTwo W
        ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum

theorem canonicalPrefixWordReturn_coord_two_returnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 2 =
      z 2 - canonicalPrefixWordReturnDebitTwo W z := by
  simpa [canonicalPrefixWordReturnDebitTwo] using
    canonicalPrefixWordReturn_coord_two_sum W z

theorem canonicalPrefixWordReturn_iter_coord_two_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 2 =
        z 2 - canonicalPrefixWordReturnIterDebitTwo W z n
  | 0, z => by
      simp [canonicalPrefixWordReturnIterDebitTwo]
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_coord_two_returnDebit]
      rw [canonicalPrefixWordReturn_iter_coord_two_sum W n z]
      change
        z 2 - ((List.range n).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitTwo W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum -
            canonicalPrefixWordReturnDebitTwo W
              ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        z 2 - ((List.range (n + 1)).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitTwo W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [canonicalPrefixWordReturnDebitTwo]
      ring

def canonicalPrefixWordLayerDebit {m : Nat}
    (W : List CanonSym) (z : Fin 6 → ZMod m) (t : Nat) : ZMod m :=
  canonicalPrefixCoordOneDebit (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))
    (canonicalPrefixWordPrefixState W t z)

theorem canonicalPrefixWordPrefixState_coord_one {m : Nat}
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      canonicalPrefixWordPrefixState W n z 1 =
        z 1 - ((List.range n).map
          (fun t : Nat => canonicalPrefixWordLayerDebit W z t)).sum
  | 0, z => by
      simp [canonicalPrefixWordPrefixState]
  | n + 1, z => by
      rw [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        canonicalPrefixMap (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m))
          (canonicalPrefixWordPrefixState W n z) 1 =
        z 1 - ((List.range n ++ [n]).map
          (fun t : Nat => canonicalPrefixWordLayerDebit W z t)).sum
      rw [canonicalPrefixMap_coord_one_debit]
      rw [canonicalPrefixWordPrefixState_coord_one W n z]
      rw [List.map_append, List.sum_append]
      simp [canonicalPrefixWordLayerDebit]
      ring

theorem canonicalPrefixWordReturn_coord_one_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 1 =
      z 1 - ((List.range m).map
        (fun t : Nat => canonicalPrefixWordLayerDebit W z t)).sum := by
  change canonicalPrefixWordPrefixState W m z 1 =
    z 1 - ((List.range m).map
      (fun t : Nat => canonicalPrefixWordLayerDebit W z t)).sum
  exact canonicalPrefixWordPrefixState_coord_one W m z

def canonicalPrefixWordReturnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  ((List.range m).map (fun t : Nat => canonicalPrefixWordLayerDebit W z t)).sum

def canonicalPrefixWordReturnIterDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (n : Nat) : ZMod m :=
  ((List.range n).map
    (fun j : Nat =>
      canonicalPrefixWordReturnDebit W
        ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum

theorem canonicalPrefixWordReturn_coord_one_returnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 1 =
      z 1 - canonicalPrefixWordReturnDebit W z := by
  simpa [canonicalPrefixWordReturnDebit] using
    canonicalPrefixWordReturn_coord_one_sum W z

theorem canonicalPrefixWordReturn_iter_coord_one_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 =
        z 1 - canonicalPrefixWordReturnIterDebit W z n
  | 0, z => by
      simp [canonicalPrefixWordReturnIterDebit]
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_coord_one_returnDebit]
      rw [canonicalPrefixWordReturn_iter_coord_one_sum W n z]
      change
        z 1 - ((List.range n).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebit W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum -
            canonicalPrefixWordReturnDebit W
              ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        z 1 - ((List.range (n + 1)).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebit W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [canonicalPrefixWordReturnDebit]
      ring

def canonicalPrefixWordLayerDebitThree {m : Nat}
    (W : List CanonSym) (z : Fin 6 → ZMod m) (t : Nat) : ZMod m :=
  canonicalPrefixCoordThreeDebit (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))
    (canonicalPrefixWordPrefixState W t z)

theorem canonicalPrefixWordPrefixState_coord_three {m : Nat}
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      canonicalPrefixWordPrefixState W n z 3 =
        z 3 - ((List.range n).map
          (fun t : Nat => canonicalPrefixWordLayerDebitThree W z t)).sum
  | 0, z => by
      simp [canonicalPrefixWordPrefixState]
  | n + 1, z => by
      rw [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        canonicalPrefixMap (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m))
          (canonicalPrefixWordPrefixState W n z) 3 =
        z 3 - ((List.range n ++ [n]).map
          (fun t : Nat => canonicalPrefixWordLayerDebitThree W z t)).sum
      rw [canonicalPrefixMap_coord_three]
      rw [canonicalPrefixWordPrefixState_coord_three W n z]
      rw [List.map_append, List.sum_append]
      simp [canonicalPrefixWordLayerDebitThree]
      ring

theorem canonicalPrefixWordReturn_coord_three_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 3 =
      z 3 - ((List.range m).map
        (fun t : Nat => canonicalPrefixWordLayerDebitThree W z t)).sum := by
  change canonicalPrefixWordPrefixState W m z 3 =
    z 3 - ((List.range m).map
      (fun t : Nat => canonicalPrefixWordLayerDebitThree W z t)).sum
  exact canonicalPrefixWordPrefixState_coord_three W m z

def canonicalPrefixWordReturnDebitThree {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  ((List.range m).map (fun t : Nat => canonicalPrefixWordLayerDebitThree W z t)).sum

def canonicalPrefixWordReturnIterDebitThree {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (n : Nat) : ZMod m :=
  ((List.range n).map
    (fun j : Nat =>
      canonicalPrefixWordReturnDebitThree W
        ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum

theorem canonicalPrefixWordReturn_coord_three_returnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 3 =
      z 3 - canonicalPrefixWordReturnDebitThree W z := by
  simpa [canonicalPrefixWordReturnDebitThree] using
    canonicalPrefixWordReturn_coord_three_sum W z

theorem canonicalPrefixWordReturn_iter_coord_three_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 3 =
        z 3 - canonicalPrefixWordReturnIterDebitThree W z n
  | 0, z => by
      simp [canonicalPrefixWordReturnIterDebitThree]
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_coord_three_returnDebit]
      rw [canonicalPrefixWordReturn_iter_coord_three_sum W n z]
      change
        z 3 - ((List.range n).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitThree W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum -
            canonicalPrefixWordReturnDebitThree W
              ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        z 3 - ((List.range (n + 1)).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitThree W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [canonicalPrefixWordReturnDebitThree]
      ring

def canonicalPrefixWordLayerDebitFour {m : Nat}
    (W : List CanonSym) (z : Fin 6 → ZMod m) (t : Nat) : ZMod m :=
  canonicalPrefixCoordFourDebit (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))
    (canonicalPrefixWordPrefixState W t z)

theorem canonicalPrefixWordPrefixState_coord_four {m : Nat}
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      canonicalPrefixWordPrefixState W n z 4 =
        z 4 - ((List.range n).map
          (fun t : Nat => canonicalPrefixWordLayerDebitFour W z t)).sum
  | 0, z => by
      simp [canonicalPrefixWordPrefixState]
  | n + 1, z => by
      rw [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        canonicalPrefixMap (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m))
          (canonicalPrefixWordPrefixState W n z) 4 =
        z 4 - ((List.range n ++ [n]).map
          (fun t : Nat => canonicalPrefixWordLayerDebitFour W z t)).sum
      rw [canonicalPrefixMap_coord_four]
      rw [canonicalPrefixWordPrefixState_coord_four W n z]
      rw [List.map_append, List.sum_append]
      simp [canonicalPrefixWordLayerDebitFour]
      ring

theorem canonicalPrefixWordReturn_coord_four_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 4 =
      z 4 - ((List.range m).map
        (fun t : Nat => canonicalPrefixWordLayerDebitFour W z t)).sum := by
  change canonicalPrefixWordPrefixState W m z 4 =
    z 4 - ((List.range m).map
      (fun t : Nat => canonicalPrefixWordLayerDebitFour W z t)).sum
  exact canonicalPrefixWordPrefixState_coord_four W m z

def canonicalPrefixWordReturnDebitFour {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  ((List.range m).map (fun t : Nat => canonicalPrefixWordLayerDebitFour W z t)).sum

def canonicalPrefixWordReturnIterDebitFour {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (n : Nat) : ZMod m :=
  ((List.range n).map
    (fun j : Nat =>
      canonicalPrefixWordReturnDebitFour W
        ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum

theorem canonicalPrefixWordReturn_coord_four_returnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 4 =
      z 4 - canonicalPrefixWordReturnDebitFour W z := by
  simpa [canonicalPrefixWordReturnDebitFour] using
    canonicalPrefixWordReturn_coord_four_sum W z

theorem canonicalPrefixWordReturn_iter_coord_four_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 4 =
        z 4 - canonicalPrefixWordReturnIterDebitFour W z n
  | 0, z => by
      simp [canonicalPrefixWordReturnIterDebitFour]
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_coord_four_returnDebit]
      rw [canonicalPrefixWordReturn_iter_coord_four_sum W n z]
      change
        z 4 - ((List.range n).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitFour W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum -
            canonicalPrefixWordReturnDebitFour W
              ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        z 4 - ((List.range (n + 1)).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitFour W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [canonicalPrefixWordReturnDebitFour]
      ring

def canonicalPrefixWordLayerDebitFive {m : Nat}
    (W : List CanonSym) (z : Fin 6 → ZMod m) (t : Nat) : ZMod m :=
  canonicalPrefixCoordFiveDebit (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))
    (canonicalPrefixWordPrefixState W t z)

theorem canonicalPrefixWordPrefixState_coord_five {m : Nat}
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      canonicalPrefixWordPrefixState W n z 5 =
        z 5 - ((List.range n).map
          (fun t : Nat => canonicalPrefixWordLayerDebitFive W z t)).sum
  | 0, z => by
      simp [canonicalPrefixWordPrefixState]
  | n + 1, z => by
      rw [canonicalPrefixWordPrefixState, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        canonicalPrefixMap (n : ZMod m) (canonicalPrefixWordAt W (n : ZMod m))
          (canonicalPrefixWordPrefixState W n z) 5 =
        z 5 - ((List.range n ++ [n]).map
          (fun t : Nat => canonicalPrefixWordLayerDebitFive W z t)).sum
      rw [canonicalPrefixMap_coord_five]
      rw [canonicalPrefixWordPrefixState_coord_five W n z]
      rw [List.map_append, List.sum_append]
      simp [canonicalPrefixWordLayerDebitFive]
      ring

theorem canonicalPrefixWordReturn_coord_five_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 5 =
      z 5 - ((List.range m).map
        (fun t : Nat => canonicalPrefixWordLayerDebitFive W z t)).sum := by
  change canonicalPrefixWordPrefixState W m z 5 =
    z 5 - ((List.range m).map
      (fun t : Nat => canonicalPrefixWordLayerDebitFive W z t)).sum
  exact canonicalPrefixWordPrefixState_coord_five W m z

def canonicalPrefixWordReturnDebitFive {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) : ZMod m :=
  ((List.range m).map (fun t : Nat => canonicalPrefixWordLayerDebitFive W z t)).sum

def canonicalPrefixWordReturnIterDebitFive {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (n : Nat) : ZMod m :=
  ((List.range n).map
    (fun j : Nat =>
      canonicalPrefixWordReturnDebitFive W
        ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum

theorem canonicalPrefixWordReturn_coord_five_returnDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 5 =
      z 5 - canonicalPrefixWordReturnDebitFive W z := by
  simpa [canonicalPrefixWordReturnDebitFive] using
    canonicalPrefixWordReturn_coord_five_sum W z

theorem canonicalPrefixWordReturn_iter_coord_five_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 5 =
        z 5 - canonicalPrefixWordReturnIterDebitFive W z n
  | 0, z => by
      simp [canonicalPrefixWordReturnIterDebitFive]
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_coord_five_returnDebit]
      rw [canonicalPrefixWordReturn_iter_coord_five_sum W n z]
      change
        z 5 - ((List.range n).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitFive W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum -
            canonicalPrefixWordReturnDebitFive W
              ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        z 5 - ((List.range (n + 1)).map
          (fun j : Nat =>
            canonicalPrefixWordReturnDebitFive W
              ((canonicalPrefixWordReturn (m := m) W)^[j] z))).sum
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [canonicalPrefixWordReturnDebitFive]
      ring

theorem canonicalPrefixWordReturn_coord_zero_fold {m : Nat} [NeZero m]
    (W : List CanonSym) :
    ∀ L : List Nat, ∀ z : Fin 6 → ZMod m,
      (L.foldl
        (fun x (t : Nat) =>
          canonicalPrefixMap (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m)) x)
        z) 0 =
      z 0 - (L.countP
        (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) != 0) : ZMod m)
  | [], z => by simp
  | t :: L, z => by
      rw [List.foldl_cons]
      rw [canonicalPrefixWordReturn_coord_zero_fold W L]
      rw [canonicalPrefixMap_coord_zero]
      rw [List.countP_cons]
      by_cases hsym : canonicalPrefixWordAt W (t : ZMod m) = 0
      · simp [hsym]
      · simp [hsym, Nat.cast_add]
        ring

theorem canonicalPrefixWordPrefixState_coord_zero_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (n : Nat) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordPrefixState W n z 0 =
      z 0 - ((List.range n).countP
        (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) != 0) : ZMod m) := by
  simpa [canonicalPrefixWordPrefixState] using
    canonicalPrefixWordReturn_coord_zero_fold W (List.range n) z

theorem canonicalPrefixWordPairPrefix_injective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Injective (canonicalPrefixWordPairPrefix (m := m) W t) := by
  intro p q hpq
  rcases p with ⟨p0, p1⟩
  rcases q with ⟨q0, q1⟩
  apply Prod.ext
  · let debt : ZMod m :=
      ((List.range t).countP
        (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m)
    have hfst := congrArg Prod.fst hpq
    have hfst' : p0 - debt = q0 - debt := by
      dsimp [canonicalPrefixWordPairPrefix, prefixPair] at hfst
      rw [canonicalPrefixWordPrefixState_coord_zero_sum,
        canonicalPrefixWordPrefixState_coord_zero_sum] at hfst
      simpa [prefixPairBase, debt] using hfst
    have hcancel := congrArg (fun x : ZMod m => x + debt) hfst'
    simpa using hcancel
  · have hfst_eq : q0 = p0 := by
      let debt : ZMod m :=
        ((List.range t).countP
          (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m)
      have hfst := congrArg Prod.fst hpq
      have hfst' : p0 - debt = q0 - debt := by
        dsimp [canonicalPrefixWordPairPrefix, prefixPair] at hfst
        rw [canonicalPrefixWordPrefixState_coord_zero_sum,
          canonicalPrefixWordPrefixState_coord_zero_sum] at hfst
        simpa [prefixPairBase, debt] using hfst
      have hcancel := congrArg (fun x : ZMod m => x + debt) hfst'
      simpa using hcancel.symm
    let d : ZMod m := q1 - p1
    have hdep :=
      canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
        W t (prefixPairBase (p0, p1)) (prefixPairBase (q0, q1)) d
        (by simpa [prefixPairBase] using hfst_eq)
        (by dsimp [prefixPairBase, d]; ring)
    have hsnd := congrArg Prod.snd hpq
    have hsnd' :
        canonicalPrefixWordPrefixState W t (prefixPairBase (p0, p1)) 1 =
          canonicalPrefixWordPrefixState W t (prefixPairBase (q0, q1)) 1 := by
      simpa [canonicalPrefixWordPairPrefix, prefixPair] using hsnd
    rw [hdep.2] at hsnd'
    have hd : d = 0 := by
      have hcancel := congrArg
        (fun x : ZMod m =>
          x - canonicalPrefixWordPrefixState W t (prefixPairBase (p0, p1)) 1)
        hsnd'
      simpa [d] using hcancel.symm
    dsimp [d] at hd
    have hq : q1 - p1 + p1 = 0 + p1 := by rw [hd]
    simpa using hq.symm

theorem canonicalPrefixWordPairPrefix_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Bijective (canonicalPrefixWordPairPrefix (m := m) W t) := by
  have hinj := canonicalPrefixWordPairPrefix_injective (m := m) W t
  exact (Fintype.bijective_iff_injective_and_card
    (canonicalPrefixWordPairPrefix (m := m) W t)).2 ⟨hinj, rfl⟩

theorem canonicalPrefixWordPairReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordPairReturn (m := m) W) := by
  change Function.Bijective (canonicalPrefixWordPairPrefix (m := m) W m)
  exact canonicalPrefixWordPairPrefix_bijective W m

theorem canonicalPrefixWordTriplePrefix_injective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Injective (canonicalPrefixWordTriplePrefix (m := m) W t) := by
  intro p q hpq
  rcases p with ⟨p0, p1, p2⟩
  rcases q with ⟨q0, q1, q2⟩
  let debt : ZMod m :=
    ((List.range t).countP
      (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m)
  have hfst := congrArg Prod.fst hpq
  have hfst' : p0 - debt = q0 - debt := by
    dsimp [canonicalPrefixWordTriplePrefix, prefixTriple] at hfst
    rw [canonicalPrefixWordPrefixState_coord_zero_sum,
      canonicalPrefixWordPrefixState_coord_zero_sum] at hfst
    simpa [prefixTripleBase, debt] using hfst
  have hcancel0 := congrArg (fun x : ZMod m => x + debt) hfst'
  have hq0 : q0 = p0 := by
    simpa using hcancel0.symm
  let d1 : ZMod m := q1 - p1
  have hdep1 :=
    canonicalPrefixWordPrefixState_coord_zero_one_add_of_coord_zero_eq
      W t (prefixTripleBase (p0, p1, p2))
        (prefixTripleBase (q0, q1, q2)) d1
      (by simpa [prefixTripleBase] using hq0)
      (by dsimp [prefixTripleBase, d1]; ring)
  have hsnd := congrArg (fun r : ZMod m × ZMod m × ZMod m => r.2.1) hpq
  have hsnd' :
      canonicalPrefixWordPrefixState W t (prefixTripleBase (p0, p1, p2)) 1 =
        canonicalPrefixWordPrefixState W t (prefixTripleBase (q0, q1, q2)) 1 := by
    simpa [canonicalPrefixWordTriplePrefix, prefixTriple] using hsnd
  rw [hdep1.2] at hsnd'
  have hd1 : d1 = 0 := by
    have hcancel := congrArg
      (fun x : ZMod m =>
        x - canonicalPrefixWordPrefixState W t (prefixTripleBase (p0, p1, p2)) 1)
      hsnd'
    simpa [d1] using hcancel.symm
  dsimp [d1] at hd1
  have hq1 : q1 = p1 := by
    have hq : q1 - p1 + p1 = 0 + p1 := by rw [hd1]
    simpa using hq
  let d2 : ZMod m := q2 - p2
  have hdep2 :=
    canonicalPrefixWordPrefixState_coord_zero_one_two_add_of_coord_zero_one_eq
      W t (prefixTripleBase (p0, p1, p2))
        (prefixTripleBase (q0, q1, q2)) d2
      (by simpa [prefixTripleBase] using hq0)
      (by simpa [prefixTripleBase] using hq1)
      (by dsimp [prefixTripleBase, d2]; ring)
  have hthird := congrArg (fun r : ZMod m × ZMod m × ZMod m => r.2.2) hpq
  have hthird' :
      canonicalPrefixWordPrefixState W t (prefixTripleBase (p0, p1, p2)) 2 =
        canonicalPrefixWordPrefixState W t (prefixTripleBase (q0, q1, q2)) 2 := by
    simpa [canonicalPrefixWordTriplePrefix, prefixTriple] using hthird
  rw [hdep2.2.2] at hthird'
  have hd2 : d2 = 0 := by
    have hcancel := congrArg
      (fun x : ZMod m =>
        x - canonicalPrefixWordPrefixState W t (prefixTripleBase (p0, p1, p2)) 2)
      hthird'
    simpa [d2] using hcancel.symm
  dsimp [d2] at hd2
  have hq2 : q2 = p2 := by
    have hq : q2 - p2 + p2 = 0 + p2 := by rw [hd2]
    simpa using hq
  subst q0
  subst q1
  subst q2
  rfl

theorem canonicalPrefixWordTriplePrefix_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Bijective (canonicalPrefixWordTriplePrefix (m := m) W t) := by
  have hinj := canonicalPrefixWordTriplePrefix_injective (m := m) W t
  exact (Fintype.bijective_iff_injective_and_card
    (canonicalPrefixWordTriplePrefix (m := m) W t)).2 ⟨hinj, rfl⟩

theorem canonicalPrefixWordTripleReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordTripleReturn (m := m) W) := by
  change Function.Bijective (canonicalPrefixWordTriplePrefix (m := m) W m)
  exact canonicalPrefixWordTriplePrefix_bijective W m

theorem canonicalPrefixWordQuadPrefix_injective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Injective (canonicalPrefixWordQuadPrefix (m := m) W t) := by
  intro p q hpq
  rcases p with ⟨p0, p1, p2, p3⟩
  rcases q with ⟨q0, q1, q2, q3⟩
  have htri := congrArg prefixQuadTriple hpq
  rw [canonicalPrefixWordQuadPrefix_triple] at htri
  rw [canonicalPrefixWordQuadPrefix_triple] at htri
  have hbaseTri :
      (p0, p1, p2) = (q0, q1, q2) :=
    (canonicalPrefixWordTriplePrefix_bijective W t).1 (by
      simpa [prefixQuadTriple] using htri)
  have hq0 : q0 = p0 := by
    simpa using (congrArg Prod.fst hbaseTri).symm
  have hq1 : q1 = p1 := by
    simpa using (congrArg (fun r : ZMod m × ZMod m × ZMod m => r.2.1) hbaseTri).symm
  have hq2 : q2 = p2 := by
    simpa using (congrArg (fun r : ZMod m × ZMod m × ZMod m => r.2.2) hbaseTri).symm
  let d3 : ZMod m := q3 - p3
  have hdep :=
    canonicalPrefixWordPrefixState_coord_zero_one_two_three_add_of_coord_zero_one_two_eq
      W t (prefixQuadBase (p0, p1, p2, p3))
        (prefixQuadBase (q0, q1, q2, q3)) d3
      (by simpa [prefixQuadBase] using hq0)
      (by simpa [prefixQuadBase] using hq1)
      (by simpa [prefixQuadBase] using hq2)
      (by dsimp [prefixQuadBase, d3]; ring)
  have hfour := congrArg
    (fun r : ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.2) hpq
  have hfour' :
      canonicalPrefixWordPrefixState W t (prefixQuadBase (p0, p1, p2, p3)) 3 =
        canonicalPrefixWordPrefixState W t (prefixQuadBase (q0, q1, q2, q3)) 3 := by
    simpa [canonicalPrefixWordQuadPrefix, prefixQuad] using hfour
  rw [hdep.2.2.2] at hfour'
  have hd3 : d3 = 0 := by
    have hcancel := congrArg
      (fun x : ZMod m =>
        x - canonicalPrefixWordPrefixState W t (prefixQuadBase (p0, p1, p2, p3)) 3)
      hfour'
    simpa [d3] using hcancel.symm
  dsimp [d3] at hd3
  have hq3 : q3 = p3 := by
    have hq : q3 - p3 + p3 = 0 + p3 := by rw [hd3]
    simpa using hq
  subst q0
  subst q1
  subst q2
  subst q3
  rfl

theorem canonicalPrefixWordQuadPrefix_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Bijective (canonicalPrefixWordQuadPrefix (m := m) W t) := by
  have hinj := canonicalPrefixWordQuadPrefix_injective (m := m) W t
  exact (Fintype.bijective_iff_injective_and_card
    (canonicalPrefixWordQuadPrefix (m := m) W t)).2 ⟨hinj, rfl⟩

theorem canonicalPrefixWordQuadReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordQuadReturn (m := m) W) := by
  change Function.Bijective (canonicalPrefixWordQuadPrefix (m := m) W m)
  exact canonicalPrefixWordQuadPrefix_bijective W m

theorem canonicalPrefixWordQuintPrefix_injective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Injective (canonicalPrefixWordQuintPrefix (m := m) W t) := by
  intro p q hpq
  rcases p with ⟨p0, p1, p2, p3, p4⟩
  rcases q with ⟨q0, q1, q2, q3, q4⟩
  have hquad := congrArg prefixQuintQuad hpq
  rw [canonicalPrefixWordQuintPrefix_quad] at hquad
  rw [canonicalPrefixWordQuintPrefix_quad] at hquad
  have hbaseQuad :
      (p0, p1, p2, p3) = (q0, q1, q2, q3) :=
    (canonicalPrefixWordQuadPrefix_bijective W t).1 (by
      simpa [prefixQuintQuad] using hquad)
  have hq0 : q0 = p0 := by
    simpa using (congrArg Prod.fst hbaseQuad).symm
  have hq1 : q1 = p1 := by
    simpa using (congrArg (fun r : ZMod m × ZMod m × ZMod m × ZMod m => r.2.1)
      hbaseQuad).symm
  have hq2 : q2 = p2 := by
    simpa using (congrArg (fun r : ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.1)
      hbaseQuad).symm
  have hq3 : q3 = p3 := by
    simpa using (congrArg (fun r : ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.2)
      hbaseQuad).symm
  let d4 : ZMod m := q4 - p4
  have hdep :=
    canonicalPrefixWordPrefixState_coord_zero_one_two_three_four_add_of_coord_zero_one_two_three_eq
      W t (prefixQuintBase (p0, p1, p2, p3, p4))
        (prefixQuintBase (q0, q1, q2, q3, q4)) d4
      (by simpa [prefixQuintBase] using hq0)
      (by simpa [prefixQuintBase] using hq1)
      (by simpa [prefixQuintBase] using hq2)
      (by simpa [prefixQuintBase] using hq3)
      (by dsimp [prefixQuintBase, d4]; ring)
  have hfifth := congrArg
    (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.2.2) hpq
  have hfifth' :
      canonicalPrefixWordPrefixState W t (prefixQuintBase (p0, p1, p2, p3, p4)) 4 =
        canonicalPrefixWordPrefixState W t (prefixQuintBase (q0, q1, q2, q3, q4)) 4 := by
    simpa [canonicalPrefixWordQuintPrefix, prefixQuint] using hfifth
  rw [hdep.2.2.2.2] at hfifth'
  have hd4 : d4 = 0 := by
    have hcancel := congrArg
      (fun x : ZMod m =>
        x - canonicalPrefixWordPrefixState W t (prefixQuintBase (p0, p1, p2, p3, p4)) 4)
      hfifth'
    simpa [d4] using hcancel.symm
  dsimp [d4] at hd4
  have hq4 : q4 = p4 := by
    have hq : q4 - p4 + p4 = 0 + p4 := by rw [hd4]
    simpa using hq
  subst q0
  subst q1
  subst q2
  subst q3
  subst q4
  rfl

theorem canonicalPrefixWordQuintPrefix_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (t : Nat) :
    Function.Bijective (canonicalPrefixWordQuintPrefix (m := m) W t) := by
  have hinj := canonicalPrefixWordQuintPrefix_injective (m := m) W t
  exact (Fintype.bijective_iff_injective_and_card
    (canonicalPrefixWordQuintPrefix (m := m) W t)).2 ⟨hinj, rfl⟩

theorem canonicalPrefixWordQuintReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordQuintReturn (m := m) W) := by
  change Function.Bijective (canonicalPrefixWordQuintPrefix (m := m) W m)
  exact canonicalPrefixWordQuintPrefix_bijective W m

theorem canonicalPrefixWordAt_range_map {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    (List.range m).map (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m)) = W := by
  apply List.ext_getElem
  · simp [hW]
  · intro i _ h₂
    have hi : i < m := by omega
    simp [canonicalPrefixWordAt, List.getElem_range, hW, hi, Nat.mod_eq_of_lt hi]

theorem canonicalPrefixWordAt_range_count {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (sym : CanonSym) :
    (List.range m).countP
        (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) == sym) =
      canonicalWordCount W sym := by
  have h := congrArg (fun L : List CanonSym => L.countP (fun x => x == sym))
    (canonicalPrefixWordAt_range_map W hW)
  simpa [canonicalWordCount, List.countP_map, Function.comp_def] using h

theorem canonicalWordCount_ne_zero {m : Nat} (W : List CanonSym)
    (hW : W.length = m) :
    W.countP (fun sym : CanonSym => sym != 0) = m - canonicalWordCount W 0 := by
  have hlen := List.length_eq_countP_add_countP (fun sym : CanonSym => sym == 0) (l := W)
  rw [hW] at hlen
  have hsum :
      m = canonicalWordCount W 0 + W.countP (fun sym : CanonSym => sym != 0) := by
    simpa [canonicalWordCount, BEq.beq, decide_eq_true_eq] using hlen
  omega

theorem canonicalPrefixWordAt_range_count_ne_zero {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    (List.range m).countP
        (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) != 0) =
      m - canonicalWordCount W 0 := by
  have h := congrArg (fun L : List CanonSym => L.countP (fun sym => sym != 0))
    (canonicalPrefixWordAt_range_map W hW)
  have hmap :
      (List.range m).countP
          (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) != 0) =
        W.countP (fun sym : CanonSym => sym != 0) := by
    simpa [List.countP_map, Function.comp_def] using h
  rw [hmap, canonicalWordCount_ne_zero W hW]

theorem canonicalPrefixWordReturn_coord_zero {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 0 =
      z 0 + (canonicalWordCount W 0 : ZMod m) := by
  unfold canonicalPrefixWordReturn
  rw [canonicalPrefixWordReturn_coord_zero_fold W (List.range m) z]
  rw [canonicalPrefixWordAt_range_count_ne_zero W hW]
  have hle : canonicalWordCount W 0 ≤ m := by
    rw [← hW]
    exact List.countP_le_length
  have hsumNat :
      m - canonicalWordCount W 0 + canonicalWordCount W 0 = m :=
    Nat.sub_add_cancel hle
  have hsumZ : ((m - canonicalWordCount W 0 : Nat) : ZMod m) +
      (canonicalWordCount W 0 : ZMod m) = 0 := by
    rw [← Nat.cast_add, hsumNat, ZMod.natCast_self]
  calc
    z 0 - ((m - canonicalWordCount W 0 : Nat) : ZMod m) =
        z 0 + (canonicalWordCount W 0 : ZMod m) -
          (((m - canonicalWordCount W 0 : Nat) : ZMod m) +
            (canonicalWordCount W 0 : ZMod m)) := by ring
    _ = z 0 + (canonicalWordCount W 0 : ZMod m) := by rw [hsumZ]; ring

theorem canonicalPrefixWordReturn_head {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (z : Fin 6 → ZMod m) :
    prefixHead (canonicalPrefixWordReturn (m := m) W z) =
      prefixHead z + (canonicalWordCount W 0 : ZMod m) :=
  canonicalPrefixWordReturn_coord_zero W hW z

theorem canonicalPrefixWordPairReturn_head {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (p : ZMod m × ZMod m) :
    (canonicalPrefixWordPairReturn W p).1 =
      p.1 + (canonicalWordCount W 0 : ZMod m) := by
  rcases p with ⟨x, y⟩
  unfold canonicalPrefixWordPairReturn prefixPair
  simpa [prefixHead, prefixPairBase] using
    canonicalPrefixWordReturn_head W hW (prefixPairBase (x, y))

theorem canonicalPrefixWordPairReturn_head_iter {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m,
      ((canonicalPrefixWordPairReturn W)^[n] p).1 =
        p.1 + (n : ZMod m) * (canonicalWordCount W 0 : ZMod m)
  | 0, p => by simp
  | n + 1, p => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordPairReturn_head W hW]
      rw [canonicalPrefixWordPairReturn_head_iter W hW n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordReturn_head_iter {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    ∀ n : Nat, ∀ z : Fin 6 → ZMod m,
      prefixHead ((canonicalPrefixWordReturn (m := m) W)^[n] z) =
        prefixHead z + (n : ZMod m) * (canonicalWordCount W 0 : ZMod m)
  | 0, z => by simp
  | n + 1, z => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordReturn_head W hW]
      rw [canonicalPrefixWordReturn_head_iter W hW n z]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordReturn_head_iter_m {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (z : Fin 6 → ZMod m) :
    prefixHead ((canonicalPrefixWordReturn (m := m) W)^[m] z) = prefixHead z := by
  rw [canonicalPrefixWordReturn_head_iter W hW]
  simp

theorem canonicalPrefixWordReturn_prefix_head_after_iter {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (j t : Nat)
    (z : Fin 6 → ZMod m) :
    ((List.range t).foldl
        (fun x (s : Nat) =>
          canonicalPrefixMap (s : ZMod m) (canonicalPrefixWordAt W (s : ZMod m)) x)
        ((canonicalPrefixWordReturn (m := m) W)^[j] z)) 0 =
      z 0 + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) -
        ((List.range t).countP
          (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m) := by
  rw [canonicalPrefixWordReturn_coord_zero_fold W (List.range t)]
  have hhead :
      ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 =
        z 0 + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
    simpa [prefixHead] using canonicalPrefixWordReturn_head_iter W hW j z
  rw [hhead]

theorem canonicalPrefixWordReturn_layer_hit_count_eq_one {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    (List.range m).countP
        (fun j : Nat => decide
          (((List.range t).foldl
              (fun x (s : Nat) =>
                canonicalPrefixMap (s : ZMod m) (canonicalPrefixWordAt W (s : ZMod m)) x)
              ((canonicalPrefixWordReturn (m := m) W)^[j] z)) 0 = (t : ZMod m))) = 1 := by
  let debt : ZMod m :=
    ((List.range t).countP
      (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m)
  let offset : ZMod m := z 0 - debt
  have hbase := zmod_affine_range_countP_eq_one
    (m := m) (a := canonicalWordCount W 0) hW.coprime_zero offset (t : ZMod m)
  rw [← hbase]
  apply List.countP_congr
  intro j _hj
  simp only [decide_eq_true_eq]
  rw [canonicalPrefixWordReturn_prefix_head_after_iter W hW.length_eq j t z]
  constructor
  · intro h
    calc
      offset + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) =
          z 0 + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) - debt := by
        dsimp [offset]
        ring
      _ = (t : ZMod m) := h
  · intro h
    calc
      z 0 + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) - debt =
          offset + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
        dsimp [offset]
        ring
      _ = (t : ZMod m) := h

def canonicalPrefixWordLayerHit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixWordPrefixState W t
    ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 = (t : ZMod m)

instance canonicalPrefixWordLayerHit_decidable {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    Decidable (canonicalPrefixWordLayerHit W z j t) := by
  unfold canonicalPrefixWordLayerHit
  infer_instance

theorem canonicalPrefixWordLayerHit_count_eq_one {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    (List.range m).countP
        (fun j : Nat => decide (canonicalPrefixWordLayerHit W z j t)) = 1 := by
  simpa [canonicalPrefixWordLayerHit, canonicalPrefixWordPrefixState] using
    canonicalPrefixWordReturn_layer_hit_count_eq_one W hW z t

theorem canonicalPrefixWordLayerHit_indicator_sum_eq_one {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range m)
        (fun j : Nat => if canonicalPrefixWordLayerHit W z j t then (1 : ZMod m) else 0) =
      1 := by
  classical
  rw [zmod_sum_range_indicator_eq_countP
    (m := m) (p := fun j : Nat => canonicalPrefixWordLayerHit W z j t)]
  rw [canonicalPrefixWordLayerHit_count_eq_one W hW z t]
  simp

def canonicalPrefixWordLayerHitTwo {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixCoordTwoHit (t : ZMod m)
    (canonicalPrefixWordPrefixState W t
      ((canonicalPrefixWordReturn (m := m) W)^[j] z))

instance canonicalPrefixWordLayerHitTwo_decidable {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    Decidable (canonicalPrefixWordLayerHitTwo W z j t) := by
  unfold canonicalPrefixWordLayerHitTwo
  infer_instance

theorem canonicalPrefixWordLayerHitTwo_iff_pair {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    canonicalPrefixWordLayerHitTwo W z j t ↔
      (canonicalPrefixWordPairPrefix W t
          (prefixPair ((canonicalPrefixWordReturn (m := m) W)^[j] z))).1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordPairPrefix W t
          (prefixPair ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2 =
          (t : ZMod m) := by
  rw [canonicalPrefixWordPairPrefix_apply_eq_of_pair]
  simp [canonicalPrefixWordLayerHitTwo, canonicalPrefixCoordTwoHit_iff, prefixPair]

def CanonicalPrefixWordLayerHitTwoSumTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (z : Fin 6 → ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitTwo W z j t then (1 : ZMod m) else 0) =
          -1

theorem zmod_sum_range_const_one {m : Nat} [NeZero m] :
    Finset.sum (Finset.range m) (fun _ : Nat => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.natCast_self]
  simp

theorem zmod_sum_range_mul_self_const_one {m : Nat} [NeZero m] :
    Finset.sum (Finset.range (m * m)) (fun _ : Nat => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul,
    ZMod.natCast_self]
  simp

theorem zmod_sum_range_mul_self_self_const_one {m : Nat} [NeZero m] :
    Finset.sum (Finset.range (m * m * m)) (fun _ : Nat => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul,
    ZMod.natCast_self]
  simp

theorem zmod_sum_range_mul_self_self_self_const_one {m : Nat} [NeZero m] :
    Finset.sum (Finset.range (m * m * m * m)) (fun _ : Nat => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul,
    ZMod.natCast_self]
  simp

theorem zmod_sum_range_mul_self_self_self_self_const_one {m : Nat} [NeZero m] :
    Finset.sum (Finset.range (m * m * m * m * m)) (fun _ : Nat => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul,
    ZMod.natCast_self]
  simp

theorem zmod_univ_sum_const_one {m : Nat} [NeZero m] :
    Finset.sum Finset.univ (fun _ : ZMod m => (1 : ZMod m)) = 0 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    ZMod.natCast_self]
  simp

theorem zmod_univ_sum_indicator_eq_one {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then (1 : ZMod m) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _hb hb
    simp [hb]
  · intro h
    simp at h

theorem zmod_univ_sum_indicator_ne_eq_neg_one {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) = -1 := by
  calc
    Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) =
      Finset.sum Finset.univ (fun _ : ZMod m => (1 : ZMod m)) -
        Finset.sum Finset.univ
          (fun x : ZMod m => if x = t then (1 : ZMod m) else 0) := by
        symm
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t <;> simp [hxt]
    _ = -1 := by
      rw [zmod_univ_sum_const_one, zmod_univ_sum_indicator_eq_one]
      ring

theorem zmod_pair_hit_sum {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m =>
          if p.1 = t ∨ p.2 = t then (1 : ZMod m) else 0) =
      -1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    Finset.sum Finset.univ
        (fun x : ZMod m =>
          Finset.sum Finset.univ
            (fun y : ZMod m =>
              if (x, y).1 = t ∨ (x, y).2 = t then (1 : ZMod m) else 0)) =
      Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t
        · simp [hxt]
        · calc
            Finset.sum Finset.univ
                (fun y : ZMod m =>
                  if (x, y).1 = t ∨ (x, y).2 = t then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun y : ZMod m => if y = t then (1 : ZMod m) else 0) := by
                apply Finset.sum_congr rfl
                intro y _hy
                simp [hxt]
            _ = 1 := zmod_univ_sum_indicator_eq_one t
            _ = (if x = t then 0 else (1 : ZMod m)) := by simp [hxt]
    _ =
      Finset.sum Finset.univ (fun _ : ZMod m => (1 : ZMod m)) -
        Finset.sum Finset.univ
          (fun x : ZMod m => if x = t then (1 : ZMod m) else 0) := by
        symm
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t <;> simp [hxt]
    _ = -1 := by
      rw [zmod_univ_sum_const_one, zmod_univ_sum_indicator_eq_one]
      ring

theorem zmod_triple_hit_sum {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m =>
          if p.1 = t ∨ p.2.1 = t ∨ p.2.2 = t then (1 : ZMod m) else 0) =
      1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    Finset.sum Finset.univ
        (fun x : ZMod m =>
          Finset.sum Finset.univ
            (fun yz : ZMod m × ZMod m =>
              if (x, yz).1 = t ∨ (x, yz).2.1 = t ∨ (x, yz).2.2 = t
              then (1 : ZMod m) else 0)) =
      Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (-1 : ZMod m)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t
        · calc
            Finset.sum Finset.univ
                (fun yz : ZMod m × ZMod m =>
                  if (x, yz).1 = t ∨ (x, yz).2.1 = t ∨ (x, yz).2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ (fun _ : ZMod m × ZMod m => (1 : ZMod m)) := by
                apply Finset.sum_congr rfl
                intro yz _hyz
                simp [hxt]
            _ = 0 := by
              rw [Fintype.sum_prod_type]
              simp
            _ = (if x = t then 0 else (-1 : ZMod m)) := by simp [hxt]
        · calc
            Finset.sum Finset.univ
                (fun yz : ZMod m × ZMod m =>
                  if (x, yz).1 = t ∨ (x, yz).2.1 = t ∨ (x, yz).2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun yz : ZMod m × ZMod m =>
                  if yz.1 = t ∨ yz.2 = t then (1 : ZMod m) else 0) := by
                apply Finset.sum_congr rfl
                intro yz _hyz
                simp [hxt]
            _ = -1 := zmod_pair_hit_sum t
            _ = (if x = t then 0 else (-1 : ZMod m)) := by simp [hxt]
    _ = 1 := by
      calc
        Finset.sum Finset.univ
            (fun x : ZMod m => if x = t then 0 else (-1 : ZMod m)) =
          - Finset.sum Finset.univ
            (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxt : x = t <;> simp [hxt]
        _ = 1 := by
          rw [zmod_univ_sum_indicator_ne_eq_neg_one]
          ring

theorem zmod_quad_hit_sum {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m × ZMod m =>
          if p.1 = t ∨ p.2.1 = t ∨ p.2.2.1 = t ∨ p.2.2.2 = t
          then (1 : ZMod m) else 0) =
      -1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    Finset.sum Finset.univ
        (fun x : ZMod m =>
          Finset.sum Finset.univ
            (fun yzw : ZMod m × ZMod m × ZMod m =>
              if (x, yzw).1 = t ∨ (x, yzw).2.1 = t ∨
                  (x, yzw).2.2.1 = t ∨ (x, yzw).2.2.2 = t
              then (1 : ZMod m) else 0)) =
      Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t
        · calc
            Finset.sum Finset.univ
                (fun yzw : ZMod m × ZMod m × ZMod m =>
                  if (x, yzw).1 = t ∨ (x, yzw).2.1 = t ∨
                      (x, yzw).2.2.1 = t ∨ (x, yzw).2.2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun _ : ZMod m × ZMod m × ZMod m => (1 : ZMod m)) := by
                apply Finset.sum_congr rfl
                intro yzw _hyzw
                simp [hxt]
            _ = 0 := by
              rw [Fintype.sum_prod_type]
              simp
            _ = (if x = t then 0 else (1 : ZMod m)) := by simp [hxt]
        · calc
            Finset.sum Finset.univ
                (fun yzw : ZMod m × ZMod m × ZMod m =>
                  if (x, yzw).1 = t ∨ (x, yzw).2.1 = t ∨
                      (x, yzw).2.2.1 = t ∨ (x, yzw).2.2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun yzw : ZMod m × ZMod m × ZMod m =>
                  if yzw.1 = t ∨ yzw.2.1 = t ∨ yzw.2.2 = t
                  then (1 : ZMod m) else 0) := by
                apply Finset.sum_congr rfl
                intro yzw _hyzw
                simp [hxt]
            _ = 1 := zmod_triple_hit_sum t
            _ = (if x = t then 0 else (1 : ZMod m)) := by simp [hxt]
    _ = -1 := zmod_univ_sum_indicator_ne_eq_neg_one t

theorem zmod_quint_hit_sum {m : Nat} [NeZero m] (t : ZMod m) :
    Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
          if p.1 = t ∨ p.2.1 = t ∨ p.2.2.1 = t ∨ p.2.2.2.1 = t ∨
              p.2.2.2.2 = t
          then (1 : ZMod m) else 0) =
      1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    Finset.sum Finset.univ
        (fun x : ZMod m =>
          Finset.sum Finset.univ
            (fun yzvw : ZMod m × ZMod m × ZMod m × ZMod m =>
              if (x, yzvw).1 = t ∨ (x, yzvw).2.1 = t ∨
                  (x, yzvw).2.2.1 = t ∨ (x, yzvw).2.2.2.1 = t ∨
                    (x, yzvw).2.2.2.2 = t
              then (1 : ZMod m) else 0)) =
      Finset.sum Finset.univ
        (fun x : ZMod m => if x = t then 0 else (-1 : ZMod m)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxt : x = t
        · calc
            Finset.sum Finset.univ
                (fun yzvw : ZMod m × ZMod m × ZMod m × ZMod m =>
                  if (x, yzvw).1 = t ∨ (x, yzvw).2.1 = t ∨
                      (x, yzvw).2.2.1 = t ∨ (x, yzvw).2.2.2.1 = t ∨
                        (x, yzvw).2.2.2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun _ : ZMod m × ZMod m × ZMod m × ZMod m => (1 : ZMod m)) := by
                apply Finset.sum_congr rfl
                intro yzvw _hyzvw
                simp [hxt]
            _ = 0 := by
              rw [Fintype.sum_prod_type]
              simp
            _ = (if x = t then 0 else (-1 : ZMod m)) := by simp [hxt]
        · calc
            Finset.sum Finset.univ
                (fun yzvw : ZMod m × ZMod m × ZMod m × ZMod m =>
                  if (x, yzvw).1 = t ∨ (x, yzvw).2.1 = t ∨
                      (x, yzvw).2.2.1 = t ∨ (x, yzvw).2.2.2.1 = t ∨
                        (x, yzvw).2.2.2.2 = t
                  then (1 : ZMod m) else 0) =
              Finset.sum Finset.univ
                (fun yzvw : ZMod m × ZMod m × ZMod m × ZMod m =>
                  if yzvw.1 = t ∨ yzvw.2.1 = t ∨ yzvw.2.2.1 = t ∨
                      yzvw.2.2.2 = t
                  then (1 : ZMod m) else 0) := by
                apply Finset.sum_congr rfl
                intro yzvw _hyzvw
                simp [hxt]
            _ = -1 := zmod_quad_hit_sum t
            _ = (if x = t then 0 else (-1 : ZMod m)) := by simp [hxt]
    _ = 1 := by
      calc
        Finset.sum Finset.univ
            (fun x : ZMod m => if x = t then 0 else (-1 : ZMod m)) =
          - Finset.sum Finset.univ
            (fun x : ZMod m => if x = t then 0 else (1 : ZMod m)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxt : x = t <;> simp [hxt]
        _ = 1 := by
          rw [zmod_univ_sum_indicator_ne_eq_neg_one]
          ring

theorem fin_eq_of_zmod_natCast_eq {m : Nat} [NeZero m] {a b : Fin m}
    (h : (a.val : ZMod m) = (b.val : ZMod m)) : a = b := by
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv

theorem zmod_sum_range_mul_self_reindex {m : Nat} [NeZero m]
    (f : Nat → ZMod m) :
    Finset.sum (Finset.range (m * m)) f =
      Finset.sum Finset.univ
        (fun a : Fin m =>
          Finset.sum Finset.univ (fun b : Fin m => f (b.val + m * a.val))) := by
  rw [Finset.sum_range]
  symm
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m => f (p.2.val + m * p.1.val))]
  exact Fintype.sum_equiv finProdFinEquiv
    (fun p : Fin m × Fin m => f ((finProdFinEquiv p).val))
    (fun i : Fin (m * m) => f i.val)
    (by intro p; simp [finProdFinEquiv])

theorem zmod_sum_range_mul_self_self_reindex {m : Nat} [NeZero m]
    (f : Nat → ZMod m) :
    Finset.sum (Finset.range (m * m * m)) f =
      Finset.sum Finset.univ
        (fun a : Fin m =>
          Finset.sum Finset.univ
            (fun b : Fin m =>
              Finset.sum Finset.univ
                (fun c : Fin m => f (c.val + m * b.val + (m * m) * a.val)))) := by
  rw [Finset.sum_range]
  symm
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m => f (c.val + m * p.2.val + (m * m) * p.1.val)))]
  rw [← Fintype.sum_prod_type
    (f := fun P : (Fin m × Fin m) × Fin m =>
      f (P.2.val + m * P.1.2.val + (m * m) * P.1.1.val))]
  let e : (Fin m × Fin m) × Fin m ≃ Fin (m * m * m) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finProdFinEquiv
  exact Fintype.sum_equiv e
    (fun P : (Fin m × Fin m) × Fin m =>
      f (P.2.val + m * P.1.2.val + (m * m) * P.1.1.val))
    (fun i : Fin (m * m * m) => f i.val)
    (by
      intro P
      rcases P with ⟨⟨a, b⟩, c⟩
      simp [e, finProdFinEquiv, Nat.mul_add]
      congr 1
      ring)

theorem zmod_sum_range_mul_self_self_self_reindex {m : Nat} [NeZero m]
    (f : Nat → ZMod m) :
    Finset.sum (Finset.range (m * m * m * m)) f =
      Finset.sum Finset.univ
        (fun a : Fin m =>
          Finset.sum Finset.univ
            (fun b : Fin m =>
              Finset.sum Finset.univ
                (fun c : Fin m =>
                  Finset.sum Finset.univ
                    (fun d : Fin m =>
                      f (d.val + m * c.val + (m * m) * b.val +
                        (m * m * m) * a.val))))) := by
  rw [Finset.sum_range]
  symm
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m =>
          Finset.sum Finset.univ
            (fun d : Fin m =>
              f (d.val + m * c.val + (m * m) * p.2.val +
                (m * m * m) * p.1.val))))]
  rw [← Fintype.sum_prod_type
    (f := fun P : (Fin m × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun d : Fin m =>
          f (d.val + m * P.2.val + (m * m) * P.1.2.val +
            (m * m * m) * P.1.1.val)))]
  rw [← Fintype.sum_prod_type
    (f := fun Q : ((Fin m × Fin m) × Fin m) × Fin m =>
      f (Q.2.val + m * Q.1.2.val + (m * m) * Q.1.1.2.val +
        (m * m * m) * Q.1.1.1.val))]
  let e3 : (Fin m × Fin m) × Fin m ≃ Fin (m * m * m) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finProdFinEquiv
  let e4 : ((Fin m × Fin m) × Fin m) × Fin m ≃ Fin (m * m * m * m) :=
    (Equiv.prodCongr e3 (Equiv.refl (Fin m))).trans finProdFinEquiv
  exact Fintype.sum_equiv e4
    (fun Q : ((Fin m × Fin m) × Fin m) × Fin m =>
      f (Q.2.val + m * Q.1.2.val + (m * m) * Q.1.1.2.val +
        (m * m * m) * Q.1.1.1.val))
    (fun i : Fin (m * m * m * m) => f i.val)
    (by
      intro Q
      rcases Q with ⟨⟨⟨a, b⟩, c⟩, d⟩
      simp [e3, e4, finProdFinEquiv, Nat.mul_add]
      congr 1
      ring)

theorem zmod_sum_range_mul_self_self_self_self_reindex {m : Nat} [NeZero m]
    (f : Nat → ZMod m) :
    Finset.sum (Finset.range (m * m * m * m * m)) f =
      Finset.sum Finset.univ
        (fun a : Fin m =>
          Finset.sum Finset.univ
            (fun b : Fin m =>
              Finset.sum Finset.univ
                (fun c : Fin m =>
                  Finset.sum Finset.univ
                    (fun d : Fin m =>
                      Finset.sum Finset.univ
                        (fun e : Fin m =>
                          f (e.val + m * d.val + (m * m) * c.val +
                            (m * m * m) * b.val + (m * m * m * m) * a.val)))))) := by
  rw [Finset.sum_range]
  symm
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m =>
          Finset.sum Finset.univ
            (fun d : Fin m =>
              Finset.sum Finset.univ
                (fun e : Fin m =>
                  f (e.val + m * d.val + (m * m) * c.val +
                    (m * m * m) * p.2.val + (m * m * m * m) * p.1.val)))))]
  rw [← Fintype.sum_prod_type
    (f := fun P : (Fin m × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun d : Fin m =>
          Finset.sum Finset.univ
            (fun e : Fin m =>
              f (e.val + m * d.val + (m * m) * P.2.val +
                (m * m * m) * P.1.2.val +
                  (m * m * m * m) * P.1.1.val))))]
  rw [← Fintype.sum_prod_type
    (f := fun Q : ((Fin m × Fin m) × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun e : Fin m =>
          f (e.val + m * Q.2.val + (m * m) * Q.1.2.val +
            (m * m * m) * Q.1.1.2.val +
              (m * m * m * m) * Q.1.1.1.val)))]
  rw [← Fintype.sum_prod_type
    (f := fun R : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
      f (R.2.val + m * R.1.2.val + (m * m) * R.1.1.2.val +
        (m * m * m) * R.1.1.1.2.val +
          (m * m * m * m) * R.1.1.1.1.val))]
  let e3 : (Fin m × Fin m) × Fin m ≃ Fin (m * m * m) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finProdFinEquiv
  let e4 : ((Fin m × Fin m) × Fin m) × Fin m ≃ Fin (m * m * m * m) :=
    (Equiv.prodCongr e3 (Equiv.refl (Fin m))).trans finProdFinEquiv
  let e5 : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m ≃
      Fin (m * m * m * m * m) :=
    (Equiv.prodCongr e4 (Equiv.refl (Fin m))).trans finProdFinEquiv
  exact Fintype.sum_equiv e5
    (fun R : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
      f (R.2.val + m * R.1.2.val + (m * m) * R.1.1.2.val +
        (m * m * m) * R.1.1.1.2.val +
          (m * m * m * m) * R.1.1.1.1.val))
    (fun i : Fin (m * m * m * m * m) => f i.val)
    (by
      intro R
      rcases R with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
      simp [e3, e4, e5, finProdFinEquiv, Nat.mul_add]
      congr 1
      ring)

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordLayerDebitTwo_iter_sum_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range (m * m))
        (fun j : Nat =>
          canonicalPrefixWordLayerDebitTwo W
            ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
      if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
      else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 3 then (-1 : ZMod m)
      else 0 := by
  classical
  have hhit := hhitTwo W hW z t
  by_cases h0 : canonicalPrefixWordAt W (t : ZMod m) = 0
  · simp [canonicalPrefixWordLayerDebitTwo, canonicalPrefixCoordTwoDebit, h0]
  · by_cases h1 : canonicalPrefixWordAt W (t : ZMod m) = 1
    · simp [h0, h1]
      calc
        Finset.sum (Finset.range (m * m))
            (fun j : Nat =>
              canonicalPrefixWordLayerDebitTwo W
                ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
          Finset.sum (Finset.range (m * m))
            (fun j : Nat =>
              (1 : ZMod m) -
                if canonicalPrefixWordLayerHitTwo W z j t then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hh :
                canonicalPrefixCoordTwoHit (t : ZMod m)
                  (canonicalPrefixWordPrefixState W t
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
              simp [canonicalPrefixWordLayerDebitTwo, canonicalPrefixCoordTwoDebit,
                canonicalPrefixWordLayerHitTwo, h1, hh]
        _ =
          Finset.sum (Finset.range (m * m)) (fun _ : Nat => (1 : ZMod m)) -
            Finset.sum (Finset.range (m * m))
              (fun j : Nat =>
                if canonicalPrefixWordLayerHitTwo W z j t then (1 : ZMod m) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = 1 := by
            rw [zmod_sum_range_mul_self_const_one, hhit]
            ring
    · by_cases h2 : canonicalPrefixWordAt W (t : ZMod m) = 2
      · simp [h0, h1, h2, canonicalPrefixWordLayerDebitTwo,
          canonicalPrefixCoordTwoDebit]
      · by_cases h3 : canonicalPrefixWordAt W (t : ZMod m) = 3
        · simp [h0, h1, h2, h3]
          calc
            Finset.sum (Finset.range (m * m))
                (fun j : Nat =>
                  canonicalPrefixWordLayerDebitTwo W
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
              Finset.sum (Finset.range (m * m))
                (fun j : Nat =>
                  if canonicalPrefixWordLayerHitTwo W z j t then (1 : ZMod m) else 0) := by
                apply Finset.sum_congr rfl
                intro j _hj
                by_cases hh :
                    canonicalPrefixCoordTwoHit (t : ZMod m)
                      (canonicalPrefixWordPrefixState W t
                        ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
                  simp [canonicalPrefixWordLayerDebitTwo, canonicalPrefixCoordTwoDebit,
                    canonicalPrefixWordLayerHitTwo, h3, hh]
            _ = -1 := hhit
        · simp [h0, h1, h2, h3, canonicalPrefixWordLayerDebitTwo,
            canonicalPrefixCoordTwoDebit, zmod_sum_range_mul_self_const_one]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordLayerDebit_iter_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range m)
        (fun j : Nat =>
          canonicalPrefixWordLayerDebit W
            ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
      if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
      else if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m)
      else 0 := by
  classical
  have hhit := canonicalPrefixWordLayerHit_indicator_sum_eq_one W hW z t
  by_cases h0 : canonicalPrefixWordAt W (t : ZMod m) = 0
  · simp [canonicalPrefixWordLayerDebit, canonicalPrefixCoordOneDebit, h0]
  · by_cases h1 : canonicalPrefixWordAt W (t : ZMod m) = 1
    · simp [h0, h1]
      calc
        Finset.sum (Finset.range m)
            (fun j : Nat =>
              canonicalPrefixWordLayerDebit W
                ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
          Finset.sum (Finset.range m)
            (fun j : Nat =>
              (1 : ZMod m) -
                if canonicalPrefixWordLayerHit W z j t then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hh :
                canonicalPrefixWordPrefixState W t
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 = (t : ZMod m) <;>
              simp [canonicalPrefixWordLayerDebit, canonicalPrefixCoordOneDebit,
                canonicalPrefixWordLayerHit, h1, hh]
        _ =
          Finset.sum (Finset.range m) (fun _ : Nat => (1 : ZMod m)) -
            Finset.sum (Finset.range m)
              (fun j : Nat =>
                if canonicalPrefixWordLayerHit W z j t then (1 : ZMod m) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = -1 := by
            rw [zmod_sum_range_const_one, hhit]
            ring
    · by_cases h2 : canonicalPrefixWordAt W (t : ZMod m) = 2
      · simp [h0, h1, h2]
        calc
          Finset.sum (Finset.range m)
              (fun j : Nat =>
                canonicalPrefixWordLayerDebit W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
            Finset.sum (Finset.range m)
              (fun j : Nat =>
                if canonicalPrefixWordLayerHit W z j t then (1 : ZMod m) else 0) := by
              apply Finset.sum_congr rfl
              intro j _hj
              by_cases hh :
                  canonicalPrefixWordPrefixState W t
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z) 0 = (t : ZMod m) <;>
                simp [canonicalPrefixWordLayerDebit, canonicalPrefixCoordOneDebit,
                  canonicalPrefixWordLayerHit, h2, hh]
          _ = 1 := hhit
      · simp [h0, h1, h2, canonicalPrefixWordLayerDebit, canonicalPrefixCoordOneDebit,
          zmod_sum_range_const_one]

theorem canonicalPrefixWordReturnIterDebit_eq_symbol_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturnIterDebit W z m =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m)
          else 0) := by
  calc
    canonicalPrefixWordReturnIterDebit W z m =
        Finset.sum (Finset.range m)
          (fun j : Nat =>
            Finset.sum (Finset.range m)
              (fun t : Nat =>
                canonicalPrefixWordLayerDebit W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          unfold canonicalPrefixWordReturnIterDebit canonicalPrefixWordReturnDebit
          rw [zmod_list_range_sum_eq_finset_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [zmod_list_range_sum_eq_finset_sum]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            Finset.sum (Finset.range m)
              (fun j : Nat =>
                canonicalPrefixWordLayerDebit W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
            else if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m)
            else 0) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact canonicalPrefixWordLayerDebit_iter_sum W hW z t

theorem canonicalPrefixWordReturnIterDebitTwo_eq_symbol_sum_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturnIterDebitTwo W z (m * m) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then (-1 : ZMod m)
          else 0) := by
  calc
    canonicalPrefixWordReturnIterDebitTwo W z (m * m) =
        Finset.sum (Finset.range (m * m))
          (fun j : Nat =>
            Finset.sum (Finset.range m)
              (fun t : Nat =>
                canonicalPrefixWordLayerDebitTwo W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          unfold canonicalPrefixWordReturnIterDebitTwo canonicalPrefixWordReturnDebitTwo
          rw [zmod_list_range_sum_eq_finset_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [zmod_list_range_sum_eq_finset_sum]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            Finset.sum (Finset.range (m * m))
              (fun j : Nat =>
                canonicalPrefixWordLayerDebitTwo W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
            else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 3 then (-1 : ZMod m)
            else 0) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact canonicalPrefixWordLayerDebitTwo_iter_sum_of_hit_two_sum
            hhitTwo W hW z t

theorem canonicalPrefixWordAt_range_count_eq {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (sym : CanonSym) :
    (List.range m).countP
        (fun t : Nat => decide (canonicalPrefixWordAt W (t : ZMod m) = sym)) =
      canonicalWordCount W sym := by
  trans (List.range m).countP
      (fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) == sym)
  · apply List.countP_congr
    intro t _ht
    simp [BEq.beq, decide_eq_true_eq]
  · exact canonicalPrefixWordAt_range_count W hW sym

set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordSymbolDebit_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m)
          else 0) =
      (canonicalWordCount W 2 : ZMod m) - (canonicalWordCount W 1 : ZMod m) := by
  calc
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m)
          else 0) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          (if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m) else 0) -
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro t _ht
        let sym := canonicalPrefixWordAt W (t : ZMod m)
        change
          (if sym = 0 then 0
          else if sym = 1 then (-1 : ZMod m)
          else if sym = 2 then (1 : ZMod m)
          else 0) =
            (if sym = 2 then (1 : ZMod m) else 0) -
              if sym = 1 then (1 : ZMod m) else 0
        by_cases h0 : sym = 0
        · simp [h0]
        · by_cases h1 : sym = 1
          · simp [h0, h1]
          · by_cases h2 : sym = 2
            · simp [h0, h1, h2]
            · simp [h0, h1, h2]
    _ =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 2 then (1 : ZMod m) else 0) -
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (canonicalWordCount W 2 : ZMod m) -
        (canonicalWordCount W 1 : ZMod m) := by
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 2)]
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 1)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (2 : Fin 7)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (1 : Fin 7)]

set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordSymbolDebitTwo_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then (-1 : ZMod m)
          else 0) =
      (canonicalWordCount W 1 : ZMod m) - (canonicalWordCount W 3 : ZMod m) := by
  calc
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then (-1 : ZMod m)
          else 0) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          (if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) -
            if canonicalPrefixWordAt W (t : ZMod m) = 3 then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro t _ht
        let sym := canonicalPrefixWordAt W (t : ZMod m)
        change
          (if sym = 0 then 0
          else if sym = 1 then (1 : ZMod m)
          else if sym = 2 then 0
          else if sym = 3 then (-1 : ZMod m)
          else 0) =
            (if sym = 1 then (1 : ZMod m) else 0) -
              if sym = 3 then (1 : ZMod m) else 0
        by_cases h0 : sym = 0
        · simp [h0]
        · by_cases h1 : sym = 1
          · simp [h0, h1]
          · by_cases h2 : sym = 2
            · simp [h0, h1, h2]
            · by_cases h3 : sym = 3
              · simp [h0, h1, h2, h3]
              · simp [h0, h1, h2, h3]
    _ =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) -
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 3 then (1 : ZMod m) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (canonicalWordCount W 1 : ZMod m) -
        (canonicalWordCount W 3 : ZMod m) := by
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 1)]
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 3)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (1 : Fin 7)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (3 : Fin 7)]

theorem canonicalPrefixWordReturn_base_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W) :
    IsSingleCycleMap (fun x : ZMod m => x + (canonicalWordCount W 0 : ZMod m)) :=
  zmod_add_single_cycle_of_coprime hW.coprime_zero

def canonicalWordDeltaTwoDrift (W : List CanonSym) : Int :=
  Int.ofNat (canonicalWordCount W 1) - Int.ofNat (canonicalWordCount W 2)

def canonicalWordDeltaDrift (W : List CanonSym) (k : CanonSym) : Int :=
  Int.ofNat (canonicalWordCount W 1) - Int.ofNat (canonicalWordCount W k)

theorem canonicalWordDeltaTwoDrift_coprime_abs {m : Nat}
    {W : List CanonSym} (hW : CanonicalWordCertified m W) :
    Nat.Coprime (Int.natAbs (canonicalWordDeltaTwoDrift W)) m := by
  have hdiff := hW.coprime_diff (2 : Fin 7) (by decide)
  have hnatAbs :
      Int.natAbs (canonicalWordDeltaTwoDrift W) =
        Int.natAbs (Int.ofNat (canonicalWordCount W 2) -
          Int.ofNat (canonicalWordCount W 1)) := by
    unfold canonicalWordDeltaTwoDrift
    rw [show Int.ofNat (canonicalWordCount W 1) -
          Int.ofNat (canonicalWordCount W 2) =
        -(Int.ofNat (canonicalWordCount W 2) -
          Int.ofNat (canonicalWordCount W 1)) by ring]
    rw [Int.natAbs_neg]
  rw [hnatAbs]
  exact hdiff

theorem canonicalWordDeltaTwoDrift_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (canonicalWordDeltaTwoDrift W : ZMod m)) := by
  exact zmod_int_add_single_cycle_of_coprime_abs
    (canonicalWordDeltaTwoDrift W)
    (canonicalWordDeltaTwoDrift_coprime_abs hW)

theorem canonicalWordDeltaDrift_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W)
    (k : CanonSym) (hk : 2 ≤ k.val) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (canonicalWordDeltaDrift W k : ZMod m)) := by
  have hdiff := hW.coprime_diff k hk
  have hnatAbs :
      Int.natAbs (canonicalWordDeltaDrift W k) =
        Int.natAbs (Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) := by
    unfold canonicalWordDeltaDrift
    rw [show Int.ofNat (canonicalWordCount W 1) -
          Int.ofNat (canonicalWordCount W k) =
        -(Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) by ring]
    rw [Int.natAbs_neg]
  exact zmod_int_add_single_cycle_of_coprime_abs
    (canonicalWordDeltaDrift W k)
    (by rw [hnatAbs]; exact hdiff)

theorem canonicalWordDeltaDrift_coprime_abs {m : Nat}
    {W : List CanonSym} (hW : CanonicalWordCertified m W)
    (k : CanonSym) (hk : 2 ≤ k.val) :
    Nat.Coprime (Int.natAbs (canonicalWordDeltaDrift W k)) m := by
  have hdiff := hW.coprime_diff k hk
  have hnatAbs :
      Int.natAbs (canonicalWordDeltaDrift W k) =
        Int.natAbs (Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) := by
    unfold canonicalWordDeltaDrift
    rw [show Int.ofNat (canonicalWordCount W 1) -
          Int.ofNat (canonicalWordCount W k) =
        -(Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) by ring]
    rw [Int.natAbs_neg]
  rw [hnatAbs]
  exact hdiff

theorem canonicalWordDeltaDrift_neg_coprime_abs {m : Nat}
    {W : List CanonSym} (hW : CanonicalWordCertified m W)
    (k : CanonSym) (hk : 2 ≤ k.val) :
    Nat.Coprime (Int.natAbs (-(canonicalWordDeltaDrift W k))) m := by
  have hdiff := hW.coprime_diff k hk
  have hnatAbs :
      Int.natAbs (-(canonicalWordDeltaDrift W k)) =
        Int.natAbs (Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) := by
    unfold canonicalWordDeltaDrift
    simp
  rw [hnatAbs]
  exact hdiff

theorem canonicalWordDeltaDrift_neg_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W)
    (k : CanonSym) (hk : 2 ≤ k.val) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (-(canonicalWordDeltaDrift W k) : ZMod m)) := by
  have hdiff := hW.coprime_diff k hk
  have hnatAbs :
      Int.natAbs (-(canonicalWordDeltaDrift W k)) =
        Int.natAbs (Int.ofNat (canonicalWordCount W k) -
          Int.ofNat (canonicalWordCount W 1)) := by
    unfold canonicalWordDeltaDrift
    simp
  simpa [Int.cast_neg] using
    zmod_int_add_single_cycle_of_coprime_abs
      (-(canonicalWordDeltaDrift W k))
      (by rw [hnatAbs]; exact hdiff)

theorem canonicalPrefixWordReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordReturn (m := m) W) := by
  unfold canonicalPrefixWordReturn
  apply foldl_bijective_of_forall_mem
  intro t _
  exact (canonicalPrefixLayerBijective_of_inverse canonicalPrefixLayerInverse)
    (t : ZMod m) (canonicalPrefixWordAt W (t : ZMod m))

def canonicalPrefixWordFiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b : ZMod m) :
    (Fin 5 → ZMod m) → (Fin 5 → ZMod m) :=
  fun tail => prefixTail ((canonicalPrefixWordReturn (m := m) W)^[m] (prefixFiberBase b tail))

theorem canonicalPrefixWordFiberReturn_coord_zero_of_iterDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (b : ZMod m) (tail : Fin 5 → ZMod m) :
    (canonicalPrefixWordFiberReturn W b tail) 0 =
      tail 0 - canonicalPrefixWordReturnIterDebit W (prefixFiberBase b tail) m := by
  unfold canonicalPrefixWordFiberReturn prefixTail
  change
    ((canonicalPrefixWordReturn (m := m) W)^[m] (prefixFiberBase b tail)) 1 =
      tail 0 - canonicalPrefixWordReturnIterDebit W (prefixFiberBase b tail) m
  rw [canonicalPrefixWordReturn_iter_coord_one_sum W m (prefixFiberBase b tail)]
  simp [prefixFiberBase, prefixOfHeadTail]

def CanonicalPrefixWordFiberDebitTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b : ZMod m) (tail : Fin 5 → ZMod m),
        canonicalPrefixWordReturnIterDebit W (prefixFiberBase b tail) m =
          - (canonicalWordDeltaTwoDrift W : ZMod m)

theorem canonicalPrefixWordFiberDebit :
    CanonicalPrefixWordFiberDebitTheorem := by
  intro m _ W hW b tail
  rw [canonicalPrefixWordReturnIterDebit_eq_symbol_sum W hW]
  rw [canonicalPrefixWordSymbolDebit_sum W hW.length_eq]
  simp [canonicalWordDeltaTwoDrift]

def tail5Head {m : Nat} (z : Fin 5 → ZMod m) : ZMod m :=
  z 0

def tail5Tail {m : Nat} (z : Fin 5 → ZMod m) : Fin 4 → ZMod m :=
  fun i => z ⟨i.val + 1, by omega⟩

def tail5OfHeadTail {m : Nat} (x : ZMod m) (tail : Fin 4 → ZMod m) :
    Fin 5 → ZMod m
  | 0 => x
  | 1 => tail 0
  | 2 => tail 1
  | 3 => tail 2
  | 4 => tail 3

@[simp] theorem tail5Head_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 4 → ZMod m) :
    tail5Head (tail5OfHeadTail x tail) = x := by
  rfl

@[simp] theorem tail5Tail_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 4 → ZMod m) :
    tail5Tail (tail5OfHeadTail x tail) = tail := by
  funext i
  fin_cases i <;> rfl

theorem tail5OfHeadTail_head_tail {m : Nat} (z : Fin 5 → ZMod m) :
    tail5OfHeadTail (tail5Head z) (tail5Tail z) = z := by
  funext i
  fin_cases i <;> rfl

def tail5FiberBase {m : Nat} (b : ZMod m) (tail : Fin 4 → ZMod m) :
    Fin 5 → ZMod m :=
  tail5OfHeadTail b tail

theorem tail5FiberBase_surj {m : Nat} (b : ZMod m) :
    ∀ z : Fin 5 → ZMod m, tail5Head z = b → ∃ tail : Fin 4 → ZMod m,
      tail5FiberBase b tail = z := by
  intro z hz
  refine ⟨tail5Tail z, ?_⟩
  unfold tail5FiberBase
  rw [← hz]
  exact tail5OfHeadTail_head_tail z

def CanonicalPrefixWordFiberHeadDriftTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b : ZMod m) (tail : Fin 5 → ZMod m),
        (canonicalPrefixWordFiberReturn W b tail) 0 =
          tail 0 + (canonicalWordDeltaTwoDrift W : ZMod m)

theorem canonicalPrefixWordFiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordFiberDebitTheorem) :
    CanonicalPrefixWordFiberHeadDriftTheorem := by
  intro m _ W hW b tail
  rw [canonicalPrefixWordFiberReturn_coord_zero_of_iterDebit]
  rw [hdebit W hW b tail]
  ring

theorem canonicalPrefixWordFiberHeadDrift :
    CanonicalPrefixWordFiberHeadDriftTheorem :=
  canonicalPrefixWordFiberHeadDrift_of_debit canonicalPrefixWordFiberDebit

def canonicalPrefixWordSubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b₀ b₁ : ZMod m) :
    (Fin 4 → ZMod m) → (Fin 4 → ZMod m) :=
  fun tail => tail5Tail
    ((canonicalPrefixWordFiberReturn W b₀)^[m] (tail5FiberBase b₁ tail))

def CanonicalPrefixWordSubfiberSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ b₀ b₁ : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubfiberReturn W b₀ b₁)

def tail4Head {m : Nat} (z : Fin 4 → ZMod m) : ZMod m :=
  z 0

def tail4Tail {m : Nat} (z : Fin 4 → ZMod m) : Fin 3 → ZMod m :=
  fun i => z ⟨i.val + 1, by omega⟩

def tail4OfHeadTail {m : Nat} (x : ZMod m) (tail : Fin 3 → ZMod m) :
    Fin 4 → ZMod m
  | 0 => x
  | 1 => tail 0
  | 2 => tail 1
  | 3 => tail 2

@[simp] theorem tail4Head_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 3 → ZMod m) :
    tail4Head (tail4OfHeadTail x tail) = x := by
  rfl

@[simp] theorem tail4Tail_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 3 → ZMod m) :
    tail4Tail (tail4OfHeadTail x tail) = tail := by
  funext i
  fin_cases i <;> rfl

theorem tail4OfHeadTail_head_tail {m : Nat} (z : Fin 4 → ZMod m) :
    tail4OfHeadTail (tail4Head z) (tail4Tail z) = z := by
  funext i
  fin_cases i <;> rfl

def tail4FiberBase {m : Nat} (b : ZMod m) (tail : Fin 3 → ZMod m) :
    Fin 4 → ZMod m :=
  tail4OfHeadTail b tail

theorem tail4FiberBase_surj {m : Nat} (b : ZMod m) :
    ∀ z : Fin 4 → ZMod m, tail4Head z = b → ∃ tail : Fin 3 → ZMod m,
      tail4FiberBase b tail = z := by
  intro z hz
  refine ⟨tail4Tail z, ?_⟩
  unfold tail4FiberBase
  rw [← hz]
  exact tail4OfHeadTail_head_tail z

def CanonicalPrefixWordSubfiberHeadDriftTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ : ZMod m) (tail : Fin 4 → ZMod m),
        (canonicalPrefixWordSubfiberReturn W b₀ b₁ tail) 0 =
          tail 0 + (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m)

def canonicalPrefixWordSubsubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b₀ b₁ b₂ : ZMod m) :
    (Fin 3 → ZMod m) → (Fin 3 → ZMod m) :=
  fun tail => tail4Tail
    ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m] (tail4FiberBase b₂ tail))

def CanonicalPrefixWordSubsubfiberSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ b₀ b₁ b₂ : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)

def tail3Head {m : Nat} (z : Fin 3 → ZMod m) : ZMod m :=
  z 0

def tail3Tail {m : Nat} (z : Fin 3 → ZMod m) : Fin 2 → ZMod m :=
  fun i => z ⟨i.val + 1, by omega⟩

def tail3OfHeadTail {m : Nat} (x : ZMod m) (tail : Fin 2 → ZMod m) :
    Fin 3 → ZMod m
  | 0 => x
  | 1 => tail 0
  | 2 => tail 1

@[simp] theorem tail3Head_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 2 → ZMod m) :
    tail3Head (tail3OfHeadTail x tail) = x := by
  rfl

@[simp] theorem tail3Tail_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 2 → ZMod m) :
    tail3Tail (tail3OfHeadTail x tail) = tail := by
  funext i
  fin_cases i <;> rfl

theorem tail3OfHeadTail_head_tail {m : Nat} (z : Fin 3 → ZMod m) :
    tail3OfHeadTail (tail3Head z) (tail3Tail z) = z := by
  funext i
  fin_cases i <;> rfl

def tail3FiberBase {m : Nat} (b : ZMod m) (tail : Fin 2 → ZMod m) :
    Fin 3 → ZMod m :=
  tail3OfHeadTail b tail

theorem tail3FiberBase_surj {m : Nat} (b : ZMod m) :
    ∀ z : Fin 3 → ZMod m, tail3Head z = b → ∃ tail : Fin 2 → ZMod m,
      tail3FiberBase b tail = z := by
  intro z hz
  refine ⟨tail3Tail z, ?_⟩
  unfold tail3FiberBase
  rw [← hz]
  exact tail3OfHeadTail_head_tail z

def CanonicalPrefixWordSubsubfiberHeadDriftTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ : ZMod m) (tail : Fin 3 → ZMod m),
        (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂ tail) 0 =
          tail 0 + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m)

def canonicalPrefixWordSubsubsubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b₀ b₁ b₂ b₃ : ZMod m) :
    (Fin 2 → ZMod m) → (Fin 2 → ZMod m) :=
  fun tail => tail3Tail
    ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m]
      (tail3FiberBase b₃ tail))

def CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ b₀ b₁ b₂ b₃ : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)

def tail2Head {m : Nat} (z : Fin 2 → ZMod m) : ZMod m :=
  z 0

def tail2Tail {m : Nat} (z : Fin 2 → ZMod m) : Fin 1 → ZMod m :=
  fun i => z ⟨i.val + 1, by omega⟩

def tail2OfHeadTail {m : Nat} (x : ZMod m) (tail : Fin 1 → ZMod m) :
    Fin 2 → ZMod m
  | 0 => x
  | 1 => tail 0

@[simp] theorem tail2Head_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 1 → ZMod m) :
    tail2Head (tail2OfHeadTail x tail) = x := by
  rfl

@[simp] theorem tail2Tail_ofHeadTail {m : Nat}
    (x : ZMod m) (tail : Fin 1 → ZMod m) :
    tail2Tail (tail2OfHeadTail x tail) = tail := by
  funext i
  fin_cases i
  rfl

theorem tail2OfHeadTail_head_tail {m : Nat} (z : Fin 2 → ZMod m) :
    tail2OfHeadTail (tail2Head z) (tail2Tail z) = z := by
  funext i
  fin_cases i <;> rfl

def tail2FiberBase {m : Nat} (b : ZMod m) (tail : Fin 1 → ZMod m) :
    Fin 2 → ZMod m :=
  tail2OfHeadTail b tail

theorem tail2FiberBase_surj {m : Nat} (b : ZMod m) :
    ∀ z : Fin 2 → ZMod m, tail2Head z = b → ∃ tail : Fin 1 → ZMod m,
      tail2FiberBase b tail = z := by
  intro z hz
  refine ⟨tail2Tail z, ?_⟩
  unfold tail2FiberBase
  rw [← hz]
  exact tail2OfHeadTail_head_tail z

def CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ b₃ : ZMod m) (tail : Fin 2 → ZMod m),
        (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) 0 =
          tail 0 + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m)

def canonicalPrefixWordSubsubsubsubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b₀ b₁ b₂ b₃ b₄ : ZMod m) :
    (Fin 1 → ZMod m) → (Fin 1 → ZMod m) :=
  fun tail => tail2Tail
    ((canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m]
      (tail2FiberBase b₄ tail))

def CanonicalPrefixWordSubsubsubsubfiberSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ b₀ b₁ b₂ b₃ b₄ : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄)

def tail1Head {m : Nat} (z : Fin 1 → ZMod m) : ZMod m :=
  z 0

def tail1OfHead {m : Nat} (x : ZMod m) : Fin 1 → ZMod m
  | 0 => x

@[simp] theorem tail1Head_ofHead {m : Nat} (x : ZMod m) :
    tail1Head (tail1OfHead x) = x := by
  rfl

theorem tail1OfHead_head {m : Nat} (z : Fin 1 → ZMod m) :
    tail1OfHead (tail1Head z) = z := by
  funext i
  fin_cases i
  rfl

theorem tail1OfHead_bijective {m : Nat} :
    Function.Bijective (tail1OfHead : ZMod m → (Fin 1 → ZMod m)) :=
  bijective_of_inverse tail1OfHead tail1Head
    tail1Head_ofHead tail1OfHead_head

def CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ b₃ b₄ : ZMod m) (tail : Fin 1 → ZMod m),
        (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄ tail) 0 =
          tail 0 + (canonicalWordDeltaDrift W (6 : Fin 7) : ZMod m)

def CanonicalPrefixWordFiberSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ b : ZMod m, IsSingleCycleMap (canonicalPrefixWordFiberReturn W b)

theorem canonicalPrefixWordReturn_iter_m_fiber {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (b : ZMod m) (tail : Fin 5 → ZMod m) :
    (canonicalPrefixWordReturn (m := m) W)^[m] (prefixFiberBase b tail) =
      prefixFiberBase b (canonicalPrefixWordFiberReturn W b tail) := by
  let z := (canonicalPrefixWordReturn (m := m) W)^[m] (prefixFiberBase b tail)
  have hhead : prefixHead z = b := by
    dsimp [z]
    rw [canonicalPrefixWordReturn_head_iter_m W hW]
    simp
  unfold canonicalPrefixWordFiberReturn
  change z = prefixFiberBase b (prefixTail z)
  symm
  calc
    prefixFiberBase b (prefixTail z) = prefixOfHeadTail b (prefixTail z) := rfl
    _ = prefixOfHeadTail (prefixHead z) (prefixTail z) := by rw [hhead]
    _ = z := prefixOfHeadTail_head_tail z

theorem canonicalPrefixWordPairReturn_iter_m_fiber {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (b y : ZMod m) :
    (canonicalPrefixWordPairReturn W)^[m] (b, y) =
      (b, y + (canonicalWordDeltaTwoDrift W : ZMod m)) := by
  let z : Fin 6 → ZMod m := prefixPairBase (b, y)
  change (canonicalPrefixWordPairReturn W)^[m] (prefixPair z) =
    (b, y + (canonicalWordDeltaTwoDrift W : ZMod m))
  rw [canonicalPrefixWordPairReturn_iter_apply_eq_of_pair W m z]
  have hfull :
      (canonicalPrefixWordReturn (m := m) W)^[m] z =
        prefixFiberBase b (canonicalPrefixWordFiberReturn W b (prefixTail z)) := by
    simpa [z, prefixFiberBase, prefixOfHeadTail, prefixTail, prefixPairBase] using
      canonicalPrefixWordReturn_iter_m_fiber W hW.length_eq b (prefixTail z)
  rw [hfull]
  have hhead := canonicalPrefixWordFiberHeadDrift W hW b (prefixTail z)
  apply Prod.ext
  · rfl
  · simpa [prefixPair, prefixFiberBase, prefixOfHeadTail, prefixTail, z, prefixPairBase]
      using hhead

theorem canonicalPrefixWordPairReturn_iter_mul_m {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m,
      (canonicalPrefixWordPairReturn W)^[n * m] p =
        (p.1, p.2 + (n : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m))
  | 0, p => by simp
  | n + 1, p => by
      rcases p with ⟨b, y⟩
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordPairReturn_iter_m_fiber W hW b y]
      rw [canonicalPrefixWordPairReturn_iter_mul_m W hW n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordPairReturn_blockOrbit_bijective
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (p : ZMod m × ZMod m) :
    Function.Bijective
      (fun I : Fin m × Fin m =>
        (canonicalPrefixWordPairReturn W)^[I.2.val + m * I.1.val] p) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro I J hIJ
    rcases I with ⟨a, b⟩
    rcases J with ⟨a', b'⟩
    have hhead := congrArg Prod.fst hIJ
    have hhead' :
        p.1 + (b.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) =
          p.1 + (b'.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
      rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
      rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
      simpa [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_add, add_assoc,
        add_comm, add_left_comm] using hhead
    have hbcast : (b.val : ZMod m) = (b'.val : ZMod m) :=
      (zmod_affine_mul_right_bijective hW.coprime_zero p.1).1 hhead'
    have hb : b = b' := fin_eq_of_zmod_natCast_eq hbcast
    subst b'
    have hcancel :
        (canonicalPrefixWordPairReturn W)^[m * a.val] p =
          (canonicalPrefixWordPairReturn W)^[m * a'.val] p := by
      have hIJ' : (canonicalPrefixWordPairReturn W)^[b.val + m * a.val] p =
          (canonicalPrefixWordPairReturn W)^[b.val + m * a'.val] p := by
        simpa using hIJ
      rw [Function.iterate_add_apply, Function.iterate_add_apply] at hIJ'
      exact (Function.Bijective.iterate
        (canonicalPrefixWordPairReturn_bijective W) b.val).1 hIJ'
    rw [Nat.mul_comm m a.val] at hcancel
    rw [Nat.mul_comm m a'.val] at hcancel
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW a.val p] at hcancel
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW a'.val p] at hcancel
    have hsnd := congrArg Prod.snd hcancel
    have hadelta : (a.val : ZMod m) = (a'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaTwoDrift W)
        (canonicalWordDeltaTwoDrift_coprime_abs hW) p.2).1 (by
          simpa [add_comm, add_left_comm, add_assoc] using hsnd)
    have ha : a = a' := fin_eq_of_zmod_natCast_eq hadelta
    subst a'
    rfl
  · simp

theorem canonicalPrefixWordLayerHitTwoSum :
    CanonicalPrefixWordLayerHitTwoSumTheorem := by
  intro m _ W hW z t
  classical
  rw [zmod_sum_range_mul_self_reindex]
  rw [← Fintype.sum_prod_type
    (f := fun I : Fin m × Fin m =>
      if canonicalPrefixWordLayerHitTwo W z (I.2.val + m * I.1.val) t
      then (1 : ZMod m) else 0)]
  let blockMap : Fin m × Fin m → ZMod m × ZMod m :=
    fun I =>
      (canonicalPrefixWordPairReturn W)^[I.2.val + m * I.1.val] (prefixPair z)
  let orbitMap : Fin m × Fin m → ZMod m × ZMod m :=
    fun I => canonicalPrefixWordPairPrefix W t (blockMap I)
  have hblock : Function.Bijective blockMap := by
    simpa [blockMap] using
      canonicalPrefixWordPairReturn_blockOrbit_bijective W hW (prefixPair z)
  have horbit : Function.Bijective orbitMap := by
    simpa [orbitMap, Function.comp_def] using
      Function.Bijective.comp (canonicalPrefixWordPairPrefix_bijective W t) hblock
  calc
    Finset.sum Finset.univ
        (fun I : Fin m × Fin m =>
          if canonicalPrefixWordLayerHitTwo W z (I.2.val + m * I.1.val) t
          then (1 : ZMod m) else 0) =
      Finset.sum Finset.univ
        (fun I : Fin m × Fin m =>
          if (orbitMap I).1 = (t : ZMod m) ∨ (orbitMap I).2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro I _hI
        have hpair :=
          canonicalPrefixWordPairReturn_iter_apply_eq_of_pair
            W (I.2.val + m * I.1.val) z
        have hiff :
            canonicalPrefixWordLayerHitTwo W z (I.2.val + m * I.1.val) t ↔
              (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2 = (t : ZMod m) := by
          rw [canonicalPrefixWordLayerHitTwo_iff_pair]
          simp [orbitMap, blockMap, hpair]
        by_cases hhit :
            canonicalPrefixWordLayerHitTwo W z (I.2.val + m * I.1.val) t
        · have horb := hiff.mp hhit
          simp [hhit, horb]
        · have hnorb :
              ¬ ((orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2 = (t : ZMod m)) := fun h => hhit (hiff.mpr h)
          simp [hhit, hnorb]
    _ =
      Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m =>
          if p.1 = (t : ZMod m) ∨ p.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        exact Fintype.sum_bijective orbitMap horbit
          (fun I : Fin m × Fin m =>
            if (orbitMap I).1 = (t : ZMod m) ∨ (orbitMap I).2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (fun p : ZMod m × ZMod m =>
            if p.1 = (t : ZMod m) ∨ p.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (by intro I; rfl)
    _ = -1 := zmod_pair_hit_sum (t : ZMod m)

theorem canonicalPrefixWordPairReturn_single_cycle {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W) :
    IsSingleCycleMap (canonicalPrefixWordPairReturn (m := m) W) := by
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordPairReturn (m := m) W)
    (g := fun x : ZMod m => x + (canonicalWordCount W 0 : ZMod m))
    (proj := Prod.fst)
    (fiberBase := fun y : ZMod m => ((0 : ZMod m), y))
    (fiberNext := fun y : ZMod m =>
      y + (canonicalWordDeltaTwoDrift W : ZMod m))
    (returnTime := m)
    (b₀ := 0)
    (canonicalPrefixWordPairReturn_bijective W)
    (by
      intro p
      simpa using canonicalPrefixWordPairReturn_head W hW.length_eq p)
    (by
      intro p hp
      rcases p with ⟨x, y⟩
      refine ⟨y, ?_⟩
      simp at hp
      simp [hp])
    (by
      intro y
      exact canonicalPrefixWordPairReturn_iter_m_fiber W hW 0 y)
    (canonicalPrefixWordReturn_base_single_cycle hW)
    (canonicalWordDeltaTwoDrift_single_cycle hW)

theorem canonicalPrefixWordReturn_iter_mul_m_fiber {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (b : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 5 → ZMod m,
      (canonicalPrefixWordReturn (m := m) W)^[n * m] (prefixFiberBase b tail) =
        prefixFiberBase b ((canonicalPrefixWordFiberReturn W b)^[n] tail)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordReturn_iter_m_fiber W hW b tail]
      rw [canonicalPrefixWordReturn_iter_mul_m_fiber W hW b n]
      rw [← Function.iterate_succ_apply]

theorem canonicalPrefixWordSubfiberReturn_coord_zero_of_iterDebitTwo
    {m : Nat} [NeZero m] (W : List CanonSym) (hW : W.length = m)
    (b₀ b₁ : ZMod m) (tail : Fin 4 → ZMod m) :
    (canonicalPrefixWordSubfiberReturn W b₀ b₁ tail) 0 =
      tail 0 -
        canonicalPrefixWordReturnIterDebitTwo W
          (prefixFiberBase b₀ (tail5FiberBase b₁ tail)) (m * m) := by
  let z := prefixFiberBase b₀ (tail5FiberBase b₁ tail)
  have hiter :=
    canonicalPrefixWordReturn_iter_mul_m_fiber W hW b₀ m (tail5FiberBase b₁ tail)
  have hcoord :
      (canonicalPrefixWordSubfiberReturn W b₀ b₁ tail) 0 =
        ((canonicalPrefixWordReturn (m := m) W)^[m * m] z) 2 := by
    unfold canonicalPrefixWordSubfiberReturn
    dsimp [z]
    have hcoord := congrFun hiter 2
    rw [hcoord]
    rfl
  rw [hcoord]
  rw [canonicalPrefixWordReturn_iter_coord_two_sum W (m * m) z]
  simp [z, prefixFiberBase, prefixOfHeadTail, tail5FiberBase, tail5OfHeadTail]

def CanonicalPrefixWordSubfiberDebitTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ : ZMod m) (tail : Fin 4 → ZMod m),
        canonicalPrefixWordReturnIterDebitTwo W
          (prefixFiberBase b₀ (tail5FiberBase b₁ tail)) (m * m) =
            (canonicalWordDeltaDrift W (3 : Fin 7) : ZMod m)

theorem canonicalPrefixWordSubfiberDebit_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem) :
    CanonicalPrefixWordSubfiberDebitTheorem := by
  intro m _ W hW b₀ b₁ tail
  rw [canonicalPrefixWordReturnIterDebitTwo_eq_symbol_sum_of_hit_two_sum
    hhitTwo W hW]
  rw [canonicalPrefixWordSymbolDebitTwo_sum W hW.length_eq]
  simp [canonicalWordDeltaDrift]

theorem canonicalPrefixWordSubfiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordSubfiberDebitTheorem) :
    CanonicalPrefixWordSubfiberHeadDriftTheorem := by
  intro m _ W hW b₀ b₁ tail
  rw [canonicalPrefixWordSubfiberReturn_coord_zero_of_iterDebitTwo W hW.length_eq]
  rw [hdebit W hW b₀ b₁ tail]
  ring

theorem canonicalPrefixWordSubfiberHeadDrift_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem) :
    CanonicalPrefixWordSubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubfiberHeadDrift_of_debit
    (canonicalPrefixWordSubfiberDebit_of_hit_two_sum hhitTwo)

theorem canonicalPrefixWordSubfiberHeadDrift :
    CanonicalPrefixWordSubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubfiberHeadDrift_of_hit_two_sum
    canonicalPrefixWordLayerHitTwoSum

theorem canonicalPrefixWordFiberReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (b : ZMod m) :
    Function.Bijective (canonicalPrefixWordFiberReturn W b) := by
  let F := canonicalPrefixWordReturn (m := m) W
  have hF : Function.Bijective (F^[m]) :=
    Function.Bijective.iterate (canonicalPrefixWordReturn_bijective W) m
  constructor
  · intro tail₁ tail₂ htail
    have hbase : F^[m] (prefixFiberBase b tail₁) = F^[m] (prefixFiberBase b tail₂) := by
      rw [canonicalPrefixWordReturn_iter_m_fiber W hW b tail₁,
        canonicalPrefixWordReturn_iter_m_fiber W hW b tail₂, htail]
    have hpre : prefixFiberBase b tail₁ = prefixFiberBase b tail₂ := hF.1 hbase
    have := congrArg prefixTail hpre
    simpa [prefixFiberBase] using this
  · intro tail
    rcases hF.2 (prefixFiberBase b tail) with ⟨z, hz⟩
    have hzhead : prefixHead z = b := by
      have hhead := canonicalPrefixWordReturn_head_iter_m W hW z
      change prefixHead (F^[m] z) = prefixHead z at hhead
      rw [hz] at hhead
      simpa using hhead.symm
    rcases prefixFiberBase_surj b z hzhead with ⟨tail₀, htail₀⟩
    refine ⟨tail₀, ?_⟩
    have hbase : F^[m] (prefixFiberBase b tail₀) = prefixFiberBase b tail := by
      rw [htail₀, hz]
    have hbase' := hbase
    rw [canonicalPrefixWordReturn_iter_m_fiber W hW b tail₀] at hbase'
    have := congrArg prefixTail hbase'
    simpa [canonicalPrefixWordFiberReturn, prefixFiberBase] using this

theorem canonicalPrefixWordFiberReturn_head_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b : ZMod m) (tail : Fin 5 → ZMod m) :
    tail5Head (canonicalPrefixWordFiberReturn W b tail) =
      tail5Head tail + (canonicalWordDeltaTwoDrift W : ZMod m) :=
  hhead W hW b tail

theorem canonicalPrefixWordFiberReturn_head_iter_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 5 → ZMod m,
      tail5Head ((canonicalPrefixWordFiberReturn W b)^[n] tail) =
        tail5Head tail + (n : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordFiberReturn_head_of hhead W hW b]
      rw [canonicalPrefixWordFiberReturn_head_iter_of hhead W hW b n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordFiberReturn_head_iter_m_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b : ZMod m) (tail : Fin 5 → ZMod m) :
    tail5Head ((canonicalPrefixWordFiberReturn W b)^[m] tail) = tail5Head tail := by
  rw [canonicalPrefixWordFiberReturn_head_iter_of hhead W hW b]
  simp

theorem canonicalPrefixWordSubfiberReturn_iter_m_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m)
    (tail : Fin 4 → ZMod m) :
    (canonicalPrefixWordFiberReturn W b₀)^[m] (tail5FiberBase b₁ tail) =
      tail5FiberBase b₁ (canonicalPrefixWordSubfiberReturn W b₀ b₁ tail) := by
  let z := (canonicalPrefixWordFiberReturn W b₀)^[m] (tail5FiberBase b₁ tail)
  have hhead_z : tail5Head z = b₁ := by
    dsimp [z]
    rw [canonicalPrefixWordFiberReturn_head_iter_m_of hhead W hW b₀]
    rfl
  unfold canonicalPrefixWordSubfiberReturn
  change z = tail5FiberBase b₁ (tail5Tail z)
  symm
  calc
    tail5FiberBase b₁ (tail5Tail z) = tail5OfHeadTail b₁ (tail5Tail z) := rfl
    _ = tail5OfHeadTail (tail5Head z) (tail5Tail z) := by rw [hhead_z]
    _ = z := tail5OfHeadTail_head_tail z

theorem canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 4 → ZMod m,
      (canonicalPrefixWordFiberReturn W b₀)^[n * m] (tail5FiberBase b₁ tail) =
        tail5FiberBase b₁ ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[n] tail)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordSubfiberReturn_iter_m_of hhead W hW b₀ b₁ tail]
      rw [canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of hhead W hW b₀ b₁ n]
      rw [← Function.iterate_succ_apply]

theorem canonicalPrefixWordTripleReturn_iter_mul_self
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (p : ZMod m × ZMod m × ZMod m) :
    (canonicalPrefixWordTripleReturn W)^[m * m] p =
      (p.1, p.2.1, p.2.2 +
        (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m)) := by
  rcases p with ⟨p0, p1, p2⟩
  let tail4 : Fin 4 → ZMod m := tail4FiberBase p2 (fun _ : Fin 3 => 0)
  let z : Fin 6 → ZMod m := prefixFiberBase p0 (tail5FiberBase p1 tail4)
  have hz : z = prefixTripleBase (p0, p1, p2) := by
    funext k
    fin_cases k <;> rfl
  have hfull :=
    canonicalPrefixWordReturn_iter_mul_m_fiber
      W hW.length_eq p0 m (tail5FiberBase p1 tail4)
  have hsub :=
    canonicalPrefixWordSubfiberReturn_iter_m_of
      canonicalPrefixWordFiberHeadDrift W hW p0 p1 tail4
  have hfull' :
      (canonicalPrefixWordReturn (m := m) W)^[m * m] z =
        prefixFiberBase p0
          (tail5FiberBase p1 (canonicalPrefixWordSubfiberReturn W p0 p1 tail4)) := by
    have hfull0 :
        (canonicalPrefixWordReturn (m := m) W)^[m * m] z =
          prefixFiberBase p0
            ((canonicalPrefixWordFiberReturn W p0)^[m] (tail5FiberBase p1 tail4)) := by
      simpa [z] using hfull
    rw [hsub] at hfull0
    exact hfull0
  rw [show (p0, p1, p2) = prefixTriple (prefixTripleBase (p0, p1, p2)) by rfl]
  rw [canonicalPrefixWordTripleReturn_iter_apply_eq_of_triple
    W (m * m) (prefixTripleBase (p0, p1, p2))]
  change prefixTriple
      ((canonicalPrefixWordReturn (m := m) W)^[m * m] (prefixTripleBase (p0, p1, p2))) =
    (p0, p1, p2 + (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m))
  rw [← hz, hfull']
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · have hhead := canonicalPrefixWordSubfiberHeadDrift W hW p0 p1 tail4
      simpa [prefixTriple, prefixFiberBase, prefixOfHeadTail, tail5FiberBase,
        tail5OfHeadTail, tail4, tail4FiberBase, tail4OfHeadTail] using hhead

theorem canonicalPrefixWordTripleReturn_iter_mul_self_mul
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m,
      (canonicalPrefixWordTripleReturn W)^[n * (m * m)] p =
        (p.1, p.2.1, p.2.2 + (n : ZMod m) *
          (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m))
  | 0, p => by simp
  | n + 1, p => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordTripleReturn_iter_mul_self W hW]
      rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordTripleReturn_blockOrbit_bijective
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (p : ZMod m × ZMod m × ZMod m) :
    Function.Bijective
      (fun I : (Fin m × Fin m) × Fin m =>
        (canonicalPrefixWordTripleReturn W)^[
          I.2.val + m * I.1.2.val + (m * m) * I.1.1.val] p) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro I J hIJ
    rcases I with ⟨⟨a, b⟩, c⟩
    rcases J with ⟨⟨a', b'⟩, c'⟩
    have hhead := congrArg (fun r : ZMod m × ZMod m × ZMod m =>
      (prefixTriplePair r).1) hIJ
    change
      (prefixTriplePair
        ((canonicalPrefixWordTripleReturn W)^[
          c.val + m * b.val + (m * m) * a.val] p)).1 =
      (prefixTriplePair
        ((canonicalPrefixWordTripleReturn W)^[
          c'.val + m * b'.val + (m * m) * a'.val] p)).1 at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    have hhead' :
        p.1 + (c.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) =
          p.1 + (c'.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
      simpa [prefixTriplePair, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        mul_add, add_assoc, add_comm, add_left_comm] using hhead
    have hccast : (c.val : ZMod m) = (c'.val : ZMod m) :=
      (zmod_affine_mul_right_bijective hW.coprime_zero p.1).1 hhead'
    have hc : c = c' := fin_eq_of_zmod_natCast_eq hccast
    subst c'
    have hcancelC :
        (canonicalPrefixWordTripleReturn W)^[m * b.val + (m * m) * a.val] p =
          (canonicalPrefixWordTripleReturn W)^[m * b'.val + (m * m) * a'.val] p := by
      let rI : Nat := m * b.val + (m * m) * a.val
      let rJ : Nat := m * b'.val + (m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordTripleReturn W)^[c.val + rI] p =
            (canonicalPrefixWordTripleReturn W)^[c.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hIJ
      have hIJ'' :
          (canonicalPrefixWordTripleReturn W)^[c.val]
              ((canonicalPrefixWordTripleReturn W)^[rI] p) =
            (canonicalPrefixWordTripleReturn W)^[c.val]
              ((canonicalPrefixWordTripleReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordTripleReturn_bijective W) c.val).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hsnd := congrArg (fun r : ZMod m × ZMod m × ZMod m =>
      (prefixTriplePair r).2) hcancelC
    change
      (prefixTriplePair
        ((canonicalPrefixWordTripleReturn W)^[m * b.val + (m * m) * a.val] p)).2 =
      (prefixTriplePair
        ((canonicalPrefixWordTripleReturn W)^[m * b'.val + (m * m) * a'.val] p)).2 at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    have hbexp : m * b.val + (m * m) * a.val = (b.val + m * a.val) * m := by
      ring
    have hbexp' : m * b'.val + (m * m) * a'.val = (b'.val + m * a'.val) * m := by
      ring
    rw [hbexp, hbexp'] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    have hsnd' :
        p.2.1 + (b.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) =
          p.2.1 + (b'.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) := by
      simpa [prefixTriplePair, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        mul_add, add_assoc, add_comm, add_left_comm] using hsnd
    have hbcast : (b.val : ZMod m) = (b'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaTwoDrift W)
        (canonicalWordDeltaTwoDrift_coprime_abs hW) p.2.1).1 hsnd'
    have hb : b = b' := fin_eq_of_zmod_natCast_eq hbcast
    subst b'
    have hcancelB :
        (canonicalPrefixWordTripleReturn W)^[(m * m) * a.val] p =
          (canonicalPrefixWordTripleReturn W)^[(m * m) * a'.val] p := by
      have hIJ' :
          (canonicalPrefixWordTripleReturn W)^[
              m * b.val + (m * m) * a.val] p =
            (canonicalPrefixWordTripleReturn W)^[
              m * b.val + (m * m) * a'.val] p := by
        simpa using hcancelC
      rw [Function.iterate_add_apply, Function.iterate_add_apply] at hIJ'
      exact (Function.Bijective.iterate
        (canonicalPrefixWordTripleReturn_bijective W) (m * b.val)).1 hIJ'
    rw [show (m * m) * a.val = a.val * (m * m) by ring] at hcancelB
    rw [show (m * m) * a'.val = a'.val * (m * m) by ring] at hcancelB
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW a.val p] at hcancelB
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW a'.val p] at hcancelB
    have hthird := congrArg (fun r : ZMod m × ZMod m × ZMod m => r.2.2) hcancelB
    have hacast : (a.val : ZMod m) = (a'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (-(canonicalWordDeltaDrift W (3 : Fin 7)))
        (canonicalWordDeltaDrift_neg_coprime_abs hW (3 : Fin 7) (by decide))
        p.2.2).1 (by
          simpa [add_assoc, add_comm, add_left_comm] using hthird)
    have ha : a = a' := fin_eq_of_zmod_natCast_eq hacast
    subst a'
    rfl
  · simp
    ring

def canonicalPrefixWordLayerHitThree {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixCoordThreeHit (t : ZMod m)
    (canonicalPrefixWordPrefixState W t
      ((canonicalPrefixWordReturn (m := m) W)^[j] z))

instance canonicalPrefixWordLayerHitThree_decidable {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    Decidable (canonicalPrefixWordLayerHitThree W z j t) := by
  unfold canonicalPrefixWordLayerHitThree
  infer_instance

theorem canonicalPrefixWordLayerHitThree_iff_triple {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    canonicalPrefixWordLayerHitThree W z j t ↔
      (canonicalPrefixWordTriplePrefix W t
          (prefixTriple ((canonicalPrefixWordReturn (m := m) W)^[j] z))).1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordTriplePrefix W t
          (prefixTriple ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordTriplePrefix W t
          (prefixTriple ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2 =
          (t : ZMod m) := by
  rw [canonicalPrefixWordTriplePrefix_apply_eq_of_triple]
  simp [canonicalPrefixWordLayerHitThree, canonicalPrefixCoordThreeHit_iff,
    prefixTriple]

def CanonicalPrefixWordLayerHitThreeSumTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (z : Fin 6 → ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitThree W z j t then (1 : ZMod m) else 0) =
          1

theorem canonicalPrefixWordLayerHitThreeSum :
    CanonicalPrefixWordLayerHitThreeSumTheorem := by
  intro m _ W hW z t
  classical
  rw [zmod_sum_range_mul_self_self_reindex]
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m =>
          if canonicalPrefixWordLayerHitThree W z
            (c.val + m * p.2.val + (m * m) * p.1.val) t
          then (1 : ZMod m) else 0))]
  rw [← Fintype.sum_prod_type
    (f := fun I : (Fin m × Fin m) × Fin m =>
      if canonicalPrefixWordLayerHitThree W z
        (I.2.val + m * I.1.2.val + (m * m) * I.1.1.val) t
      then (1 : ZMod m) else 0)]
  let blockMap : (Fin m × Fin m) × Fin m → ZMod m × ZMod m × ZMod m :=
    fun I =>
      (canonicalPrefixWordTripleReturn W)^[
        I.2.val + m * I.1.2.val + (m * m) * I.1.1.val] (prefixTriple z)
  let orbitMap : (Fin m × Fin m) × Fin m → ZMod m × ZMod m × ZMod m :=
    fun I => canonicalPrefixWordTriplePrefix W t (blockMap I)
  have hblock : Function.Bijective blockMap := by
    simpa [blockMap] using
      canonicalPrefixWordTripleReturn_blockOrbit_bijective W hW (prefixTriple z)
  have horbit : Function.Bijective orbitMap := by
    simpa [orbitMap, Function.comp_def] using
      Function.Bijective.comp (canonicalPrefixWordTriplePrefix_bijective W t) hblock
  calc
    Finset.sum Finset.univ
        (fun I : (Fin m × Fin m) × Fin m =>
          if canonicalPrefixWordLayerHitThree W z
            (I.2.val + m * I.1.2.val + (m * m) * I.1.1.val) t
          then (1 : ZMod m) else 0) =
      Finset.sum Finset.univ
        (fun I : (Fin m × Fin m) × Fin m =>
          if (orbitMap I).1 = (t : ZMod m) ∨
              (orbitMap I).2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro I _hI
        have htriple :=
          canonicalPrefixWordTripleReturn_iter_apply_eq_of_triple
            W (I.2.val + m * I.1.2.val + (m * m) * I.1.1.val) z
        have hiff :
            canonicalPrefixWordLayerHitThree W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.val) t ↔
              (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2 = (t : ZMod m) := by
          rw [canonicalPrefixWordLayerHitThree_iff_triple]
          simp [orbitMap, blockMap, htriple]
        by_cases hhit :
            canonicalPrefixWordLayerHitThree W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.val) t
        · have horb := hiff.mp hhit
          simp [hhit, horb]
        · have hnorb :
              ¬ ((orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2 = (t : ZMod m)) := fun h => hhit (hiff.mpr h)
          simp [hhit, hnorb]
    _ =
      Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m =>
          if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
              p.2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        exact Fintype.sum_bijective orbitMap horbit
          (fun I : (Fin m × Fin m) × Fin m =>
            if (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (fun p : ZMod m × ZMod m × ZMod m =>
            if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
                p.2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (by intro I; rfl)
    _ = 1 := zmod_triple_hit_sum (t : ZMod m)

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordLayerDebitThree_iter_sum_of_hit_three_sum
    (hhitThree : CanonicalPrefixWordLayerHitThreeSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range (m * m * m))
        (fun j : Nat =>
          canonicalPrefixWordLayerDebitThree W
            ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
      if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
      else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m)
      else 0 := by
  classical
  have hhit := hhitThree W hW z t
  by_cases h0 : canonicalPrefixWordAt W (t : ZMod m) = 0
  · simp [canonicalPrefixWordLayerDebitThree, canonicalPrefixCoordThreeDebit, h0]
  · by_cases h1 : canonicalPrefixWordAt W (t : ZMod m) = 1
    · simp [h0, h1]
      calc
        Finset.sum (Finset.range (m * m * m))
            (fun j : Nat =>
              canonicalPrefixWordLayerDebitThree W
                ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
          Finset.sum (Finset.range (m * m * m))
            (fun j : Nat =>
              (1 : ZMod m) -
                if canonicalPrefixWordLayerHitThree W z j t then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hh :
                canonicalPrefixCoordThreeHit (t : ZMod m)
                  (canonicalPrefixWordPrefixState W t
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
              simp [canonicalPrefixWordLayerDebitThree, canonicalPrefixCoordThreeDebit,
                canonicalPrefixWordLayerHitThree, h1, hh]
        _ =
          Finset.sum (Finset.range (m * m * m)) (fun _ : Nat => (1 : ZMod m)) -
            Finset.sum (Finset.range (m * m * m))
              (fun j : Nat =>
                if canonicalPrefixWordLayerHitThree W z j t then (1 : ZMod m) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = -1 := by
            rw [zmod_sum_range_mul_self_self_const_one, hhit]
            ring
    · by_cases h2 : canonicalPrefixWordAt W (t : ZMod m) = 2
      · simp [h0, h1, h2, canonicalPrefixWordLayerDebitThree,
          canonicalPrefixCoordThreeDebit]
      · by_cases h3 : canonicalPrefixWordAt W (t : ZMod m) = 3
        · simp [h0, h1, h2, h3, canonicalPrefixWordLayerDebitThree,
            canonicalPrefixCoordThreeDebit]
        · by_cases h4 : canonicalPrefixWordAt W (t : ZMod m) = 4
          · simp [h0, h1, h2, h3, h4]
            calc
              Finset.sum (Finset.range (m * m * m))
                  (fun j : Nat =>
                    canonicalPrefixWordLayerDebitThree W
                      ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
                Finset.sum (Finset.range (m * m * m))
                  (fun j : Nat =>
                    if canonicalPrefixWordLayerHitThree W z j t then (1 : ZMod m) else 0) := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  by_cases hh :
                      canonicalPrefixCoordThreeHit (t : ZMod m)
                        (canonicalPrefixWordPrefixState W t
                          ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
                    simp [canonicalPrefixWordLayerDebitThree, canonicalPrefixCoordThreeDebit,
                      canonicalPrefixWordLayerHitThree, h4, hh]
              _ = 1 := hhit
          · simp [h0, h1, h2, h3, h4, canonicalPrefixWordLayerDebitThree,
              canonicalPrefixCoordThreeDebit, zmod_sum_range_mul_self_self_const_one]

theorem canonicalPrefixWordReturnIterDebitThree_eq_symbol_sum_of_hit_three_sum
    (hhitThree : CanonicalPrefixWordLayerHitThreeSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturnIterDebitThree W z (m * m * m) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m)
          else 0) := by
  calc
    canonicalPrefixWordReturnIterDebitThree W z (m * m * m) =
        Finset.sum (Finset.range (m * m * m))
          (fun j : Nat =>
            Finset.sum (Finset.range m)
              (fun t : Nat =>
                canonicalPrefixWordLayerDebitThree W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          unfold canonicalPrefixWordReturnIterDebitThree canonicalPrefixWordReturnDebitThree
          rw [zmod_list_range_sum_eq_finset_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [zmod_list_range_sum_eq_finset_sum]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            Finset.sum (Finset.range (m * m * m))
              (fun j : Nat =>
                canonicalPrefixWordLayerDebitThree W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
            else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m)
            else 0) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact canonicalPrefixWordLayerDebitThree_iter_sum_of_hit_three_sum
            hhitThree W hW z t

set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordSymbolDebitThree_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m)
          else 0) =
      (canonicalWordCount W 4 : ZMod m) - (canonicalWordCount W 1 : ZMod m) := by
  calc
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m)
          else 0) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          (if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m) else 0) -
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro t _ht
        let sym := canonicalPrefixWordAt W (t : ZMod m)
        change
          (if sym = 0 then 0
          else if sym = 1 then (-1 : ZMod m)
          else if sym = 2 then 0
          else if sym = 3 then 0
          else if sym = 4 then (1 : ZMod m)
          else 0) =
            (if sym = 4 then (1 : ZMod m) else 0) -
              if sym = 1 then (1 : ZMod m) else 0
        by_cases h0 : sym = 0
        · simp [h0]
        · by_cases h1 : sym = 1
          · simp [h0, h1]
          · by_cases h2 : sym = 2
            · simp [h0, h1, h2]
            · by_cases h3 : sym = 3
              · simp [h0, h1, h2, h3]
              · by_cases h4 : sym = 4
                · simp [h0, h1, h2, h3, h4]
                · simp [h0, h1, h2, h3, h4]
    _ =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 4 then (1 : ZMod m) else 0) -
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (canonicalWordCount W 4 : ZMod m) -
        (canonicalWordCount W 1 : ZMod m) := by
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 4)]
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 1)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (4 : Fin 7)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (1 : Fin 7)]

theorem canonicalPrefixWordSubfiberReturn_bijective_of
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m) :
    Function.Bijective (canonicalPrefixWordSubfiberReturn W b₀ b₁) := by
  let F := canonicalPrefixWordFiberReturn W b₀
  have hF : Function.Bijective (F^[m]) :=
    Function.Bijective.iterate
      (canonicalPrefixWordFiberReturn_bijective W hW.length_eq b₀) m
  constructor
  · intro tail₁ tail₂ htail
    have hbase : F^[m] (tail5FiberBase b₁ tail₁) =
        F^[m] (tail5FiberBase b₁ tail₂) := by
      rw [canonicalPrefixWordSubfiberReturn_iter_m_of hhead W hW b₀ b₁ tail₁,
        canonicalPrefixWordSubfiberReturn_iter_m_of hhead W hW b₀ b₁ tail₂, htail]
    have hpre : tail5FiberBase b₁ tail₁ = tail5FiberBase b₁ tail₂ := hF.1 hbase
    have := congrArg tail5Tail hpre
    simpa [tail5FiberBase] using this
  · intro tail
    rcases hF.2 (tail5FiberBase b₁ tail) with ⟨z, hz⟩
    have hzhead : tail5Head z = b₁ := by
      have hhead_iter := canonicalPrefixWordFiberReturn_head_iter_m_of hhead W hW b₀ z
      change tail5Head (F^[m] z) = tail5Head z at hhead_iter
      rw [hz] at hhead_iter
      simpa using hhead_iter.symm
    rcases tail5FiberBase_surj b₁ z hzhead with ⟨tail₀, htail₀⟩
    refine ⟨tail₀, ?_⟩
    have hbase : F^[m] (tail5FiberBase b₁ tail₀) = tail5FiberBase b₁ tail := by
      rw [htail₀, hz]
    have hbase' := hbase
    rw [canonicalPrefixWordSubfiberReturn_iter_m_of hhead W hW b₀ b₁ tail₀] at hbase'
    have := congrArg tail5Tail hbase'
    simpa [canonicalPrefixWordSubfiberReturn, tail5FiberBase] using this

theorem canonicalPrefixWordSubfiberReturn_head_of
    (hhead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m)
    (tail : Fin 4 → ZMod m) :
    tail4Head (canonicalPrefixWordSubfiberReturn W b₀ b₁ tail) =
      tail4Head tail + (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m) :=
  hhead W hW b₀ b₁ tail

theorem canonicalPrefixWordSubfiberReturn_head_iter_of
    (hhead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 4 → ZMod m,
      tail4Head ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[n] tail) =
        tail4Head tail + (n : ZMod m) *
          (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordSubfiberReturn_head_of hhead W hW b₀ b₁]
      rw [canonicalPrefixWordSubfiberReturn_head_iter_of hhead W hW b₀ b₁ n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordSubfiberReturn_head_iter_m_of
    (hhead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ : ZMod m)
    (tail : Fin 4 → ZMod m) :
    tail4Head ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m] tail) =
      tail4Head tail := by
  rw [canonicalPrefixWordSubfiberReturn_head_iter_of hhead W hW b₀ b₁]
  simp

theorem canonicalPrefixWordSubsubfiberReturn_iter_m_of
    (hhead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m)
    (tail : Fin 3 → ZMod m) :
    (canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m] (tail4FiberBase b₂ tail) =
      tail4FiberBase b₂ (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂ tail) := by
  let z := (canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m] (tail4FiberBase b₂ tail)
  have hhead_z : tail4Head z = b₂ := by
    dsimp [z]
    rw [canonicalPrefixWordSubfiberReturn_head_iter_m_of hhead W hW b₀ b₁]
    rfl
  unfold canonicalPrefixWordSubsubfiberReturn
  change z = tail4FiberBase b₂ (tail4Tail z)
  symm
  calc
    tail4FiberBase b₂ (tail4Tail z) = tail4OfHeadTail b₂ (tail4Tail z) := rfl
    _ = tail4OfHeadTail (tail4Head z) (tail4Tail z) := by rw [hhead_z]
    _ = z := tail4OfHeadTail_head_tail z

theorem canonicalPrefixWordSubfiberReturn_iter_mul_m_subsubfiber_of
    (hhead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 3 → ZMod m,
      (canonicalPrefixWordSubfiberReturn W b₀ b₁)^[n * m]
          (tail4FiberBase b₂ tail) =
        tail4FiberBase b₂
          ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[n] tail)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordSubsubfiberReturn_iter_m_of hhead W hW b₀ b₁ b₂ tail]
      rw [canonicalPrefixWordSubfiberReturn_iter_mul_m_subsubfiber_of
        hhead W hW b₀ b₁ b₂ n]
      rw [← Function.iterate_succ_apply]

theorem canonicalPrefixWordSubsubfiberReturn_coord_zero_of_iterDebitThree
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (b₀ b₁ b₂ : ZMod m) (tail : Fin 3 → ZMod m) :
    (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂ tail) 0 =
      tail 0 -
        canonicalPrefixWordReturnIterDebitThree W
          (prefixFiberBase b₀ (tail5FiberBase b₁ (tail4FiberBase b₂ tail)))
          (m * m * m) := by
  let tail4 : Fin 4 → ZMod m := tail4FiberBase b₂ tail
  let tail5 : Fin 5 → ZMod m := tail5FiberBase b₁ tail4
  let z : Fin 6 → ZMod m := prefixFiberBase b₀ tail5
  have hfull0 :
      (canonicalPrefixWordReturn (m := m) W)^[m * m * m] z =
        prefixFiberBase b₀ ((canonicalPrefixWordFiberReturn W b₀)^[m * m] tail5) := by
    simpa [z] using
      canonicalPrefixWordReturn_iter_mul_m_fiber
        W hW.length_eq b₀ (m * m) tail5
  have hfiber :
      (canonicalPrefixWordFiberReturn W b₀)^[m * m] tail5 =
        tail5FiberBase b₁
          ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m] tail4) := by
    simpa [tail5] using
      canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
        canonicalPrefixWordFiberHeadDrift W hW b₀ b₁ m tail4
  rw [hfiber] at hfull0
  have hcoord :
      (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂ tail) 0 =
        ((canonicalPrefixWordReturn (m := m) W)^[m * m * m] z) 3 := by
    unfold canonicalPrefixWordSubsubfiberReturn
    rw [hfull0]
    rfl
  rw [hcoord]
  rw [canonicalPrefixWordReturn_iter_coord_three_sum W (m * m * m) z]
  simp [z, tail5, tail4, prefixFiberBase, prefixOfHeadTail, tail5FiberBase,
    tail5OfHeadTail, tail4FiberBase, tail4OfHeadTail]

def CanonicalPrefixWordSubsubfiberDebitTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ : ZMod m) (tail : Fin 3 → ZMod m),
        canonicalPrefixWordReturnIterDebitThree W
          (prefixFiberBase b₀ (tail5FiberBase b₁ (tail4FiberBase b₂ tail)))
          (m * m * m) =
            (-(canonicalWordDeltaDrift W (4 : Fin 7)) : ZMod m)

theorem canonicalPrefixWordSubsubfiberDebit_of_hit_three_sum
    (hhitThree : CanonicalPrefixWordLayerHitThreeSumTheorem) :
    CanonicalPrefixWordSubsubfiberDebitTheorem := by
  intro m _ W hW b₀ b₁ b₂ tail
  rw [canonicalPrefixWordReturnIterDebitThree_eq_symbol_sum_of_hit_three_sum
    hhitThree W hW]
  rw [canonicalPrefixWordSymbolDebitThree_sum W hW.length_eq]
  simp [canonicalWordDeltaDrift]

theorem canonicalPrefixWordSubsubfiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordSubsubfiberDebitTheorem) :
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem := by
  intro m _ W hW b₀ b₁ b₂ tail
  rw [canonicalPrefixWordSubsubfiberReturn_coord_zero_of_iterDebitThree W hW]
  rw [hdebit W hW b₀ b₁ b₂ tail]
  ring

theorem canonicalPrefixWordSubsubfiberHeadDrift_of_hit_three_sum
    (hhitThree : CanonicalPrefixWordLayerHitThreeSumTheorem) :
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubfiberHeadDrift_of_debit
    (canonicalPrefixWordSubsubfiberDebit_of_hit_three_sum hhitThree)

theorem canonicalPrefixWordSubsubfiberHeadDrift :
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubfiberHeadDrift_of_hit_three_sum
    canonicalPrefixWordLayerHitThreeSum

theorem canonicalPrefixWordQuadReturn_iter_mul_cube
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    (canonicalPrefixWordQuadReturn W)^[m * m * m] p =
      (p.1, p.2.1, p.2.2.1,
        p.2.2.2 + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m)) := by
  rcases p with ⟨p0, p1, p2, p3⟩
  let tail3 : Fin 3 → ZMod m := tail3FiberBase p3 (fun _ : Fin 2 => 0)
  let tail4 : Fin 4 → ZMod m := tail4FiberBase p2 tail3
  let tail5 : Fin 5 → ZMod m := tail5FiberBase p1 tail4
  let z : Fin 6 → ZMod m := prefixFiberBase p0 tail5
  have hz : z = prefixQuadBase (p0, p1, p2, p3) := by
    funext k
    fin_cases k <;> rfl
  have hfull :
      (canonicalPrefixWordReturn (m := m) W)^[m * m * m] z =
        prefixFiberBase p0 ((canonicalPrefixWordFiberReturn W p0)^[m * m] tail5) := by
    simpa [z] using
      canonicalPrefixWordReturn_iter_mul_m_fiber W hW.length_eq p0 (m * m) tail5
  have hfiber :
      (canonicalPrefixWordFiberReturn W p0)^[m * m] tail5 =
        tail5FiberBase p1
          ((canonicalPrefixWordSubfiberReturn W p0 p1)^[m] tail4) := by
    simpa [tail5] using
      canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
        canonicalPrefixWordFiberHeadDrift W hW p0 p1 m tail4
  have hsub :
      (canonicalPrefixWordSubfiberReturn W p0 p1)^[m] tail4 =
        tail4FiberBase p2 (canonicalPrefixWordSubsubfiberReturn W p0 p1 p2 tail3) := by
    simpa [tail4] using
      canonicalPrefixWordSubsubfiberReturn_iter_m_of
        canonicalPrefixWordSubfiberHeadDrift W hW p0 p1 p2 tail3
  rw [hfiber, hsub] at hfull
  rw [show (p0, p1, p2, p3) = prefixQuad (prefixQuadBase (p0, p1, p2, p3)) by rfl]
  rw [canonicalPrefixWordQuadReturn_iter_apply_eq_of_quad
    W (m * m * m) (prefixQuadBase (p0, p1, p2, p3))]
  change prefixQuad
      ((canonicalPrefixWordReturn (m := m) W)^[m * m * m]
        (prefixQuadBase (p0, p1, p2, p3))) =
    (p0, p1, p2, p3 + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m))
  rw [← hz, hfull]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · have hhead := canonicalPrefixWordSubsubfiberHeadDrift W hW p0 p1 p2 tail3
        simpa [prefixQuad, prefixFiberBase, prefixOfHeadTail, tail5FiberBase,
          tail5OfHeadTail, tail4FiberBase, tail4OfHeadTail, tail3,
          tail3FiberBase, tail3OfHeadTail] using hhead

theorem canonicalPrefixWordQuadReturn_iter_mul_cube_mul
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m × ZMod m,
      (canonicalPrefixWordQuadReturn W)^[n * (m * m * m)] p =
        (p.1, p.2.1, p.2.2.1,
          p.2.2.2 + (n : ZMod m) *
            (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m))
  | 0, p => by simp
  | n + 1, p => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordQuadReturn_iter_mul_cube W hW]
      rw [canonicalPrefixWordQuadReturn_iter_mul_cube_mul W hW n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordQuadReturn_blockOrbit_bijective
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (p : ZMod m × ZMod m × ZMod m × ZMod m) :
    Function.Bijective
      (fun I : ((Fin m × Fin m) × Fin m) × Fin m =>
        (canonicalPrefixWordQuadReturn W)^[
          I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
            (m * m * m) * I.1.1.1.val] p) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro I J hIJ
    rcases I with ⟨⟨⟨a, b⟩, c⟩, d⟩
    rcases J with ⟨⟨⟨a', b'⟩, c'⟩, d'⟩
    have hhead := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixTriplePair (prefixQuadTriple r)).1) hIJ
    change
      (prefixTriplePair (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          d.val + m * c.val + (m * m) * b.val + (m * m * m) * a.val] p))).1 =
      (prefixTriplePair (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          d'.val + m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val] p))).1
        at hhead
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hhead
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    have hhead' :
        p.1 + (d.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) =
          p.1 + (d'.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
      simpa [prefixQuadTriple, prefixTriplePair, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, mul_add, add_assoc, add_comm, add_left_comm] using hhead
    have hdcast : (d.val : ZMod m) = (d'.val : ZMod m) :=
      (zmod_affine_mul_right_bijective hW.coprime_zero p.1).1 hhead'
    have hd : d = d' := fin_eq_of_zmod_natCast_eq hdcast
    subst d'
    have hcancelD :
        (canonicalPrefixWordQuadReturn W)^[
            m * c.val + (m * m) * b.val + (m * m * m) * a.val] p =
          (canonicalPrefixWordQuadReturn W)^[
            m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val] p := by
      let rI : Nat := m * c.val + (m * m) * b.val + (m * m * m) * a.val
      let rJ : Nat := m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordQuadReturn W)^[d.val + rI] p =
            (canonicalPrefixWordQuadReturn W)^[d.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hIJ
      have hIJ'' :
          (canonicalPrefixWordQuadReturn W)^[d.val]
              ((canonicalPrefixWordQuadReturn W)^[rI] p) =
            (canonicalPrefixWordQuadReturn W)^[d.val]
              ((canonicalPrefixWordQuadReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordQuadReturn_bijective W) d.val).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hsnd := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixTriplePair (prefixQuadTriple r)).2) hcancelD
    change
      (prefixTriplePair (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          m * c.val + (m * m) * b.val + (m * m * m) * a.val] p))).2 =
      (prefixTriplePair (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val] p))).2
        at hsnd
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hsnd
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    have hcexp :
        m * c.val + (m * m) * b.val + (m * m * m) * a.val =
          (c.val + m * b.val + (m * m) * a.val) * m := by
      ring
    have hcexp' :
        m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val =
          (c'.val + m * b'.val + (m * m) * a'.val) * m := by
      ring
    rw [hcexp, hcexp'] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    have hsnd' :
        p.2.1 + (c.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) =
          p.2.1 + (c'.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) := by
      simpa [prefixQuadTriple, prefixTriplePair, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, mul_add, add_assoc, add_comm, add_left_comm] using hsnd
    have hccast : (c.val : ZMod m) = (c'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaTwoDrift W)
        (canonicalWordDeltaTwoDrift_coprime_abs hW) p.2.1).1 hsnd'
    have hc : c = c' := fin_eq_of_zmod_natCast_eq hccast
    subst c'
    have hcancelC :
        (canonicalPrefixWordQuadReturn W)^[
            (m * m) * b.val + (m * m * m) * a.val] p =
          (canonicalPrefixWordQuadReturn W)^[
            (m * m) * b'.val + (m * m * m) * a'.val] p := by
      let rI : Nat := (m * m) * b.val + (m * m * m) * a.val
      let rJ : Nat := (m * m) * b'.val + (m * m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordQuadReturn W)^[m * c.val + rI] p =
            (canonicalPrefixWordQuadReturn W)^[m * c.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hcancelD
      have hIJ'' :
          (canonicalPrefixWordQuadReturn W)^[m * c.val]
              ((canonicalPrefixWordQuadReturn W)^[rI] p) =
            (canonicalPrefixWordQuadReturn W)^[m * c.val]
              ((canonicalPrefixWordQuadReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordQuadReturn_bijective W) (m * c.val)).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hthird := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixQuadTriple r).2.2) hcancelC
    change
      (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          (m * m) * b.val + (m * m * m) * a.val] p)).2.2 =
      (prefixQuadTriple
        ((canonicalPrefixWordQuadReturn W)^[
          (m * m) * b'.val + (m * m * m) * a'.val] p)).2.2 at hthird
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hthird
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hthird
    have hbexp :
        (m * m) * b.val + (m * m * m) * a.val =
          (b.val + m * a.val) * (m * m) := by
      ring
    have hbexp' :
        (m * m) * b'.val + (m * m * m) * a'.val =
          (b'.val + m * a'.val) * (m * m) := by
      ring
    rw [hbexp, hbexp'] at hthird
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW] at hthird
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW] at hthird
    have hthird' :
        p.2.2.1 + (b.val : ZMod m) *
            (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m) =
          p.2.2.1 + (b'.val : ZMod m) *
            (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m) := by
      simpa [prefixQuadTriple, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        mul_add, add_assoc, add_comm, add_left_comm] using hthird
    have hbcast : (b.val : ZMod m) = (b'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (-(canonicalWordDeltaDrift W (3 : Fin 7)))
        (canonicalWordDeltaDrift_neg_coprime_abs hW (3 : Fin 7) (by decide))
        p.2.2.1).1 (by simpa [Int.cast_neg] using hthird')
    have hb : b = b' := fin_eq_of_zmod_natCast_eq hbcast
    subst b'
    have hcancelB :
        (canonicalPrefixWordQuadReturn W)^[(m * m * m) * a.val] p =
          (canonicalPrefixWordQuadReturn W)^[(m * m * m) * a'.val] p := by
      have hIJ' :
          (canonicalPrefixWordQuadReturn W)^[
              (m * m) * b.val + (m * m * m) * a.val] p =
            (canonicalPrefixWordQuadReturn W)^[
              (m * m) * b.val + (m * m * m) * a'.val] p := by
        simpa using hcancelC
      rw [Function.iterate_add_apply, Function.iterate_add_apply] at hIJ'
      exact (Function.Bijective.iterate
        (canonicalPrefixWordQuadReturn_bijective W) ((m * m) * b.val)).1 hIJ'
    rw [show (m * m * m) * a.val = a.val * (m * m * m) by ring] at hcancelB
    rw [show (m * m * m) * a'.val = a'.val * (m * m * m) by ring] at hcancelB
    rw [canonicalPrefixWordQuadReturn_iter_mul_cube_mul W hW a.val p] at hcancelB
    rw [canonicalPrefixWordQuadReturn_iter_mul_cube_mul W hW a'.val p] at hcancelB
    have hfourth := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.2) hcancelB
    have hacast : (a.val : ZMod m) = (a'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaDrift W (4 : Fin 7))
        (canonicalWordDeltaDrift_coprime_abs hW (4 : Fin 7) (by decide))
        p.2.2.2).1 (by
          simpa [add_assoc, add_comm, add_left_comm] using hfourth)
    have ha : a = a' := fin_eq_of_zmod_natCast_eq hacast
    subst a'
    rfl
  · simp
    ring

def canonicalPrefixWordLayerHitFour {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixCoordFourHit (t : ZMod m)
    (canonicalPrefixWordPrefixState W t
      ((canonicalPrefixWordReturn (m := m) W)^[j] z))

instance canonicalPrefixWordLayerHitFour_decidable {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    Decidable (canonicalPrefixWordLayerHitFour W z j t) := by
  unfold canonicalPrefixWordLayerHitFour
  infer_instance

theorem canonicalPrefixWordLayerHitFour_iff_quad {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    canonicalPrefixWordLayerHitFour W z j t ↔
      (canonicalPrefixWordQuadPrefix W t
          (prefixQuad ((canonicalPrefixWordReturn (m := m) W)^[j] z))).1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuadPrefix W t
          (prefixQuad ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuadPrefix W t
          (prefixQuad ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuadPrefix W t
          (prefixQuad ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2.2 =
          (t : ZMod m) := by
  rw [canonicalPrefixWordQuadPrefix_apply_eq_of_quad]
  simp [canonicalPrefixWordLayerHitFour, canonicalPrefixCoordFourHit_iff,
    prefixQuad]

def CanonicalPrefixWordLayerHitFourSumTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (z : Fin 6 → ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m * m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitFour W z j t then (1 : ZMod m) else 0) =
          -1

theorem canonicalPrefixWordLayerHitFourSum :
    CanonicalPrefixWordLayerHitFourSumTheorem := by
  intro m _ W hW z t
  classical
  rw [zmod_sum_range_mul_self_self_self_reindex]
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m =>
          Finset.sum Finset.univ
            (fun d : Fin m =>
              if canonicalPrefixWordLayerHitFour W z
                (d.val + m * c.val + (m * m) * p.2.val +
                  (m * m * m) * p.1.val) t
              then (1 : ZMod m) else 0)))]
  rw [← Fintype.sum_prod_type
    (f := fun P : (Fin m × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun d : Fin m =>
          if canonicalPrefixWordLayerHitFour W z
            (d.val + m * P.2.val + (m * m) * P.1.2.val +
              (m * m * m) * P.1.1.val) t
          then (1 : ZMod m) else 0))]
  rw [← Fintype.sum_prod_type
    (f := fun I : ((Fin m × Fin m) × Fin m) × Fin m =>
      if canonicalPrefixWordLayerHitFour W z
        (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
          (m * m * m) * I.1.1.1.val) t
      then (1 : ZMod m) else 0)]
  let blockMap : ((Fin m × Fin m) × Fin m) × Fin m →
      ZMod m × ZMod m × ZMod m × ZMod m :=
    fun I =>
      (canonicalPrefixWordQuadReturn W)^[
        I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
          (m * m * m) * I.1.1.1.val] (prefixQuad z)
  let orbitMap : ((Fin m × Fin m) × Fin m) × Fin m →
      ZMod m × ZMod m × ZMod m × ZMod m :=
    fun I => canonicalPrefixWordQuadPrefix W t (blockMap I)
  have hblock : Function.Bijective blockMap := by
    simpa [blockMap] using
      canonicalPrefixWordQuadReturn_blockOrbit_bijective W hW (prefixQuad z)
  have horbit : Function.Bijective orbitMap := by
    simpa [orbitMap, Function.comp_def] using
      Function.Bijective.comp (canonicalPrefixWordQuadPrefix_bijective W t) hblock
  calc
    Finset.sum Finset.univ
        (fun I : ((Fin m × Fin m) × Fin m) × Fin m =>
          if canonicalPrefixWordLayerHitFour W z
            (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
              (m * m * m) * I.1.1.1.val) t
          then (1 : ZMod m) else 0) =
      Finset.sum Finset.univ
        (fun I : ((Fin m × Fin m) × Fin m) × Fin m =>
          if (orbitMap I).1 = (t : ZMod m) ∨
              (orbitMap I).2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro I _hI
        have hquad :=
          canonicalPrefixWordQuadReturn_iter_apply_eq_of_quad
            W (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
              (m * m * m) * I.1.1.1.val) z
        have hiff :
            canonicalPrefixWordLayerHitFour W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
                (m * m * m) * I.1.1.1.val) t ↔
              (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2 = (t : ZMod m) := by
          rw [canonicalPrefixWordLayerHitFour_iff_quad]
          simp [orbitMap, blockMap, hquad]
        by_cases hhit :
            canonicalPrefixWordLayerHitFour W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
                (m * m * m) * I.1.1.1.val) t
        · have horb := hiff.mp hhit
          simp [hhit, horb]
        · have hnorb :
              ¬ ((orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2 = (t : ZMod m)) := fun h => hhit (hiff.mpr h)
          simp [hhit, hnorb]
    _ =
      Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m × ZMod m =>
          if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
              p.2.2.1 = (t : ZMod m) ∨ p.2.2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        exact Fintype.sum_bijective orbitMap horbit
          (fun I : ((Fin m × Fin m) × Fin m) × Fin m =>
            if (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (fun p : ZMod m × ZMod m × ZMod m × ZMod m =>
            if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
                p.2.2.1 = (t : ZMod m) ∨ p.2.2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (by intro I; rfl)
    _ = -1 := zmod_quad_hit_sum (t : ZMod m)

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordLayerDebitFour_iter_sum_of_hit_four_sum
    (hhitFour : CanonicalPrefixWordLayerHitFourSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range (m * m * m * m))
        (fun j : Nat =>
          canonicalPrefixWordLayerDebitFour W
            ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
      if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
      else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 5 then (-1 : ZMod m)
      else 0 := by
  classical
  have hhit := hhitFour W hW z t
  by_cases h0 : canonicalPrefixWordAt W (t : ZMod m) = 0
  · simp [canonicalPrefixWordLayerDebitFour, canonicalPrefixCoordFourDebit, h0]
  · by_cases h1 : canonicalPrefixWordAt W (t : ZMod m) = 1
    · simp [h0, h1]
      calc
        Finset.sum (Finset.range (m * m * m * m))
            (fun j : Nat =>
              canonicalPrefixWordLayerDebitFour W
                ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
          Finset.sum (Finset.range (m * m * m * m))
            (fun j : Nat =>
              (1 : ZMod m) -
                if canonicalPrefixWordLayerHitFour W z j t then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hh :
                canonicalPrefixCoordFourHit (t : ZMod m)
                  (canonicalPrefixWordPrefixState W t
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
              simp [canonicalPrefixWordLayerDebitFour, canonicalPrefixCoordFourDebit,
                canonicalPrefixWordLayerHitFour, h1, hh]
        _ =
          Finset.sum (Finset.range (m * m * m * m)) (fun _ : Nat => (1 : ZMod m)) -
            Finset.sum (Finset.range (m * m * m * m))
              (fun j : Nat =>
                if canonicalPrefixWordLayerHitFour W z j t then (1 : ZMod m) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = 1 := by
            rw [zmod_sum_range_mul_self_self_self_const_one, hhit]
            ring
    · by_cases h2 : canonicalPrefixWordAt W (t : ZMod m) = 2
      · simp [h0, h1, h2, canonicalPrefixWordLayerDebitFour,
          canonicalPrefixCoordFourDebit]
      · by_cases h3 : canonicalPrefixWordAt W (t : ZMod m) = 3
        · simp [h0, h1, h2, h3, canonicalPrefixWordLayerDebitFour,
            canonicalPrefixCoordFourDebit]
        · by_cases h4 : canonicalPrefixWordAt W (t : ZMod m) = 4
          · simp [h0, h1, h2, h3, h4, canonicalPrefixWordLayerDebitFour,
              canonicalPrefixCoordFourDebit]
          · by_cases h5 : canonicalPrefixWordAt W (t : ZMod m) = 5
            · simp [h0, h1, h2, h3, h4, h5]
              calc
                Finset.sum (Finset.range (m * m * m * m))
                    (fun j : Nat =>
                      canonicalPrefixWordLayerDebitFour W
                        ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
                  Finset.sum (Finset.range (m * m * m * m))
                    (fun j : Nat =>
                      if canonicalPrefixWordLayerHitFour W z j t then (1 : ZMod m) else 0) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    by_cases hh :
                        canonicalPrefixCoordFourHit (t : ZMod m)
                          (canonicalPrefixWordPrefixState W t
                            ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
                      simp [canonicalPrefixWordLayerDebitFour, canonicalPrefixCoordFourDebit,
                        canonicalPrefixWordLayerHitFour, h5, hh]
                _ = -1 := hhit
            · simp [h0, h1, h2, h3, h4, h5, canonicalPrefixWordLayerDebitFour,
                canonicalPrefixCoordFourDebit, zmod_sum_range_mul_self_self_self_const_one]

theorem canonicalPrefixWordReturnIterDebitFour_eq_symbol_sum_of_hit_four_sum
    (hhitFour : CanonicalPrefixWordLayerHitFourSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturnIterDebitFour W z (m * m * m * m) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then (-1 : ZMod m)
          else 0) := by
  calc
    canonicalPrefixWordReturnIterDebitFour W z (m * m * m * m) =
        Finset.sum (Finset.range (m * m * m * m))
          (fun j : Nat =>
            Finset.sum (Finset.range m)
              (fun t : Nat =>
                canonicalPrefixWordLayerDebitFour W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          unfold canonicalPrefixWordReturnIterDebitFour canonicalPrefixWordReturnDebitFour
          rw [zmod_list_range_sum_eq_finset_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [zmod_list_range_sum_eq_finset_sum]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            Finset.sum (Finset.range (m * m * m * m))
              (fun j : Nat =>
                canonicalPrefixWordLayerDebitFour W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
            else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 5 then (-1 : ZMod m)
            else 0) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact canonicalPrefixWordLayerDebitFour_iter_sum_of_hit_four_sum
            hhitFour W hW z t

set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordSymbolDebitFour_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then (-1 : ZMod m)
          else 0) =
      (canonicalWordCount W 1 : ZMod m) - (canonicalWordCount W 5 : ZMod m) := by
  calc
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then (-1 : ZMod m)
          else 0) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          (if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) -
            if canonicalPrefixWordAt W (t : ZMod m) = 5 then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro t _ht
        let sym := canonicalPrefixWordAt W (t : ZMod m)
        change
          (if sym = 0 then 0
          else if sym = 1 then (1 : ZMod m)
          else if sym = 2 then 0
          else if sym = 3 then 0
          else if sym = 4 then 0
          else if sym = 5 then (-1 : ZMod m)
          else 0) =
            (if sym = 1 then (1 : ZMod m) else 0) -
              if sym = 5 then (1 : ZMod m) else 0
        by_cases h0 : sym = 0
        · simp [h0]
        · by_cases h1 : sym = 1
          · simp [h0, h1]
          · by_cases h2 : sym = 2
            · simp [h0, h1, h2]
            · by_cases h3 : sym = 3
              · simp [h0, h1, h2, h3]
              · by_cases h4 : sym = 4
                · simp [h0, h1, h2, h3, h4]
                · by_cases h5 : sym = 5
                  · simp [h0, h1, h2, h3, h4, h5]
                  · simp [h0, h1, h2, h3, h4, h5]
    _ =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) -
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 5 then (1 : ZMod m) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (canonicalWordCount W 1 : ZMod m) -
        (canonicalWordCount W 5 : ZMod m) := by
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 1)]
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 5)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (1 : Fin 7)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (5 : Fin 7)]

theorem canonicalPrefixWordSubfiberSingleCycle_of_head_drift_subsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsub : CanonicalPrefixWordSubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubfiberSingleCycleTheorem := by
  intro m _ W hW b₀ b₁
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordSubfiberReturn W b₀ b₁)
    (g := fun x : ZMod m =>
      x + (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m))
    (proj := tail4Head)
    (fiberBase := tail4FiberBase 0)
    (fiberNext := canonicalPrefixWordSubsubfiberReturn W b₀ b₁ 0)
    (returnTime := m)
    (b₀ := 0)
    (canonicalPrefixWordSubfiberReturn_bijective_of hfiberHead W hW b₀ b₁)
    (canonicalPrefixWordSubfiberReturn_head_of hsubHead W hW b₀ b₁)
    (tail4FiberBase_surj 0)
    (canonicalPrefixWordSubsubfiberReturn_iter_m_of hsubHead W hW b₀ b₁ 0)
    (canonicalWordDeltaDrift_neg_single_cycle hW (3 : Fin 7) (by decide))
    (hsubsub W hW b₀ b₁ 0)

theorem canonicalPrefixWordSubsubfiberReturn_bijective_of
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m) :
    Function.Bijective (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂) := by
  let F := canonicalPrefixWordSubfiberReturn W b₀ b₁
  have hF : Function.Bijective (F^[m]) :=
    Function.Bijective.iterate
      (canonicalPrefixWordSubfiberReturn_bijective_of hfiberHead W hW b₀ b₁) m
  constructor
  · intro tail₁ tail₂ htail
    have hbase : F^[m] (tail4FiberBase b₂ tail₁) =
        F^[m] (tail4FiberBase b₂ tail₂) := by
      rw [canonicalPrefixWordSubsubfiberReturn_iter_m_of hsubHead W hW b₀ b₁ b₂ tail₁,
        canonicalPrefixWordSubsubfiberReturn_iter_m_of hsubHead W hW b₀ b₁ b₂ tail₂, htail]
    have hpre : tail4FiberBase b₂ tail₁ = tail4FiberBase b₂ tail₂ := hF.1 hbase
    have := congrArg tail4Tail hpre
    simpa [tail4FiberBase] using this
  · intro tail
    rcases hF.2 (tail4FiberBase b₂ tail) with ⟨z, hz⟩
    have hzhead : tail4Head z = b₂ := by
      have hhead_iter := canonicalPrefixWordSubfiberReturn_head_iter_m_of hsubHead W hW b₀ b₁ z
      change tail4Head (F^[m] z) = tail4Head z at hhead_iter
      rw [hz] at hhead_iter
      simpa using hhead_iter.symm
    rcases tail4FiberBase_surj b₂ z hzhead with ⟨tail₀, htail₀⟩
    refine ⟨tail₀, ?_⟩
    have hbase : F^[m] (tail4FiberBase b₂ tail₀) = tail4FiberBase b₂ tail := by
      rw [htail₀, hz]
    have hbase' := hbase
    rw [canonicalPrefixWordSubsubfiberReturn_iter_m_of hsubHead W hW b₀ b₁ b₂ tail₀] at hbase'
    have := congrArg tail4Tail hbase'
    simpa [canonicalPrefixWordSubsubfiberReturn, tail4FiberBase] using this

theorem canonicalPrefixWordSubsubfiberReturn_head_of
    (hhead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m)
    (tail : Fin 3 → ZMod m) :
    tail3Head (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂ tail) =
      tail3Head tail + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m) :=
  hhead W hW b₀ b₁ b₂ tail

theorem canonicalPrefixWordSubsubfiberReturn_head_iter_of
    (hhead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 3 → ZMod m,
      tail3Head ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[n] tail) =
        tail3Head tail + (n : ZMod m) *
          (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordSubsubfiberReturn_head_of hhead W hW b₀ b₁ b₂]
      rw [canonicalPrefixWordSubsubfiberReturn_head_iter_of hhead W hW b₀ b₁ b₂ n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordSubsubfiberReturn_head_iter_m_of
    (hhead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ : ZMod m)
    (tail : Fin 3 → ZMod m) :
    tail3Head ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m] tail) =
      tail3Head tail := by
  rw [canonicalPrefixWordSubsubfiberReturn_head_iter_of hhead W hW b₀ b₁ b₂]
  simp

theorem canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
    (hhead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m)
    (tail : Fin 2 → ZMod m) :
    (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m] (tail3FiberBase b₃ tail) =
      tail3FiberBase b₃ (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) := by
  let z := (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m]
    (tail3FiberBase b₃ tail)
  have hhead_z : tail3Head z = b₃ := by
    dsimp [z]
    rw [canonicalPrefixWordSubsubfiberReturn_head_iter_m_of hhead W hW b₀ b₁ b₂]
    rfl
  unfold canonicalPrefixWordSubsubsubfiberReturn
  change z = tail3FiberBase b₃ (tail3Tail z)
  symm
  calc
    tail3FiberBase b₃ (tail3Tail z) = tail3OfHeadTail b₃ (tail3Tail z) := rfl
    _ = tail3OfHeadTail (tail3Head z) (tail3Tail z) := by rw [hhead_z]
    _ = z := tail3OfHeadTail_head_tail z

theorem canonicalPrefixWordSubsubsubfiberReturn_coord_zero_of_iterDebitFour
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (b₀ b₁ b₂ b₃ : ZMod m) (tail : Fin 2 → ZMod m) :
    (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) 0 =
      tail 0 -
        canonicalPrefixWordReturnIterDebitFour W
          (prefixFiberBase b₀
            (tail5FiberBase b₁
              (tail4FiberBase b₂ (tail3FiberBase b₃ tail))))
          (m * m * m * m) := by
  let tail3 : Fin 3 → ZMod m := tail3FiberBase b₃ tail
  let tail4 : Fin 4 → ZMod m := tail4FiberBase b₂ tail3
  let tail5 : Fin 5 → ZMod m := tail5FiberBase b₁ tail4
  let z : Fin 6 → ZMod m := prefixFiberBase b₀ tail5
  have hfull0 :
      (canonicalPrefixWordReturn (m := m) W)^[m * m * m * m] z =
        prefixFiberBase b₀ ((canonicalPrefixWordFiberReturn W b₀)^[m * m * m] tail5) := by
    simpa [z] using
      canonicalPrefixWordReturn_iter_mul_m_fiber
        W hW.length_eq b₀ (m * m * m) tail5
  have hfiber :
      (canonicalPrefixWordFiberReturn W b₀)^[m * m * m] tail5 =
        tail5FiberBase b₁
          ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m * m] tail4) := by
    simpa [tail5] using
      canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
        canonicalPrefixWordFiberHeadDrift W hW b₀ b₁ (m * m) tail4
  have hsub :
      (canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m * m] tail4 =
        tail4FiberBase b₂
          ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m] tail3) := by
    simpa [tail4] using
      canonicalPrefixWordSubfiberReturn_iter_mul_m_subsubfiber_of
        canonicalPrefixWordSubfiberHeadDrift W hW b₀ b₁ b₂ m tail3
  have hsubsub :
      (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m] tail3 =
        tail3FiberBase b₃
          (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) := by
    simpa [tail3] using
      canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
        canonicalPrefixWordSubsubfiberHeadDrift W hW b₀ b₁ b₂ b₃ tail
  rw [hfiber, hsub, hsubsub] at hfull0
  have hcoord :
      (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) 0 =
        ((canonicalPrefixWordReturn (m := m) W)^[m * m * m * m] z) 4 := by
    unfold canonicalPrefixWordSubsubsubfiberReturn
    rw [hfull0]
    rfl
  rw [hcoord]
  rw [canonicalPrefixWordReturn_iter_coord_four_sum W (m * m * m * m) z]
  simp [z, tail5, tail4, tail3, prefixFiberBase, prefixOfHeadTail,
    tail5FiberBase, tail5OfHeadTail, tail4FiberBase, tail4OfHeadTail,
    tail3FiberBase, tail3OfHeadTail]

def CanonicalPrefixWordSubsubsubfiberDebitTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ b₃ : ZMod m) (tail : Fin 2 → ZMod m),
        canonicalPrefixWordReturnIterDebitFour W
          (prefixFiberBase b₀
            (tail5FiberBase b₁
              (tail4FiberBase b₂ (tail3FiberBase b₃ tail))))
          (m * m * m * m) =
            (canonicalWordDeltaDrift W (5 : Fin 7) : ZMod m)

theorem canonicalPrefixWordSubsubsubfiberDebit_of_hit_four_sum
    (hhitFour : CanonicalPrefixWordLayerHitFourSumTheorem) :
    CanonicalPrefixWordSubsubsubfiberDebitTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃ tail
  rw [canonicalPrefixWordReturnIterDebitFour_eq_symbol_sum_of_hit_four_sum
    hhitFour W hW]
  rw [canonicalPrefixWordSymbolDebitFour_sum W hW.length_eq]
  simp [canonicalWordDeltaDrift]

theorem canonicalPrefixWordSubsubsubfiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordSubsubsubfiberDebitTheorem) :
    CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃ tail
  rw [canonicalPrefixWordSubsubsubfiberReturn_coord_zero_of_iterDebitFour W hW]
  rw [hdebit W hW b₀ b₁ b₂ b₃ tail]
  ring

theorem canonicalPrefixWordSubsubsubfiberHeadDrift_of_hit_four_sum
    (hhitFour : CanonicalPrefixWordLayerHitFourSumTheorem) :
    CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubsubfiberHeadDrift_of_debit
    (canonicalPrefixWordSubsubsubfiberDebit_of_hit_four_sum hhitFour)

theorem canonicalPrefixWordSubsubsubfiberHeadDrift :
    CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubsubfiberHeadDrift_of_hit_four_sum
    canonicalPrefixWordLayerHitFourSum

theorem canonicalPrefixWordSubsubfiberSingleCycle_of_head_drift_subsubsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsubHead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    (hsubsubsub : CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubsubfiberSingleCycleTheorem := by
  intro m _ W hW b₀ b₁ b₂
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)
    (g := fun x : ZMod m => x + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m))
    (proj := tail3Head)
    (fiberBase := tail3FiberBase 0)
    (fiberNext := canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ 0)
    (returnTime := m)
    (b₀ := 0)
    (canonicalPrefixWordSubsubfiberReturn_bijective_of hfiberHead hsubHead W hW b₀ b₁ b₂)
    (canonicalPrefixWordSubsubfiberReturn_head_of hsubsubHead W hW b₀ b₁ b₂)
    (tail3FiberBase_surj 0)
    (canonicalPrefixWordSubsubsubfiberReturn_iter_m_of hsubsubHead W hW b₀ b₁ b₂ 0)
    (canonicalWordDeltaDrift_single_cycle hW (4 : Fin 7) (by decide))
    (hsubsubsub W hW b₀ b₁ b₂ 0)

theorem canonicalPrefixWordSubsubsubfiberReturn_bijective_of
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsubHead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m) :
    Function.Bijective (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃) := by
  let F := canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂
  have hF : Function.Bijective (F^[m]) :=
    Function.Bijective.iterate
      (canonicalPrefixWordSubsubfiberReturn_bijective_of
        hfiberHead hsubHead W hW b₀ b₁ b₂) m
  constructor
  · intro tail₁ tail₂ htail
    have hbase : F^[m] (tail3FiberBase b₃ tail₁) =
        F^[m] (tail3FiberBase b₃ tail₂) := by
      rw [canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
          hsubsubHead W hW b₀ b₁ b₂ b₃ tail₁,
        canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
          hsubsubHead W hW b₀ b₁ b₂ b₃ tail₂, htail]
    have hpre : tail3FiberBase b₃ tail₁ = tail3FiberBase b₃ tail₂ := hF.1 hbase
    have := congrArg tail3Tail hpre
    simpa [tail3FiberBase] using this
  · intro tail
    rcases hF.2 (tail3FiberBase b₃ tail) with ⟨z, hz⟩
    have hzhead : tail3Head z = b₃ := by
      have hhead_iter :=
        canonicalPrefixWordSubsubfiberReturn_head_iter_m_of
          hsubsubHead W hW b₀ b₁ b₂ z
      change tail3Head (F^[m] z) = tail3Head z at hhead_iter
      rw [hz] at hhead_iter
      simpa using hhead_iter.symm
    rcases tail3FiberBase_surj b₃ z hzhead with ⟨tail₀, htail₀⟩
    refine ⟨tail₀, ?_⟩
    have hbase : F^[m] (tail3FiberBase b₃ tail₀) = tail3FiberBase b₃ tail := by
      rw [htail₀, hz]
    have hbase' := hbase
    rw [canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
      hsubsubHead W hW b₀ b₁ b₂ b₃ tail₀] at hbase'
    have := congrArg tail3Tail hbase'
    simpa [canonicalPrefixWordSubsubsubfiberReturn, tail3FiberBase] using this

theorem canonicalPrefixWordSubsubsubfiberReturn_head_of
    (hhead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m)
    (tail : Fin 2 → ZMod m) :
    tail2Head (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃ tail) =
      tail2Head tail + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m) :=
  hhead W hW b₀ b₁ b₂ b₃ tail

theorem canonicalPrefixWordSubsubsubfiberReturn_head_iter_of
    (hhead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 2 → ZMod m,
      tail2Head ((canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[n] tail) =
        tail2Head tail + (n : ZMod m) *
          (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Function.iterate_succ_apply']
      rw [canonicalPrefixWordSubsubsubfiberReturn_head_of hhead W hW b₀ b₁ b₂ b₃]
      rw [canonicalPrefixWordSubsubsubfiberReturn_head_iter_of
        hhead W hW b₀ b₁ b₂ b₃ n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordSubsubsubfiberReturn_head_iter_m_of
    (hhead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m)
    (tail : Fin 2 → ZMod m) :
    tail2Head ((canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m] tail) =
      tail2Head tail := by
  rw [canonicalPrefixWordSubsubsubfiberReturn_head_iter_of hhead W hW b₀ b₁ b₂ b₃]
  simp

theorem canonicalPrefixWordSubsubsubsubfiberReturn_iter_m_of
    (hhead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ b₄ : ZMod m)
    (tail : Fin 1 → ZMod m) :
    (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m]
        (tail2FiberBase b₄ tail) =
      tail2FiberBase b₄
        (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄ tail) := by
  let z := (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m]
    (tail2FiberBase b₄ tail)
  have hhead_z : tail2Head z = b₄ := by
    dsimp [z]
    rw [canonicalPrefixWordSubsubsubfiberReturn_head_iter_m_of
      hhead W hW b₀ b₁ b₂ b₃]
    rfl
  unfold canonicalPrefixWordSubsubsubsubfiberReturn
  change z = tail2FiberBase b₄ (tail2Tail z)
  symm
  calc
    tail2FiberBase b₄ (tail2Tail z) = tail2OfHeadTail b₄ (tail2Tail z) := rfl
    _ = tail2OfHeadTail (tail2Head z) (tail2Tail z) := by rw [hhead_z]
    _ = z := tail2OfHeadTail_head_tail z

theorem canonicalPrefixWordSubsubfiberReturn_iter_mul_m_subsubsubfiber_of
    (hhead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (b₀ b₁ b₂ b₃ : ZMod m) :
    ∀ n : Nat, ∀ tail : Fin 2 → ZMod m,
      (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[n * m]
          (tail3FiberBase b₃ tail) =
        tail3FiberBase b₃
          ((canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[n] tail)
  | 0, tail => by simp
  | n + 1, tail => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordSubsubsubfiberReturn_iter_m_of hhead W hW b₀ b₁ b₂ b₃ tail]
      rw [canonicalPrefixWordSubsubfiberReturn_iter_mul_m_subsubsubfiber_of
        hhead W hW b₀ b₁ b₂ b₃ n]
      rw [← Function.iterate_succ_apply]

theorem canonicalPrefixWordQuintReturn_iter_mul_fourth
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    (canonicalPrefixWordQuintReturn W)^[m * m * m * m] p =
      (p.1, p.2.1, p.2.2.1, p.2.2.2.1,
        p.2.2.2.2 + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m)) := by
  rcases p with ⟨p0, p1, p2, p3, p4⟩
  let tail2 : Fin 2 → ZMod m := tail2FiberBase p4 (fun _ : Fin 1 => 0)
  let tail3 : Fin 3 → ZMod m := tail3FiberBase p3 tail2
  let tail4 : Fin 4 → ZMod m := tail4FiberBase p2 tail3
  let tail5 : Fin 5 → ZMod m := tail5FiberBase p1 tail4
  let z : Fin 6 → ZMod m := prefixFiberBase p0 tail5
  have hz : z = prefixQuintBase (p0, p1, p2, p3, p4) := by
    funext k
    fin_cases k <;> rfl
  have hfull :
      (canonicalPrefixWordReturn (m := m) W)^[m * m * m * m] z =
        prefixFiberBase p0 ((canonicalPrefixWordFiberReturn W p0)^[m * m * m] tail5) := by
    simpa [z] using
      canonicalPrefixWordReturn_iter_mul_m_fiber W hW.length_eq p0 (m * m * m) tail5
  have hfiber :
      (canonicalPrefixWordFiberReturn W p0)^[m * m * m] tail5 =
        tail5FiberBase p1
          ((canonicalPrefixWordSubfiberReturn W p0 p1)^[m * m] tail4) := by
    simpa [tail5] using
      canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
        canonicalPrefixWordFiberHeadDrift W hW p0 p1 (m * m) tail4
  have hsub :
      (canonicalPrefixWordSubfiberReturn W p0 p1)^[m * m] tail4 =
        tail4FiberBase p2
          ((canonicalPrefixWordSubsubfiberReturn W p0 p1 p2)^[m] tail3) := by
    simpa [tail4] using
      canonicalPrefixWordSubfiberReturn_iter_mul_m_subsubfiber_of
        canonicalPrefixWordSubfiberHeadDrift W hW p0 p1 p2 m tail3
  have hsubsub :
      (canonicalPrefixWordSubsubfiberReturn W p0 p1 p2)^[m] tail3 =
        tail3FiberBase p3
          (canonicalPrefixWordSubsubsubfiberReturn W p0 p1 p2 p3 tail2) := by
    simpa [tail3] using
      canonicalPrefixWordSubsubsubfiberReturn_iter_m_of
        canonicalPrefixWordSubsubfiberHeadDrift W hW p0 p1 p2 p3 tail2
  rw [hfiber, hsub, hsubsub] at hfull
  rw [show (p0, p1, p2, p3, p4) =
      prefixQuint (prefixQuintBase (p0, p1, p2, p3, p4)) by rfl]
  rw [canonicalPrefixWordQuintReturn_iter_apply_eq_of_quint
    W (m * m * m * m) (prefixQuintBase (p0, p1, p2, p3, p4))]
  change prefixQuint
      ((canonicalPrefixWordReturn (m := m) W)^[m * m * m * m]
        (prefixQuintBase (p0, p1, p2, p3, p4))) =
    (p0, p1, p2, p3, p4 + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m))
  rw [← hz, hfull]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · have hhead := canonicalPrefixWordSubsubsubfiberHeadDrift W hW p0 p1 p2 p3 tail2
          simpa [prefixQuint, prefixFiberBase, prefixOfHeadTail, tail5FiberBase,
            tail5OfHeadTail, tail4FiberBase, tail4OfHeadTail, tail3FiberBase,
            tail3OfHeadTail, tail2, tail2FiberBase, tail2OfHeadTail] using hhead

theorem canonicalPrefixWordQuintReturn_iter_mul_fourth_mul
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m,
      (canonicalPrefixWordQuintReturn W)^[n * (m * m * m * m)] p =
        (p.1, p.2.1, p.2.2.1, p.2.2.2.1,
          p.2.2.2.2 + (n : ZMod m) *
            (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m))
  | 0, p => by simp
  | n + 1, p => by
      rw [Nat.succ_mul, Function.iterate_add_apply]
      rw [canonicalPrefixWordQuintReturn_iter_mul_fourth W hW]
      rw [canonicalPrefixWordQuintReturn_iter_mul_fourth_mul W hW n]
      simp [Nat.cast_add, Nat.cast_one]
      ring

theorem canonicalPrefixWordQuintReturn_blockOrbit_bijective
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m) :
    Function.Bijective
      (fun I : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
        (canonicalPrefixWordQuintReturn W)^[
          I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
            (m * m * m) * I.1.1.1.2.val +
              (m * m * m * m) * I.1.1.1.1.val] p) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro I J hIJ
    rcases I with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
    rcases J with ⟨⟨⟨⟨a', b'⟩, c'⟩, d'⟩, e'⟩
    have hhead := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixTriplePair (prefixQuadTriple (prefixQuintQuad r))).1) hIJ
    change
      (prefixTriplePair (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          e.val + m * d.val + (m * m) * c.val +
            (m * m * m) * b.val + (m * m * m * m) * a.val] p)))).1 =
      (prefixTriplePair (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          e'.val + m * d'.val + (m * m) * c'.val +
            (m * m * m) * b'.val + (m * m * m * m) * a'.val] p)))).1
        at hhead
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hhead
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hhead
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hhead
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    rw [canonicalPrefixWordPairReturn_head_iter W hW.length_eq] at hhead
    have hhead' :
        p.1 + (e.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) =
          p.1 + (e'.val : ZMod m) * (canonicalWordCount W 0 : ZMod m) := by
      simpa [prefixQuintQuad, prefixQuadTriple, prefixTriplePair, Nat.cast_add,
        Nat.cast_mul, ZMod.natCast_self, mul_add, add_assoc, add_comm,
        add_left_comm] using hhead
    have hecast : (e.val : ZMod m) = (e'.val : ZMod m) :=
      (zmod_affine_mul_right_bijective hW.coprime_zero p.1).1 hhead'
    have he : e = e' := fin_eq_of_zmod_natCast_eq hecast
    subst e'
    have hcancelE :
        (canonicalPrefixWordQuintReturn W)^[
            m * d.val + (m * m) * c.val + (m * m * m) * b.val +
              (m * m * m * m) * a.val] p =
          (canonicalPrefixWordQuintReturn W)^[
            m * d'.val + (m * m) * c'.val + (m * m * m) * b'.val +
              (m * m * m * m) * a'.val] p := by
      let rI : Nat := m * d.val + (m * m) * c.val + (m * m * m) * b.val +
        (m * m * m * m) * a.val
      let rJ : Nat := m * d'.val + (m * m) * c'.val + (m * m * m) * b'.val +
        (m * m * m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordQuintReturn W)^[e.val + rI] p =
            (canonicalPrefixWordQuintReturn W)^[e.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hIJ
      have hIJ'' :
          (canonicalPrefixWordQuintReturn W)^[e.val]
              ((canonicalPrefixWordQuintReturn W)^[rI] p) =
            (canonicalPrefixWordQuintReturn W)^[e.val]
              ((canonicalPrefixWordQuintReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordQuintReturn_bijective W) e.val).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hsnd := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixTriplePair (prefixQuadTriple (prefixQuintQuad r))).2) hcancelE
    change
      (prefixTriplePair (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          m * d.val + (m * m) * c.val + (m * m * m) * b.val +
            (m * m * m * m) * a.val] p)))).2 =
      (prefixTriplePair (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          m * d'.val + (m * m) * c'.val + (m * m * m) * b'.val +
            (m * m * m * m) * a'.val] p)))).2 at hsnd
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hsnd
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hsnd
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hsnd
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    rw [canonicalPrefixWordTripleReturn_pair_iter W] at hsnd
    have hdexp :
        m * d.val + (m * m) * c.val + (m * m * m) * b.val +
            (m * m * m * m) * a.val =
          (d.val + m * c.val + (m * m) * b.val + (m * m * m) * a.val) * m := by
      ring
    have hdexp' :
        m * d'.val + (m * m) * c'.val + (m * m * m) * b'.val +
            (m * m * m * m) * a'.val =
          (d'.val + m * c'.val + (m * m) * b'.val + (m * m * m) * a'.val) * m := by
      ring
    rw [hdexp, hdexp'] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    rw [canonicalPrefixWordPairReturn_iter_mul_m W hW] at hsnd
    have hsnd' :
        p.2.1 + (d.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) =
          p.2.1 + (d'.val : ZMod m) * (canonicalWordDeltaTwoDrift W : ZMod m) := by
      simpa [prefixQuintQuad, prefixQuadTriple, prefixTriplePair, Nat.cast_add,
        Nat.cast_mul, ZMod.natCast_self, mul_add, add_assoc, add_comm,
        add_left_comm] using hsnd
    have hdcast : (d.val : ZMod m) = (d'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaTwoDrift W)
        (canonicalWordDeltaTwoDrift_coprime_abs hW) p.2.1).1 hsnd'
    have hd : d = d' := fin_eq_of_zmod_natCast_eq hdcast
    subst d'
    have hcancelD :
        (canonicalPrefixWordQuintReturn W)^[
            (m * m) * c.val + (m * m * m) * b.val +
              (m * m * m * m) * a.val] p =
          (canonicalPrefixWordQuintReturn W)^[
            (m * m) * c'.val + (m * m * m) * b'.val +
              (m * m * m * m) * a'.val] p := by
      let rI : Nat := (m * m) * c.val + (m * m * m) * b.val +
        (m * m * m * m) * a.val
      let rJ : Nat := (m * m) * c'.val + (m * m * m) * b'.val +
        (m * m * m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordQuintReturn W)^[m * d.val + rI] p =
            (canonicalPrefixWordQuintReturn W)^[m * d.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hcancelE
      have hIJ'' :
          (canonicalPrefixWordQuintReturn W)^[m * d.val]
              ((canonicalPrefixWordQuintReturn W)^[rI] p) =
            (canonicalPrefixWordQuintReturn W)^[m * d.val]
              ((canonicalPrefixWordQuintReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordQuintReturn_bijective W) (m * d.val)).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hthird := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixQuadTriple (prefixQuintQuad r)).2.2) hcancelD
    change
      (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          (m * m) * c.val + (m * m * m) * b.val +
            (m * m * m * m) * a.val] p))).2.2 =
      (prefixQuadTriple (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          (m * m) * c'.val + (m * m * m) * b'.val +
            (m * m * m * m) * a'.val] p))).2.2 at hthird
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hthird
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hthird
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hthird
    rw [canonicalPrefixWordQuadReturn_triple_iter W] at hthird
    have hcexp :
        (m * m) * c.val + (m * m * m) * b.val +
            (m * m * m * m) * a.val =
          (c.val + m * b.val + (m * m) * a.val) * (m * m) := by
      ring
    have hcexp' :
        (m * m) * c'.val + (m * m * m) * b'.val +
            (m * m * m * m) * a'.val =
          (c'.val + m * b'.val + (m * m) * a'.val) * (m * m) := by
      ring
    rw [hcexp, hcexp'] at hthird
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW] at hthird
    rw [canonicalPrefixWordTripleReturn_iter_mul_self_mul W hW] at hthird
    have hthird' :
        p.2.2.1 + (c.val : ZMod m) *
            (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m) =
          p.2.2.1 + (c'.val : ZMod m) *
            (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m) := by
      simpa [prefixQuintQuad, prefixQuadTriple, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, mul_add, add_assoc, add_comm, add_left_comm] using hthird
    have hccast : (c.val : ZMod m) = (c'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (-(canonicalWordDeltaDrift W (3 : Fin 7)))
        (canonicalWordDeltaDrift_neg_coprime_abs hW (3 : Fin 7) (by decide))
        p.2.2.1).1 (by simpa [Int.cast_neg] using hthird')
    have hc : c = c' := fin_eq_of_zmod_natCast_eq hccast
    subst c'
    have hcancelC :
        (canonicalPrefixWordQuintReturn W)^[
            (m * m * m) * b.val + (m * m * m * m) * a.val] p =
          (canonicalPrefixWordQuintReturn W)^[
            (m * m * m) * b'.val + (m * m * m * m) * a'.val] p := by
      let rI : Nat := (m * m * m) * b.val + (m * m * m * m) * a.val
      let rJ : Nat := (m * m * m) * b'.val + (m * m * m * m) * a'.val
      have hIJ' :
          (canonicalPrefixWordQuintReturn W)^[(m * m) * c.val + rI] p =
            (canonicalPrefixWordQuintReturn W)^[(m * m) * c.val + rJ] p := by
        dsimp [rI, rJ]
        simpa [Nat.add_assoc] using hcancelD
      have hIJ'' :
          (canonicalPrefixWordQuintReturn W)^[(m * m) * c.val]
              ((canonicalPrefixWordQuintReturn W)^[rI] p) =
            (canonicalPrefixWordQuintReturn W)^[(m * m) * c.val]
              ((canonicalPrefixWordQuintReturn W)^[rJ] p) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hIJ'
      have hcancel := (Function.Bijective.iterate
        (canonicalPrefixWordQuintReturn_bijective W) ((m * m) * c.val)).1 hIJ''
      simpa [rI, rJ] using hcancel
    have hfourth := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
        (prefixQuintQuad r).2.2.2) hcancelC
    change
      (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          (m * m * m) * b.val + (m * m * m * m) * a.val] p)).2.2.2 =
      (prefixQuintQuad
        ((canonicalPrefixWordQuintReturn W)^[
          (m * m * m) * b'.val + (m * m * m * m) * a'.val] p)).2.2.2 at hfourth
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hfourth
    rw [canonicalPrefixWordQuintReturn_quad_iter W] at hfourth
    have hbexp :
        (m * m * m) * b.val + (m * m * m * m) * a.val =
          (b.val + m * a.val) * (m * m * m) := by
      ring
    have hbexp' :
        (m * m * m) * b'.val + (m * m * m * m) * a'.val =
          (b'.val + m * a'.val) * (m * m * m) := by
      ring
    rw [hbexp, hbexp'] at hfourth
    rw [canonicalPrefixWordQuadReturn_iter_mul_cube_mul W hW] at hfourth
    rw [canonicalPrefixWordQuadReturn_iter_mul_cube_mul W hW] at hfourth
    have hfourth' :
        p.2.2.2.1 + (b.val : ZMod m) *
            (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m) =
          p.2.2.2.1 + (b'.val : ZMod m) *
            (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m) := by
      simpa [prefixQuintQuad, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        mul_add, add_assoc, add_comm, add_left_comm] using hfourth
    have hbcast : (b.val : ZMod m) = (b'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (canonicalWordDeltaDrift W (4 : Fin 7))
        (canonicalWordDeltaDrift_coprime_abs hW (4 : Fin 7) (by decide))
        p.2.2.2.1).1 (by
          simpa [add_assoc, add_comm, add_left_comm] using hfourth')
    have hb : b = b' := fin_eq_of_zmod_natCast_eq hbcast
    subst b'
    have hcancelB :
        (canonicalPrefixWordQuintReturn W)^[(m * m * m * m) * a.val] p =
          (canonicalPrefixWordQuintReturn W)^[(m * m * m * m) * a'.val] p := by
      have hIJ' :
          (canonicalPrefixWordQuintReturn W)^[
              (m * m * m) * b.val + (m * m * m * m) * a.val] p =
            (canonicalPrefixWordQuintReturn W)^[
              (m * m * m) * b.val + (m * m * m * m) * a'.val] p := by
        simpa using hcancelC
      rw [Function.iterate_add_apply, Function.iterate_add_apply] at hIJ'
      exact (Function.Bijective.iterate
        (canonicalPrefixWordQuintReturn_bijective W) ((m * m * m) * b.val)).1 hIJ'
    rw [show (m * m * m * m) * a.val = a.val * (m * m * m * m) by ring] at hcancelB
    rw [show (m * m * m * m) * a'.val = a'.val * (m * m * m * m) by ring] at hcancelB
    rw [canonicalPrefixWordQuintReturn_iter_mul_fourth_mul W hW a.val p] at hcancelB
    rw [canonicalPrefixWordQuintReturn_iter_mul_fourth_mul W hW a'.val p] at hcancelB
    have hfifth := congrArg
      (fun r : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m => r.2.2.2.2) hcancelB
    have hacast : (a.val : ZMod m) = (a'.val : ZMod m) :=
      (zmod_int_affine_mul_right_bijective
        (-(canonicalWordDeltaDrift W (5 : Fin 7)))
        (canonicalWordDeltaDrift_neg_coprime_abs hW (5 : Fin 7) (by decide))
        p.2.2.2.2).1 (by
          simpa [Int.cast_neg, add_assoc, add_comm, add_left_comm] using hfifth)
    have ha : a = a' := fin_eq_of_zmod_natCast_eq hacast
    subst a'
    rfl
  · simp
    ring

def canonicalPrefixWordLayerHitFive {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixCoordFiveHit (t : ZMod m)
    (canonicalPrefixWordPrefixState W t
      ((canonicalPrefixWordReturn (m := m) W)^[j] z))

instance canonicalPrefixWordLayerHitFive_decidable {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    Decidable (canonicalPrefixWordLayerHitFive W z j t) := by
  unfold canonicalPrefixWordLayerHitFive
  infer_instance

theorem canonicalPrefixWordLayerHitFive_iff_quint {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 → ZMod m) (j t : Nat) :
    canonicalPrefixWordLayerHitFive W z j t ↔
      (canonicalPrefixWordQuintPrefix W t
          (prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[j] z))).1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuintPrefix W t
          (prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuintPrefix W t
          (prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuintPrefix W t
          (prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2.2.1 =
          (t : ZMod m) ∨
        (canonicalPrefixWordQuintPrefix W t
          (prefixQuint ((canonicalPrefixWordReturn (m := m) W)^[j] z))).2.2.2.2 =
          (t : ZMod m) := by
  rw [canonicalPrefixWordQuintPrefix_apply_eq_of_quint]
  simp [canonicalPrefixWordLayerHitFive, canonicalPrefixCoordFiveHit_iff,
    prefixQuint]

def CanonicalPrefixWordLayerHitFiveSumTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (z : Fin 6 → ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m * m * m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitFive W z j t then (1 : ZMod m) else 0) =
          1

theorem canonicalPrefixWordLayerHitFiveSum :
    CanonicalPrefixWordLayerHitFiveSumTheorem := by
  intro m _ W hW z t
  classical
  rw [zmod_sum_range_mul_self_self_self_self_reindex]
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin m × Fin m =>
      Finset.sum Finset.univ
        (fun c : Fin m =>
          Finset.sum Finset.univ
            (fun d : Fin m =>
              Finset.sum Finset.univ
                (fun e : Fin m =>
                  if canonicalPrefixWordLayerHitFive W z
                    (e.val + m * d.val + (m * m) * c.val +
                      (m * m * m) * p.2.val +
                        (m * m * m * m) * p.1.val) t
                  then (1 : ZMod m) else 0))))]
  rw [← Fintype.sum_prod_type
    (f := fun P : (Fin m × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun d : Fin m =>
          Finset.sum Finset.univ
            (fun e : Fin m =>
              if canonicalPrefixWordLayerHitFive W z
                (e.val + m * d.val + (m * m) * P.2.val +
                  (m * m * m) * P.1.2.val +
                    (m * m * m * m) * P.1.1.val) t
              then (1 : ZMod m) else 0)))]
  rw [← Fintype.sum_prod_type
    (f := fun Q : ((Fin m × Fin m) × Fin m) × Fin m =>
      Finset.sum Finset.univ
        (fun e : Fin m =>
          if canonicalPrefixWordLayerHitFive W z
            (e.val + m * Q.2.val + (m * m) * Q.1.2.val +
              (m * m * m) * Q.1.1.2.val +
                (m * m * m * m) * Q.1.1.1.val) t
          then (1 : ZMod m) else 0))]
  rw [← Fintype.sum_prod_type
    (f := fun I : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
      if canonicalPrefixWordLayerHitFive W z
        (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
          (m * m * m) * I.1.1.1.2.val +
            (m * m * m * m) * I.1.1.1.1.val) t
      then (1 : ZMod m) else 0)]
  let blockMap : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m →
      ZMod m × ZMod m × ZMod m × ZMod m × ZMod m :=
    fun I =>
      (canonicalPrefixWordQuintReturn W)^[
        I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
          (m * m * m) * I.1.1.1.2.val +
            (m * m * m * m) * I.1.1.1.1.val] (prefixQuint z)
  let orbitMap : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m →
      ZMod m × ZMod m × ZMod m × ZMod m × ZMod m :=
    fun I => canonicalPrefixWordQuintPrefix W t (blockMap I)
  have hblock : Function.Bijective blockMap := by
    simpa [blockMap] using
      canonicalPrefixWordQuintReturn_blockOrbit_bijective W hW (prefixQuint z)
  have horbit : Function.Bijective orbitMap := by
    simpa [orbitMap, Function.comp_def] using
      Function.Bijective.comp (canonicalPrefixWordQuintPrefix_bijective W t) hblock
  calc
    Finset.sum Finset.univ
        (fun I : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
          if canonicalPrefixWordLayerHitFive W z
            (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
              (m * m * m) * I.1.1.1.2.val +
                (m * m * m * m) * I.1.1.1.1.val) t
          then (1 : ZMod m) else 0) =
      Finset.sum Finset.univ
        (fun I : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
          if (orbitMap I).1 = (t : ZMod m) ∨
              (orbitMap I).2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2.2.1 = (t : ZMod m) ∨
              (orbitMap I).2.2.2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro I _hI
        have hquint :=
          canonicalPrefixWordQuintReturn_iter_apply_eq_of_quint
            W (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
              (m * m * m) * I.1.1.1.2.val +
                (m * m * m * m) * I.1.1.1.1.val) z
        have hiff :
            canonicalPrefixWordLayerHitFive W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
                (m * m * m) * I.1.1.1.2.val +
                  (m * m * m * m) * I.1.1.1.1.val) t ↔
              (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.2 = (t : ZMod m) := by
          rw [canonicalPrefixWordLayerHitFive_iff_quint]
          simp [orbitMap, blockMap, hquint]
        by_cases hhit :
            canonicalPrefixWordLayerHitFive W z
              (I.2.val + m * I.1.2.val + (m * m) * I.1.1.2.val +
                (m * m * m) * I.1.1.1.2.val +
                  (m * m * m * m) * I.1.1.1.1.val) t
        · have horb := hiff.mp hhit
          simp [hhit, horb]
        · have hnorb :
              ¬ ((orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.2 = (t : ZMod m)) := fun h => hhit (hiff.mpr h)
          simp [hhit, hnorb]
    _ =
      Finset.sum Finset.univ
        (fun p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
          if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
              p.2.2.1 = (t : ZMod m) ∨ p.2.2.2.1 = (t : ZMod m) ∨
              p.2.2.2.2 = (t : ZMod m)
          then (1 : ZMod m) else 0) := by
        exact Fintype.sum_bijective orbitMap horbit
          (fun I : (((Fin m × Fin m) × Fin m) × Fin m) × Fin m =>
            if (orbitMap I).1 = (t : ZMod m) ∨
                (orbitMap I).2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.1 = (t : ZMod m) ∨
                (orbitMap I).2.2.2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (fun p : ZMod m × ZMod m × ZMod m × ZMod m × ZMod m =>
            if p.1 = (t : ZMod m) ∨ p.2.1 = (t : ZMod m) ∨
                p.2.2.1 = (t : ZMod m) ∨ p.2.2.2.1 = (t : ZMod m) ∨
                p.2.2.2.2 = (t : ZMod m)
            then (1 : ZMod m) else 0)
          (by intro I; rfl)
    _ = 1 := zmod_quint_hit_sum (t : ZMod m)

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordLayerDebitFive_iter_sum_of_hit_five_sum
    (hhitFive : CanonicalPrefixWordLayerHitFiveSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 → ZMod m) (t : Nat) :
    Finset.sum (Finset.range (m * m * m * m * m))
        (fun j : Nat =>
          canonicalPrefixWordLayerDebitFive W
            ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
      if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
      else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 5 then 0
      else if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m)
      else 0 := by
  classical
  have hhit := hhitFive W hW z t
  by_cases h0 : canonicalPrefixWordAt W (t : ZMod m) = 0
  · simp [canonicalPrefixWordLayerDebitFive, canonicalPrefixCoordFiveDebit, h0]
  · by_cases h1 : canonicalPrefixWordAt W (t : ZMod m) = 1
    · simp [h0, h1]
      calc
        Finset.sum (Finset.range (m * m * m * m * m))
            (fun j : Nat =>
              canonicalPrefixWordLayerDebitFive W
                ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
          Finset.sum (Finset.range (m * m * m * m * m))
            (fun j : Nat =>
              (1 : ZMod m) -
                if canonicalPrefixWordLayerHitFive W z j t then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hh :
                canonicalPrefixCoordFiveHit (t : ZMod m)
                  (canonicalPrefixWordPrefixState W t
                    ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
              simp [canonicalPrefixWordLayerDebitFive, canonicalPrefixCoordFiveDebit,
                canonicalPrefixWordLayerHitFive, h1, hh]
        _ =
          Finset.sum (Finset.range (m * m * m * m * m)) (fun _ : Nat => (1 : ZMod m)) -
            Finset.sum (Finset.range (m * m * m * m * m))
              (fun j : Nat =>
                if canonicalPrefixWordLayerHitFive W z j t then (1 : ZMod m) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = -1 := by
            rw [zmod_sum_range_mul_self_self_self_self_const_one, hhit]
            ring
    · by_cases h2 : canonicalPrefixWordAt W (t : ZMod m) = 2
      · simp [h0, h1, h2, canonicalPrefixWordLayerDebitFive,
          canonicalPrefixCoordFiveDebit]
      · by_cases h3 : canonicalPrefixWordAt W (t : ZMod m) = 3
        · simp [h0, h1, h2, h3, canonicalPrefixWordLayerDebitFive,
            canonicalPrefixCoordFiveDebit]
        · by_cases h4 : canonicalPrefixWordAt W (t : ZMod m) = 4
          · simp [h0, h1, h2, h3, h4, canonicalPrefixWordLayerDebitFive,
              canonicalPrefixCoordFiveDebit]
          · by_cases h5 : canonicalPrefixWordAt W (t : ZMod m) = 5
            · simp [h0, h1, h2, h3, h4, h5, canonicalPrefixWordLayerDebitFive,
                canonicalPrefixCoordFiveDebit]
            · by_cases h6 : canonicalPrefixWordAt W (t : ZMod m) = 6
              · simp [h0, h1, h2, h3, h4, h5, h6]
                calc
                  Finset.sum (Finset.range (m * m * m * m * m))
                      (fun j : Nat =>
                        canonicalPrefixWordLayerDebitFive W
                          ((canonicalPrefixWordReturn (m := m) W)^[j] z) t) =
                    Finset.sum (Finset.range (m * m * m * m * m))
                      (fun j : Nat =>
                        if canonicalPrefixWordLayerHitFive W z j t then (1 : ZMod m) else 0) := by
                      apply Finset.sum_congr rfl
                      intro j _hj
                      by_cases hh :
                          canonicalPrefixCoordFiveHit (t : ZMod m)
                            (canonicalPrefixWordPrefixState W t
                              ((canonicalPrefixWordReturn (m := m) W)^[j] z)) <;>
                        simp [canonicalPrefixWordLayerDebitFive, canonicalPrefixCoordFiveDebit,
                          canonicalPrefixWordLayerHitFive, h6, hh]
                  _ = 1 := hhit
              · have hs : False := by
                  let sym : CanonSym := canonicalPrefixWordAt W (t : ZMod m)
                  change sym ≠ (0 : CanonSym) at h0
                  change sym ≠ (1 : CanonSym) at h1
                  change sym ≠ (2 : CanonSym) at h2
                  change sym ≠ (3 : CanonSym) at h3
                  change sym ≠ (4 : CanonSym) at h4
                  change sym ≠ (5 : CanonSym) at h5
                  change sym ≠ (6 : CanonSym) at h6
                  rcases sym with ⟨n, hn⟩
                  interval_cases n <;> simp at h0 h1 h2 h3 h4 h5 h6
                exact False.elim hs

theorem canonicalPrefixWordReturnIterDebitFive_eq_symbol_sum_of_hit_five_sum
    (hhitFive : CanonicalPrefixWordLayerHitFiveSumTheorem)
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W) (z : Fin 6 → ZMod m) :
    canonicalPrefixWordReturnIterDebitFive W z (m * m * m * m * m) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m)
          else 0) := by
  calc
    canonicalPrefixWordReturnIterDebitFive W z (m * m * m * m * m) =
        Finset.sum (Finset.range (m * m * m * m * m))
          (fun j : Nat =>
            Finset.sum (Finset.range m)
              (fun t : Nat =>
                canonicalPrefixWordLayerDebitFive W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          unfold canonicalPrefixWordReturnIterDebitFive canonicalPrefixWordReturnDebitFive
          rw [zmod_list_range_sum_eq_finset_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [zmod_list_range_sum_eq_finset_sum]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            Finset.sum (Finset.range (m * m * m * m * m))
              (fun j : Nat =>
                canonicalPrefixWordLayerDebitFive W
                  ((canonicalPrefixWordReturn (m := m) W)^[j] z) t)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
            else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 5 then 0
            else if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m)
            else 0) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact canonicalPrefixWordLayerDebitFive_iter_sum_of_hit_five_sum
            hhitFive W hW z t

set_option linter.unusedSimpArgs false in
theorem canonicalPrefixWordSymbolDebitFive_sum {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) :
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m)
          else 0) =
      (canonicalWordCount W 6 : ZMod m) - (canonicalWordCount W 1 : ZMod m) := by
  calc
    Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 0 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 1 then (-1 : ZMod m)
          else if canonicalPrefixWordAt W (t : ZMod m) = 2 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 3 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 4 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 5 then 0
          else if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m)
          else 0) =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          (if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m) else 0) -
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro t _ht
        let sym := canonicalPrefixWordAt W (t : ZMod m)
        change
          (if sym = 0 then 0
          else if sym = 1 then (-1 : ZMod m)
          else if sym = 2 then 0
          else if sym = 3 then 0
          else if sym = 4 then 0
          else if sym = 5 then 0
          else if sym = 6 then (1 : ZMod m)
          else 0) =
            (if sym = 6 then (1 : ZMod m) else 0) -
              if sym = 1 then (1 : ZMod m) else 0
        by_cases h0 : sym = 0
        · simp [h0]
        · by_cases h1 : sym = 1
          · simp [h0, h1]
          · by_cases h2 : sym = 2
            · simp [h0, h1, h2]
            · by_cases h3 : sym = 3
              · simp [h0, h1, h2, h3]
              · by_cases h4 : sym = 4
                · simp [h0, h1, h2, h3, h4]
                · by_cases h5 : sym = 5
                  · simp [h0, h1, h2, h3, h4, h5]
                  · by_cases h6 : sym = 6
                    · simp [h0, h1, h2, h3, h4, h5, h6]
                    · simp [h0, h1, h2, h3, h4, h5, h6]
    _ =
      Finset.sum (Finset.range m)
        (fun t : Nat =>
          if canonicalPrefixWordAt W (t : ZMod m) = 6 then (1 : ZMod m) else 0) -
        Finset.sum (Finset.range m)
          (fun t : Nat =>
            if canonicalPrefixWordAt W (t : ZMod m) = 1 then (1 : ZMod m) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (canonicalWordCount W 6 : ZMod m) -
        (canonicalWordCount W 1 : ZMod m) := by
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 6)]
        rw [zmod_sum_range_indicator_eq_countP
          (m := m) (p := fun t : Nat => canonicalPrefixWordAt W (t : ZMod m) = 1)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (6 : Fin 7)]
        rw [canonicalPrefixWordAt_range_count_eq W hW (1 : Fin 7)]

theorem canonicalPrefixWordSubsubsubsubfiberReturn_coord_zero_of_iterDebitFive
    {m : Nat} [NeZero m] (W : List CanonSym)
    (hW : CanonicalWordCertified m W)
    (b₀ b₁ b₂ b₃ b₄ : ZMod m) (tail : Fin 1 → ZMod m) :
    (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄ tail) 0 =
      tail 0 -
        canonicalPrefixWordReturnIterDebitFive W
          (prefixFiberBase b₀
            (tail5FiberBase b₁
              (tail4FiberBase b₂
                (tail3FiberBase b₃ (tail2FiberBase b₄ tail)))))
          (m * m * m * m * m) := by
  let tail2 : Fin 2 → ZMod m := tail2FiberBase b₄ tail
  let tail3 : Fin 3 → ZMod m := tail3FiberBase b₃ tail2
  let tail4 : Fin 4 → ZMod m := tail4FiberBase b₂ tail3
  let tail5 : Fin 5 → ZMod m := tail5FiberBase b₁ tail4
  let z : Fin 6 → ZMod m := prefixFiberBase b₀ tail5
  have hfull0 :
      (canonicalPrefixWordReturn (m := m) W)^[m * m * m * m * m] z =
        prefixFiberBase b₀ ((canonicalPrefixWordFiberReturn W b₀)^[m * m * m * m] tail5) := by
    simpa [z] using
      canonicalPrefixWordReturn_iter_mul_m_fiber
        W hW.length_eq b₀ (m * m * m * m) tail5
  have hfiber :
      (canonicalPrefixWordFiberReturn W b₀)^[m * m * m * m] tail5 =
        tail5FiberBase b₁
          ((canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m * m * m] tail4) := by
    simpa [tail5] using
      canonicalPrefixWordFiberReturn_iter_mul_m_subfiber_of
        canonicalPrefixWordFiberHeadDrift W hW b₀ b₁ (m * m * m) tail4
  have hsub :
      (canonicalPrefixWordSubfiberReturn W b₀ b₁)^[m * m * m] tail4 =
        tail4FiberBase b₂
          ((canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m * m] tail3) := by
    simpa [tail4] using
      canonicalPrefixWordSubfiberReturn_iter_mul_m_subsubfiber_of
        canonicalPrefixWordSubfiberHeadDrift W hW b₀ b₁ b₂ (m * m) tail3
  have hsubsub :
      (canonicalPrefixWordSubsubfiberReturn W b₀ b₁ b₂)^[m * m] tail3 =
        tail3FiberBase b₃
          ((canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m] tail2) := by
    simpa [tail3] using
      canonicalPrefixWordSubsubfiberReturn_iter_mul_m_subsubsubfiber_of
        canonicalPrefixWordSubsubfiberHeadDrift W hW b₀ b₁ b₂ b₃ m tail2
  have hsubsubsub :
      (canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)^[m] tail2 =
        tail2FiberBase b₄
          (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄ tail) := by
    simpa [tail2] using
      canonicalPrefixWordSubsubsubsubfiberReturn_iter_m_of
        canonicalPrefixWordSubsubsubfiberHeadDrift W hW b₀ b₁ b₂ b₃ b₄ tail
  rw [hfiber, hsub, hsubsub, hsubsubsub] at hfull0
  have hcoord :
      (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄ tail) 0 =
        ((canonicalPrefixWordReturn (m := m) W)^[m * m * m * m * m] z) 5 := by
    unfold canonicalPrefixWordSubsubsubsubfiberReturn
    rw [hfull0]
    rfl
  rw [hcoord]
  rw [canonicalPrefixWordReturn_iter_coord_five_sum W (m * m * m * m * m) z]
  simp [z, tail5, tail4, tail3, tail2, prefixFiberBase, prefixOfHeadTail,
    tail5FiberBase, tail5OfHeadTail, tail4FiberBase, tail4OfHeadTail,
    tail3FiberBase, tail3OfHeadTail, tail2FiberBase, tail2OfHeadTail]

def CanonicalPrefixWordSubsubsubsubfiberDebitTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∀ (b₀ b₁ b₂ b₃ b₄ : ZMod m) (tail : Fin 1 → ZMod m),
        canonicalPrefixWordReturnIterDebitFive W
          (prefixFiberBase b₀
            (tail5FiberBase b₁
              (tail4FiberBase b₂
                (tail3FiberBase b₃ (tail2FiberBase b₄ tail)))))
          (m * m * m * m * m) =
            (-(canonicalWordDeltaDrift W (6 : Fin 7)) : ZMod m)

theorem canonicalPrefixWordSubsubsubsubfiberDebit_of_hit_five_sum
    (hhitFive : CanonicalPrefixWordLayerHitFiveSumTheorem) :
    CanonicalPrefixWordSubsubsubsubfiberDebitTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃ b₄ tail
  rw [canonicalPrefixWordReturnIterDebitFive_eq_symbol_sum_of_hit_five_sum
    hhitFive W hW]
  rw [canonicalPrefixWordSymbolDebitFive_sum W hW.length_eq]
  simp [canonicalWordDeltaDrift]

theorem canonicalPrefixWordSubsubsubsubfiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordSubsubsubsubfiberDebitTheorem) :
    CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃ b₄ tail
  rw [canonicalPrefixWordSubsubsubsubfiberReturn_coord_zero_of_iterDebitFive W hW]
  rw [hdebit W hW b₀ b₁ b₂ b₃ b₄ tail]
  ring

theorem canonicalPrefixWordSubsubsubsubfiberHeadDrift_of_hit_five_sum
    (hhitFive : CanonicalPrefixWordLayerHitFiveSumTheorem) :
    CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubsubsubfiberHeadDrift_of_debit
    (canonicalPrefixWordSubsubsubsubfiberDebit_of_hit_five_sum hhitFive)

theorem canonicalPrefixWordSubsubsubsubfiberHeadDrift :
    CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem :=
  canonicalPrefixWordSubsubsubsubfiberHeadDrift_of_hit_five_sum
    canonicalPrefixWordLayerHitFiveSum

theorem canonicalPrefixWordSubsubsubfiberSingleCycle_of_head_drift_subsubsubsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsubHead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    (hsubsubsubHead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    (hsubsubsubsub : CanonicalPrefixWordSubsubsubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordSubsubsubfiberReturn W b₀ b₁ b₂ b₃)
    (g := fun x : ZMod m =>
      x + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m))
    (proj := tail2Head)
    (fiberBase := tail2FiberBase 0)
    (fiberNext := canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ 0)
    (returnTime := m)
    (b₀ := 0)
    (canonicalPrefixWordSubsubsubfiberReturn_bijective_of
      hfiberHead hsubHead hsubsubHead W hW b₀ b₁ b₂ b₃)
    (canonicalPrefixWordSubsubsubfiberReturn_head_of
      hsubsubsubHead W hW b₀ b₁ b₂ b₃)
    (tail2FiberBase_surj 0)
    (canonicalPrefixWordSubsubsubsubfiberReturn_iter_m_of
      hsubsubsubHead W hW b₀ b₁ b₂ b₃ 0)
    (canonicalWordDeltaDrift_neg_single_cycle hW (5 : Fin 7) (by decide))
    (hsubsubsubsub W hW b₀ b₁ b₂ b₃ 0)

theorem canonicalPrefixWordSubsubsubsubfiberSingleCycle_of_head_drift
    (hhead : CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem) :
    CanonicalPrefixWordSubsubsubsubfiberSingleCycleTheorem := by
  intro m _ W hW b₀ b₁ b₂ b₃ b₄
  exact single_cycle_of_bijective_semiconj
    (f := fun x : ZMod m =>
      x + (canonicalWordDeltaDrift W (6 : Fin 7) : ZMod m))
    (g := canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄)
    (φ := tail1OfHead)
    tail1OfHead_bijective
    (by
      intro x
      apply funext
      intro i
      fin_cases i
      change
        x + (canonicalWordDeltaDrift W (6 : Fin 7) : ZMod m) =
          (canonicalPrefixWordSubsubsubsubfiberReturn W b₀ b₁ b₂ b₃ b₄
            (tail1OfHead x)) 0
      rw [hhead W hW b₀ b₁ b₂ b₃ b₄ (tail1OfHead x)]
      rfl
    )
    (canonicalWordDeltaDrift_single_cycle hW (6 : Fin 7) (by decide))

theorem canonicalPrefixWordFiberSingleCycle_of_head_drift_subfiber
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsub : CanonicalPrefixWordSubfiberSingleCycleTheorem) :
    CanonicalPrefixWordFiberSingleCycleTheorem := by
  intro m _ W hW b
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordFiberReturn W b)
    (g := fun x : ZMod m => x + (canonicalWordDeltaTwoDrift W : ZMod m))
    (proj := tail5Head)
    (fiberBase := tail5FiberBase 0)
    (fiberNext := canonicalPrefixWordSubfiberReturn W b 0)
    (returnTime := m)
    (b₀ := 0)
    (canonicalPrefixWordFiberReturn_bijective W hW.length_eq b)
    (canonicalPrefixWordFiberReturn_head_of hhead W hW b)
    (tail5FiberBase_surj 0)
    (canonicalPrefixWordSubfiberReturn_iter_m_of hhead W hW b 0)
    (canonicalWordDeltaTwoDrift_single_cycle hW)
    (hsub W hW b 0)

def CanonicalPrefixWordRemainingHeadDriftsTheorem : Prop :=
  CanonicalPrefixWordSubfiberHeadDriftTheorem ∧
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem ∧
      CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem ∧
        CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem

theorem canonicalPrefixWordRemainingHeadDrifts :
    CanonicalPrefixWordRemainingHeadDriftsTheorem :=
  ⟨canonicalPrefixWordSubfiberHeadDrift,
    canonicalPrefixWordSubsubfiberHeadDrift,
    canonicalPrefixWordSubsubsubfiberHeadDrift,
    canonicalPrefixWordSubsubsubsubfiberHeadDrift⟩

theorem canonicalPrefixWordSubsubsubfiberSingleCycle_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem :=
  canonicalPrefixWordSubsubsubfiberSingleCycle_of_head_drift_subsubsubsubfiber
    canonicalPrefixWordFiberHeadDrift
    hheads.1
    hheads.2.1
    hheads.2.2.1
    (canonicalPrefixWordSubsubsubsubfiberSingleCycle_of_head_drift hheads.2.2.2)

theorem canonicalPrefixWordSubsubfiberSingleCycle_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalPrefixWordSubsubfiberSingleCycleTheorem :=
  canonicalPrefixWordSubsubfiberSingleCycle_of_head_drift_subsubsubfiber
    canonicalPrefixWordFiberHeadDrift
    hheads.1
    hheads.2.1
    (canonicalPrefixWordSubsubsubfiberSingleCycle_of_remaining_head_drifts hheads)

theorem canonicalPrefixWordSubfiberSingleCycle_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalPrefixWordSubfiberSingleCycleTheorem :=
  canonicalPrefixWordSubfiberSingleCycle_of_head_drift_subsubfiber
    canonicalPrefixWordFiberHeadDrift
    hheads.1
    (canonicalPrefixWordSubsubfiberSingleCycle_of_remaining_head_drifts hheads)

theorem canonicalPrefixWordFiberSingleCycle_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalPrefixWordFiberSingleCycleTheorem :=
  canonicalPrefixWordFiberSingleCycle_of_head_drift_subfiber
    canonicalPrefixWordFiberHeadDrift
    (canonicalPrefixWordSubfiberSingleCycle_of_remaining_head_drifts hheads)

theorem canonicalPrefixWordSingleCycle_of_fiber_return {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (b₀ : ZMod m) (fiberNext : (Fin 5 → ZMod m) → (Fin 5 → ZMod m))
    (returnTime : Nat)
    (hreturn : ∀ tail : Fin 5 → ZMod m,
      (canonicalPrefixWordReturn (m := m) W)^[returnTime] (prefixFiberBase b₀ tail) =
        prefixFiberBase b₀ (fiberNext tail))
    (hfiber : IsSingleCycleMap fiberNext) :
    IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W) := by
  exact single_cycle_of_fiber_return
    (f := canonicalPrefixWordReturn (m := m) W)
    (g := fun x : ZMod m => x + (canonicalWordCount W 0 : ZMod m))
    (proj := prefixHead)
    (fiberBase := prefixFiberBase b₀)
    (fiberNext := fiberNext)
    (returnTime := returnTime)
    (b₀ := b₀)
    (canonicalPrefixWordReturn_bijective W)
    (by intro z; exact canonicalPrefixWordReturn_head W hW.length_eq z)
    (prefixFiberBase_surj b₀)
    hreturn
    (canonicalPrefixWordReturn_base_single_cycle hW)
    hfiber

theorem canonicalPrefixWordSingleCycle_of_fiber_return_m {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W) (b₀ : ZMod m)
    (hfiber : IsSingleCycleMap (canonicalPrefixWordFiberReturn W b₀)) :
    IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W) :=
  canonicalPrefixWordSingleCycle_of_fiber_return W hW b₀
    (canonicalPrefixWordFiberReturn W b₀) m
    (canonicalPrefixWordReturn_iter_m_fiber W hW.length_eq b₀)
    hfiber

theorem rootPrefixCoord_canonicalPrefixScheduleReturn_fold {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) :
    ∀ L : List Nat, ∀ w : RootState7 m,
      rootPrefixCoord
        (L.foldl
          (fun x (t : Nat) =>
            (canonicalRootFlatSchedule P).layerMap (t : ZMod m) c x) w) =
      L.foldl
        (fun z (t : Nat) => canonicalPrefixMap (t : ZMod m)
          ((countMatrixScheduleAt P (t : ZMod m)) c) z)
        (rootPrefixCoord w)
  | [], w => rfl
  | t :: L, w => by
      rw [List.foldl_cons, List.foldl_cons]
      rw [rootPrefixCoord_canonicalPrefixScheduleReturn_fold P c L]
      congr 1
      change rootPrefixCoord
          (canonicalLayerMap (t : ZMod m) ((countMatrixScheduleAt P (t : ZMod m)) c) w) =
        canonicalPrefixMap (t : ZMod m) ((countMatrixScheduleAt P (t : ZMod m)) c)
          (rootPrefixCoord w)
      rw [rootPrefixCoord_canonicalLayerMap]

theorem rootPrefixCoord_canonicalPrefixScheduleReturn {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) (w : RootState7 m) :
    rootPrefixCoord ((canonicalRootFlatSchedule P).returnMap c w) =
      canonicalPrefixScheduleReturn P c (rootPrefixCoord w) := by
  unfold RootFlatSchedule.returnMap canonicalPrefixScheduleReturn
  exact rootPrefixCoord_canonicalPrefixScheduleReturn_fold P c (List.range m) w

theorem rootOfPrefix_canonicalPrefixScheduleReturn {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) (z : Fin 6 → ZMod m) :
    rootOfPrefix (canonicalPrefixScheduleReturn P c z) =
      (canonicalRootFlatSchedule P).returnMap c (rootOfPrefix z) := by
  apply rootPrefixCoord_bijective.1
  rw [rootPrefixCoord_rootOfPrefix, rootPrefixCoord_canonicalPrefixScheduleReturn,
    rootPrefixCoord_rootOfPrefix]

def CanonicalPrefixWordSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W)

theorem canonicalPrefixWordSingleCycle_of_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    CanonicalPrefixWordSingleCycleTheorem := by
  intro m _ W hW
  exact canonicalPrefixWordSingleCycle_of_fiber_return_m W hW 0 (hfiber W hW 0)

theorem canonicalPrefixWordSingleCycle_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalPrefixWordSingleCycleTheorem :=
  canonicalPrefixWordSingleCycle_of_fiber
    (canonicalPrefixWordFiberSingleCycle_of_remaining_head_drifts hheads)

def CanonicalPrefixWordReturnRankTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W →
      ∃ rank : ((Fin 6 → ZMod m) → ZMod (m ^ 6)),
        Function.Bijective rank ∧
          ∀ z, rank (canonicalPrefixWordReturn (m := m) W z) = rank z + 1

theorem canonicalPrefixWordSingleCycle_of_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    CanonicalPrefixWordSingleCycleTheorem := by
  intro m _ W hW
  haveI : NeZero (m ^ 6) := ⟨pow_ne_zero 6 (NeZero.ne m)⟩
  rcases hrank W hW with ⟨rank, hrank_bij, hstep⟩
  exact single_cycle_of_zmod_rank
    (f := canonicalPrefixWordReturn (m := m) W)
    (rank := rank)
    hrank_bij
    hstep

def CanonicalPrefixReturnSingleCycleTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) →
      ∀ c : Fin 7, IsSingleCycleMap (canonicalPrefixScheduleReturn P c)

theorem canonicalPrefixReturnSingleCycle_of_word
    (hword : CanonicalPrefixWordSingleCycleTheorem) :
    CanonicalPrefixReturnSingleCycleTheorem := by
  intro m _ P hwords c
  rw [canonicalPrefixScheduleReturn_eq_word P c]
  exact hword (m := m) (canonicalWord P.schedule c) (hwords c)

theorem canonicalPrefixReturnSingleCycle_of_word_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    CanonicalPrefixReturnSingleCycleTheorem :=
  canonicalPrefixReturnSingleCycle_of_word
    (canonicalPrefixWordSingleCycle_of_rank hrank)

theorem canonicalReturnSingleCycle_of_prefix
    (hprefix : CanonicalPrefixReturnSingleCycleTheorem) :
    CanonicalReturnSingleCycleTheorem := by
  intro m _ P hwords c
  exact single_cycle_of_bijective_semiconj
    (f := canonicalPrefixScheduleReturn P c)
    (g := (canonicalRootFlatSchedule P).returnMap c)
    (φ := rootOfPrefix)
    rootOfPrefix_bijective
    (rootOfPrefix_canonicalPrefixScheduleReturn P c)
    (hprefix P hwords c)

theorem canonicalReturnSingleCycle_of_word
    (hword : CanonicalPrefixWordSingleCycleTheorem) :
    CanonicalReturnSingleCycleTheorem :=
  canonicalReturnSingleCycle_of_prefix
    (canonicalPrefixReturnSingleCycle_of_word hword)

theorem canonicalRootFlatSchedule_layerBijective_of
    (hlayer : CanonicalLayerBijectiveTheorem)
    {m : Nat} [NeZero m] (P : CountMatrixSchedule m) :
    (canonicalRootFlatSchedule P).layerBijective := by
  intro t c
  exact hlayer t ((countMatrixScheduleAt P t) c)

def canonicalScheduleRealizationOf
    (hlayer : CanonicalLayerBijectiveTheorem)
    (hreturn : CanonicalReturnSingleCycleTheorem)
    {m : Nat} [NeZero m] (P : CountMatrixSchedule m) :
    CanonicalScheduleRealization m P where
  schedule := canonicalRootFlatSchedule P
  rowLatin := canonicalRootFlatSchedule_rowLatin P
  layerBijective := canonicalRootFlatSchedule_layerBijective_of hlayer P
  returnsSingleCycle := hreturn P

theorem canonical_realization_theorem_of_parts
    (hlayer : CanonicalLayerBijectiveTheorem)
    (hreturn : CanonicalReturnSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem := by
  intro m _ P
  exact ⟨canonicalScheduleRealizationOf hlayer hreturn P⟩

theorem canonical_realization_theorem_of_prefix_inverse
    (hinv : CanonicalPrefixLayerInverseTheorem)
    (hreturn : CanonicalReturnSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_parts
    (canonicalLayerBijective_of_prefix_inverse hinv)
    hreturn

theorem canonical_realization_theorem_of_return
    (hreturn : CanonicalReturnSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_parts canonicalLayerBijective hreturn

theorem canonical_realization_theorem_of_word
    (hword : CanonicalPrefixWordSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_return
    (canonicalReturnSingleCycle_of_word hword)

theorem main_odd_from_canonical_word
    (hword : CanonicalPrefixWordSingleCycleTheorem) :
    MainOddTheoremTarget :=
  main_odd_from_canonical_realization
    (canonical_realization_theorem_of_word hword)

theorem canonical_realization_theorem_of_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_word
    (canonicalPrefixWordSingleCycle_of_fiber hfiber)

theorem canonical_realization_theorem_of_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_word
    (canonicalPrefixWordSingleCycle_of_remaining_head_drifts hheads)

theorem canonical_realization_theorem_of_word_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_word
    (canonicalPrefixWordSingleCycle_of_rank hrank)

theorem main_odd_from_canonical_word_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    MainOddTheoremTarget :=
  main_odd_from_canonical_realization
    (canonical_realization_theorem_of_word_rank hrank)

theorem main_odd_from_canonical_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    MainOddTheoremTarget :=
  main_odd_from_canonical_realization
    (canonical_realization_theorem_of_fiber hfiber)

theorem main_odd_from_canonical_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    MainOddTheoremTarget :=
  main_odd_from_canonical_realization
    (canonical_realization_theorem_of_remaining_head_drifts hheads)

theorem canonicalPrefixWordSingleCycle :
    CanonicalPrefixWordSingleCycleTheorem :=
  canonicalPrefixWordSingleCycle_of_remaining_head_drifts
    canonicalPrefixWordRemainingHeadDrifts

theorem canonical_realization_theorem :
    CanonicalScheduleRealizationTheorem :=
  canonical_realization_theorem_of_word canonicalPrefixWordSingleCycle

theorem main_odd :
    MainOddTheoremTarget :=
  main_odd_from_canonical_word canonicalPrefixWordSingleCycle

end Handoff
end D7Odd
