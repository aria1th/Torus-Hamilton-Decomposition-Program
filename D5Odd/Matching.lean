import D5Odd.Schedule

namespace D5Odd

inductive ReducedVal where
  | zero
  | shift
  | other
deriving DecidableEq, Fintype, Repr

abbrev ReducedSig := Fin 5 -> ReducedVal

instance : DecidableEq ReducedSig := inferInstance
instance : Fintype ReducedSig := inferInstance

instance {m : Nat} : DecidablePred (Root5 m) := by
  intro w
  unfold Root5 sum5
  infer_instance

instance : DecidableEq (ARoot5 3) := inferInstance
instance : Fintype (ARoot5 3) := inferInstance

def UniqueDirection (p : Direction -> Prop) : Prop :=
  ∃ i : Direction, p i ∧ ∀ j : Direction, p j -> j = i

instance (p : Direction -> Prop) [DecidablePred p] : Decidable (UniqueDirection p) := by
  unfold UniqueDirection
  infer_instance

theorem UniqueDirection.existsUnique {p : Direction -> Prop} (h : UniqueDirection p) :
    ∃! i : Direction, p i := by
  rcases h with ⟨i, hi, huniq⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact huniq j hj

def firstClass {m : Nat} (x : ZMod m) : ReducedVal :=
  if x = 0 then .zero else if x = 1 then .shift else .other

def lastClass {m : Nat} (x : ZMod m) : ReducedVal :=
  if x = 0 then .zero else if x = (-1 : ZMod m) then .shift else .other

theorem firstClass_eq_zero_iff {m : Nat} {x : ZMod m} :
    firstClass x = .zero ↔ x = 0 := by
  unfold firstClass
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0, h1]

theorem firstClass_eq_shift_iff {m : Nat} {x : ZMod m} :
    firstClass x = .shift ↔ x ≠ 0 ∧ x = 1 := by
  unfold firstClass
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0, h1]

theorem firstClass_eq_other_iff {m : Nat} {x : ZMod m} :
    firstClass x = .other ↔ x ≠ 0 ∧ x ≠ 1 := by
  unfold firstClass
  by_cases h0 : x = 0
  · by_cases h1 : x = 1
    · simp [h0]
    · simp [h0]
  · by_cases h1 : x = 1
    · subst h1
      simp [h0]
    · simp [h0, h1]

theorem lastClass_eq_zero_iff {m : Nat} {x : ZMod m} :
    lastClass x = .zero ↔ x = 0 := by
  unfold lastClass
  by_cases h0 : x = 0 <;> by_cases h1 : x = (-1 : ZMod m) <;> simp [h0, h1]

theorem lastClass_eq_shift_iff {m : Nat} {x : ZMod m} :
    lastClass x = .shift ↔ x ≠ 0 ∧ x = (-1 : ZMod m) := by
  unfold lastClass
  by_cases h0 : x = 0 <;> by_cases h1 : x = (-1 : ZMod m) <;> simp [h0, h1]

theorem lastClass_eq_other_iff {m : Nat} {x : ZMod m} :
    lastClass x = .other ↔ x ≠ 0 ∧ x ≠ (-1 : ZMod m) := by
  unfold lastClass
  by_cases h0 : x = 0
  · by_cases h1 : x = (-1 : ZMod m)
    · simp [h0]
    · simp [h0]
  · by_cases h1 : x = (-1 : ZMod m)
    · subst h1
      simp [h0]
    · simp [h0, h1]

theorem zmod_nat_ne_zero {m k : Nat} [NeZero m] (hk : 0 < k) (hkm : k < m) :
    (((k : Nat) : ZMod m) ≠ 0) := by
  intro h
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hd : m ∣ k := (ZMod.natCast_eq_zero_iff k m).mp h
  have hkge : m ≤ k := by
    rcases hd with ⟨t, rfl⟩
    cases t with
    | zero => omega
    | succ t =>
        have ht : 1 ≤ Nat.succ t := Nat.succ_le_succ (Nat.zero_le _)
        have hmul : m * 1 ≤ m * Nat.succ t := Nat.mul_le_mul_left m ht
        simpa using hmul
  exact (Nat.not_lt_of_ge hkge hkm).elim

theorem firstClass_eq_shift_iff_sub_eq_zero {m : Nat} [NeZero m] (hm : 5 <= m)
    {x : ZMod m} :
    firstClass x = .shift ↔ x - 1 = 0 := by
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using zmod_nat_ne_zero (m := m) (k := 1) (by norm_num) (by omega)
  constructor
  · intro h
    have hx : x = 1 := (firstClass_eq_shift_iff.mp h).2
    simp [hx]
  · intro h
    have hx : x = 1 := sub_eq_zero.mp h
    exact firstClass_eq_shift_iff.mpr ⟨by simpa [hx] using h10, hx⟩

theorem lastClass_eq_shift_iff_add_eq_zero {m : Nat} [NeZero m] (hm : 5 <= m)
    {x : ZMod m} :
    lastClass x = .shift ↔ x + 1 = 0 := by
  have hneg10 : (-1 : ZMod m) ≠ 0 := by
    intro h
    have h1 : (1 : ZMod m) = 0 := neg_eq_zero.mp h
    exact (zmod_nat_ne_zero (m := m) (k := 1) (by norm_num) (by omega))
      (by simpa using h1)
  constructor
  · intro h
    have hx : x = -1 := (lastClass_eq_shift_iff.mp h).2
    simp [hx]
  · intro h
    have hx : x = (-1 : ZMod m) := add_eq_zero_iff_eq_neg.mp h
    exact lastClass_eq_shift_iff.mpr ⟨by simpa [hx] using hneg10, hx⟩

def reducedSig {m : Nat} (w : Vec5 m) : ReducedSig :=
  fun i =>
    if _ : i = 4 then lastClass (w i) else firstClass (w i)

def predMaskOfSig (s : ReducedSig) (i : Direction) : Mask5 :=
  fun j =>
    let k := fin5AddNat j 1
    if _ : i = 4 then
      decide (s k = .zero)
    else if _ : k = i then
      decide (s k = .shift)
    else if _ : k = 4 then
      decide (s 4 = .shift)
    else
      decide (s k = .zero)

set_option linter.unusedSimpArgs false in
theorem predMaskOfSig_reducedSig {m : Nat} [NeZero m] (hm : 5 <= m)
    (w : Vec5 m) (i : Direction) :
    predMaskOfSig (reducedSig w) i = zeroMaskMinusOne (w - q5 m i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [predMaskOfSig, reducedSig, zeroMaskMinusOne, zeroMask, fin5AddNat, q5, e5,
      firstClass_eq_zero_iff, firstClass_eq_shift_iff_sub_eq_zero,
      lastClass_eq_zero_iff, lastClass_eq_shift_iff_add_eq_zero, hm]

def firstShiftCount (s : ReducedSig) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => s (Fin.castLT i (by omega)) = .shift).card

def firstOtherCount (s : ReducedSig) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => s (Fin.castLT i (by omega)) = .other).card

theorem firstShiftCount_eq_sum4 (s : ReducedSig) :
    firstShiftCount s =
      (if s 0 = .shift then 1 else 0) +
      (if s 1 = .shift then 1 else 0) +
      (if s 2 = .shift then 1 else 0) +
      (if s 3 = .shift then 1 else 0) := by
  unfold firstShiftCount
  rw [Finset.card_filter]
  rw [Fin.sum_univ_four]
  rfl

theorem firstOtherCount_eq_sum4 (s : ReducedSig) :
    firstOtherCount s =
      (if s 0 = .other then 1 else 0) +
      (if s 1 = .other then 1 else 0) +
      (if s 2 = .other then 1 else 0) +
      (if s 3 = .other then 1 else 0) := by
  unfold firstOtherCount
  rw [Finset.card_filter]
  rw [Fin.sum_univ_four]
  rfl

def ge5Feasible (s : ReducedSig) : Bool :=
  let a := firstShiftCount s
  let b := firstOtherCount s
  let l := s 4
  if 2 <= b then
    true
  else if b = 1 then
    match l with
    | .zero => decide (a ≠ 0)
    | .shift => decide (2 <= a)
    | .other => true
  else if a = 0 then
    decide (l = .zero)
  else if a = 1 then
    decide (l = .shift)
  else
    decide (l = .other)

@[simp] theorem reducedSig_four {m : Nat} (w : Vec5 m) :
    reducedSig w 4 = lastClass (w 4) := by
  simp [reducedSig]

@[simp] theorem reducedSig_ne_four {m : Nat} (w : Vec5 m) {i : Fin 5} (hi : i ≠ 4) :
    reducedSig w i = firstClass (w i) := by
  simp [reducedSig, hi]

set_option linter.style.maxHeartbeats false in
set_option linter.flexible false in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem ge5Feasible_of_root {m : Nat} [NeZero m] (hm : 5 <= m)
    {w : Vec5 m} (hw : Root5 m w) :
    ge5Feasible (reducedSig w) = true := by
  generalize h0 : firstClass (w 0) = c0
  generalize h1 : firstClass (w 1) = c1
  generalize h2 : firstClass (w 2) = c2
  generalize h3 : firstClass (w 3) = c3
  generalize h4 : lastClass (w 4) = c4
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4
  all_goals
    first
    | solve |
        rw [ge5Feasible, firstShiftCount_eq_sum4, firstOtherCount_eq_sum4]
        simp [reducedSig, h0, h1, h2, h3, h4]
    | exfalso
      simp only [firstClass_eq_zero_iff, firstClass_eq_shift_iff, firstClass_eq_other_iff,
        lastClass_eq_zero_iff, lastClass_eq_shift_iff, lastClass_eq_other_iff] at h0 h1 h2 h3 h4
      unfold Root5 sum5 at hw
      rw [Fin.sum_univ_five] at hw
      simp [h0, h1, h2, h3, h4] at hw
      all_goals
        try norm_num at hw
        first
        | exact (zmod_nat_ne_zero (m := m) (k := 1) (by norm_num) (by omega))
            (by simpa using hw)
        | exact (zmod_nat_ne_zero (m := m) (k := 2) (by norm_num) (by omega))
            (by simpa using hw)
        | exact (zmod_nat_ne_zero (m := m) (k := 3) (by norm_num) (by omega))
            (by simpa using hw)
        | exact (zmod_nat_ne_zero (m := m) (k := 4) (by norm_num) (by omega))
            (by simpa using hw)
        | exact h0.1 (by simpa using hw)
        | exact h0.2 (by simpa using hw)
        | exact h1.1 (by simpa using hw)
        | exact h1.2 (by simpa using hw)
        | exact h2.1 (by simpa using hw)
        | exact h2.2 (by simpa using hw)
        | exact h3.1 (by simpa using hw)
        | exact h3.2 (by simpa using hw)
        | exact h4.1 (by simpa using hw)
        | exact h4.2 (by simpa using hw)
        | exact h0.2 (by simpa using add_eq_zero_iff_eq_neg.mp hw)
        | exact h1.2 (by simpa using add_eq_zero_iff_eq_neg.mp hw)
        | exact h2.2 (by simpa using add_eq_zero_iff_eq_neg.mp hw)
        | exact h3.2 (by simpa using add_eq_zero_iff_eq_neg.mp hw)
        | exact h4.2 (by
            rw [add_comm] at hw
            simpa using add_eq_zero_iff_eq_neg.mp hw)

set_option linter.style.nativeDecide false in
theorem ge5_exact_of_feasible :
    ∀ s : ReducedSig, ge5Feasible s = true ->
      ∀ c : Color, ∃! i : Direction, Lambda1 (predMaskOfSig s i) c = i := by
  intro s hs c
  have h :
      UniqueDirection fun i : Direction => Lambda1 (predMaskOfSig s i) c = i := by
    native_decide +revert
  exact h.existsUnique

theorem existsUnique_eq_direction (d : Direction) : ∃! i : Direction, d = i := by
  exact ⟨d, rfl, by intro j hj; exact hj.symm⟩

set_option linter.unnecessarySimpa false in
theorem ge5Schedule_exact {m : Nat} [NeZero m] (hm : 5 <= m) :
    IsLayerExactCover (ge5Schedule m) := by
  intro t c y
  by_cases h1 : t.val = 1
  · have hfeas : ge5Feasible (reducedSig y.1) = true := ge5Feasible_of_root hm y.2
    have hcert := ge5_exact_of_feasible (reducedSig y.1) hfeas c
    simpa [ge5Schedule, ge5Dir, h1, predMaskOfSig_reducedSig hm y.1] using hcert
  · by_cases h2 : t.val = 2
    · simpa [ge5Schedule, ge5Dir, h1, h2] using
        existsUnique_eq_direction (fin5AddNat c 3)
    · by_cases h3 : t.val = 3
      · simpa [ge5Schedule, ge5Dir, h1, h2, h3] using
          existsUnique_eq_direction (fin5AddNat c 4)
      · simpa [ge5Schedule, ge5Dir, h1, h2, h3] using existsUnique_eq_direction c

set_option linter.style.nativeDecide false in
theorem m3Schedule_exact : IsLayerExactCover m3Schedule := by
  intro t c y
  have h :
      UniqueDirection fun i : Direction => m3Schedule.dir t c (y.1 - q5 3 i) = i := by
    native_decide +revert
  exact h.existsUnique

end D5Odd
