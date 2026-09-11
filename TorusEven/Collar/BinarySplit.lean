-- STATUS: main-path
import TorusEven.Collar.Multitorus
import TorusEven.Collar.OrbitLift

namespace TorusEven.Collar

variable {C I : Type*} [Fintype C] [DecidableEq C] [DecidableEq I] {m : ℕ}

def splitChart (i : I) : ((I → ZMod m) × ZMod m) ≃ (Option I → ZMod m) where
  toFun p j := match j with
    | none => p.2
    | some j => if j = i then p.1 j - p.2 else p.1 j
  invFun x := (fun j => if j = i then x (some j) + x none else x (some j), x none)
  left_inv p := by
    apply Prod.ext
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · rfl
  right_inv x := by
    funext j
    cases j with
    | none => rfl
    | some j => by_cases hj : j = i <;> simp [hj]

variable (F : MultitorusFactorization C I m) (i : I)
variable (J : (I → ZMod m) → Finset C)

def splitVoltage (c : C) (x : I → ZMod m) : ZMod m := if c ∈ J x then 1 else 0

def splitDirection (c : C) (x : I → ZMod m) : Option I :=
  if c ∈ J x then none else some (F.direction c x)

theorem splitDirection_parent (hJ : ∀ x, J x ⊆ F.users x i) (c : C) (x : I → ZMod m) :
    (splitDirection F J c x).getD i = F.direction c x := by
  by_cases hc : c ∈ J x
  · simp [splitDirection, hc, (F.mem_users _ _ _).mp (hJ x hc)]
  · simp [splitDirection, hc]

theorem splitChart_step (hJ : ∀ x, J x ⊆ F.users x i)
    (c : C) (p : (I → ZMod m) × ZMod m) (j : Option I) :
    splitChart i (lift (F.step c) (splitVoltage J c) p) j =
      splitChart i p j + if j = splitDirection F J c p.1 then 1 else 0 := by
  by_cases hc : c ∈ J p.1
  · have hd : F.direction c p.1 = i := (F.mem_users _ _ _).mp (hJ _ hc)
    cases j with
    | none => simp [splitChart, splitVoltage, splitDirection, lift, hc]
    | some j =>
      by_cases hj : j = i <;>
        simp [splitChart, splitVoltage, splitDirection, lift, hc, F.step_eq, hd, hj]
  · cases j with
    | none => simp [splitChart, splitVoltage, splitDirection, lift, hc]
    | some j =>
      by_cases hj : j = i <;>
        simp [splitChart, splitVoltage, splitDirection, lift, hc, F.step_eq, hj]
      split_ifs <;> ring

def splitWidth (b : ℕ) : Option I → ℕ
  | none => b
  | some j => if j = i then F.width i - b else F.width j

theorem split_quota (b : ℕ) (hJ : ∀ x, J x ⊆ F.users x i) (hcard : ∀ x, (J x).card = b)
    (x : I → ZMod m) (j : Option I) :
    (Finset.univ.filter (fun c => splitDirection F J c x = j)).card = splitWidth F i b j := by
  cases j with
  | none =>
    have heq : Finset.univ.filter (fun c => splitDirection F J c x = none) = J x := by
      ext c
      by_cases hc : c ∈ J x <;> simp [splitDirection, hc]
    rw [heq]
    exact hcard x
  | some j =>
    have heq : Finset.univ.filter (fun c => splitDirection F J c x = some j) =
        F.users x j \ J x := by
      ext c
      by_cases hc : c ∈ J x <;> simp [splitDirection, hc, and_comm]
    rw [heq]
    by_cases hj : j = i
    · subst j
      rw [Finset.card_sdiff_of_subset (hJ x), hcard, F.card_users]
      simp [splitWidth]
    · have hd : Disjoint (F.users x j) (J x) := by
        rw [Finset.disjoint_left]
        intro c hc hcJ
        exact hj (((F.mem_users _ _ _).mp hc).symm.trans ((F.mem_users _ _ _).mp (hJ x hcJ)))
      rw [hd.sdiff_eq_left, F.card_users]
      simp [splitWidth, hj]

def MultitorusFactorization.split (b : ℕ) (hb : 0 < b) (hbi : b < F.width i)
    (hJ : ∀ x, J x ⊆ F.users x i) (hcard : ∀ x, (J x).card = b) :
    MultitorusFactorization C (Option I) m where
  width := splitWidth F i b
  width_pos j := by
    cases j with
    | none => exact hb
    | some j => by_cases hj : j = i <;> simp [splitWidth, hj, hbi, F.width_pos]
  direction c x := splitDirection F J c ((splitChart i).symm x).1
  step c := (splitChart i).symm.trans ((lift (F.step c) (splitVoltage J c)).trans (splitChart i))
  step_eq c x j := by
    obtain ⟨p, rfl⟩ := (splitChart (m := m) i).surjective x
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using splitChart_step F i J hJ c p j
  quota x j := split_quota F i J b hJ hcard ((splitChart i).symm x).1 j

def MultitorusFactorization.balancedSplit (hi : 2 ≤ F.width i)
    (hJ : ∀ x, J x ⊆ F.users x i) (hcard : ∀ x, (J x).card = F.width i / 2) :
    MultitorusFactorization C (Option I) m :=
  F.split i J (F.width i / 2) (by omega) (by omega) hJ hcard

theorem MultitorusFactorization.balancedSplit_width (hi : 2 ≤ F.width i)
    (hJ : ∀ x, J x ⊆ F.users x i) (hcard : ∀ x, (J x).card = F.width i / 2) :
    (F.balancedSplit i J hi hJ hcard).width none = F.width i / 2 ∧
      (F.balancedSplit i J hi hJ hcard).width (some i) = (F.width i + 1) / 2 := by
  constructor
  · rfl
  · change (if i = i then F.width i - F.width i / 2 else F.width i) = (F.width i + 1) / 2
    rw [if_pos rfl]
    omega

variable (b : ℕ) (hb : 0 < b) (hbi : b < F.width i)
variable (hJ : ∀ x, J x ⊆ F.users x i) (hcard : ∀ x, (J x).card = b)

theorem MultitorusFactorization.split_semiconj (c : C) :
    Function.Semiconj (splitChart i) (lift (F.step c) (splitVoltage J c))
      ((F.split i J b hb hbi hJ hcard).step c) := by
  intro p
  simp [split, Equiv.trans_apply]

theorem MultitorusFactorization.split_activeSeparated (active : Set C)
    (h : F.ActiveSeparated active) : (F.split i J b hb hbi hJ hcard).ActiveSeparated active := by
  intro x c hc c' hc' heq
  apply h ((splitChart i).symm x).1 hc hc'
  have hp := congrArg (fun k : Option I => k.getD i) heq
  change (splitDirection F J c _).getD i = (splitDirection F J c' _).getD i at hp
  simpa only [splitDirection_parent F i J hJ] using hp

theorem MultitorusFactorization.split_fibre_direction (c : C) (x : I → ZMod m) (t s : ZMod m) :
    (F.split i J b hb hbi hJ hcard).direction c (splitChart i (x, t)) =
      (F.split i J b hb hbi hJ hcard).direction c (splitChart i (x, s)) := by
  simp [split]

theorem MultitorusFactorization.split_excess [Fintype I] :
    (F.split i J b hb hbi hJ hcard).excess + 1 = F.excess := by
  have h := (F.split i J b hb hbi hJ hcard).excess_add_card
  have h' := F.excess_add_card
  simp only [Fintype.card_option] at h
  omega

variable [Fintype I] [NeZero m]

theorem MultitorusFactorization.split_circuit_iff (c : C)
    (hunit : UnitCarry (F.step c) (splitVoltage J c))
    (p q : (I → ZMod m) × ZMod m) :
    Surgery.circuitOf ((F.split i J b hb hbi hJ hcard).step c) (splitChart i p) =
        Surgery.circuitOf ((F.split i J b hb hbi hJ hcard).step c) (splitChart i q) ↔
      Surgery.circuitOf (F.step c) p.1 = Surgery.circuitOf (F.step c) q.1 := by
  rw [Surgery.circuitOf_eq, Surgery.circuitOf_eq,
    Surgery.orbit_equiv_iff _ _ (splitChart i) (F.split_semiconj i J b hb hbi hJ hcard c),
    lift_orbit_iff _ _ hunit]

theorem MultitorusFactorization.split_circuitCount (c : C)
    (hunit : UnitCarry (F.step c) (splitVoltage J c)) :
    Surgery.circuitCount ((F.split i J b hb hbi hJ hcard).step c) =
      Surgery.circuitCount (F.step c) := by
  rw [← Surgery.circuitCount_congr _ _ (splitChart i)
    (F.split_semiconj i J b hb hbi hJ hcard c)]
  exact lift_circuitCount _ _ hunit

theorem MultitorusFactorization.split_fibre_circuit (c : C)
    (hunit : UnitCarry (F.step c) (splitVoltage J c)) (x : I → ZMod m) (t s : ZMod m) :
    Surgery.circuitOf ((F.split i J b hb hbi hJ hcard).step c) (splitChart i (x, t)) =
      Surgery.circuitOf ((F.split i J b hb hbi hJ hcard).step c) (splitChart i (x, s)) :=
  (F.split_circuit_iff i J b hb hbi hJ hcard c hunit (x, t) (x, s)).mpr rfl

end TorusEven.Collar
