import TorusD4.ReturnMaps
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Iterate

namespace TorusD4

def CycleOn (N : ℕ) (f : α → α) (x : α) : Prop :=
  Function.Bijective (fun i : Fin N => (f^[i.1]) x) ∧ (f^[N]) x = x

def HasCycle (N : ℕ) (f : α → α) : Prop :=
  ∃ x, CycleOn N f x

theorem cycleOn_conj {N : ℕ} {f : α → α} {g : β → β} (e : α ≃ β) {x : α}
    (h : Function.Semiconj e f g) (hc : CycleOn N f x) :
    CycleOn N g (e x) := by
  constructor
  · constructor
    · intro i j hij
      apply hc.1.1
      apply e.injective
      calc
        e ((f^[i.1]) x) = (g^[i.1]) (e x) := (h.iterate_right i.1).eq x
        _ = (g^[j.1]) (e x) := hij
        _ = e ((f^[j.1]) x) := by symm; exact (h.iterate_right j.1).eq x
    · intro y
      rcases hc.1.2 (e.symm y) with ⟨i, hi⟩
      have hi' : (f^[i.1]) x = e.symm y := by
        simpa using hi
      refine ⟨i, ?_⟩
      calc
        (g^[i.1]) (e x) = e ((f^[i.1]) x) := by
          symm
          exact (h.iterate_right i.1).eq x
        _ = e (e.symm y) := by rw [hi']
        _ = y := by simp
  · calc
      (g^[N]) (e x) = e ((f^[N]) x) := by
        symm
        exact (h.iterate_right N).eq x
      _ = e x := by rw [hc.2]

def odometerWrap (x : QCoord m) : QCoord m :=
  let (u, v) := x
  (u + 1, v + delta m (u = (-1 : ZMod m)))

def shiftEquiv : QCoord m ≃ QCoord m where
  toFun x := (x.1 + 1, x.2)
  invFun x := (x.1 - 1, x.2)
  left_inv x := by
    rcases x with ⟨u, v⟩
    simp
  right_inv x := by
    rcases x with ⟨u, v⟩
    simp

theorem shift_conj_wrap (x : QCoord m) :
    shiftEquiv (odometerWrap (m := m) x) = odometer (m := m) (shiftEquiv x) := by
  rcases x with ⟨u, v⟩
  ext
  · simp [shiftEquiv, odometerWrap, odometer]
  · by_cases hu : u = (-1 : ZMod m)
    · simp [shiftEquiv, odometerWrap, odometer, delta, hu]
    · have hu' : u + 1 ≠ (0 : ZMod m) := by
        intro huz
        exact hu (eq_neg_iff_add_eq_zero.mpr huz)
      simp [shiftEquiv, odometerWrap, odometer, delta, hu, hu']

def wrapState (m n : ℕ) : QCoord m :=
  ((n : ZMod m), ((n / m : ℕ) : ZMod m))

theorem odometerWrap_iterate_zero [Fact (0 < m)] (n : ℕ) :
    (odometerWrap (m := m)^[n]) ((0 : ZMod m), (0 : ZMod m)) = wrapState m n := by
  have hm : 0 < m := Fact.out
  induction n with
  | zero =>
      simp [wrapState]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, odometerWrap, wrapState]
      by_cases hd : m ∣ n + 1
      · have hcarry : (n : ZMod m) = (-1 : ZMod m) := by
          apply eq_neg_iff_add_eq_zero.mpr
          have hzero : (((n + 1 : ℕ) : ZMod m)) = 0 := by
            exact (ZMod.natCast_eq_zero_iff (n + 1) m).2 hd
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hzero
        ext <;> simp [delta, hcarry, wrapState, Nat.succ_div_of_dvd hd, Nat.cast_add, add_comm]
      · have hcarry : (n : ZMod m) ≠ (-1 : ZMod m) := by
          intro hneg
          have hzero : (((n + 1 : ℕ) : ZMod m)) = 0 := by
            simp [Nat.cast_add, hneg, add_comm]
          exact hd ((ZMod.natCast_eq_zero_iff (n + 1) m).1 hzero)
        ext <;> simp [delta, hcarry, wrapState, Nat.succ_div_of_not_dvd hd, Nat.cast_add]

def wrapOrbitMap (m : ℕ) (i : Fin (m * m)) : QCoord m :=
  wrapState m i.1

theorem wrapOrbitMap_injective [Fact (0 < m)] :
    Function.Injective (wrapOrbitMap m) := by
  intro i j hij
  have hm : 0 < m := Fact.out
  have hfst : ((i.1 : ℕ) : ZMod m) = ((j.1 : ℕ) : ZMod m) := by
    simpa [wrapOrbitMap, wrapState] using congrArg Prod.fst hij
  have hsnd : (((i.1 / m : ℕ) : ZMod m)) = (((j.1 / m : ℕ) : ZMod m)) := by
    simpa [wrapOrbitMap, wrapState] using congrArg Prod.snd hij
  have hmod : i.1 % m = j.1 % m := by
    exact (ZMod.natCast_eq_natCast_iff' i.1 j.1 m).1 hfst
  have hiDivLt : i.1 / m < m := by
    exact (Nat.div_lt_iff_lt_mul hm).2 i.2
  have hjDivLt : j.1 / m < m := by
    exact (Nat.div_lt_iff_lt_mul hm).2 j.2
  have hdiv : i.1 / m = j.1 / m := by
    have hdivMod : (i.1 / m) % m = (j.1 / m) % m := by
      exact (ZMod.natCast_eq_natCast_iff' (i.1 / m) (j.1 / m) m).1 hsnd
    rwa [Nat.mod_eq_of_lt hiDivLt, Nat.mod_eq_of_lt hjDivLt] at hdivMod
  apply Fin.eq_of_val_eq
  calc
    i.1 = i.1 % m + m * (i.1 / m) := by symm; exact Nat.mod_add_div _ _
    _ = j.1 % m + m * (j.1 / m) := by rw [hmod, hdiv]
    _ = j.1 := by exact Nat.mod_add_div _ _

theorem cycleOn_odometerWrap [Fact (0 < m)] :
    CycleOn (m * m) (odometerWrap (m := m)) ((0 : ZMod m), (0 : ZMod m)) := by
  letI : NeZero m := ⟨Nat.ne_of_gt Fact.out⟩
  letI : Fintype (QCoord m) := inferInstance
  have hm : 0 < m := Fact.out
  have horbit :
      (fun i : Fin (m * m) => (odometerWrap (m := m)^[i.1]) ((0 : ZMod m), (0 : ZMod m))) =
        wrapOrbitMap m := by
    funext i
    exact odometerWrap_iterate_zero i.1
  have hbij :
      Function.Bijective (wrapOrbitMap m) := by
    exact (Fintype.bijective_iff_injective_and_card (wrapOrbitMap m)).2
      ⟨wrapOrbitMap_injective (m := m), by simp [QCoord]⟩
  refine ⟨by simpa [horbit] using hbij, ?_⟩
  calc
    (odometerWrap (m := m)^[m * m]) ((0 : ZMod m), (0 : ZMod m)) = wrapState m (m * m) := by
      exact odometerWrap_iterate_zero (m := m) (m * m)
    _ = ((0 : ZMod m), (0 : ZMod m)) := by
      ext <;> simp [wrapState, hm.ne']

theorem cycleOn_odometer [Fact (0 < m)] :
    CycleOn (m * m) (odometer (m := m)) (shiftEquiv ((0 : ZMod m), (0 : ZMod m))) := by
  exact cycleOn_conj shiftEquiv (f := odometerWrap (m := m)) (g := odometer (m := m))
    shift_conj_wrap cycleOn_odometerWrap

def psi0Equiv : QCoord m ≃ QCoord m where
  toFun := psi0
  invFun x := (-x.2, 1 - x.1)
  left_inv x := by
    rcases x with ⟨a, b⟩
    ext <;> simp [psi0]
  right_inv x := by
    rcases x with ⟨u, v⟩
    ext <;> simp [psi0]

def psi1Equiv : QCoord m ≃ QCoord m where
  toFun := psi1
  invFun := psi1
  left_inv x := by
    rcases x with ⟨a, b⟩
    ext <;> simp [psi1]
  right_inv x := by
    rcases x with ⟨a, b⟩
    ext <;> simp [psi1]

def psi2Equiv : QCoord m ≃ QCoord m where
  toFun := psi2
  invFun x := (x.2, x.1 + 2)
  left_inv x := by
    rcases x with ⟨a, b⟩
    ext <;> simp [psi2]
  right_inv x := by
    rcases x with ⟨u, v⟩
    ext <;> simp [psi2]

def psi3Equiv : QCoord m ≃ QCoord m := Equiv.refl _

theorem cycleOn_T0 [Fact (0 < m)] :
    HasCycle (m * m) (T0 (m := m)) := by
  refine ⟨psi0Equiv.symm (shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi0Equiv (T0 (m := m)) (odometer (m := m)) := psi0_conj
  have hsymm : Function.Semiconj psi0Equiv.symm (odometer (m := m)) (T0 (m := m)) :=
    hsemi.inverse_left psi0Equiv.left_inv psi0Equiv.right_inv
  exact cycleOn_conj psi0Equiv.symm (f := odometer (m := m)) (g := T0 (m := m)) hsymm
    cycleOn_odometer

theorem cycleOn_T1 [Fact (0 < m)] :
    HasCycle (m * m) (T1 (m := m)) := by
  refine ⟨psi1Equiv.symm (shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi1Equiv (T1 (m := m)) (odometer (m := m)) := psi1_conj
  have hsymm : Function.Semiconj psi1Equiv.symm (odometer (m := m)) (T1 (m := m)) :=
    hsemi.inverse_left psi1Equiv.left_inv psi1Equiv.right_inv
  exact cycleOn_conj psi1Equiv.symm (f := odometer (m := m)) (g := T1 (m := m)) hsymm
    cycleOn_odometer

theorem cycleOn_T2 [Fact (0 < m)] :
    HasCycle (m * m) (T2 (m := m)) := by
  refine ⟨psi2Equiv.symm (shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi2Equiv (T2 (m := m)) (odometer (m := m)) := psi2_conj
  have hsymm : Function.Semiconj psi2Equiv.symm (odometer (m := m)) (T2 (m := m)) :=
    hsemi.inverse_left psi2Equiv.left_inv psi2Equiv.right_inv
  exact cycleOn_conj psi2Equiv.symm (f := odometer (m := m)) (g := T2 (m := m)) hsymm
    cycleOn_odometer

theorem cycleOn_T3 [Fact (0 < m)] :
    HasCycle (m * m) (T3 (m := m)) := by
  refine ⟨psi3Equiv.symm (shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi3Equiv (T3 (m := m)) (odometer (m := m)) := psi3_conj
  have hsymm : Function.Semiconj psi3Equiv.symm (odometer (m := m)) (T3 (m := m)) :=
    hsemi.inverse_left psi3Equiv.left_inv psi3Equiv.right_inv
  exact cycleOn_conj psi3Equiv.symm (f := odometer (m := m)) (g := T3 (m := m)) hsymm
    cycleOn_odometer

end TorusD4
