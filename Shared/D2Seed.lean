import Shared.TorusCayley
import Shared.RootFlat
import Shared.Monodromy

namespace Shared
namespace D2

abbrev Color := Fin 2
abbrev Direction := Fin 2
abbrev RootState (m : Nat) := ZMod m

def swapColor (c : Color) : Color :=
  if c = 0 then 1 else 0

@[simp] theorem swapColor_zero : swapColor 0 = 1 := by
  simp [swapColor]

@[simp] theorem swapColor_one : swapColor 1 = 0 := by
  simp [swapColor]

theorem swapColor_bijective : Function.Bijective swapColor := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp [swapColor] at h ⊢
  · intro y
    fin_cases y
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

def dir {m : Nat} (t : ZMod m) (c : Color) : Direction :=
  if t = 0 then c else swapColor c

def rootStep {m : Nat} (i : Direction) (a : RootState m) : RootState m :=
  if i = 0 then a + 1 else a

def schedule (m : Nat) : RootFlatSchedule Color Direction (RootState m) m where
  dir := fun t _ c => dir t c
  step := rootStep

theorem rowLatin (m : Nat) : (schedule m).rowLatin := by
  intro t _a
  by_cases ht : t = 0
  · simp [schedule, dir, ht]
  · simpa [schedule, dir, ht] using swapColor_bijective

theorem layerBijective (m : Nat) : (schedule m).layerBijective := by
  intro t c
  change Function.Bijective
    (fun a : ZMod m => rootStep (dir t c) a)
  by_cases hdir : dir t c = 0
  · simpa [rootStep, hdir] using (Equiv.addRight (1 : ZMod m)).bijective
  · simpa [rootStep, hdir] using (Equiv.refl (ZMod m)).bijective

theorem natCast_ne_zero_of_pos_lt {m k : Nat} [NeZero m]
    (hk0 : 0 < k) (hkm : k < m) :
    (k : ZMod m) ≠ 0 := by
  intro h
  have hdvd : m ∣ k := (ZMod.natCast_eq_zero_iff k m).mp h
  exact (not_lt_of_ge (Nat.le_of_dvd hk0 hdvd)) hkm

theorem prefix_color0 {m : Nat} [NeZero m] :
    ∀ k : Nat, k ≤ m → ∀ a : ZMod m,
      (schedule m).prefixMap 0 k a = if k = 0 then a else a + 1 := by
  intro k
  induction k with
  | zero =>
      intro _ a
      simp [RootFlatSchedule.prefixMap]
  | succ k ih =>
      intro hk a
      by_cases hk0 : k = 0
      · subst k
        simp [RootFlatSchedule.prefixMap, schedule, RootFlatSchedule.layerMap,
          dir, rootStep]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkm : k < m := Nat.lt_of_succ_le hk
        have hne : (k : ZMod m) ≠ 0 :=
          natCast_ne_zero_of_pos_lt hkpos hkm
        have hle : k ≤ m := Nat.le_of_lt hkm
        calc
          (schedule m).prefixMap 0 (k + 1) a
              = rootStep (dir (k : ZMod m) 0)
                  ((schedule m).prefixMap 0 k a) := rfl
          _ = rootStep (dir (k : ZMod m) 0) (a + 1) := by
                rw [ih hle a]
                simp [hk0]
          _ = a + 1 := by
                simp [dir, rootStep, hne]

theorem prefix_color1 {m : Nat} [NeZero m] :
    ∀ k : Nat, k ≤ m → ∀ a : ZMod m,
      (schedule m).prefixMap 1 k a = a + ((k - 1 : Nat) : ZMod m) := by
  intro k
  induction k with
  | zero =>
      intro _ a
      simp [RootFlatSchedule.prefixMap]
  | succ k ih =>
      intro hk a
      by_cases hk0 : k = 0
      · subst k
        simp [RootFlatSchedule.prefixMap, schedule, RootFlatSchedule.layerMap,
          dir, rootStep]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkm : k < m := Nat.lt_of_succ_le hk
        have hne : (k : ZMod m) ≠ 0 :=
          natCast_ne_zero_of_pos_lt hkpos hkm
        have hle : k ≤ m := Nat.le_of_lt hkm
        have hsub : k - 1 + 1 = k :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        have hcastNat :
            (((k - 1 + 1 : Nat) : ZMod m)) = (k : ZMod m) := by
          rw [hsub]
        have hcast :
            (((k - 1 : Nat) : ZMod m) + 1) = (k : ZMod m) := by
          simpa [Nat.cast_add, Nat.cast_one] using hcastNat
        calc
          (schedule m).prefixMap 1 (k + 1) a
              = (a + ((k - 1 : Nat) : ZMod m)) + 1 := by
                calc
                  (schedule m).prefixMap 1 (k + 1) a =
                      rootStep (dir (k : ZMod m) 1)
                        ((schedule m).prefixMap 1 k a) := rfl
                  _ = rootStep (dir (k : ZMod m) 1)
                        (a + ((k - 1 : Nat) : ZMod m)) := by
                          rw [ih hle a]
                  _ = (a + ((k - 1 : Nat) : ZMod m)) + 1 := by
                          simp [dir, rootStep, hne]
          _ = a + ((k : Nat) : ZMod m) := by
                calc
                  (a + ((k - 1 : Nat) : ZMod m)) + 1 =
                      a + (((k - 1 : Nat) : ZMod m) + 1) := by ring
                  _ = a + ((k : Nat) : ZMod m) := by rw [hcast]
          _ = a + (((k + 1) - 1 : Nat) : ZMod m) := by
                simp

theorem returnMap_color0 {m : Nat} [NeZero m] :
    (schedule m).returnMap 0 = fun a : ZMod m => a + 1 := by
  funext a
  rw [RootFlatSchedule.returnMap_eq_prefixMap]
  have hm : m ≠ 0 := NeZero.ne m
  simpa [hm] using prefix_color0 (m := m) m le_rfl a

theorem returnMap_color1 {m : Nat} [NeZero m] :
    (schedule m).returnMap 1 =
      fun a : ZMod m => a + ((m - 1 : Nat) : ZMod m) := by
  funext a
  rw [RootFlatSchedule.returnMap_eq_prefixMap]
  simpa using prefix_color1 (m := m) m le_rfl a

theorem coprime_m_sub_one (m : Nat) [NeZero m] :
    Nat.Coprime (m - 1) m := by
  have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne m))
  exact (Nat.coprime_self_sub_left hm1).2 (by simp)

theorem returnsSingleCycle {m : Nat} [NeZero m] :
    (schedule m).returnsSingleCycle := by
  intro c
  fin_cases c
  · simpa [returnMap_color0] using zmod_add_single_cycle_of_coprime
      (m := m) (a := 1) (by simp : Nat.Coprime 1 m)
  · simpa [returnMap_color1] using zmod_add_single_cycle_of_coprime
      (m := m) (a := m - 1) (coprime_m_sub_one m)

def layerRootEquiv (m : Nat) :
    ZMod m × RootState m ≃ TorusVertex 2 m where
  toFun tw := fun i => if i = 0 then tw.2 else tw.1 - tw.2
  invFun x := (x 0 + x 1, x 0)
  left_inv := by
    intro tw
    rcases tw with ⟨t, a⟩
    ext <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp

def colorDir {m : Nat} (c : TorusColor 2) (x : TorusVertex 2 m) :
    TorusDirection 2 :=
  dir ((layerRootEquiv m).symm x).1 c

theorem colorStep_layerRootEquiv {m : Nat}
    (c : TorusColor 2) (tw : ZMod m × RootState m) :
    cayleyColorStep colorDir c (layerRootEquiv m tw) =
      layerRootEquiv m ((schedule m).fullStep c tw) := by
  rcases tw with ⟨t, a⟩
  by_cases hdir : dir t c = 0
  · ext i
    fin_cases i <;>
      simp [cayleyColorStep, colorDir, layerRootEquiv, torusBasis,
        RootFlatSchedule.fullStep, RootFlatSchedule.layerMap,
        schedule, rootStep, hdir]
  · have hdir1 : dir t c = 1 := by
      apply Fin.ext
      have hval_ne : (dir t c).val ≠ 0 := by
        intro hval
        apply hdir
        exact Fin.ext hval
      have hval_lt : (dir t c).val < 2 := (dir t c).isLt
      have hval_eq : (dir t c).val = 1 := by omega
      simpa using hval_eq
    ext i
    fin_cases i
    · simp [cayleyColorStep, colorDir, layerRootEquiv, torusBasis,
        RootFlatSchedule.fullStep, RootFlatSchedule.layerMap,
        schedule, rootStep, hdir1]
    · simp [cayleyColorStep, colorDir, layerRootEquiv, torusBasis,
        RootFlatSchedule.fullStep, RootFlatSchedule.layerMap,
        schedule, rootStep, hdir1]
      ring

theorem edgePartition (m : Nat) :
    IsCayleyEdgePartition (colorDir (m := m)) := by
  intro x i
  let t : ZMod m := ((layerRootEquiv m).symm x).1
  have hrow : Function.Bijective fun c : Color => dir t c := by
    simpa [schedule, RootFlatSchedule.rowLatin] using
      rowLatin m t (((layerRootEquiv m).symm x).2)
  rcases hrow.2 i with ⟨c, hc⟩
  refine ⟨c, by simpa [colorDir, t] using hc, ?_⟩
  intro c' hc'
  apply hrow.1
  have hc'' : dir t c' = i := by
    simpa [colorDir, t] using hc'
  exact hc''.trans hc.symm

theorem colorHamiltonian {m : Nat} [NeZero m] :
    IsCayleyColorHamiltonian (colorDir (m := m)) := by
  intro c
  have hRoot : IsSingleCycleMap ((schedule m).fullStep c) :=
    RootFlatSchedule.fullStep_singleCycle_of_return
      (schedule m) (layerBijective m) (returnsSingleCycle c)
  refine single_cycle_of_equiv_conj
    (e := layerRootEquiv m)
    (f := cayleyColorStep colorDir c)
    (g := (schedule m).fullStep c)
    hRoot ?_
  intro tw
  simpa using congrArg (layerRootEquiv m).symm
    (colorStep_layerRootEquiv (m := m) c tw)

theorem cayleyHamiltonDecomposition {m : Nat} [NeZero m] :
    CayleyHamiltonDecomposition 2 m := by
  exact ⟨{
    colorDir := colorDir
    edgePartition := edgePartition m
    colorHamiltonian := colorHamiltonian
  }⟩

theorem shared_cayley_uniform :
    ∀ {m : Nat}, 3 ≤ m → Odd m → CayleyHamiltonDecomposition 2 m := by
  intro m hm _hodd
  haveI : NeZero m := ⟨by omega⟩
  exact cayleyHamiltonDecomposition

end D2
end Shared
