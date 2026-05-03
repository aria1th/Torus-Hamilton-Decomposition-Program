import Shared.TorusCayley
import TorusD3Odd

namespace Shared
namespace D3

open TorusD3Odd

noncomputable def cycleCoordinateOfCycleOn {N : Nat} [NeZero N]
    (hN1 : 1 < N) {α : Type*} {f : α → α} {x : α}
    (hc : TorusD4.CycleOn N f x) :
    CycleCoordinate N f := by
  let e : Fin N ≃ α :=
    Equiv.ofBijective (fun i : Fin N => (f^[i.val]) x) hc.1
  refine CycleCoordinate.ofFinEquiv e ?_
  intro i
  dsimp [e]
  by_cases hlt : i.val + 1 < N
  · have hval : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, Fin.val_one']
      have h1mod : 1 % N = 1 := Nat.mod_eq_of_lt hN1
      simp [h1mod, Nat.mod_eq_of_lt hlt]
    rw [hval]
    rw [show i.val + 1 = Nat.succ i.val by omega]
    rw [Function.iterate_succ_apply']
  · have hN : i.val + 1 = N := by omega
    have hval0 : (i + 1).val = 0 := by
      rw [Fin.val_add, Fin.val_one']
      have h1mod : 1 % N = 1 := Nat.mod_eq_of_lt hN1
      rw [h1mod, hN]
      exact Nat.mod_self N
    rw [hval0]
    have hi : i.val = N - 1 := by omega
    rw [hi]
    have hsucc : N - 1 + 1 = N :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
    calc
      (f^[0]) x = x := by simp
      _ = (f^[N]) x := by rw [hc.2]
      _ = f ((f^[N - 1]) x) := by
            simpa [Nat.succ_eq_add_one, hsucc] using
              (Function.iterate_succ_apply' f (N - 1) x)

theorem singleCycleOfCycleOn {N : Nat} [NeZero N]
    (hN1 : 1 < N) {α : Type*} {f : α → α} {x : α}
    (hc : TorusD4.CycleOn N f x) :
    IsSingleCycleMap f :=
  (cycleCoordinateOfCycleOn hN1 hc).singleCycle

def perm120 : Equiv.Perm (Fin 3) where
  toFun c := if c = 0 then 1 else if c = 1 then 2 else 0
  invFun c := if c = 0 then 2 else if c = 1 then 0 else 1
  left_inv := by
    intro c
    fin_cases c <;> simp
  right_inv := by
    intro c
    fin_cases c <;> simp

def colorPerm {m : Nat} (x : TorusVertex 3 m) : Equiv.Perm (Fin 3) :=
  if S x = 0 then
    if kCoord x = 0 then
      Equiv.swap 1 2
    else
      perm120
  else if S x = 1 then
    if kCoord x = 0 then
      perm120.symm
    else
      Equiv.swap 0 2
  else
    Equiv.refl _

def colorDir {m : Nat}
    (c : TorusColor 3) (x : TorusVertex 3 m) : TorusDirection 3 :=
  colorPerm x c

theorem colorDir_bijective {m : Nat} (x : TorusVertex 3 m) :
    Function.Bijective (fun c : TorusColor 3 => colorDir c x) :=
  (colorPerm x).bijective

theorem edgePartition (m : Nat) :
    IsCayleyEdgePartition (colorDir (m := m)) := by
  intro x i
  have hrow : Function.Bijective fun c : TorusColor 3 => colorDir c x :=
    colorDir_bijective x
  rcases hrow.2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact hrow.1 (hc'.trans hc.symm)

theorem bump_eq_add_torusBasis {m : Nat}
    (x : TorusVertex 3 m) (d : TorusDirection 3) :
    bump x d = x + torusBasis 3 m d := by
  ext i
  simp [bump, torusBasis]

theorem colorMap_eq_cayleyColorStep {m : Nat} [Fact (2 < m)]
    (c : TorusColor 3) (x : TorusVertex 3 m) :
    colorMap c x = cayleyColorStep (colorDir (m := m)) c x := by
  fin_cases c
  · by_cases h0 : S x = 0
    · by_cases hk : kCoord x = 0
      · simpa [colorMap, f0, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (0 : TorusDirection 3)
      · simpa [colorMap, f0, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (1 : TorusDirection 3)
    · by_cases h1 : S x = 1
      · by_cases hk : kCoord x = 0
        · simpa [colorMap, f0, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (2 : TorusDirection 3)
        · simpa [colorMap, f0, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (2 : TorusDirection 3)
      · simpa [colorMap, f0, colorDir, colorPerm, h0, h1, cayleyColorStep] using
          bump_eq_add_torusBasis x (0 : TorusDirection 3)
  · by_cases h0 : S x = 0
    · by_cases hk : kCoord x = 0
      · simpa [colorMap, f1, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (2 : TorusDirection 3)
      · simpa [colorMap, f1, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (2 : TorusDirection 3)
    · by_cases h1 : S x = 1
      · by_cases hk : kCoord x = 0
        · simpa [colorMap, f1, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (0 : TorusDirection 3)
        · simpa [colorMap, f1, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (1 : TorusDirection 3)
      · simpa [colorMap, f1, colorDir, colorPerm, h0, h1, cayleyColorStep] using
          bump_eq_add_torusBasis x (1 : TorusDirection 3)
  · by_cases h0 : S x = 0
    · by_cases hk : kCoord x = 0
      · simpa [colorMap, f2, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (1 : TorusDirection 3)
      · simpa [colorMap, f2, colorDir, colorPerm, h0, hk, cayleyColorStep] using
          bump_eq_add_torusBasis x (0 : TorusDirection 3)
    · by_cases h1 : S x = 1
      · by_cases hk : kCoord x = 0
        · simpa [colorMap, f2, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (1 : TorusDirection 3)
        · simpa [colorMap, f2, colorDir, colorPerm, h0, h1, hk, cayleyColorStep,
            one_ne_zero (m := m)] using
            bump_eq_add_torusBasis x (0 : TorusDirection 3)
      · simpa [colorMap, f2, colorDir, colorPerm, h0, h1, cayleyColorStep] using
          bump_eq_add_torusBasis x (2 : TorusDirection 3)

theorem colorHamiltonian {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 ≤ m) :
    IsCayleyColorHamiltonian (colorDir (m := m)) := by
  intro c
  letI : Fact (Odd m) := ⟨hodd⟩
  letI : Fact (2 < m) := ⟨by omega⟩
  letI : NeZero (m ^ 3) := ⟨by
    exact ne_of_gt (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) 3)⟩
  rcases hasCycle_colorMap (m := m) c with ⟨x, hx⟩
  have hN1 : 1 < m ^ 3 := by
    have hm1 : 1 < m := by omega
    exact one_lt_pow₀ hm1 (by decide : 3 ≠ 0)
  have hcycle : IsSingleCycleMap (colorMap (m := m) c) :=
    singleCycleOfCycleOn hN1 hx
  have hfun :
      colorMap (m := m) c = cayleyColorStep (colorDir (m := m)) c := by
    funext x
    exact colorMap_eq_cayleyColorStep c x
  simpa [hfun] using hcycle

theorem cayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 ≤ m) :
    CayleyHamiltonDecomposition 3 m := by
  exact ⟨{
    colorDir := colorDir
    edgePartition := edgePartition m
    colorHamiltonian := colorHamiltonian hodd hm3
  }⟩

theorem shared_cayley_uniform :
    ∀ {m : Nat}, 3 ≤ m → Odd m → CayleyHamiltonDecomposition 3 m := by
  intro m hm3 hodd
  haveI : NeZero m := ⟨by omega⟩
  exact cayleyHamiltonDecomposition hodd hm3

end D3
end Shared
