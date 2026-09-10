-- STATUS: main-path (the degree-five schedule of the manuscript, m ≥ 6: definitions and Latin rows)
import TorusEven.D5.Chart

/-!
# The degree-five schedule (`m ≥ 6`)

Root coordinates `x : Fin 4 → ZMod m`, height `t : ZMod m`, directions `Fin 5`
(`u_j = e_j` for `j < 4`, `u_4 = 0` on the root).  The neutral direction of colour `c` at
height `t` is `c + t` for `t ≤ 4` and `c` afterwards.  Five cylinder modifications
(Table `tab:d5-cylinders`) and the terminal planar rule (Table `tab:d5-omega`) are applied as
direction permutations on the indicated sources.  Every row is a permutation composed with
the neutral row, so the Latin condition is immediate.
-/

namespace TorusEven
namespace D5

open Chart

abbrev Root (m : ℕ) := Chart.Root 4 m

variable {m : ℕ}

/-! ### Direction permutations -/

/-- The cycle `(0 2 1)`: `0 ↦ 2 ↦ 1 ↦ 0`. -/
def cyc021 : Equiv.Perm (Fin 5) := ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide, by decide⟩
/-- The transposition `(3 4)`. -/
def swap34 : Equiv.Perm (Fin 5) := ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide, by decide⟩
/-- The cycle `(1 0 4)`: `1 ↦ 0 ↦ 4 ↦ 1`. -/
def cyc104 : Equiv.Perm (Fin 5) := ⟨![4, 0, 2, 3, 1], ![1, 4, 2, 3, 0], by decide, by decide⟩
/-- The transposition `(2 3)`. -/
def swap23 : Equiv.Perm (Fin 5) := ⟨![0, 1, 3, 2, 4], ![0, 1, 3, 2, 4], by decide, by decide⟩
/-- The transposition `(2 4)`. -/
def swap24 : Equiv.Perm (Fin 5) := ⟨![0, 1, 4, 3, 2], ![0, 1, 4, 3, 2], by decide, by decide⟩

/-- Row permutations of the terminal plane, as permutations of `Fin 3`. -/
def p012 : Equiv.Perm (Fin 3) := 1
def p021 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def p102 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def p120 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def p201 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def p210 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The terminal planar rule `ω_m(q)` (Table `tab:d5-omega`), for `q = (a, b)` in `ZMod m`.
Index ranges are expressed by exclusion of the small residues, which agrees with the
manuscript for `m ≥ 6`. -/
def omega (q : ZMod m × ZMod m) : Equiv.Perm (Fin 3) :=
  let a := q.1
  let b := q.2
  if a = 1 ∧ b = 0 then p021
  else if a = 3 ∧ b = 0 then p102
  else if a = 1 ∧ b = 1 then p120
  else if a = 2 ∧ b = 1 then p201
  else if a = 0 ∧ b = 2 then p201
  else if a = 2 ∧ b = 2 then p120
  else if a = 0 ∧ b = 3 then p120
  else if a = 1 ∧ b = 3 then p201
  else if b = 2 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 2 then p210
  else if a = 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 2 ∧ b ≠ 3 then p021
  else if a + b = 3 ∧ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 2 ∧ b ≠ 3 then p102
  else p012

/-- The three terminal directions `(d_0, d_1, d_2) = (3, 0, 1)`. -/
def dirs : Fin 3 → Fin 5 := ![3, 0, 1]

/-- `ω` acting on the direction symbols `3, 0, 1`, fixing `2, 4`. -/
def tauFun (ω : Equiv.Perm (Fin 3)) (d : Fin 5) : Fin 5 :=
  if d = 3 then dirs (ω 0) else if d = 0 then dirs (ω 1) else if d = 1 then dirs (ω 2) else d

theorem tauFun_left : ∀ ω : Equiv.Perm (Fin 3), ∀ d, tauFun ω.symm (tauFun ω d) = d := by
  decide

theorem tauFun_right : ∀ ω : Equiv.Perm (Fin 3), ∀ d, tauFun ω (tauFun ω.symm d) = d := by
  decide

def tau (ω : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 5) :=
  ⟨tauFun ω, tauFun ω.symm, tauFun_left ω, tauFun_right ω⟩

/-! ### Cylinders -/

def sum4 (x : Root m) : ZMod m := x 0 + x 1 + x 2 + x 3

/-- `P_0`: `x_0 + x_1 + x_2 + x_3 = 0`. -/
def mask0 (x : Root m) : Prop := sum4 x = 0
/-- `P_1`: `x_2 = 1`. -/
def mask1 (x : Root m) : Prop := x 2 = 1
/-- `P_2`: `x_2 = x_3 = 0`. -/
def mask2 (x : Root m) : Prop := x 2 = 0 ∧ x 3 = 0
/-- `P_3`: `x_1 = 0` and `x_0 + x_2 + x_3 = -1`. -/
def mask3 (x : Root m) : Prop := x 1 = 0 ∧ sum4 x = -1
/-- `P_4`: `x_0 = x_1 = x_3 = 0`. -/
def mask4 (x : Root m) : Prop := x 0 = 0 ∧ x 1 = 0 ∧ x 3 = 0
/-- The terminal plane `Θ = {x_2 = 0, x_0 + x_1 + x_3 = 0}`. -/
def plane (x : Root m) : Prop := x 2 = 0 ∧ x 0 + x 1 + x 3 = 0

instance : DecidablePred (mask0 (m := m)) := fun _ => by unfold mask0; infer_instance
instance : DecidablePred (mask1 (m := m)) := fun _ => by unfold mask1; infer_instance
instance : DecidablePred (mask2 (m := m)) := fun _ => by unfold mask2; infer_instance
instance : DecidablePred (mask3 (m := m)) := fun _ => by unfold mask3; infer_instance
instance : DecidablePred (mask4 (m := m)) := fun _ => by unfold mask4; infer_instance
instance : DecidablePred (plane (m := m)) := fun _ => by unfold plane; infer_instance

/-- The point `q = (x_3, x_0)` of the terminal plane chart `φ(a, b) = (b, -a-b, 0, a)`. -/
def planePoint (x : Root m) : ZMod m × ZMod m := (x 3, x 0)

/-! ### Rows -/

/-- Neutral row at height `t`: `c ↦ c + t` for `t ≤ 4`, identity afterwards. -/
def rhoPerm (t : ZMod m) : Equiv.Perm (Fin 5) :=
  if t.val ≤ 4 then Equiv.addRight (⟨t.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) else 1

/-- The modification permutation at height `t` and source `x`. -/
def rowPerm (t : ZMod m) (x : Root m) : Equiv.Perm (Fin 5) :=
  if t.val = 0 then (if mask1 x then swap34 else 1) * (if mask0 x then cyc021 else 1)
  else if t.val = 1 then (if mask3 x then swap23 else 1) * (if mask2 x then cyc104 else 1)
  else if t.val = 2 then
    (if plane x then tau (omega (planePoint x)) else 1) * (if mask4 x then swap24 else 1)
  else 1

/-- The complete direction rule. -/
def dir (t : ZMod m) (x : Root m) (c : Fin 5) : Fin 5 := rowPerm t x (rhoPerm t c)

/-- The schedule as a root-flat schedule. -/
def schedule (m : ℕ) : Shared.RootFlatSchedule (Fin 5) (Fin 5) (Root m) m where
  dir := dir
  step := rootStep 4 m

theorem schedule_step : (schedule m).step = rootStep 4 m := rfl

theorem rowLatin : (schedule m).rowLatin := by
  intro t x
  exact (rowPerm t x).bijective.comp (rhoPerm t).bijective

end D5
end TorusEven
