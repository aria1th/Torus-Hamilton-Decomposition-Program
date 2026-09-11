-- STATUS: main-path
import TorusEven.Entry.Rows
import TorusEven.Collar.Lift

namespace TorusEven.Entry.NearCore

open Collar

variable {m : ℕ}

def chart : ((ZMod m × ZMod m) × ZMod m) ≃ Point m where
  toFun p := ![p.1.1 - p.1.2 - p.2, p.2, p.1.2]
  invFun v := ((height v, v 2), v 1)
  left_inv p := by
    rcases p with ⟨⟨h, w⟩, y⟩
    dsimp [height]
    congr 2
    ring
  right_inv v := by
    funext j
    fin_cases j <;> simp [height]

@[simp] theorem height_chart (p : (ZMod m × ZMod m) × ZMod m) :
    height (chart p) = p.1.1 := by simp [height, chart]

def wVoltage (c : Fin 3) (h : ZMod m) : ZMod m :=
  if h = 0 then (if c = 0 then 1 else 0) else
  if h = 1 then (if c = 1 then 1 else 0) else (if c = 2 then 1 else 0)

def yVoltage (c : Fin 3) (p : ZMod m × ZMod m) : ZMod m :=
  if nearRow p.1 p.2 c = 1 then 1 else 0

theorem wVoltage_eq (c : Fin 3) (h w : ZMod m) :
    wVoltage c h = if nearRow h w c = 2 then 1 else 0 := by
  by_cases h0 : h = 0
  · simp only [wVoltage, nearRow, if_pos h0]
    fin_cases c <;> simp [Equiv.swap_apply_def]
  · simp only [wVoltage, nearRow, if_neg h0]
    by_cases h1 : h = 1
    · simp only [if_pos h1]
      by_cases hw : w = 0 ∨ w = 1
      · simp only [if_pos hw]
        fin_cases c <;> simp [Equiv.swap_apply_def]
      · simp only [if_neg hw]
        fin_cases c <;> simp [rotate]
    · simp only [if_neg h1]
      by_cases hw : h = 2 ∧ w = 0
      · simp only [if_pos hw]
        fin_cases c <;> simp [Equiv.swap_apply_def]
      · simp only [if_neg hw]
        fin_cases c <;> simp

def baseStep (c : Fin 3) : Equiv.Perm (ZMod m × ZMod m) :=
  lift (Equiv.addRight 1) (wVoltage c)

def step (c : Fin 3) : Equiv.Perm (Point m) :=
  chart.symm.trans ((lift (baseStep c) (yVoltage c)).trans chart)

@[simp] theorem step_chart (c : Fin 3) (p : (ZMod m × ZMod m) × ZMod m) :
    step c (chart p) = chart (lift (baseStep c) (yVoltage c) p) := by simp [step]

theorem step_eq (c : Fin 3) (v : Point m) (j : Fin 3) :
    step c v j = v j + if j = nearRow (height v) (v 2) c then 1 else 0 := by
  obtain ⟨⟨⟨h, w⟩, y⟩, rfl⟩ := chart.surjective v
  rw [step_chart, height_chart]
  change chart (lift (baseStep c) (yVoltage c) ((h, w), y)) j =
    chart ((h, w), y) j + if j = nearRow h w c then 1 else 0
  change chart ((h + 1, w + wVoltage c h), y + yVoltage c (h, w)) j =
    chart ((h, w), y) j + if j = nearRow h w c then 1 else 0
  rw [wVoltage_eq c h w, yVoltage]
  generalize nearRow h w c = k
  fin_cases j <;> fin_cases k <;> simp [chart] <;> ring

def factorization : MultitorusFactorization (Fin 3) (Fin 3) m where
  width _ := 1
  width_pos _ := by decide
  direction c v := nearRow (height v) (v 2) c
  step := step
  step_eq := step_eq
  quota v i := by
    apply Finset.card_eq_one.mpr
    refine ⟨(nearRow (height v) (v 2)).symm i, ?_⟩
    ext c
    simp [Equiv.apply_eq_iff_eq_symm_apply]

end TorusEven.Entry.NearCore
