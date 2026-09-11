-- STATUS: main-path
import TorusEven.Entry.Shell.Rows
import TorusEven.Entry.NearCore

namespace TorusEven.Entry.Shell

open Collar

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ}

def baseStep (c : Color p) : Equiv.Perm (ZMod m × ZMod m) :=
  lift (Equiv.addRight 1) (wVoltage p c)

def step (c : Color p) : Equiv.Perm (Point m) :=
  NearCore.chart.symm.trans ((lift (baseStep p c) (yVoltage p hp c)).trans NearCore.chart)

@[simp] theorem step_chart (c : Color p) (q : (ZMod m × ZMod m) × ZMod m) :
    step p hp c (NearCore.chart q) = NearCore.chart (lift (baseStep p c) (yVoltage p hp c) q) := by
  simp [step]

theorem step_eq (c : Color p) (v : Point m) (j : Fin 3) :
    step p hp c v j = v j + if j = direction p hp (height v) (v 2) c then 1 else 0 := by
  obtain ⟨⟨⟨h, w⟩, y⟩, rfl⟩ := NearCore.chart.surjective v
  rw [step_chart, NearCore.height_chart]
  change NearCore.chart ((h + 1, w + wVoltage p c h), y + yVoltage p hp c (h, w)) j =
    NearCore.chart ((h, w), y) j + if j = direction p hp h w c then 1 else 0
  rw [wVoltage_eq p hp c h w, yVoltage_eq p hp c h w]
  generalize direction p hp h w c = k
  fin_cases j <;> fin_cases k <;> simp [NearCore.chart] <;> ring

def factorization : MultitorusFactorization (Color p) (Fin 3) m where
  width := ![p - p / 2, p / 2, p]
  width_pos j := by fin_cases j <;> simp <;> omega
  direction c v := direction p hp (height v) (v 2) c
  step := step p hp
  step_eq := step_eq p hp
  quota v j := quota p hp (height v) (v 2) j

end TorusEven.Entry.Shell
