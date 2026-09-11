-- STATUS: main-path
import TorusEven.Entry.Seed.NumericRows
import TorusEven.Collar.MatchedSelection

namespace TorusEven.Entry.Seed

open Collar Incidence

def coreIndex (c : Fin 3) (d : ZMod 2) : Fin 4 :=
  if c = 0 then 0 else if c = 1 then 1 else if d = 0 then 2 else 3

def activeAt {m : ℕ} (heven : Even m) (hw : ZMod m × ZMod m) : Fin 4 :=
  coreIndex ((nearRow hw.1 hw.2).symm 0) (NearCore.baseDefect heven hw)

theorem corePresent_iff_activeAt {m : ℕ} (heven : Even m) (hw : ZMod m × ZMod m)
    (q : Fin 4) : corePresent heven 0 hw q ↔ q = activeAt heven hw := by
  simp only [corePresent, Equiv.apply_eq_iff_eq_symm_apply, activeAt]
  exact (by decide : ∀ (c : Fin 3) (d : ZMod 2) (q : Fin 4),
    (anchorColor q = c ∧ (q = 2 → d = 0) ∧ (q = 3 → d = 1)) ↔ q = coreIndex c d) _ _ _

def anchorBlockNat : Fin 4 → Fin 4 × Fin 4 := ![(1, 0), (2, 0), (0, 0), (1, 3)]

def anchorRowNat : Fin 4 → Fin 4 := ![0, 1, 0, 0]

variable {m : ℕ} (hm : 4 ≤ m)

def blockRanks : Fin 4 × Fin 4 ↪ ZMod m × ZMod m where
  toFun hw := (fourRanks hm 0 hw.1, fourRanks hm 0 hw.2)
  inj' _ _ h := Prod.ext ((fourRanks hm 0).injective (congrArg Prod.fst h))
    ((fourRanks hm 0).injective (congrArg Prod.snd h))

def anchorBlock : Fin 4 ↪ ZMod m × ZMod m :=
  (⟨anchorBlockNat, by decide⟩ : Fin 4 ↪ Fin 4 × Fin 4).trans (blockRanks hm)

def anchorRow (q : Fin 4) : ZMod m := fourRanks hm 0 (anchorRowNat q)

@[simp] theorem blockRanks_apply (hw : Fin 4 × Fin 4) :
    blockRanks hm hw = ((hw.1.val : ZMod m), (hw.2.val : ZMod m)) := by
  simp [blockRanks, fourRanks]

theorem anchor_coordinates (q : Fin 4) : xChart (anchorBlock hm q, anchorRow hm q) = anchor q := by
  fin_cases q <;> ext j <;> fin_cases j <;>
    simp [xChart, anchorBlock, anchorBlockNat, anchorRow, anchorRowNat, anchor, fourRanks] <;> ring

variable [NeZero m] (heven : Even m)
include hm

theorem activeAt_anchor (q : Fin 4) : activeAt heven (anchorBlock hm q) = q := by
  apply (corePresent_iff_activeAt heven _ q).mp ?_ |>.symm
  change corePresent heven 0 (blockRanks hm (anchorBlockNat q)) q
  rw [blockRanks_apply]
  rw [corePresent_eq_nat hm heven, ZMod.val_natCast_of_lt
    ((anchorBlockNat q).1.isLt.trans_le hm), ZMod.val_natCast_of_lt
    ((anchorBlockNat q).2.isLt.trans_le hm)]
  fin_cases q <;> decide

end TorusEven.Entry.Seed
