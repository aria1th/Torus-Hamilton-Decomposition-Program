-- STATUS: main-path
import TorusEven.Entry.Seed.MatchAnchors

namespace TorusEven.Entry.Seed

open Collar Incidence

def mateIndex (p : ℕ) : Fin 4 → ℕ :=
  if p = 3 then ![1, p, 0, 2] else ![p, p + 1, 0, if p % 2 = 0 then 1 else 2]

variable (p : ℕ) (hp : 2 ≤ p)

def mate : Fin 4 ↪ Shell.Color p where
  toFun q := ⟨mateIndex p q, by
    by_cases h3 : p = 3 <;> by_cases he : p % 2 = 0 <;>
      fin_cases q <;> simp_all [mateIndex] <;> omega⟩
  inj' q r h := by
    have hv := congrArg Fin.val h
    change mateIndex p q = mateIndex p r at hv
    by_cases h3 : p = 3 <;> by_cases he : p % 2 = 0 <;>
      fin_cases q <;> fin_cases r <;> simp [mateIndex, h3, he] at hv ⊢ <;> omega

def auxiliaryNat (h w : ℕ) : Finset (Shell.Color p) :=
  Shell.aUsers p h \ Shell.selectedNat p hp h w

theorem mem_auxiliaryNat (h w : ℕ) (c : Shell.Color p) :
    c ∈ auxiliaryNat p hp h w ↔ Shell.directionNat p hp h w c = 0 := by
  by_cases ha : c ∈ Shell.aUsers p h <;> by_cases hs : c ∈ Shell.selectedNat p hp h w <;>
    simp [auxiliaryNat, Shell.directionNat, ha, hs]

theorem mate_eligible_nat (q : Fin 4) :
    mate p hp q ∈ auxiliaryNat p hp (anchorBlockNat q).1.val (anchorBlockNat q).2.val := by
  rw [auxiliaryNat, Finset.mem_sdiff, Shell.mem_aUsers, Shell.mem_selectedNat]
  change Shell.aUser p (anchorBlockNat q).1.val (mateIndex p q) ∧ _
  constructor
  · by_cases h3 : p = 3 <;> by_cases he : p % 2 = 0 <;>
      fin_cases q <;> simp [anchorBlockNat, mateIndex, Shell.aUser, h3, he] <;> omega
  · rintro (⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩)
    · change Shell.fillerIndex p (anchorBlockNat q).1.val i = mateIndex p q at hi'
      by_cases h3 : p = 3 <;> by_cases he : p % 2 = 0 <;>
        fin_cases q <;> simp [anchorBlockNat, mateIndex, Shell.pairCount,
          Shell.fillerIndex, h3, he] at hi hi'
      all_goals omega
    · change Shell.endpointIndex p (anchorBlockNat q).1.val i
        (if (anchorBlockNat q).2.val = (if i = 1 then 1 else 0) then true else false) =
          mateIndex p q at hi'
      by_cases h3 : p = 3
      all_goals by_cases he : p % 2 = 0 <;>
        by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        fin_cases q <;> simp [anchorBlockNat, mateIndex, Shell.pairCount,
          Shell.endpointIndex, h3, he, hi0, hi1] at hi hi' <;> omega

variable {m : ℕ} (hm : 4 ≤ m) [NeZero m] (heven : Even m)

def auxiliary (hw : ZMod m × ZMod m) : Finset (Shell.Color p) :=
  Finset.univ.filter (fun c => Shell.direction p hp hw.1 hw.2 c = 0)

theorem auxiliary_at_ranks (hw : Fin 4 × Fin 4) :
    auxiliary p hp (blockRanks hm hw) = auxiliaryNat p hp hw.1.val hw.2.val := by
  ext c
  simp only [auxiliary, Finset.mem_filter, Finset.mem_univ, true_and, blockRanks_apply,
    Shell.direction_eq_nat hm, ZMod.val_natCast_of_lt (hw.1.isLt.trans_le hm),
    ZMod.val_natCast_of_lt (hw.2.isLt.trans_le hm), mem_auxiliaryNat]

def matched : MatchedData (Q := Fin 4) (auxiliary (m := m) p hp) m where
  active := activeAt heven
  anchor := anchorBlock hm
  mate := mate p hp
  event := anchorRow hm
  active_anchor := activeAt_anchor hm heven
  eligible q := by
    change mate p hp q ∈ auxiliary p hp (blockRanks hm (anchorBlockNat q))
    rw [auxiliary_at_ranks p hp hm]
    exact mate_eligible_nat p hp q

theorem matched_fullSupport (hw : ZMod m × ZMod m) :
    (matched p hp hm heven).fullSupport hw = support p hp heven 0 hw := by
  ext q
  cases q with
  | inl q => simp [MatchedData.fullSupport, matched, mem_support_left, corePresent_iff_activeAt]
  | inr c => simp [MatchedData.fullSupport, matched, auxiliary]

end TorusEven.Entry.Seed
