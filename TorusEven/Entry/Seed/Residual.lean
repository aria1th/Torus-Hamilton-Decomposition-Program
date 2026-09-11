-- STATUS: main-path
import TorusEven.Entry.Seed.Mates
import TorusEven.Collar.TargetPairs

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p)

def nonmates : Finset (Shell.Color p) := Finset.univ \ Finset.univ.map (mate p hp)

def residualNat (hw : Fin 4 × Fin 4) : Finset (Shell.Color p) :=
  (auxiliaryNat p hp hw.1.val hw.2.val).filter
    (fun c => ∀ q : Fin 4, anchorBlockNat q = hw → c ≠ mate p hp q)

theorem mem_nonmates_iff (c : Shell.Color p) : c ∈ nonmates p hp ↔
    if p = 3 then c.val = 4 ∨ c.val = 5 else
    if p % 2 = 0 then (2 ≤ c.val ∧ c.val < p) ∨ p + 2 ≤ c.val else
      c.val = 1 ∨ (3 ≤ c.val ∧ c.val < p) ∨ p + 2 ≤ c.val := by
  have hc := c.isLt
  by_cases h3 : p = 3 <;> by_cases he : p % 2 = 0 <;>
    simp [nonmates, mate, mateIndex, Fin.ext_iff, Fin.forall_fin_succ, h3, he] <;> omega

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

theorem matched_nonmates : (matched p hp hm heven).nonmates = nonmates p hp := rfl

theorem residualNat_subset (hw : Fin 4 × Fin 4) :
    residualNat p hp hw ⊆ (matched p hp hm heven).residual (blockRanks hm hw) := by
  intro c hc
  obtain ⟨ha, hd⟩ := Finset.mem_filter.mp hc
  have ha' : c ∈ auxiliary p hp (blockRanks hm hw) := by
    rwa [auxiliary_at_ranks p hp hm]
  cases h : (matched p hp hm heven).query (blockRanks hm hw) with
  | none => simpa only [MatchedData.residual, h] using ha'
  | some q =>
    have hb := ((matched p hp hm heven).query_some _ q).mp h
    change blockRanks hm (anchorBlockNat q) = blockRanks hm hw at hb
    have hn := hd q ((blockRanks hm).injective hb)
    simpa only [MatchedData.residual, h, Finset.mem_erase] using And.intro hn ha'

noncomputable def residualComponent : Shell.Color p → Component (matched p hp hm heven).residual :=
  componentOf (matched p hp hm heven).residual

theorem residual_same_nat (hw : Fin 4 × Fin 4) {x y : Shell.Color p}
    (hx : x ∈ residualNat p hp hw) (hy : y ∈ residualNat p hp hw) :
    residualComponent p hp hm heven x = residualComponent p hp hm heven y :=
  same_component _ (residualNat_subset p hp hm heven hw hx)
    (residualNat_subset p hp hm heven hw hy)

end TorusEven.Entry.Seed
