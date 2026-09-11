-- STATUS: main-path
import TorusEven.Entry.Shell.Pairs
import TorusEven.Entry.Rows

namespace TorusEven.Entry.Shell

open Collar

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ}

def event {n : ℕ} (j : Fin n) : ZMod m := if j.val = 1 then 1 else 0

def selected (h w : ZMod m) : Finset (Color p) :=
  (pairs p hp h.val).row event (fillers p hp h.val) false w

theorem selected_subset (h w : ZMod m) : selected p hp h w ⊆ aUsers p h.val :=
  (pairs p hp h.val).row_subset event _ (fillers_subset p hp h.val) false w

theorem card_selected (h w : ZMod m) : (selected p hp h w).card = p / 2 := by
  rw [selected, LocalPairs.card_row _ _ _ (fillers_disjoint p hp h.val)]
  exact card_fillers_add_pairs p hp h.val

def direction (h w : ZMod m) (c : Color p) : Fin 3 :=
  if c ∈ aUsers p h.val then (if c ∈ selected p hp h w then 1 else 0) else 2

theorem direction_zero (h w : ZMod m) :
    Finset.univ.filter (fun c => direction p hp h w c = 0) =
      aUsers p h.val \ selected p hp h w := by
  ext c
  by_cases ha : c ∈ aUsers p h.val <;> by_cases hs : c ∈ selected p hp h w <;>
    simp [direction, ha, hs]

theorem direction_one (h w : ZMod m) :
    Finset.univ.filter (fun c => direction p hp h w c = 1) = selected p hp h w := by
  ext c
  have hc := selected_subset p hp h w (a := c)
  by_cases ha : c ∈ aUsers p h.val <;> by_cases hs : c ∈ selected p hp h w <;>
    simp_all [direction]

theorem direction_two (h w : ZMod m) :
    Finset.univ.filter (fun c => direction p hp h w c = 2) =
      Finset.univ \ aUsers p h.val := by
  ext c
  by_cases ha : c ∈ aUsers p h.val <;> by_cases hs : c ∈ selected p hp h w <;>
    simp [direction, ha, hs]

theorem quota (h w : ZMod m) (j : Fin 3) :
    (Finset.univ.filter (fun c => direction p hp h w c = j)).card = ![p - p / 2, p / 2, p] j := by
  fin_cases j
  · change (Finset.univ.filter (fun c => direction p hp h w c = (0 : Fin 3))).card = p - p / 2
    rw [direction_zero p hp h w, Finset.card_sdiff_of_subset (selected_subset p hp h w),
      card_aUsers p hp, card_selected]
  · change (Finset.univ.filter (fun c => direction p hp h w c = (1 : Fin 3))).card = p / 2
    rw [direction_one p hp h w, card_selected]
  · change (Finset.univ.filter (fun c => direction p hp h w c = (2 : Fin 3))).card = p
    rw [direction_two p hp h w, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      card_aUsers p hp]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega

def wVoltage (c : Color p) (h : ZMod m) : ZMod m := if c ∈ aUsers p h.val then 0 else 1

def yVoltage (c : Color p) (q : ZMod m × ZMod m) : ZMod m :=
  if c ∈ selected p hp q.1 q.2 then 1 else 0

theorem wVoltage_eq (c : Color p) (h w : ZMod m) :
    wVoltage p c h = if direction p hp h w c = 2 then 1 else 0 := by
  by_cases ha : c ∈ aUsers p h.val <;> by_cases hs : c ∈ selected p hp h w <;>
    simp [wVoltage, direction, ha, hs]

theorem yVoltage_eq (c : Color p) (h w : ZMod m) :
    yVoltage p hp c (h, w) = if direction p hp h w c = 1 then 1 else 0 := by
  have hc := selected_subset p hp h w (a := c)
  by_cases ha : c ∈ aUsers p h.val <;> by_cases hs : c ∈ selected p hp h w <;>
    simp_all [yVoltage, direction]

end TorusEven.Entry.Shell
