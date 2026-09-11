-- STATUS: main-path
import TorusEven.Entry.Seed.Support

namespace TorusEven.Entry

open Collar

def nearRowNat (h w : ℕ) : Equiv.Perm (Fin 3) :=
  if h = 0 then Equiv.swap 0 2 else
  if h = 1 then (if w = 0 ∨ w = 1 then Equiv.swap 1 2 else rotate) else
  if h = 2 ∧ w = 0 then Equiv.swap 0 1 else Equiv.refl _

namespace Shell

variable (p : ℕ) (hp : 2 ≤ p)

def selectedNat (h w : ℕ) : Finset (Color p) :=
  (pairs p hp h).row (fun j => if j.val = 1 then 1 else 0) (fillers p hp h) false w

def directionNat (h w : ℕ) (c : Color p) : Fin 3 :=
  if c ∈ aUsers p h then (if c ∈ selectedNat p hp h w then 1 else 0) else 2

theorem mem_selectedNat (h w : ℕ) (c : Color p) :
    c ∈ selectedNat p hp h w ↔
      (∃ i, i < p / 2 - pairCount p h ∧ fillerIndex p h i = c.val) ∨
      (∃ i, i < pairCount p h ∧ endpointIndex p h i
        (if w = (if i = 1 then 1 else 0) then true else false) = c.val) := by
  simp only [selectedNat, LocalPairs.row, LocalPairs.chosen, Finset.mem_union,
    Finset.mem_map, Finset.mem_univ, true_and, fillers, fillerEmbedding, pairs,
    LocalPairs.choice, endpoint, Function.Embedding.coeFn_mk, Fin.ext_iff, Fin.exists_iff,
    Bool.not_false]
  change ((∃ i, ∃ _ : i < p / 2 - pairCount p h, fillerIndex p h i = c.val) ∨
    (∃ i, ∃ _ : i < pairCount p h, endpointIndex p h i
      (if w = (if i = 1 then 1 else 0) then true else false) = c.val)) ↔ _
  simp only [exists_prop]

end Shell

namespace Seed

def corePresentNat (j : Fin 3) (h w : ℕ) (q : Fin 4) : Prop :=
  nearRowNat h w (anchorColor q) = j ∧
    (q = 2 → (w : ZMod 2) - (h - 2 : ℕ) = 0) ∧
    (q = 3 → (w : ZMod 2) - (h - 2 : ℕ) = 1)

instance (j : Fin 3) (h w : ℕ) (q : Fin 4) : Decidable (corePresentNat j h w q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def supportNat (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (h w : ℕ) :
    Finset (Fin 4 ⊕ Shell.Color p) :=
  (Finset.univ.filter (corePresentNat j h w)).map Function.Embedding.inl ∪
    (Finset.univ.filter (fun c => Shell.directionNat p hp h w c = j)).map
      Function.Embedding.inr

@[simp] theorem mem_supportNat_left (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (h w : ℕ)
    (q : Fin 4) : Sum.inl q ∈ supportNat p hp j h w ↔ corePresentNat j h w q := by
  simp [supportNat]

@[simp] theorem mem_supportNat_right (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (h w : ℕ)
    (c : Shell.Color p) :
    Sum.inr c ∈ supportNat p hp j h w ↔ Shell.directionNat p hp h w c = j := by
  simp [supportNat]

end Seed

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)
include hm

theorem eq_natCast_small (w : ZMod m) (n : ℕ) (hn : n < 4) :
    w = (n : ZMod m) ↔ w.val = n := by
  have he : w = (n : ZMod m) ↔ w.val = (n : ZMod m).val :=
    (ZMod.val_injective m).eq_iff.symm
  simpa only [ZMod.val_natCast_of_lt (hn.trans_le hm)] using he

theorem nearRow_eq_nat (h w : ZMod m) : nearRow h w = nearRowNat h.val w.val := by
  have h0 := eq_natCast_small hm h 0 (by decide)
  have h1 := eq_natCast_small hm h 1 (by decide)
  have h2 := eq_natCast_small hm h 2 (by decide)
  have w0 := eq_natCast_small hm w 0 (by decide)
  have w1 := eq_natCast_small hm w 1 (by decide)
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2 w0 w1
  simp only [nearRow, nearRowNat, h0, h1, h2, w0, w1]

namespace Shell

theorem selected_eq_nat (p : ℕ) (hp : 2 ≤ p) (h w : ZMod m) :
    selected p hp h w = selectedNat p hp h.val w.val := by
  unfold selected selectedNat LocalPairs.row LocalPairs.chosen
  congr 2
  apply Function.Embedding.ext
  intro i
  change (pairs p hp h.val).endpoint
    (i, if w = event i then !false else false) =
      (pairs p hp h.val).endpoint (i, if w.val = (if i.val = 1 then 1 else 0) then
        !false else false)
  have h0 := eq_natCast_small hm w 0 (by decide)
  have h1 := eq_natCast_small hm w 1 (by decide)
  simp only [Nat.cast_zero, Nat.cast_one] at h0 h1
  by_cases hi : i.val = 1 <;> simp only [event, hi, if_true, if_false, h0, h1]

theorem direction_eq_nat (p : ℕ) (hp : 2 ≤ p) (h w : ZMod m) (c : Color p) :
    direction p hp h w c = directionNat p hp h.val w.val c := by
  simp only [direction, directionNat, selected_eq_nat hm]

end Shell

namespace Seed

variable (heven : Even m)

theorem corePresent_eq_nat (j : Fin 3) (h w : ZMod m) (q : Fin 4) :
    corePresent heven j (h, w) q ↔ corePresentNat j h.val w.val q := by
  have hw : parityMap heven w = (w.val : ZMod 2) := by
    simpa only [ZMod.natCast_zmod_val] using map_natCast (parityMap heven) w.val
  simp only [corePresent, corePresentNat, nearRow_eq_nat hm, NearCore.baseDefect, hw]

theorem support_eq_nat (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (h w : ZMod m) :
    support p hp heven j (h, w) = supportNat p hp j h.val w.val := by
  ext q
  cases q with
  | inl q => simp only [mem_support_left, mem_supportNat_left, corePresent_eq_nat hm]
  | inr c => simp only [mem_support_right, mem_supportNat_right, Shell.direction_eq_nat hm]

theorem support_natCast (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (h w : ℕ)
    (hh : h < m) (hw : w < m) :
    support p hp heven j ((h : ZMod m), (w : ZMod m)) = supportNat p hp j h w := by
  rw [support_eq_nat hm heven, ZMod.val_natCast_of_lt hh, ZMod.val_natCast_of_lt hw]

end Seed
end TorusEven.Entry
