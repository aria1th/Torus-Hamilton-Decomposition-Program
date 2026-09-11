-- STATUS: main-path
import TorusEven.Collar.PairRows

namespace TorusEven.Entry.Shell

open Collar

abbrev Color (p : ℕ) := Fin (2 * p)

def aUser (p h c : ℕ) : Prop :=
  if h = 0 then c = 0 ∨ p < c else if h = 1 then 0 < c ∧ c ≤ p else p ≤ c

instance (p h c : ℕ) : Decidable (aUser p h c) := by unfold aUser; infer_instance

def aUsers (p h : ℕ) : Finset (Color p) := Finset.univ.filter (fun c => aUser p h c.val)

theorem mem_aUsers (p h : ℕ) (c : Color p) : c ∈ aUsers p h ↔ aUser p h c.val := by
  simp [aUsers]

def aIndex (p h i : ℕ) : ℕ :=
  if h = 0 then (if i = 0 then 0 else p + i) else
  if h = 1 then (if i = 0 then p else i) else p + i

variable (p : ℕ) (hp : 2 ≤ p)
include hp

def aEmbedding (h : ℕ) : Fin p ↪ Color p where
  toFun i := ⟨aIndex p h i.val, by
    have hi := i.isLt
    unfold aIndex; split_ifs <;> omega⟩
  inj' i j he := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    change aIndex p h i.val = aIndex p h j.val at hv
    have hi := i.isLt
    have hj := j.isLt
    unfold aIndex at hv
    split_ifs at hv <;> omega

theorem aUsers_eq (h : ℕ) : aUsers p h = Finset.univ.map (aEmbedding p hp h) := by
  ext c
  rw [mem_aUsers]
  constructor
  · intro hc
    have hclt := c.isLt
    apply Finset.mem_map.mpr
    by_cases h0 : h = 0
    · by_cases hc0 : c.val = 0
      · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp [aEmbedding, aIndex, h0, hc0]
      · refine ⟨⟨c.val - p, by unfold aUser at hc; simp only [if_pos h0] at hc; omega⟩,
          Finset.mem_univ _, Fin.ext ?_⟩
        change aIndex p h (c.val - p) = c.val
        unfold aUser at hc
        simp only [if_pos h0] at hc
        simp [aIndex, h0, show c.val - p ≠ 0 by omega]
        omega
    · by_cases h1 : h = 1
      · by_cases hcp : c.val = p
        · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
          simp [aEmbedding, aIndex, h1, hcp]
        · refine ⟨⟨c.val, by unfold aUser at hc; simp only [if_neg h0, if_pos h1] at hc; omega⟩,
            Finset.mem_univ _, Fin.ext ?_⟩
          change aIndex p h c.val = c.val
          unfold aUser at hc
          simp only [if_neg h0, if_pos h1] at hc
          simp [aIndex, h1, show c.val ≠ 0 by omega]
      · refine ⟨⟨c.val - p, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        change aIndex p h (c.val - p) = c.val
        unfold aUser at hc
        simp only [if_neg h0, if_neg h1] at hc
        simp only [aIndex, if_neg h0, if_neg h1]
        omega
  · rintro hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hc
    change aUser p h (aIndex p h i.val)
    have hi := i.isLt
    unfold aUser aIndex
    split_ifs <;> omega

theorem card_aUsers (h : ℕ) : (aUsers p h).card = p := by
  rw [aUsers_eq p hp]
  simp

omit hp in
def pairCount (h : ℕ) : ℕ :=
  if h = 0 then 1 else if h = 1 then p / 2 else
  if h = 2 then (if p % 2 = 0 then p / 2 - 1 else p / 2) else 0

omit hp in
def endpointIndex (h i : ℕ) (b : Bool) : ℕ :=
  if h = 0 then (if b then p + 1 else 0) else
  if h = 1 then
    (if p % 2 = 0 then
      (if i = 0 then (if b then 1 else p) else 2 * i + if b then 1 else 0)
    else 2 * i + 1 + if b then 1 else 0) else
  if p % 2 = 0 then p + 2 * i + 2 + (if b then 1 else 0) else
    if i = 0 then (if b then p + 2 else p) else p + 2 * i + 1 + if b then 1 else 0

omit hp in
theorem pairCount_height (h : ℕ) (hn : 0 < pairCount p h) : h ≤ 2 := by
  unfold pairCount at hn
  split_ifs at hn <;> omega

theorem endpoint_lt (h : ℕ) (i : Fin (pairCount p h)) (b : Bool) :
    endpointIndex p h i.val b < 2 * p := by
  have hi := i.isLt
  have hh := pairCount_height p h (by omega)
  interval_cases h <;> cases b <;> by_cases he : p % 2 = 0 <;> by_cases hi0 : i.val = 0 <;>
    simp_all [pairCount, endpointIndex] <;> omega

def endpoint (h : ℕ) : Fin (pairCount p h) × Bool ↪ Color p where
  toFun q := ⟨endpointIndex p h q.1.val q.2, endpoint_lt p hp h q.1 q.2⟩
  inj' u v he := by
    obtain ⟨i, b⟩ := u
    obtain ⟨j, d⟩ := v
    have hi := i.isLt
    have hj := j.isLt
    have hv := congrArg Fin.val he
    change endpointIndex p h i.val b = endpointIndex p h j.val d at hv
    suffices i.val = j.val ∧ b = d from Prod.ext (Fin.ext this.1) this.2
    have hh := pairCount_height p h (by omega)
    interval_cases h <;> cases b <;> cases d <;> by_cases hi0 : i.val = 0 <;>
      by_cases hj0 : j.val = 0 <;> by_cases he : p % 2 = 0 <;>
      simp [pairCount, endpointIndex, hi0, hj0, he] at hv hi hj ⊢ <;> omega

def pairs (h : ℕ) : LocalPairs (aUsers p h) where
  count := pairCount p h
  endpoint := endpoint p hp h
  mem_endpoint q := by
    rw [mem_aUsers]
    change aUser p h (endpointIndex p h q.1.val q.2)
    have hi := q.1.isLt
    rcases q with ⟨i, b⟩
    cases b <;> unfold aUser endpointIndex <;> unfold pairCount at hi <;> split_ifs at * <;> omega

omit hp in
def fillerIndex (h i : ℕ) : ℕ := if h = 0 then p + i + 2 else p + i

def fillerEmbedding (h : ℕ) : Fin (p / 2 - pairCount p h) ↪ Color p where
  toFun i := ⟨fillerIndex p h i.val, by
    have hi := i.isLt
    unfold fillerIndex; unfold pairCount at hi; split_ifs at * <;> omega⟩
  inj' i j he := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    change fillerIndex p h i.val = fillerIndex p h j.val at hv
    unfold fillerIndex at hv
    split_ifs at hv <;> omega

def fillers (h : ℕ) : Finset (Color p) := Finset.univ.map (fillerEmbedding p hp h)

theorem fillers_subset (h : ℕ) : fillers p hp h ⊆ aUsers p h := by
  intro c hc
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hc
  rw [mem_aUsers]
  change aUser p h (fillerIndex p h i.val)
  have hi := i.isLt
  unfold aUser fillerIndex
  unfold pairCount at hi
  split_ifs at * <;> omega

theorem fillers_disjoint (h : ℕ) : Disjoint (fillers p hp h) (pairs p hp h).support := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hc
  obtain ⟨⟨j, b⟩, he⟩ := (pairs p hp h).mem_support.mp hd
  have hv := congrArg Fin.val he
  change endpointIndex p h j.val b = fillerIndex p h i.val at hv
  have hi : i.val < p / 2 - pairCount p h := i.isLt
  have hj : j.val < pairCount p h := j.isLt
  have hh := pairCount_height p h (by omega)
  interval_cases h <;> cases b <;> by_cases hj0 : j.val = 0 <;> by_cases he : p % 2 = 0 <;>
    simp [pairCount, endpointIndex, fillerIndex, hj0, he] at hv hi hj <;> omega

theorem card_fillers_add_pairs (h : ℕ) : (fillers p hp h).card + (pairs p hp h).count = p / 2 := by
  simp only [fillers, Finset.card_map, Finset.card_univ, Fintype.card_fin, pairs]
  unfold pairCount
  split_ifs <;> omega

end TorusEven.Entry.Shell
