-- STATUS: main-path
import TorusEven.Collar.PinnedRows
import TorusEven.Collar.IncidenceParity

namespace TorusEven.Collar.Incidence

variable {B Ω : Type*} [Fintype B] [DecidableEq Ω] {m : ℕ} [NeZero m]

structure IsPinnedSelection (A : B → Finset Ω) (active : Finset Ω)
    (J : B → ZMod m → Finset Ω) : Prop where
  subset : ∀ b t, J b t ⊆ A b
  card : ∀ b t, (J b t).card = (A b).card / 2
  residues : ∀ x,
    ((Finset.univ.filter (fun p : B × ZMod m => x ∈ J p.1 p.2)).card : ZMod m) = 1 ∨
    ((Finset.univ.filter (fun p : B × ZMod m => x ∈ J p.1 p.2)).card : ZMod m) = -1
  pinned : ∀ b, Disjoint (J b 0) active
  selected_coherent : ∀ b, 2 ≤ (A b).card / 2 → Coherent (J b)
  complement_coherent : ∀ b, 2 ≤ (A b).card - (A b).card / 2 →
    Coherent (fun t => A b \ J b t)

theorem exists_pinnedSelection [Finite Ω] (A : B → Finset Ω) (active : Finset Ω)
    (hm : 4 ≤ m) (hactive : ∀ b, ((A b) ∩ active).card ≤ 1) (hEven : EvenComponents A) :
    ∃ J : B → ZMod m → Finset Ω, IsPinnedSelection A active J := by
  classical
  obtain ⟨P, hdiv⟩ := exists_directed_pairs A hEven
  choose bits hpin hsurj using fun b => (P b).exists_event_bits active (hactive b)
  choose F hFA hFP hFact hFcard using fun b => (P b).exists_fillers active (hactive b)
  let event (b : B) (i : Fin (P b).count) : ZMod m := if bits b i then 1 else 0
  let J (b : B) := (P b).row (event b) (F b) false
  have hsep {a b : ℕ} (ha : a < m) (hb : b < m) (hne : a ≠ b) : (a : ZMod m) ≠ b := by
    intro h
    apply hne
    have h' := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using h'
  have h01 : (0 : ZMod m) ≠ 1 := by
    simpa using hsep (a := 0) (b := 1) (by omega) (by omega) (by decide)
  have h20 : (2 : ZMod m) ≠ 0 := by
    simpa using hsep (a := 2) (b := 0) (by omega) (by omega) (by decide)
  have h21 : (2 : ZMod m) ≠ 1 := by
    simpa using hsep (a := 2) (b := 1) (by omega) (by omega) (by decide)
  have hevent (b : B) (i : Fin (P b).count) : event b i = 0 ∨ event b i = 1 := by
    cases h : bits b i <;> simp [event, h]
  have hboth (b : B) (hn : 2 ≤ (P b).count) :
      (∃ i, event b i = 0) ∧ ∃ i, event b i = 1 := by
    obtain ⟨i, hi⟩ := hsurj b hn false
    obtain ⟨j, hj⟩ := hsurj b hn true
    exact ⟨⟨i, by simp [event, hi]⟩, ⟨j, by simp [event, hj]⟩⟩
  have hsub (b : B) (t : ZMod m) : J b t ⊆ A b := (P b).row_subset _ _ (hFA b) _ _
  have hcard (b : B) (t : ZMod m) : (J b t).card = (A b).card / 2 :=
    ((P b).card_row _ _ (hFP b) _ _).trans (hFcard b)
  refine ⟨J, ⟨hsub, hcard, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    let f : Ω → ZMod m := fun y => if y = x then 1 else 0
    have htotal : ((Finset.univ.filter (fun p : B × ZMod m => x ∈ J p.1 p.2)).card : ZMod m) =
        ∑ b, ∑ t : ZMod m, ∑ y ∈ J b t, f y := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
        apply_ite, Nat.cast_zero, Fintype.sum_prod_type]
      simp [f]
    have hsum (b : B) := (P b).sum_rows f (event b) (F b) (hFP b)
    rw [htotal]
    simp only [J, hsum]
    rcases hdiv x with h | h
    · left
      have h' := congrArg (fun z : ℤ => (z : ZMod m)) h
      simpa only [Int.cast_sum, Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero, f] using h'
    · right
      have h' := congrArg (fun z : ℤ => (z : ZMod m)) h
      simpa only [Int.cast_sum, Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero,
        Int.cast_neg, f] using h'
  · intro b
    exact (P b).row_pinned 0 1 h01 active (F b) (hFact b) (bits b) (hpin b)
  · intro b hb
    exact (P b).coherent_row (event b) (F b) false 0 1 2 h01 h20 h21
      (hevent b) (hboth b) (by rw [hFcard]; exact hb)
  · intro b hb
    let G := A b \ ((P b).support ∪ F b)
    have hGP : Disjoint G (P b).support := by
      apply Finset.disjoint_left.mpr
      intro x hx hs
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hs)
    have hGcard : G.card + (P b).count = (A b).card - (A b).card / 2 := by
      have h := Finset.card_sdiff_of_subset (hsub b 0)
      rw [hcard] at h
      change (A b \ (P b).row (event b) (F b) false 0).card = _ at h
      rw [(P b).complement_row _ _ (hFP b), (P b).card_row _ _ hGP] at h
      exact h
    have hc := (P b).coherent_row (event b) G true 0 1 2 h01 h20 h21
      (hevent b) (hboth b) (by omega)
    simpa only [J, (P b).complement_row _ _ (hFP b), Bool.not_false] using hc

theorem IsPinnedSelection.column_unit {A : B → Finset Ω} {active : Finset Ω}
    {J : B → ZMod m → Finset Ω} (h : IsPinnedSelection A active J) (x : Ω) :
    IsUnit ((Finset.univ.filter (fun p : B × ZMod m => x ∈ J p.1 p.2)).card : ZMod m) := by
  rcases h.residues x with hx | hx <;> rw [hx]
  · exact isUnit_one
  · exact isUnit_one.neg

theorem IsPinnedSelection.evenComponents [Finite Ω] {A : B → Finset Ω} {active : Finset Ω}
    {J : B → ZMod m → Finset Ω} (h : IsPinnedSelection A active J)
    (hm : Even m) (hne : ∀ b, (A b).Nonempty) : EvenComponents A := by
  classical
  letI := Fintype.ofFinite Ω
  let f : B → Ω → ZMod 2 := fun b x => ∑ t : ZMod m, if x ∈ J b t then 1 else 0
  apply evenComponents_of_boundary A hne f
  · intro b x hx
    have hnot (t : ZMod m) : x ∉ J b t := fun hmem => hx (h.subset b t hmem)
    simp [f, hnot]
  · intro b
    have hrow (t : ZMod m) :
        (∑ x, if x ∈ J b t then (1 : ZMod 2) else 0) = ((A b).card / 2 : ℕ) := by
      have hh := congrArg (fun n : ℕ => (n : ZMod 2)) (h.card b t)
      simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
        Finset.sum_ite_mem, Finset.univ_inter] using hh
    simp only [f]
    rw [Finset.sum_comm]
    simp only [hrow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      hm.natCast_zmod_two, zero_mul]
  · intro x
    have hh := (odd_of_unit_mod_even hm (h.column_unit x)).natCast_zmod_two
    simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      Fintype.sum_prod_type, apply_ite, Nat.cast_zero, f] using hh

theorem pinnedSelection_iff [Finite Ω] (A : B → Finset Ω) (active : Finset Ω)
    (hm : 4 ≤ m) (heven : Even m) (hsize : ∀ b, 2 ≤ (A b).card)
    (hactive : ∀ b, ((A b) ∩ active).card ≤ 1) :
    EvenComponents A ↔ ∃ J : B → ZMod m → Finset Ω, IsPinnedSelection A active J := by
  constructor
  · exact exists_pinnedSelection A active hm hactive
  · rintro ⟨J, hJ⟩
    exact hJ.evenComponents heven (fun b => Finset.card_pos.mp (by have := hsize b; omega))

theorem IsPinnedSelection.selected_evenComponents [Finite Ω]
    {A : B → Finset Ω} {active : Finset Ω} {J : B → ZMod m → Finset Ω}
    (h : IsPinnedSelection A active J) (hm : Even m) (hwidth : ∀ b, 2 ≤ (A b).card / 2) :
    EvenComponents (fun p : B × ZMod m => J p.1 p.2) := by
  apply evenComponents_of_coherent_odd_columns J
    (fun p => Finset.card_pos.mp (by rw [h.card]; have := hwidth p.1; omega))
    (fun b => h.selected_coherent b (hwidth b)) (fun b => (A b).card / 2) h.card
    (by simpa [ZMod.card] using hm)
  exact fun x => odd_of_unit_mod_even hm (h.column_unit x)

theorem IsPinnedSelection.complement_evenComponents [Finite Ω]
    {A : B → Finset Ω} {active : Finset Ω} {J : B → ZMod m → Finset Ω}
    (h : IsPinnedSelection A active J) (hm : Even m)
    (hwidth : ∀ b, 2 ≤ (A b).card - (A b).card / 2) :
    EvenComponents (fun p : B × ZMod m => A p.1 \ J p.1 p.2) := by
  have hcard (b : B) (t : ZMod m) : (A b \ J b t).card = (A b).card - (A b).card / 2 := by
    rw [Finset.card_sdiff_of_subset (h.subset b t), h.card]
  have hR : Even (Fintype.card (ZMod m)) := by simpa [ZMod.card] using hm
  apply evenComponents_of_coherent_odd_columns (fun b t => A b \ J b t)
    (fun p => Finset.card_pos.mp (by rw [hcard]; have := hwidth p.1; omega))
    (fun b => h.complement_coherent b (hwidth b)) (fun b => (A b).card - (A b).card / 2) hcard hR
  exact odd_complement_columns A J h.subset hR (fun x => odd_of_unit_mod_even hm (h.column_unit x))

end TorusEven.Collar.Incidence
