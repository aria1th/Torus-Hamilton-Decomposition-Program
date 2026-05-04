import Mathlib

namespace RoundComposite
namespace ActiveHall

open scoped BigOperators

/--
An active-incidence instance for the Hall-symboling layer.

At each base vertex `x`, exactly `T` colors are active.  A symboling will assign
the symbols `Fin T` bijectively to this active set.
-/
structure Incidence (T : Nat) (X C : Type*) [Fintype X] [Fintype C]
    [DecidableEq C] where
  active : X → Finset C
  active_card : ∀ x : X, (active x).card = T

namespace Incidence

def colorDegree {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => c ∈ I.active x)).card

def choiceDegree {X C : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]
    (choice : X → C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => choice x = c)).card

def cutCap {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ∑ x : X, min ((I.active x ∩ U).card) S.card

def hitCount {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C)
    (U : Finset C) : Nat :=
  ((Finset.univ : Finset X).filter
    (fun x : X => (I.active x ∩ U).Nonempty)).card

theorem sum_colorDegree {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C) :
    (∑ c : C, I.colorDegree c) = T * Fintype.card X := by
  classical
  calc
    (∑ c : C, I.colorDegree c)
        = ∑ c : C, ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [colorDegree, Finset.card_filter]
    _ = ∑ x : X, ∑ c : C, if c ∈ I.active x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, (I.active x).card := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp
    _ = ∑ _x : X, T := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact I.active_card x
    _ = T * Fintype.card X := by
            simp [Finset.sum_const, Nat.mul_comm]

theorem eq_of_mem_of_active_card_one {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence 1 X C) {x : X} {a b : C}
    (ha : a ∈ I.active x) (hb : b ∈ I.active x) :
    a = b := by
  have hcard : (I.active x).card ≤ 1 := by
    rw [I.active_card x]
  exact (Finset.card_le_one.mp hcard) a ha b hb

def eraseChoice {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) :
    Incidence T X C where
  active := fun x => (I.active x).erase (choice x)
  active_card := by
    intro x
    rw [Finset.card_erase_of_mem (hchoice x), I.active_card x]
    omega

@[simp] theorem eraseChoice_active {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) (x : X) :
    (I.eraseChoice choice hchoice).active x =
      (I.active x).erase (choice x) :=
  rfl

theorem mem_eraseChoice_active {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    {x : X} {c : C} :
    c ∈ (I.eraseChoice choice hchoice).active x ↔
      c ∈ I.active x ∧ c ≠ choice x := by
  simp [eraseChoice, and_comm]

theorem eraseChoice_colorDegree_add_choiceDegree
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) (c : C) :
    (I.eraseChoice choice hchoice).colorDegree c
      + choiceDegree choice c = I.colorDegree c := by
  classical
  let B : Finset X := (Finset.univ : Finset X).filter
    (fun x => c ∈ (I.eraseChoice choice hchoice).active x)
  let D : Finset X := (Finset.univ : Finset X).filter
    (fun x => choice x = c)
  let A : Finset X := (Finset.univ : Finset X).filter
    (fun x => c ∈ I.active x)
  have hdisj : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro x hxB hxD
    have hxB' : c ≠ choice x ∧ c ∈ I.active x := by
      simpa [B] using hxB
    have hxD' : choice x = c := by
      simpa [D] using hxD
    exact hxB'.1 hxD'.symm
  have hUnion : B ∪ D = A := by
    ext x
    by_cases hxD : choice x = c
    · have hcx : c ∈ I.active x := by
        rw [← hxD]
        exact hchoice x
      simp [A, B, D, hxD, hcx]
    · by_cases hcx : c ∈ I.active x
      · have hxne : c ≠ choice x := by
          intro h
          exact hxD h.symm
        simp [A, B, D, hcx, hxD, hxne]
      · simp [A, B, D, hcx, hxD]
  change B.card + D.card = A.card
  rw [← hUnion, Finset.card_union_of_disjoint hdisj]

theorem sum_colorDegree_on {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    (∑ c ∈ U, I.colorDegree c)
      = ∑ x : X, (I.active x ∩ U).card := by
  classical
  calc
    (∑ c ∈ U, I.colorDegree c)
        = ∑ c ∈ U, ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [colorDegree, Finset.card_filter]
    _ = ∑ x : X, ∑ c ∈ U, if c ∈ I.active x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, (I.active x ∩ U).card := by
            apply Finset.sum_congr rfl
            intro x _hx
            have hfilter :
                U.filter (fun c : C => c ∈ I.active x) = I.active x ∩ U := by
              ext c
              simp [and_comm]
            rw [← hfilter]
            exact (Finset.card_filter (fun c : C => c ∈ I.active x) U).symm

theorem cutCap_symbols_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.cutCap U (Finset.univ : Finset (Fin T))
      = ∑ x : X, (I.active x ∩ U).card := by
  classical
  unfold cutCap
  apply Finset.sum_congr rfl
  intro x _hx
  rw [min_eq_left]
  have hle : (I.active x ∩ U).card ≤ (I.active x).card := by
    exact Finset.card_le_card (by
      intro c hc
      exact (Finset.mem_inter.mp hc).1)
  rw [I.active_card x] at hle
  simpa using hle

theorem cutCap_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (S : Finset (Fin T)) :
    I.cutCap (Finset.univ : Finset C) S = S.card * Fintype.card X := by
  classical
  have hS : S.card ≤ T := by
    simpa using Finset.card_le_univ S
  calc
    I.cutCap (Finset.univ : Finset C) S
        = ∑ _x : X, S.card := by
            unfold cutCap
            apply Finset.sum_congr rfl
            intro x _hx
            have hactive : (I.active x ∩ (Finset.univ : Finset C)).card = T := by
              simp [I.active_card x]
            rw [hactive, min_eq_right hS]
    _ = S.card * Fintype.card X := by
            simp [Finset.sum_const, Nat.mul_comm]

theorem cutCap_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (S : Finset (Fin T)) :
    I.cutCap (∅ : Finset C) S = 0 := by
  simp [cutCap]

theorem cutCap_symbols_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.cutCap U (∅ : Finset (Fin T)) = 0 := by
  simp [cutCap]

theorem cutCap_symbol_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) (σ : Fin T) :
    I.cutCap U ({σ} : Finset (Fin T)) = I.hitCount U := by
  classical
  calc
    I.cutCap U ({σ} : Finset (Fin T))
        = ∑ x : X,
            if (I.active x ∩ U).Nonempty then 1 else 0 := by
            unfold cutCap
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hhit : (I.active x ∩ U).Nonempty
            · have hcard : 1 ≤ (I.active x ∩ U).card :=
                hhit.card_pos
              rw [Finset.card_singleton, min_eq_right hcard]
              simp [hhit]
            · have hcard : (I.active x ∩ U).card = 0 := by
                rw [Finset.card_eq_zero]
                exact Finset.not_nonempty_iff_eq_empty.mp hhit
              simp [hhit, hcard]
    _ = I.hitCount U := by
            rw [hitCount, Finset.card_filter]

theorem cutCap_mono {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) {U₁ U₂ : Finset C} {S₁ S₂ : Finset (Fin T)}
    (hU : U₁ ⊆ U₂) (hS : S₁ ⊆ S₂) :
    I.cutCap U₁ S₁ ≤ I.cutCap U₂ S₂ := by
  unfold cutCap
  apply Finset.sum_le_sum
  intro x _hx
  exact min_le_min
    (Finset.card_le_card (Finset.inter_subset_inter_left hU))
    (Finset.card_le_card hS)

theorem cutCap_mono_colors {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) {U₁ U₂ : Finset C} (hU : U₁ ⊆ U₂)
    (S : Finset (Fin T)) :
    I.cutCap U₁ S ≤ I.cutCap U₂ S :=
  I.cutCap_mono hU (fun _ h => h)

theorem cutCap_mono_symbols {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) {S₁ S₂ : Finset (Fin T)}
    (hS : S₁ ⊆ S₂) :
    I.cutCap U S₁ ≤ I.cutCap U S₂ :=
  I.cutCap_mono (fun _ h => h) hS

theorem exists_injective_token_matching_of_hall
    {T : Nat} {X C Q : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (colorOf : Q → C)
    (hHall : ∀ A : Finset Q, A.card ≤ I.hitCount (A.image colorOf)) :
    ∃ f : Q → X, Function.Injective f ∧
      ∀ q : Q, colorOf q ∈ I.active (f q) := by
  classical
  rw [← Fintype.all_card_le_filter_rel_iff_exists_injective
    (r := fun q x => colorOf q ∈ I.active x)]
  intro A
  have hfilter :
      ({x : X | ∃ q ∈ A, colorOf q ∈ I.active x} : Finset X)
        =
      (Finset.univ.filter
        (fun x : X => (I.active x ∩ A.image colorOf).Nonempty)) := by
    ext x
    simp [Finset.Nonempty, and_comm]
  rw [hfilter]
  exact hHall A

end Incidence

/-- A nonnegative count matrix with the row and column sums forced by incidence. -/
structure CountMatrix {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) where
  val : C → Fin T → Nat
  row_sum : ∀ c : C, (∑ σ : Fin T, val c σ) = I.colorDegree c
  col_sum : ∀ σ : Fin T, (∑ c : C, val c σ) = Fintype.card X

/-- Desired residues for active symbol counts. -/
structure ResidueSpec (m T : Nat) (C : Type*) [Fintype C] where
  target : C → Fin T → ZMod m

namespace ResidueSpec

def RowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∀ c : C, (I.colorDegree c : ZMod m) = ∑ σ : Fin T, R.target c σ

def ColCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (_I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∀ σ : Fin T, (Fintype.card X : ZMod m) = ∑ c : C, R.target c σ

end ResidueSpec

def balancedUnitResidueLength : Nat → Nat
  | 0 => 3
  | k + 1 => balancedUnitResidueLength k + 2

theorem balancedUnitResidueLength_eq :
    ∀ k : Nat, balancedUnitResidueLength k = 2 * k + 3
  | 0 => by simp [balancedUnitResidueLength]
  | k + 1 => by
      rw [balancedUnitResidueLength]
      rw [balancedUnitResidueLength_eq k]
      omega

noncomputable def balancedUnitResiduesAux (m : Nat) :
    (k : Nat) → Fin (balancedUnitResidueLength k) → ZMod m
  | 0 => fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else -2
  | k + 1 => fun i =>
      if h : i.val < balancedUnitResidueLength k then
        balancedUnitResiduesAux m k ⟨i.val, h⟩
      else if i.val = balancedUnitResidueLength k then
        1
      else
        -1

theorem balancedUnitResiduesAux_sum_zero {m : Nat} :
    ∀ k : Nat,
      (∑ i : Fin (balancedUnitResidueLength k),
        balancedUnitResiduesAux m k i) = 0
  | 0 => by
      change (∑ i : Fin 3, balancedUnitResiduesAux m 0 i) = 0
      rw [Fin.sum_univ_three]
      simp [balancedUnitResiduesAux, balancedUnitResidueLength]
      ring
  | k + 1 => by
      change (∑ i : Fin (balancedUnitResidueLength k + 2),
        balancedUnitResiduesAux m (k + 1) i) = 0
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin (balancedUnitResidueLength k + 1),
              balancedUnitResiduesAux m (k + 1) i.castSucc)
            =
          (∑ i : Fin (balancedUnitResidueLength k),
              balancedUnitResiduesAux m k i) + 1 := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _hi
          simp [balancedUnitResiduesAux, i.isLt]
        · simp [balancedUnitResiduesAux]
      have hlast :
          balancedUnitResiduesAux m (k + 1)
              (Fin.last (balancedUnitResidueLength k + 1)) = -1 := by
        simp [balancedUnitResiduesAux]
      rw [hcast, hlast, balancedUnitResiduesAux_sum_zero k]
      ring

theorem balancedUnitResiduesAux_isUnit {m : Nat} (hmodd : Odd m) :
    ∀ k : Nat, ∀ i : Fin (balancedUnitResidueLength k),
      IsUnit (balancedUnitResiduesAux m k i)
  | 0, i => by
      fin_cases i <;> simp [balancedUnitResiduesAux]
      simpa using
        (IsUnit.neg (ZMod.isUnit_iff_coprime 2 m |>.2 hmodd.coprime_two_left))
  | k + 1, i => by
      by_cases h : i.val < balancedUnitResidueLength k
      · simpa [balancedUnitResiduesAux, h] using
          balancedUnitResiduesAux_isUnit hmodd k ⟨i.val, h⟩
      · by_cases hi : i.val = balancedUnitResidueLength k
        · simp [balancedUnitResiduesAux, hi]
        · simp [balancedUnitResiduesAux, h, hi]

noncomputable def balancedUnitResidues (m k : Nat) :
    Fin (2 * k + 3) → ZMod m :=
  fun i =>
    balancedUnitResiduesAux m k
      (Fin.cast (balancedUnitResidueLength_eq k).symm i)

theorem balancedUnitResidues_sum_zero {m k : Nat} :
    (∑ i : Fin (2 * k + 3), balancedUnitResidues m k i) = 0 := by
  unfold balancedUnitResidues
  let e : Fin (2 * k + 3) ≃ Fin (balancedUnitResidueLength k) :=
    finCongr (balancedUnitResidueLength_eq k).symm
  calc
    (∑ i : Fin (2 * k + 3), balancedUnitResiduesAux m k (e i))
        = ∑ j : Fin (balancedUnitResidueLength k),
            balancedUnitResiduesAux m k j := by
            exact Fintype.sum_equiv e
              (fun i : Fin (2 * k + 3) =>
                balancedUnitResiduesAux m k (e i))
              (fun j : Fin (balancedUnitResidueLength k) =>
                balancedUnitResiduesAux m k j)
              (by intro i; rfl)
    _ = 0 := balancedUnitResiduesAux_sum_zero k

theorem balancedUnitResidues_isUnit {m k : Nat} (hmodd : Odd m)
    (i : Fin (2 * k + 3)) :
    IsUnit (balancedUnitResidues m k i) := by
  unfold balancedUnitResidues
  exact balancedUnitResiduesAux_isUnit hmodd k
    (Fin.cast (balancedUnitResidueLength_eq k).symm i)

theorem exists_balanced_unit_residues_fin {d m : Nat}
    (hdodd : Odd d) (hd3 : 3 ≤ d) (hmodd : Odd m) :
    ∃ u : Fin d → ZMod m,
      (∑ i : Fin d, u i) = 0 ∧ ∀ i : Fin d, IsUnit (u i) := by
  rcases hdodd with ⟨a, rfl⟩
  have ha1 : 1 ≤ a := by omega
  let k := a - 1
  have hdim : 2 * k + 3 = 2 * a + 1 := by
    simp [k]
    omega
  let e : Fin (2 * a + 1) ≃ Fin (2 * k + 3) := finCongr hdim.symm
  refine ⟨fun i => balancedUnitResidues m k (e i), ?_, ?_⟩
  · calc
      (∑ i : Fin (2 * a + 1), balancedUnitResidues m k (e i))
          = ∑ j : Fin (2 * k + 3), balancedUnitResidues m k j := by
              exact Fintype.sum_equiv e
                (fun i : Fin (2 * a + 1) => balancedUnitResidues m k (e i))
                (fun j : Fin (2 * k + 3) => balancedUnitResidues m k j)
                (by intro i; rfl)
      _ = 0 := balancedUnitResidues_sum_zero
  · intro i
    exact balancedUnitResidues_isUnit hmodd (e i)

theorem zmod_natCast_pow_eq_zero_of_pos {m n : Nat} (hn : 0 < n) :
    ((m ^ n : Nat) : ZMod m) = 0 := by
  rcases n with _ | n
  · omega
  · simp [pow_succ]

theorem zmod_natCast_mul_pow_eq_zero_of_pos {m n a : Nat} (hn : 0 < n) :
    ((a * m ^ n : Nat) : ZMod m) = 0 := by
  rw [Nat.cast_mul, zmod_natCast_pow_eq_zero_of_pos hn, mul_zero]

theorem zmod_natCast_pow_mul_eq_zero_of_pos {m n a : Nat} (hn : 0 < n) :
    ((m ^ n * a : Nat) : ZMod m) = 0 := by
  rw [Nat.cast_mul, zmod_natCast_pow_eq_zero_of_pos hn, zero_mul]

noncomputable def universalUnitResidueSpec (m d n : Nat)
    (u : Fin d → ZMod m) : ResidueSpec m (n + 2) (Fin d) where
  target := fun c σ =>
    if σ.val = 0 then u c else if σ.val = 1 then -u c else 0

theorem universalUnitResidueSpec_row_sum {m d n : Nat}
    (u : Fin d → ZMod m) (c : Fin d) :
    (∑ σ : Fin (n + 2),
      (universalUnitResidueSpec m d n u).target c σ) = 0 := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_two]
      simp [universalUnitResidueSpec]
  | succ n ih =>
      change (∑ σ : Fin ((n + 2) + 1),
        (universalUnitResidueSpec m d (n + 1) u).target c σ) = 0
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin (n + 2),
            (universalUnitResidueSpec m d (n + 1) u).target c i.castSucc)
          =
          (∑ i : Fin (n + 2),
            (universalUnitResidueSpec m d n u).target c i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h0 : i.val = 0
        · simp [universalUnitResidueSpec, h0]
        · by_cases h1 : i.val = 1
          · simp [universalUnitResidueSpec, h1]
          · simp [universalUnitResidueSpec, h1]
      have hlast :
          (universalUnitResidueSpec m d (n + 1) u).target c
            (Fin.last (n + 2)) = 0 := by
        simp [universalUnitResidueSpec]
      rw [hcast, hlast, ih]
      simp

theorem universalUnitResidueSpec_col_sum {m d n : Nat}
    {u : Fin d → ZMod m} (hu : (∑ c : Fin d, u c) = 0)
    (σ : Fin (n + 2)) :
    (∑ c : Fin d, (universalUnitResidueSpec m d n u).target c σ) = 0 := by
  by_cases hs0 : σ = 0
  · subst σ
    simp [universalUnitResidueSpec, hu]
  · by_cases hs1 : σ = 1
    · subst σ
      simp [universalUnitResidueSpec, hu]
    · have h1 : σ.val ≠ 1 := by
        intro hval
        exact hs1 (Fin.ext hval)
      simp [universalUnitResidueSpec, hs0, h1]

theorem universalUnitResidueSpec_rowCompatible
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d)) (u : Fin d → ZMod m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0) :
    (universalUnitResidueSpec m d n u).RowCompatible I := by
  intro c
  rw [hColor c, universalUnitResidueSpec_row_sum]

theorem universalUnitResidueSpec_colCompatible
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d)) {u : Fin d → ZMod m}
    (hu : (∑ c : Fin d, u c) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    (universalUnitResidueSpec m d n u).ColCompatible I := by
  intro σ
  rw [hX, universalUnitResidueSpec_col_sum hu σ]

theorem universalUnitResidueSpec_zero_isUnit {m d n : Nat}
    {u : Fin d → ZMod m} (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) :
    IsUnit ((universalUnitResidueSpec m d n u).target c 0) := by
  simpa [universalUnitResidueSpec] using huUnit c

theorem universalUnitResidueSpec_numeric_sub_delta_isUnit {m d n : Nat}
    {u : Fin d → ZMod m} (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) {σ : Fin (n + 2)} (hσ : 2 ≤ σ.val) :
    IsUnit ((universalUnitResidueSpec m d n u).target c σ -
      (universalUnitResidueSpec m d n u).target c 1) := by
  have hs0 : σ ≠ 0 := by
    intro h
    have hval : σ.val = 0 := by
      simpa using congrArg Fin.val h
    omega
  have h1 : σ.val ≠ 1 := by omega
  simpa [universalUnitResidueSpec, hs0, h1] using huUnit c

theorem exists_universalUnitResidueSpec_compatible_primitive
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d))
    (hdodd : Odd d) (hd3 : 3 ≤ d) (hmodd : Odd m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    ∃ R : ResidueSpec m (n + 2) (Fin d),
      R.RowCompatible I ∧ R.ColCompatible I ∧
      (∀ c : Fin d, IsUnit (R.target c 0)) ∧
      (∀ c : Fin d, ∀ σ : Fin (n + 2), 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c 1)) := by
  rcases exists_balanced_unit_residues_fin hdodd hd3 hmodd with
    ⟨u, huSum, huUnit⟩
  refine ⟨universalUnitResidueSpec m d n u, ?_, ?_, ?_, ?_⟩
  · exact universalUnitResidueSpec_rowCompatible I u hColor
  · exact universalUnitResidueSpec_colCompatible I huSum hX
  · exact universalUnitResidueSpec_zero_isUnit huUnit
  · intro c σ hσ
    exact universalUnitResidueSpec_numeric_sub_delta_isUnit huUnit c hσ

namespace CountMatrix

def cutMass {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ∑ c ∈ U, ∑ σ ∈ S, M.val c σ

def HallCuts {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) : Prop :=
  ∀ U : Finset C, ∀ S : Finset (Fin T),
    M.cutMass U S ≤ I.cutCap U S

def HasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (M.val c σ : ZMod m) = R.target c σ

theorem cutMass_symbols_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (Finset.univ : Finset (Fin T))
      = ∑ c ∈ U, I.colorDegree c := by
  classical
  calc
    M.cutMass U (Finset.univ : Finset (Fin T))
        = ∑ c ∈ U, ∑ σ : Fin T, M.val c σ := by
            rfl
    _ = ∑ c ∈ U, I.colorDegree c := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact M.row_sum c

theorem cutMass_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (Finset.univ : Finset C) S = S.card * Fintype.card X := by
  classical
  calc
    M.cutMass (Finset.univ : Finset C) S
        = ∑ σ ∈ S, ∑ c : C, M.val c σ := by
            unfold cutMass
            rw [Finset.sum_comm]
    _ = ∑ _σ ∈ S, Fintype.card X := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            exact M.col_sum σ
    _ = S.card * Fintype.card X := by
            simp [Finset.sum_const]

theorem cutMass_symbols_univ_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (Finset.univ : Finset (Fin T))
      = I.cutCap U (Finset.univ : Finset (Fin T)) := by
  rw [M.cutMass_symbols_univ U, I.cutCap_symbols_univ U,
    I.sum_colorDegree_on U]

theorem cutMass_colors_univ_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (Finset.univ : Finset C) S
      = I.cutCap (Finset.univ : Finset C) S := by
  rw [M.cutMass_colors_univ S, I.cutCap_colors_univ S]

theorem cutMass_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (∅ : Finset C) S = 0 := by
  simp [cutMass]

theorem cutMass_symbols_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (∅ : Finset (Fin T)) = 0 := by
  simp [cutMass]

theorem cutMass_symbol_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (σ : Fin T) :
    M.cutMass U ({σ} : Finset (Fin T)) = ∑ c ∈ U, M.val c σ := by
  simp [cutMass]

theorem cutMass_colors_empty_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (∅ : Finset C) S = I.cutCap (∅ : Finset C) S := by
  rw [M.cutMass_colors_empty S, I.cutCap_colors_empty S]

theorem cutMass_symbols_empty_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (∅ : Finset (Fin T)) = I.cutCap U (∅ : Finset (Fin T)) := by
  rw [M.cutMass_symbols_empty U, I.cutCap_symbols_empty U]

theorem cutMass_mono {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {U₁ U₂ : Finset C} {S₁ S₂ : Finset (Fin T)}
    (hU : U₁ ⊆ U₂) (hS : S₁ ⊆ S₂) :
    M.cutMass U₁ S₁ ≤ M.cutMass U₂ S₂ := by
  unfold cutMass
  have hcolor :
      (∑ c ∈ U₁, ∑ σ ∈ S₁, M.val c σ)
        ≤ ∑ c ∈ U₂, ∑ σ ∈ S₁, M.val c σ :=
    Finset.sum_le_sum_of_subset hU
  have hsymbol :
      (∑ c ∈ U₂, ∑ σ ∈ S₁, M.val c σ)
        ≤ ∑ c ∈ U₂, ∑ σ ∈ S₂, M.val c σ := by
    apply Finset.sum_le_sum
    intro c _hc
    exact Finset.sum_le_sum_of_subset hS
  exact hcolor.trans hsymbol

theorem cutMass_mono_colors {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {U₁ U₂ : Finset C} (hU : U₁ ⊆ U₂) (S : Finset (Fin T)) :
    M.cutMass U₁ S ≤ M.cutMass U₂ S :=
  M.cutMass_mono hU (fun _ h => h)

theorem cutMass_mono_symbols {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) {S₁ S₂ : Finset (Fin T)} (hS : S₁ ⊆ S₂) :
    M.cutMass U S₁ ≤ M.cutMass U S₂ :=
  M.cutMass_mono (fun _ h => h) hS

theorem hallCuts_of_nontrivial {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hCuts :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ (Finset.univ : Finset C) →
        S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
        M.cutMass U S ≤ I.cutCap U S) :
    M.HallCuts := by
  intro U S
  by_cases hUempty : U = ∅
  · subst U
    rw [M.cutMass_colors_empty_eq_cutCap S]
  by_cases hSempty : S = ∅
  · subst S
    rw [M.cutMass_symbols_empty_eq_cutCap U]
  by_cases hUuniv : U = (Finset.univ : Finset C)
  · subst U
    rw [M.cutMass_colors_univ_eq_cutCap S]
  by_cases hSuniv : S = (Finset.univ : Finset (Fin T))
  · subst S
    rw [M.cutMass_symbols_univ_eq_cutCap U]
  exact hCuts U S
    (Finset.nonempty_iff_ne_empty.mpr hUempty) hUuniv
    (Finset.nonempty_iff_ne_empty.mpr hSempty) hSuniv

theorem hallCuts_iff_nontrivial {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) :
    M.HallCuts ↔
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ (Finset.univ : Finset C) →
        S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
        M.cutMass U S ≤ I.cutCap U S := by
  constructor
  · intro hCuts U S _hUne _hUuniv _hSne _hSuniv
    exact hCuts U S
  · exact M.hallCuts_of_nontrivial

theorem singleSymbol_hall {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (U : Finset C) (σ : Fin T) :
    (∑ c ∈ U, M.val c σ) ≤ I.hitCount U := by
  rw [← M.cutMass_symbol_singleton U σ, ← I.cutCap_symbol_singleton U σ]
  exact hHall U ({σ} : Finset (Fin T))

theorem exists_singleSymbol_token_matching {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (σ : Fin T) :
    ∃ f : (Sigma fun c : C => Fin (M.val c σ)) → X,
      Function.Injective f ∧
      ∀ q : Sigma fun c : C => Fin (M.val c σ),
        q.1 ∈ I.active (f q) := by
  classical
  apply I.exists_injective_token_matching_of_hall
    (colorOf := fun q : Sigma fun c : C => Fin (M.val c σ) => q.1)
  intro A
  let U : Finset C :=
    A.image (fun q : Sigma fun c : C => Fin (M.val c σ) => q.1)
  have hsubset :
      A ⊆ U.sigma
        (fun c : C => (Finset.univ : Finset (Fin (M.val c σ)))) := by
    intro q hq
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_image_of_mem
        (fun q : Sigma fun c : C => Fin (M.val c σ) => q.1) hq,
        Finset.mem_univ q.2⟩
  have hcardA :
      A.card ≤
        (U.sigma
          (fun c : C => (Finset.univ : Finset (Fin (M.val c σ))))).card :=
    Finset.card_le_card hsubset
  have hcardSigma :
      (U.sigma
          (fun c : C => (Finset.univ : Finset (Fin (M.val c σ))))).card
        = ∑ c ∈ U, M.val c σ := by
    rw [Finset.card_sigma]
    simp
  rw [hcardSigma] at hcardA
  exact hcardA.trans (M.singleSymbol_hall hHall U σ)

theorem exists_singleSymbol_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (σ : Fin T) :
    ∃ f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X,
      ∀ q : Sigma fun c : C => Fin (M.val c σ),
        q.1 ∈ I.active (f q) := by
  classical
  rcases M.exists_singleSymbol_token_matching hHall σ with
    ⟨f, hfInj, hfActive⟩
  have hcard :
      Fintype.card (Sigma fun c : C => Fin (M.val c σ))
        = Fintype.card X := by
    rw [Fintype.card_sigma]
    simpa using M.col_sum σ
  have hfBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩
  exact ⟨Equiv.ofBijective f hfBij, hfActive⟩

theorem choiceDegree_of_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (σ : Fin T)
    (f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X) (c : C) :
    Incidence.choiceDegree (fun x : X => (f.symm x).1) c =
      M.val c σ := by
  classical
  unfold Incidence.choiceDegree
  calc
    ((Finset.univ : Finset X).filter
        (fun x => (f.symm x).1 = c)).card
        = ∑ x : X, if (f.symm x).1 = c then 1 else 0 := by
            rw [Finset.card_filter]
    _ = ∑ q : Sigma fun c : C => Fin (M.val c σ),
          if q.1 = c then 1 else 0 := by
            exact Fintype.sum_equiv f.symm
              (fun x : X => if (f.symm x).1 = c then (1 : Nat) else 0)
              (fun q : Sigma fun c : C => Fin (M.val c σ) =>
                if q.1 = c then (1 : Nat) else 0)
              (by intro x; simp)
    _ = M.val c σ := by
            rw [Fintype.sum_sigma]
            calc
              (∑ x : C, ∑ q : Fin (M.val x σ),
                  if x = c then (1 : Nat) else 0)
                  = ∑ x : C, if x = c then M.val x σ else 0 := by
                      apply Finset.sum_congr rfl
                      intro x _hx
                      by_cases hxc : x = c <;> simp [hxc]
              _ = M.val c σ := by
                      simp

theorem eraseChoice_colorDegree_add_val_of_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I) (σ : Fin (T + 1))
    (f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X)
    (hfActive :
      ∀ q : Sigma fun c : C => Fin (M.val c σ), q.1 ∈ I.active (f q))
    (c : C) :
    let choice : X → C := fun x => (f.symm x).1
    let hchoice : ∀ x : X, choice x ∈ I.active x := by
      intro x
      simpa [choice] using hfActive (f.symm x)
    (I.eraseChoice choice hchoice).colorDegree c + M.val c σ =
      I.colorDegree c := by
  intro choice hchoice
  rw [← M.choiceDegree_of_bijective_token_matching σ f c]
  exact I.eraseChoice_colorDegree_add_choiceDegree choice hchoice c

theorem rowCompatible_of_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {R : ResidueSpec m T C} (hres : M.HasResidues R) :
    R.RowCompatible I := by
  intro c
  calc
    (I.colorDegree c : ZMod m)
        = ((∑ σ : Fin T, M.val c σ : Nat) : ZMod m) := by
            rw [M.row_sum c]
    _ = ∑ σ : Fin T, (M.val c σ : ZMod m) := by
            simp
    _ = ∑ σ : Fin T, R.target c σ := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            exact hres c σ

theorem colCompatible_of_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {R : ResidueSpec m T C} (hres : M.HasResidues R) :
    R.ColCompatible I := by
  intro σ
  calc
    (Fintype.card X : ZMod m)
        = ((∑ c : C, M.val c σ : Nat) : ZMod m) := by
            rw [M.col_sum σ]
    _ = ∑ c : C, (M.val c σ : ZMod m) := by
            simp
    _ = ∑ c : C, R.target c σ := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hres c σ

end CountMatrix

def FeasibleWithResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∃ M : CountMatrix I, M.HallCuts ∧ M.HasResidues R

namespace FeasibleWithResidues

theorem rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.RowCompatible I := by
  rcases hFeasible with ⟨M, _hHall, hResidues⟩
  exact M.rowCompatible_of_hasResidues hResidues

theorem colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.ColCompatible I := by
  rcases hFeasible with ⟨M, _hHall, hResidues⟩
  exact M.colCompatible_of_hasResidues hResidues

theorem compatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.RowCompatible I ∧ R.ColCompatible I :=
  ⟨hFeasible.rowCompatible, hFeasible.colCompatible⟩

end FeasibleWithResidues

/-- A symboling assigns each active set bijectively to the `T` active symbols. -/
structure Symboling {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence T X C) where
  equiv : ∀ x : X, Fin T ≃ {c : C // c ∈ I.active x}

namespace Symboling

def color {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C] {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (σ : Fin T) : C :=
  (Φ.equiv x σ).1

def count {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (c : C) (σ : Fin T) : Nat :=
  ∑ x : X, if Φ.color x σ = c then 1 else 0

def symbolsIn {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (x : X) (U : Finset C) (S : Finset (Fin T)) :
    Finset (Fin T) :=
  S.filter (fun σ => Φ.color x σ ∈ U)

theorem sum_color_eq_indicator {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (c : C) :
    (∑ σ : Fin T, if Φ.color x σ = c then (1 : Nat) else 0)
      = if c ∈ I.active x then 1 else 0 := by
  classical
  by_cases hc : c ∈ I.active x
  · let σ0 : Fin T := (Φ.equiv x).symm ⟨c, hc⟩
    have hσ0 : Φ.color x σ0 = c := by
      exact congrArg Subtype.val ((Φ.equiv x).apply_symm_apply ⟨c, hc⟩)
    rw [Finset.sum_eq_single σ0]
    · simp [hσ0, hc]
    · intro σ _hσ hne
      have hneq : Φ.color x σ ≠ c := by
        intro hcol
        have hsub : Φ.equiv x σ = ⟨c, hc⟩ := by
          exact Subtype.ext hcol
        have hσeq : σ = σ0 := by
          simpa [σ0] using congrArg (Φ.equiv x).symm hsub
        exact hne hσeq
      simp [hneq]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ σ0))
  · have hneq : ∀ σ : Fin T, Φ.color x σ ≠ c := by
      intro σ hcol
      have hmem : Φ.color x σ ∈ I.active x := (Φ.equiv x σ).2
      exact hc (by
        rw [← hcol]
        exact hmem)
    simp [hc, hneq]

theorem sum_color_column_eq_one {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (σ : Fin T) :
    (∑ c : C, if Φ.color x σ = c then (1 : Nat) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single (Φ.color x σ)]
  · simp
  · intro c _hc hne
    have hneq : Φ.color x σ ≠ c := by
      intro h
      exact hne h.symm
    simp [hneq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (Φ.color x σ)))

theorem count_row_sum {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    ∀ c : C, (∑ σ : Fin T, Φ.count c σ) = I.colorDegree c := by
  classical
  intro c
  calc
    (∑ σ : Fin T, Φ.count c σ)
        = ∑ σ : Fin T, ∑ x : X,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            simp [count]
    _ = ∑ x : X, ∑ σ : Fin T,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact Φ.sum_color_eq_indicator x c
    _ = I.colorDegree c := by
            rw [Incidence.colorDegree, Finset.card_filter]

theorem count_col_sum {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    ∀ σ : Fin T, (∑ c : C, Φ.count c σ) = Fintype.card X := by
  classical
  intro σ
  calc
    (∑ c : C, Φ.count c σ)
        = ∑ c : C, ∑ x : X,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            simp [count]
    _ = ∑ x : X, ∑ c : C,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ _x : X, 1 := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact Φ.sum_color_column_eq_one x σ
    _ = Fintype.card X := by
            simp

theorem local_cut_count_eq_symbolsIn_card {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
      = (Φ.symbolsIn x U S).card := by
  classical
  calc
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
        = ∑ σ ∈ S, ∑ c ∈ U,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ S, if Φ.color x σ ∈ U then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            by_cases hmem : Φ.color x σ ∈ U
            · rw [Finset.sum_eq_single (Φ.color x σ)]
              · simp [hmem]
              · intro c _hc hne
                have hneq : Φ.color x σ ≠ c := by
                  intro h
                  exact hne h.symm
                simp [hneq]
              · intro hnot
                exact False.elim (hnot hmem)
            · have hneq : ∀ c ∈ U, Φ.color x σ ≠ c := by
                intro c hc h
                exact hmem (by rw [h]; exact hc)
              simp [hmem]
    _ = (Φ.symbolsIn x U S).card := by
            rw [symbolsIn]
            exact (Finset.card_filter (fun σ => Φ.color x σ ∈ U) S).symm

theorem symbolsIn_card_le_S {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (Φ.symbolsIn x U S).card ≤ S.card :=
  Finset.card_filter_le S (fun σ => Φ.color x σ ∈ U)

theorem symbolsIn_card_le_active_inter {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (Φ.symbolsIn x U S).card ≤ (I.active x ∩ U).card := by
  classical
  let imageSet : Finset C := (Φ.symbolsIn x U S).image (Φ.color x)
  have hcardImage :
      imageSet.card = (Φ.symbolsIn x U S).card := by
    apply Finset.card_image_of_injOn
    intro σ hσ τ hτ hcolor
    have hsub : Φ.equiv x σ = Φ.equiv x τ := by
      exact Subtype.ext hcolor
    exact (Φ.equiv x).injective hsub
  have hsubset : imageSet ⊆ I.active x ∩ U := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨σ, hσ, rfl⟩
    have hactive : Φ.color x σ ∈ I.active x := (Φ.equiv x σ).2
    have hU : Φ.color x σ ∈ U := by
      exact (Finset.mem_filter.mp hσ).2
    exact Finset.mem_inter.mpr ⟨hactive, hU⟩
  calc
    (Φ.symbolsIn x U S).card = imageSet.card := hcardImage.symm
    _ ≤ (I.active x ∩ U).card := Finset.card_le_card hsubset

theorem local_cut_count_le_cap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
      ≤ min ((I.active x ∩ U).card) S.card := by
  rw [Φ.local_cut_count_eq_symbolsIn_card x U S]
  exact le_min (Φ.symbolsIn_card_le_active_inter x U S)
    (Φ.symbolsIn_card_le_S x U S)

def toCountMatrix {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) : CountMatrix I where
  val := Φ.count
  row_sum := Φ.count_row_sum
  col_sum := Φ.count_col_sum

def Realizes {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (M : C → Fin T → Nat) : Prop :=
  ∀ c σ, Φ.count c σ = M c σ

def HasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (Φ.count c σ : ZMod m) = R.target c σ

theorem hasResidues_of_realizes {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I} {M : CountMatrix I}
    {R : ResidueSpec m T C}
    (hreal : Φ.Realizes M.val) (hres : M.HasResidues R) :
    Φ.HasResidues R := by
  intro c σ
  rw [hreal c σ]
  exact hres c σ

theorem toCountMatrix_hallCuts {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    (Φ.toCountMatrix).HallCuts := by
  classical
  intro U S
  calc
    (Φ.toCountMatrix).cutMass U S
        = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            change (∑ c ∈ U, ∑ σ ∈ S, ∑ x : X,
                if Φ.color x σ = c then (1 : Nat) else 0)
              = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
                if Φ.color x σ = c then (1 : Nat) else 0
            calc
              (∑ c ∈ U, ∑ σ ∈ S, ∑ x : X,
                  if Φ.color x σ = c then (1 : Nat) else 0)
                  = ∑ c ∈ U, ∑ x : X, ∑ σ ∈ S,
                      if Φ.color x σ = c then (1 : Nat) else 0 := by
                      apply Finset.sum_congr rfl
                      intro c _hc
                      rw [Finset.sum_comm]
              _ = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
                    if Φ.color x σ = c then (1 : Nat) else 0 := by
                    rw [Finset.sum_comm]
    _ ≤ ∑ x : X, min ((I.active x ∩ U).card) S.card := by
            apply Finset.sum_le_sum
            intro x _hx
            exact Φ.local_cut_count_le_cap x U S
    _ = I.cutCap U S := by
            rfl

end Symboling

def SymbolingWithResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∃ Φ : Symboling I, Φ.HasResidues R

universe uX uC

/--
The Hoffman/Hall realization theorem needed by the active branch.

This is intentionally isolated from rounding and residue arithmetic: once a
count matrix has the forced row/column sums and Hall cuts, it can be realized by
a symboling.
-/
def HallRealizationGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ Φ : Symboling I, Φ.Realizes M.val

theorem hallRealization_zero {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 0 X C) (M : CountMatrix I) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  refine ⟨{
    equiv := fun x => ?_
  }, ?_⟩
  · refine {
      toFun := fun σ => Fin.elim0 σ
      invFun := fun c => ?_
      left_inv := fun σ => Fin.elim0 σ
      right_inv := fun c => ?_
    }
    · have hEmpty : I.active x = ∅ :=
        Finset.card_eq_zero.mp (I.active_card x)
      exact False.elim (by
        have hc : c.1 ∈ (∅ : Finset C) := by
          simpa [hEmpty] using c.2
        simp at hc)
    · have hEmpty : I.active x = ∅ :=
        Finset.card_eq_zero.mp (I.active_card x)
      exact False.elim (by
        have hc : c.1 ∈ (∅ : Finset C) := by
          simpa [hEmpty] using c.2
        simp at hc)
  · intro c σ
    exact Fin.elim0 σ

theorem hallRealization_one {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (0 : Fin 1) with
    ⟨f, hfActive⟩
  let chosen : X → C := fun x => (f.symm x).1
  have hChosenActive : ∀ x : X, chosen x ∈ I.active x := by
    intro x
    simpa [chosen] using hfActive (f.symm x)
  let Φ : Symboling I := {
    equiv := fun x => {
      toFun := fun _σ => ⟨chosen x, hChosenActive x⟩
      invFun := fun _c => 0
      left_inv := by
        intro σ
        fin_cases σ
        rfl
      right_inv := by
        intro c
        apply Subtype.ext
        exact I.eq_of_mem_of_active_card_one (hChosenActive x) c.2
    }
  }
  refine ⟨Φ, ?_⟩
  intro c σ
  fin_cases σ
  calc
    Φ.count c 0
        = ∑ x : X, if chosen x = c then 1 else 0 := by
            unfold Symboling.count
            apply Finset.sum_congr rfl
            intro x _hx
            simp [Symboling.color, Φ, chosen]
    _ = ∑ q : Sigma fun c : C => Fin (M.val c (0 : Fin 1)),
          if q.1 = c then 1 else 0 := by
            exact Fintype.sum_equiv f.symm
              (fun x : X => if chosen x = c then (1 : Nat) else 0)
              (fun q : Sigma fun c : C => Fin (M.val c (0 : Fin 1)) =>
                if q.1 = c then (1 : Nat) else 0)
              (by
                intro x
                simp [chosen])
    _ = M.val c 0 := by
            rw [Fintype.sum_sigma]
            calc
              (∑ x : C, ∑ q : Fin (M.val x (0 : Fin 1)),
                  if x = c then (1 : Nat) else 0)
                  = ∑ x : C, if x = c then M.val x 0 else 0 := by
                      apply Finset.sum_congr rfl
                      intro x _hx
                      by_cases hxc : x = c <;> simp [hxc]
              _ = M.val c 0 := by
                      simp

theorem symbolingWithResidues_of_feasible_and_realization
    (hRealize : HallRealizationGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R := by
  rcases hFeasible with ⟨M, hHall, hResidues⟩
  rcases @hRealize T X C _ _ _ _ I M hHall with ⟨Φ, hRealizes⟩
  exact ⟨Φ, Φ.hasResidues_of_realizes hRealizes hResidues⟩

theorem feasibleWithResidues_of_symbolingWithResidues
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    FeasibleWithResidues I R := by
  rcases hSymboling with ⟨Φ, hResidues⟩
  exact ⟨Φ.toCountMatrix, Φ.toCountMatrix_hallCuts, hResidues⟩

namespace SymbolingWithResidues

theorem feasible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    FeasibleWithResidues I R :=
  feasibleWithResidues_of_symbolingWithResidues hSymboling

theorem rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.RowCompatible I :=
  hSymboling.feasible.rowCompatible

theorem colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.ColCompatible I :=
  hSymboling.feasible.colCompatible

theorem compatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.RowCompatible I ∧ R.ColCompatible I :=
  hSymboling.feasible.compatible

end SymbolingWithResidues

end ActiveHall
end RoundComposite
