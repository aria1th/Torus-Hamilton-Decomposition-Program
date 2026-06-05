import EvenV11.Basic

namespace EvenV11
namespace TypeA

def chainParent {n : Nat} (edge : Fin n) : Fin (n + 1) :=
  ⟨edge.val, Nat.lt_trans edge.isLt (Nat.lt_succ_self n)⟩

def chainChild {n : Nat} (edge : Fin n) : Fin (n + 1) :=
  ⟨edge.val + 1, Nat.succ_lt_succ edge.isLt⟩

def chainDescendantCut {n : Nat}
    (cut : Fin n) (vertex : Fin (n + 1)) : Prop :=
  cut.val < vertex.val

def chainDescendantCutDecidable {n : Nat} :
    (cut : Fin n) → (vertex : Fin (n + 1)) →
      Decidable (chainDescendantCut cut vertex) :=
  fun cut vertex => inferInstanceAs (Decidable (cut.val < vertex.val))

def chainCutIndicator {n : Nat}
    (cut : Fin n) (vertex : Fin (n + 1)) : Int :=
  if cut.val < vertex.val then 1 else 0

def chainIncidence {n : Nat} (cut edge : Fin n) : Int :=
  chainCutIndicator cut (chainChild edge) -
    chainCutIndicator cut (chainParent edge)

def parentMapCutIndicator {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (cut : Edge) (vertex : Vertex) : Int :=
  if descendantCut cut vertex then 1 else 0

def parentMapIncidence {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex) (cut edge : Edge) : Int :=
  parentMapCutIndicator descendantCut cut (child edge) -
    parentMapCutIndicator descendantCut cut (parent edge)

def descendantCell {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop) (cut : Edge) :
    Set Vertex :=
  { vertex | descendantCut cut vertex }

structure ParentMapBoundary {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    (parent child : Edge → Vertex) : Prop where
  child_mem : ∀ edge : Edge, descendantCut edge (child edge)
  parent_not_mem : ∀ edge : Edge, ¬ descendantCut edge (parent edge)
  other_iff :
    ∀ cut edge : Edge, cut ≠ edge →
      (descendantCut cut (child edge) ↔ descendantCut cut (parent edge))

theorem chainDescendantCut_parent
    {n : Nat} (cut edge : Fin n) :
    chainDescendantCut cut (chainParent edge) ↔ cut.val < edge.val := by
  rfl

theorem chainDescendantCut_child
    {n : Nat} (cut edge : Fin n) :
    chainDescendantCut cut (chainChild edge) ↔ cut.val ≤ edge.val := by
  dsimp [chainDescendantCut, chainChild]
  exact Nat.lt_succ_iff

theorem chainIncidence_eq_ite
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge = if cut = edge then (1 : Int) else 0 := by
  by_cases hlt : cut.val < edge.val
  · have hchild : cut.val < (chainChild edge).val := by
      dsimp [chainChild]
      omega
    have hparent : cut.val < (chainParent edge).val := by
      exact hlt
    have hne : cut ≠ edge := by
      intro h
      have hval : cut.val = edge.val := congrArg Fin.val h
      omega
    simp [chainIncidence, chainCutIndicator, hchild, hparent, hne]
  · by_cases heq : cut = edge
    · subst cut
      have hchild : edge.val < (chainChild edge).val := by
        dsimp [chainChild]
        omega
      have hparent : ¬ edge.val < (chainParent edge).val := by
        dsimp [chainParent]
        omega
      simp [chainIncidence, chainCutIndicator, hchild, hparent]
    · have hgt : edge.val < cut.val := by
        have hvalne : cut.val ≠ edge.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      have hchild : ¬ cut.val < (chainChild edge).val := by
        intro h
        dsimp [chainChild] at h
        omega
      have hparent : ¬ cut.val < (chainParent edge).val := by
        intro h
        dsimp [chainParent] at h
        omega
      simp [chainIncidence, chainCutIndicator, hchild, hparent, heq]

theorem chainIncidence_self {n : Nat} (edge : Fin n) :
    chainIncidence edge edge = 1 := by
  rw [chainIncidence_eq_ite]
  simp

theorem chainIncidence_ne {n : Nat} {cut edge : Fin n}
    (hne : cut ≠ edge) :
    chainIncidence cut edge = 0 := by
  rw [chainIncidence_eq_ite]
  simp [hne]

theorem parentMapIncidence_eq_ite
    {Vertex Edge : Type*} [DecidableEq Edge]
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    parentMapIncidence descendantCut parent child cut edge =
      if cut = edge then (1 : Int) else 0 := by
  by_cases hcut : cut = edge
  · subst cut
    simp [parentMapIncidence, parentMapCutIndicator,
      hboundary.child_mem edge, hboundary.parent_not_mem edge]
  · have hiff := hboundary.other_iff cut edge hcut
    by_cases hchild : descendantCut cut (child edge)
    · have hparent : descendantCut cut (parent edge) := hiff.mp hchild
      simp [parentMapIncidence, parentMapCutIndicator, hcut, hchild, hparent]
    · have hparent : ¬ descendantCut cut (parent edge) := by
        intro hparent
        exact hchild (hiff.mpr hparent)
      simp [parentMapIncidence, parentMapCutIndicator, hcut, hchild, hparent]

theorem parentMapIncidence_self
    {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    (edge : Edge) :
    parentMapIncidence descendantCut parent child edge edge = 1 := by
  simp [parentMapIncidence, parentMapCutIndicator,
    hboundary.child_mem edge, hboundary.parent_not_mem edge]

theorem parentMapIncidence_ne
    {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence descendantCut parent child cut edge = 0 := by
  have hiff := hboundary.other_iff cut edge hne
  by_cases hchild : descendantCut cut (child edge)
  · have hparent : descendantCut cut (parent edge) := hiff.mp hchild
    simp [parentMapIncidence, parentMapCutIndicator, hchild, hparent]
  · have hparent : ¬ descendantCut cut (parent edge) := by
      intro hparent
      exact hchild (hiff.mpr hparent)
    simp [parentMapIncidence, parentMapCutIndicator, hchild, hparent]

theorem parentMapBoundary_child_iff
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    descendantCut cut (child edge) ↔
      cut = edge ∨ descendantCut cut (parent edge) := by
  by_cases hcut : cut = edge
  · subst cut
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact hboundary.child_mem edge
  · constructor
    · intro hchild
      exact Or.inr ((hboundary.other_iff cut edge hcut).mp hchild)
    · intro h
      rcases h with h | hparent
      · exact False.elim (hcut h)
      · exact (hboundary.other_iff cut edge hcut).mpr hparent

theorem parentMapBoundary_parent_iff
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    descendantCut cut (parent edge) ↔
      cut ≠ edge ∧ descendantCut cut (child edge) := by
  by_cases hcut : cut = edge
  · subst cut
    constructor
    · intro hparent
      exact False.elim (hboundary.parent_not_mem edge hparent)
    · intro h
      exact False.elim (h.1 rfl)
  · constructor
    · intro hparent
      exact ⟨hcut, (hboundary.other_iff cut edge hcut).mpr hparent⟩
    · intro h
      exact (hboundary.other_iff cut edge hcut).mp h.2

theorem parentMapBoundary_child_mem_descendantCell_iff
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    child edge ∈ descendantCell descendantCut cut ↔
      cut = edge ∨ parent edge ∈ descendantCell descendantCut cut := by
  exact parentMapBoundary_child_iff hboundary cut edge

theorem parentMapBoundary_parent_mem_descendantCell_iff
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    parent edge ∈ descendantCell descendantCut cut ↔
      cut ≠ edge ∧ child edge ∈ descendantCell descendantCut cut := by
  exact parentMapBoundary_parent_iff hboundary cut edge

theorem parentMapBoundary_child_mem_self_descendantCell
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (edge : Edge) :
    child edge ∈ descendantCell descendantCut edge :=
  hboundary.child_mem edge

theorem parentMapBoundary_parent_not_mem_self_descendantCell
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (edge : Edge) :
    parent edge ∉ descendantCell descendantCut edge :=
  hboundary.parent_not_mem edge

structure ParentMapIncidenceCertificate
    {Vertex Edge : Type*} [DecidableEq Edge]
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex) where
  boundary : ParentMapBoundary descendantCut parent child
  incidence_eq_ite :
    ∀ cut edge : Edge,
      parentMapIncidence descendantCut parent child cut edge =
        if cut = edge then (1 : Int) else 0
  incidence_self :
    ∀ edge : Edge,
      parentMapIncidence descendantCut parent child edge edge = 1
  incidence_ne :
    ∀ {cut edge : Edge}, cut ≠ edge →
      parentMapIncidence descendantCut parent child cut edge = 0

def parentMapIncidenceCertificate_of_boundary
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child) :
    ParentMapIncidenceCertificate descendantCut parent child where
  boundary := hboundary
  incidence_eq_ite :=
    parentMapIncidence_eq_ite descendantCut parent child hboundary
  incidence_self :=
    parentMapIncidence_self descendantCut parent child hboundary
  incidence_ne :=
    parentMapIncidence_ne descendantCut parent child hboundary

theorem parentMapIncidenceCertificate_boundary
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child) :
    ParentMapBoundary descendantCut parent child :=
  C.boundary

theorem parentMapIncidenceCertificate_eq_ite
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    (cut edge : Edge) :
    parentMapIncidence descendantCut parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  C.incidence_eq_ite cut edge

theorem parentMapIncidenceCertificate_self
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    (edge : Edge) :
    parentMapIncidence descendantCut parent child edge edge = 1 :=
  C.incidence_self edge

theorem parentMapIncidenceCertificate_ne
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence descendantCut parent child cut edge = 0 :=
  C.incidence_ne hne

theorem chainParentMapBoundary {n : Nat} :
    ParentMapBoundary
      (@chainDescendantCut n) (@chainParent n) (@chainChild n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    exact (chainDescendantCut_child edge edge).mpr (Nat.le_refl edge.val)
  · intro edge hmem
    have hlt : edge.val < edge.val :=
      (chainDescendantCut_parent edge edge).mp hmem
    exact (Nat.lt_irrefl edge.val) hlt
  · intro cut edge hne
    rw [chainDescendantCut_child, chainDescendantCut_parent]
    constructor
    · intro hle
      have hvalne : cut.val ≠ edge.val := by
        intro hval
        exact hne (Fin.ext hval)
      omega
    · intro hlt
      exact Nat.le_of_lt hlt

theorem chainIncidence_eq_parentMapIncidence
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge =
      @parentMapIncidence (Fin (n + 1)) (Fin n)
        (@chainDescendantCut n) (@chainDescendantCutDecidable n)
        (@chainParent n) (@chainChild n) cut edge := by
  rfl

theorem chainIncidence_eq_ite_from_parentMapBoundary
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge = if cut = edge then (1 : Int) else 0 := by
  rw [chainIncidence_eq_parentMapIncidence]
  exact @parentMapIncidence_eq_ite (Fin (n + 1)) (Fin n)
    inferInstance (@chainDescendantCut n) (@chainDescendantCutDecidable n)
    (@chainParent n) (@chainChild n) chainParentMapBoundary cut edge

end TypeA

export TypeA
  (chainParent chainChild chainDescendantCut chainDescendantCutDecidable
   chainCutIndicator
   chainIncidence parentMapCutIndicator parentMapIncidence
   descendantCell
   ParentMapBoundary
   chainDescendantCut_parent chainDescendantCut_child
   chainIncidence_eq_ite chainIncidence_self chainIncidence_ne
   parentMapIncidence_eq_ite parentMapIncidence_self
   parentMapIncidence_ne
   parentMapBoundary_child_iff
   parentMapBoundary_parent_iff
   parentMapBoundary_child_mem_descendantCell_iff
   parentMapBoundary_parent_mem_descendantCell_iff
   parentMapBoundary_child_mem_self_descendantCell
   parentMapBoundary_parent_not_mem_self_descendantCell
   ParentMapIncidenceCertificate
   parentMapIncidenceCertificate_of_boundary
   parentMapIncidenceCertificate_boundary
   parentMapIncidenceCertificate_eq_ite
   parentMapIncidenceCertificate_self
   parentMapIncidenceCertificate_ne
   chainParentMapBoundary
   chainIncidence_eq_parentMapIncidence
   chainIncidence_eq_ite_from_parentMapBoundary)

end EvenV11
