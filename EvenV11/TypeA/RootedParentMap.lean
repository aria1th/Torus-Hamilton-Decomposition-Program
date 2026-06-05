import EvenV11.TypeA.TreeIncidence

namespace EvenV11
namespace TypeA

def iteratedParentDescendantCut {Vertex Edge : Type*}
    (parentStep : Vertex -> Vertex) (child : Edge -> Vertex)
    (cut : Edge) (vertex : Vertex) : Prop :=
  ∃ n : Nat, (parentStep^[n]) vertex = child cut

structure RootedParentMapData {Vertex Edge : Type*}
    (parentStep : Vertex -> Vertex)
    (parent child : Edge -> Vertex) : Prop where
  child_injective : Function.Injective child
  parentStep_child : ∀ edge : Edge, parentStep (child edge) = parent edge
  parent_not_descendant :
    ∀ edge : Edge,
      ¬ iteratedParentDescendantCut parentStep child edge (parent edge)

structure RankedRootedParentMapData {Vertex Edge : Type*}
    (parentStep : Vertex -> Vertex)
    (parent child : Edge -> Vertex) where
  child_injective : Function.Injective child
  parentStep_child : ∀ edge : Edge, parentStep (child edge) = parent edge
  rank : Vertex -> Nat
  parentStep_rank_le : ∀ vertex : Vertex, rank (parentStep vertex) <= rank vertex
  parent_child_rank_lt : ∀ edge : Edge, rank (parent edge) < rank (child edge)

theorem iteratedParentDescendantCut_child
    {Vertex Edge : Type*} (parentStep : Vertex -> Vertex)
    (child : Edge -> Vertex) (edge : Edge) :
    iteratedParentDescendantCut parentStep child edge (child edge) :=
  ⟨0, rfl⟩

theorem rank_iterate_parentStep_le
    {Vertex : Type*} (parentStep : Vertex -> Vertex) (rank : Vertex -> Nat)
    (hstep : ∀ vertex : Vertex, rank (parentStep vertex) <= rank vertex)
    (n : Nat) (vertex : Vertex) :
    rank ((parentStep^[n]) vertex) <= rank vertex := by
  induction n generalizing vertex with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact le_trans (ih (parentStep vertex)) (hstep vertex)

theorem rankedRootedParentMap_parent_not_descendant
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child)
    (edge : Edge) :
    ¬ iteratedParentDescendantCut parentStep child edge (parent edge) := by
  intro hdesc
  rcases hdesc with ⟨n, hn⟩
  have hle : hdata.rank (child edge) <= hdata.rank (parent edge) := by
    rw [← hn]
    exact rank_iterate_parentStep_le parentStep hdata.rank
      hdata.parentStep_rank_le n (parent edge)
  exact (Nat.not_lt_of_ge hle) (hdata.parent_child_rank_lt edge)

theorem rootedParentMapData_of_ranked
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child) :
    RootedParentMapData parentStep parent child where
  child_injective := hdata.child_injective
  parentStep_child := hdata.parentStep_child
  parent_not_descendant :=
    rankedRootedParentMap_parent_not_descendant hdata

theorem iteratedParentDescendantCut_child_of_parent
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge}
    (hparent :
      iteratedParentDescendantCut parentStep child cut (parent edge)) :
    iteratedParentDescendantCut parentStep child cut (child edge) := by
  rcases hparent with ⟨n, hn⟩
  refine ⟨n.succ, ?_⟩
  rw [Function.iterate_succ_apply, hdata.parentStep_child edge, hn]

theorem iteratedParentDescendantCut_parent_of_child_ne
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge)
    (hchild :
      iteratedParentDescendantCut parentStep child cut (child edge)) :
    iteratedParentDescendantCut parentStep child cut (parent edge) := by
  rcases hchild with ⟨n, hn⟩
  cases n with
  | zero =>
      have hedgeCut : edge = cut := hdata.child_injective hn
      exact False.elim (hne hedgeCut.symm)
  | succ n =>
      refine ⟨n, ?_⟩
      rw [Function.iterate_succ_apply, hdata.parentStep_child edge] at hn
      exact hn

theorem iteratedParentDescendantCut_child_iff_parent_of_ne
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    iteratedParentDescendantCut parentStep child cut (child edge) ↔
      iteratedParentDescendantCut parentStep child cut (parent edge) :=
  ⟨iteratedParentDescendantCut_parent_of_child_ne hdata hne,
    iteratedParentDescendantCut_child_of_parent hdata⟩

theorem rootedParentMapBoundary
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RootedParentMapData parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    exact iteratedParentDescendantCut_child parentStep child edge
  · intro edge
    exact hdata.parent_not_descendant edge
  · intro cut edge hne
    exact iteratedParentDescendantCut_child_iff_parent_of_ne hdata hne

theorem rootedParentMapIncidence_eq_ite
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  parentMapIncidence_eq_ite
    (iteratedParentDescendantCut parentStep child)
    parent child (rootedParentMapBoundary hdata) cut edge

theorem rootedParentMapIncidence_self
    {Vertex Edge : Type*}
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  parentMapIncidence_self
    (iteratedParentDescendantCut parentStep child)
    parent child (rootedParentMapBoundary hdata) edge

theorem rootedParentMapIncidence_ne
    {Vertex Edge : Type*}
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  parentMapIncidence_ne
    (iteratedParentDescendantCut parentStep child)
    parent child (rootedParentMapBoundary hdata) hne

theorem rankedRootedParentMapBoundary
    {Vertex Edge : Type*} {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  rootedParentMapBoundary (rootedParentMapData_of_ranked hdata)

theorem rankedRootedParentMapIncidence_eq_ite
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rootedParentMapIncidence_eq_ite
    (rootedParentMapData_of_ranked hdata) cut edge

theorem rankedRootedParentMapIncidence_self
    {Vertex Edge : Type*}
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  rootedParentMapIncidence_self
    (rootedParentMapData_of_ranked hdata) edge

theorem rankedRootedParentMapIncidence_ne
    {Vertex Edge : Type*}
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  rootedParentMapIncidence_ne
    (rootedParentMapData_of_ranked hdata) hne

structure RankedParentMapIncidenceCertificate
    {Vertex Edge : Type*} [DecidableEq Edge]
    (parentStep : Vertex -> Vertex)
    (parent child : Edge -> Vertex)
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)] where
  rankedData : RankedRootedParentMapData parentStep parent child
  boundary :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child
  incidence_eq_ite :
    ∀ cut edge : Edge,
      parentMapIncidence
          (iteratedParentDescendantCut parentStep child)
          parent child cut edge =
        if cut = edge then (1 : Int) else 0
  incidence_self :
    ∀ edge : Edge,
      parentMapIncidence
          (iteratedParentDescendantCut parentStep child)
          parent child edge edge = 1
  incidence_ne :
    ∀ {cut edge : Edge}, cut ≠ edge →
      parentMapIncidence
          (iteratedParentDescendantCut parentStep child)
          parent child cut edge = 0

def rankedParentMapIncidenceCertificate_of_ranked
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child) :
    RankedParentMapIncidenceCertificate parentStep parent child where
  rankedData := hdata
  boundary := rankedRootedParentMapBoundary hdata
  incidence_eq_ite :=
    rankedRootedParentMapIncidence_eq_ite hdata
  incidence_self :=
    rankedRootedParentMapIncidence_self hdata
  incidence_ne :=
    rankedRootedParentMapIncidence_ne hdata

theorem rankedParentMapIncidenceCertificate_boundary
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  C.boundary

theorem rankedParentMapIncidenceCertificate_eq_ite
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  C.incidence_eq_ite cut edge

theorem rankedParentMapIncidenceCertificate_self
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  C.incidence_self edge

theorem rankedParentMapIncidenceCertificate_ne
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex -> Vertex}
    {parent child : Edge -> Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  C.incidence_ne hne

end TypeA

export TypeA
  (iteratedParentDescendantCut
   RootedParentMapData
   RankedRootedParentMapData
   iteratedParentDescendantCut_child
   rank_iterate_parentStep_le
   rankedRootedParentMap_parent_not_descendant
   rootedParentMapData_of_ranked
   iteratedParentDescendantCut_child_of_parent
   iteratedParentDescendantCut_parent_of_child_ne
   iteratedParentDescendantCut_child_iff_parent_of_ne
   rootedParentMapBoundary
   rootedParentMapIncidence_eq_ite
   rootedParentMapIncidence_self
   rootedParentMapIncidence_ne
   rankedRootedParentMapBoundary
   rankedRootedParentMapIncidence_eq_ite
   rankedRootedParentMapIncidence_self
   rankedRootedParentMapIncidence_ne
   RankedParentMapIncidenceCertificate
   rankedParentMapIncidenceCertificate_of_ranked
   rankedParentMapIncidenceCertificate_boundary
   rankedParentMapIncidenceCertificate_eq_ite
   rankedParentMapIncidenceCertificate_self
   rankedParentMapIncidenceCertificate_ne)

end EvenV11
