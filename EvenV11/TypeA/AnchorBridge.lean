import EvenV11.FiniteAuditBridge
import EvenV11.TypeA.CoforestExample

namespace EvenV11
namespace TypeA

def coforestRootedBoundaryAudit
    {Vertex Edge : Type*}
    (desc : Edge → Vertex → Prop)
    (parentStep : Vertex → Vertex)
    (parent child : Edge → Vertex) : Prop :=
  ParentMapBoundary desc parent child ∧
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child

def coforestIncidenceAudit
    {Vertex Edge : Type*} [DecidableEq Edge]
    (desc : Edge → Vertex → Prop)
    (dec : (cut : Edge) → (vertex : Vertex) → Decidable (desc cut vertex))
    (parent child : Edge → Vertex) : Prop :=
  ∀ cut edge : Edge,
    @parentMapIncidence Vertex Edge desc dec parent child cut edge =
      if cut = edge then (1 : Int) else 0

theorem coforestRootedBoundaryAudit_direct
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child) :
    ParentMapBoundary desc parent child :=
  h.1

theorem coforestRootedBoundaryAudit_iterated
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  h.2

theorem coforestRootedBoundaryAudit_direct_child_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    desc cut (child edge) ↔ cut = edge ∨ desc cut (parent edge) :=
  parentMapBoundary_child_iff
    (coforestRootedBoundaryAudit_direct h) cut edge

theorem coforestRootedBoundaryAudit_direct_parent_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    desc cut (parent edge) ↔ cut ≠ edge ∧ desc cut (child edge) :=
  parentMapBoundary_parent_iff
    (coforestRootedBoundaryAudit_direct h) cut edge

theorem coforestRootedBoundaryAudit_iterated_child_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    iteratedParentDescendantCut parentStep child cut (child edge) ↔
      cut = edge ∨
        iteratedParentDescendantCut parentStep child cut (parent edge) :=
  parentMapBoundary_child_iff
    (coforestRootedBoundaryAudit_iterated h) cut edge

theorem coforestRootedBoundaryAudit_iterated_parent_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    iteratedParentDescendantCut parentStep child cut (parent edge) ↔
      cut ≠ edge ∧
        iteratedParentDescendantCut parentStep child cut (child edge) :=
  parentMapBoundary_parent_iff
    (coforestRootedBoundaryAudit_iterated h) cut edge

theorem coforestRootedBoundaryAudit_direct_child_mem_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    child edge ∈ descendantCell desc cut ↔
      cut = edge ∨ parent edge ∈ descendantCell desc cut :=
  parentMapBoundary_child_mem_descendantCell_iff
    (coforestRootedBoundaryAudit_direct h) cut edge

theorem coforestRootedBoundaryAudit_direct_parent_mem_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∈ descendantCell desc cut ↔
      cut ≠ edge ∧ child edge ∈ descendantCell desc cut :=
  parentMapBoundary_parent_mem_descendantCell_iff
    (coforestRootedBoundaryAudit_direct h) cut edge

theorem coforestRootedBoundaryAudit_iterated_child_mem_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    child edge ∈
        descendantCell (iteratedParentDescendantCut parentStep child) cut ↔
      cut = edge ∨
        parent edge ∈
          descendantCell (iteratedParentDescendantCut parentStep child) cut :=
  parentMapBoundary_child_mem_descendantCell_iff
    (coforestRootedBoundaryAudit_iterated h) cut edge

theorem coforestRootedBoundaryAudit_iterated_parent_mem_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∈
        descendantCell (iteratedParentDescendantCut parentStep child) cut ↔
      cut ≠ edge ∧
        child edge ∈
          descendantCell (iteratedParentDescendantCut parentStep child) cut :=
  parentMapBoundary_parent_mem_descendantCell_iff
    (coforestRootedBoundaryAudit_iterated h) cut edge

theorem coforestIncidenceAudit_self
    {Vertex Edge : Type*} [DecidableEq Edge]
    {desc : Edge → Vertex → Prop}
    {dec : (cut : Edge) → (vertex : Vertex) → Decidable (desc cut vertex)}
    {parent child : Edge → Vertex}
    (h : coforestIncidenceAudit desc dec parent child)
    (edge : Edge) :
    @parentMapIncidence Vertex Edge desc dec parent child edge edge = 1 := by
  simpa using h edge edge

theorem coforestIncidenceAudit_ne
    {Vertex Edge : Type*} [DecidableEq Edge]
    {desc : Edge → Vertex → Prop}
    {dec : (cut : Edge) → (vertex : Vertex) → Decidable (desc cut vertex)}
    {parent child : Edge → Vertex}
    (h : coforestIncidenceAudit desc dec parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    @parentMapIncidence Vertex Edge desc dec parent child cut edge = 0 := by
  simpa [hne] using h cut edge

def d5CoforestRowsRootedAudit : Prop :=
  coforestRootedBoundaryAudit
    d5Stage1CoforestDescendantCut
    d5Stage1CoforestParentStep
    d5Stage1CoforestParent
    d5Stage1CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage1PairCoforestDescendantCut
    d5Stage1PairCoforestParentStep
    d5Stage1PairCoforestParent
    d5Stage1PairCoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage2TripleColor0CoforestDescendantCut
    d5Stage2TripleColor0CoforestParentStep
    d5Stage2TripleColor0CoforestParent
    d5Stage2TripleColor0CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage2TripleColor43CoforestDescendantCut
    d5Stage2TripleColor43CoforestParentStep
    d5Stage2TripleColor43CoforestParent
    d5Stage2TripleColor43CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage2PairColor1CoforestDescendantCut
    d5Stage2PairColor1CoforestParentStep
    d5Stage2PairColor1CoforestParent
    d5Stage2PairColor1CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage2PairColor2CoforestDescendantCut
    d5Stage2PairColor2CoforestParentStep
    d5Stage2PairColor2CoforestParent
    d5Stage2PairColor2CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage3FinalPairColor0CoforestDescendantCut
    d5Stage3FinalPairColor0CoforestParentStep
    d5Stage3FinalPairColor0CoforestParent
    d5Stage3FinalPairColor0CoforestChild ∧
  coforestRootedBoundaryAudit
    d5Stage3FinalPairColor2CoforestDescendantCut
    d5Stage3FinalPairColor2CoforestParentStep
    d5Stage3FinalPairColor2CoforestParent
    d5Stage3FinalPairColor2CoforestChild

def d5CoforestRowsIncidenceAudit : Prop :=
  coforestIncidenceAudit
    d5Stage1CoforestDescendantCut
    d5Stage1CoforestDescendantCutDecidable
    d5Stage1CoforestParent
    d5Stage1CoforestChild ∧
  coforestIncidenceAudit
    d5Stage1PairCoforestDescendantCut
    d5Stage1PairCoforestDescendantCutDecidable
    d5Stage1PairCoforestParent
    d5Stage1PairCoforestChild ∧
  coforestIncidenceAudit
    d5Stage2TripleColor0CoforestDescendantCut
    d5Stage2TripleColor0CoforestDescendantCutDecidable
    d5Stage2TripleColor0CoforestParent
    d5Stage2TripleColor0CoforestChild ∧
  coforestIncidenceAudit
    d5Stage2TripleColor43CoforestDescendantCut
    d5Stage2TripleColor43CoforestDescendantCutDecidable
    d5Stage2TripleColor43CoforestParent
    d5Stage2TripleColor43CoforestChild ∧
  coforestIncidenceAudit
    d5Stage2PairColor1CoforestDescendantCut
    d5Stage2PairColor1CoforestDescendantCutDecidable
    d5Stage2PairColor1CoforestParent
    d5Stage2PairColor1CoforestChild ∧
  coforestIncidenceAudit
    d5Stage2PairColor2CoforestDescendantCut
    d5Stage2PairColor2CoforestDescendantCutDecidable
    d5Stage2PairColor2CoforestParent
    d5Stage2PairColor2CoforestChild ∧
  coforestIncidenceAudit
    d5Stage3FinalPairColor0CoforestDescendantCut
    d5Stage3FinalPairColor0CoforestDescendantCutDecidable
    d5Stage3FinalPairColor0CoforestParent
    d5Stage3FinalPairColor0CoforestChild ∧
  coforestIncidenceAudit
    d5Stage3FinalPairColor2CoforestDescendantCut
    d5Stage3FinalPairColor2CoforestDescendantCutDecidable
    d5Stage3FinalPairColor2CoforestParent
    d5Stage3FinalPairColor2CoforestChild

def d7Stage12CoforestRowsRootedAudit : Prop :=
  coforestRootedBoundaryAudit
    d7Stage1TripleCoforestDescendantCut
    d7Stage1TripleCoforestParentStep
    d7Stage1TripleCoforestParent
    d7Stage1TripleCoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage1Pair34CoforestDescendantCut
    d7Stage1Pair34CoforestParentStep
    d7Stage1Pair34CoforestParent
    d7Stage1Pair34CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage1Pair56CoforestDescendantCut
    d7Stage1Pair56CoforestParentStep
    d7Stage1Pair56CoforestParent
    d7Stage1Pair56CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestParentStep
    d7Stage2CoforestParent
    d7Stage2CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage2Packet134Color34CoforestDescendantCut
    d7Stage2Packet134Color34CoforestParentStep
    d7Stage2Packet134Color34CoforestParent
    d7Stage2Packet134Color34CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage2Pair02Color0CoforestDescendantCut
    d7Stage2Pair02Color0CoforestParentStep
    d7Stage2Pair02Color0CoforestParent
    d7Stage2Pair02Color0CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage2Pair02Color2CoforestDescendantCut
    d7Stage2Pair02Color2CoforestParentStep
    d7Stage2Pair02Color2CoforestParent
    d7Stage2Pair02Color2CoforestChild ∧
  coforestRootedBoundaryAudit
    d7Stage2Pair56Color56CoforestDescendantCut
    d7Stage2Pair56Color56CoforestParentStep
    d7Stage2Pair56Color56CoforestParent
    d7Stage2Pair56Color56CoforestChild

def d7Stage12CoforestRowsIncidenceAudit : Prop :=
  coforestIncidenceAudit
    d7Stage1TripleCoforestDescendantCut
    d7Stage1TripleCoforestDescendantCutDecidable
    d7Stage1TripleCoforestParent
    d7Stage1TripleCoforestChild ∧
  coforestIncidenceAudit
    d7Stage1Pair34CoforestDescendantCut
    d7Stage1Pair34CoforestDescendantCutDecidable
    d7Stage1Pair34CoforestParent
    d7Stage1Pair34CoforestChild ∧
  coforestIncidenceAudit
    d7Stage1Pair56CoforestDescendantCut
    d7Stage1Pair56CoforestDescendantCutDecidable
    d7Stage1Pair56CoforestParent
    d7Stage1Pair56CoforestChild ∧
  coforestIncidenceAudit
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent
    d7Stage2CoforestChild ∧
  coforestIncidenceAudit
    d7Stage2Packet134Color34CoforestDescendantCut
    d7Stage2Packet134Color34CoforestDescendantCutDecidable
    d7Stage2Packet134Color34CoforestParent
    d7Stage2Packet134Color34CoforestChild ∧
  coforestIncidenceAudit
    d7Stage2Pair02Color0CoforestDescendantCut
    d7Stage2Pair02Color0CoforestDescendantCutDecidable
    d7Stage2Pair02Color0CoforestParent
    d7Stage2Pair02Color0CoforestChild ∧
  coforestIncidenceAudit
    d7Stage2Pair02Color2CoforestDescendantCut
    d7Stage2Pair02Color2CoforestDescendantCutDecidable
    d7Stage2Pair02Color2CoforestParent
    d7Stage2Pair02Color2CoforestChild ∧
  coforestIncidenceAudit
    d7Stage2Pair56Color56CoforestDescendantCut
    d7Stage2Pair56Color56CoforestDescendantCutDecidable
    d7Stage2Pair56Color56CoforestParent
    d7Stage2Pair56Color56CoforestChild

def v28FoldedTerminalInputAudit : Prop :=
  Shared.IsSingleCycleMap
    (wordEval (terminalSymbolStep 4)
      (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
  Shared.IsSingleCycleMap
    (wordEval (terminalSymbolStep 6)
      (FoldedSiteTrace.chronologicalTrace 6 foldedSites6))

def v28FiniteInputCoforestAudit : Prop :=
  FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true ∧
  v28FoldedTerminalInputAudit ∧
  d5CoforestRowsRootedAudit ∧
  d5CoforestRowsIncidenceAudit ∧
  d7Stage12CoforestRowsRootedAudit ∧
  d7Stage12CoforestRowsIncidenceAudit

theorem d5CoforestRowsRootedAudit_holds :
    d5CoforestRowsRootedAudit :=
  ⟨⟨d5Stage1CoforestParentMapBoundary,
      d5Stage1CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage1PairCoforestParentMapBoundary,
      d5Stage1PairCoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage2TripleColor0CoforestParentMapBoundary,
      d5Stage2TripleColor0CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage2TripleColor43CoforestParentMapBoundary,
      d5Stage2TripleColor43CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage2PairColor1CoforestParentMapBoundary,
      d5Stage2PairColor1CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage2PairColor2CoforestParentMapBoundary,
      d5Stage2PairColor2CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage3FinalPairColor0CoforestParentMapBoundary,
      d5Stage3FinalPairColor0CoforestIteratedParentMapBoundary⟩,
    ⟨d5Stage3FinalPairColor2CoforestParentMapBoundary,
      d5Stage3FinalPairColor2CoforestIteratedParentMapBoundary⟩⟩

theorem d5CoforestRowsIncidenceAudit_holds :
    d5CoforestRowsIncidenceAudit :=
  ⟨d5Stage1CoforestIncidence_eq_ite,
    d5Stage1PairCoforestIncidence_eq_ite,
    d5Stage2TripleColor0CoforestIncidence_eq_ite,
    d5Stage2TripleColor43CoforestIncidence_eq_ite,
    d5Stage2PairColor1CoforestIncidence_eq_ite,
    d5Stage2PairColor2CoforestIncidence_eq_ite,
    d5Stage3FinalPairColor0CoforestIncidence_eq_ite,
    d5Stage3FinalPairColor2CoforestIncidence_eq_ite⟩

theorem d7Stage12CoforestRowsRootedAudit_holds :
    d7Stage12CoforestRowsRootedAudit :=
  ⟨⟨d7Stage1TripleCoforestParentMapBoundary,
      d7Stage1TripleCoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage1Pair34CoforestParentMapBoundary,
      d7Stage1Pair34CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage1Pair56CoforestParentMapBoundary,
      d7Stage1Pair56CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage2CoforestParentMapBoundary,
      d7Stage2CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage2Packet134Color34CoforestParentMapBoundary,
      d7Stage2Packet134Color34CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage2Pair02Color0CoforestParentMapBoundary,
      d7Stage2Pair02Color0CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage2Pair02Color2CoforestParentMapBoundary,
      d7Stage2Pair02Color2CoforestIteratedParentMapBoundary⟩,
    ⟨d7Stage2Pair56Color56CoforestParentMapBoundary,
      d7Stage2Pair56Color56CoforestIteratedParentMapBoundary⟩⟩

theorem d7Stage12CoforestRowsIncidenceAudit_holds :
    d7Stage12CoforestRowsIncidenceAudit :=
  ⟨d7Stage1TripleCoforestIncidence_eq_ite,
    d7Stage1Pair34CoforestIncidence_eq_ite,
    d7Stage1Pair56CoforestIncidence_eq_ite,
    d7Stage2CoforestIncidence_eq_ite,
    d7Stage2Packet134Color34CoforestIncidence_eq_ite,
    d7Stage2Pair02Color0CoforestIncidence_eq_ite,
    d7Stage2Pair02Color2CoforestIncidence_eq_ite,
    d7Stage2Pair56Color56CoforestIncidence_eq_ite⟩

theorem v28FiniteInputCoforestAudit_holds :
    v28FiniteInputCoforestAudit :=
  ⟨EvenV11.v28FiniteInputBridgeAudit.1,
    ⟨EvenV11.v28FiniteInputBridgeAudit.2.1,
      EvenV11.v28FiniteInputBridgeAudit.2.2⟩,
    d5CoforestRowsRootedAudit_holds,
    d5CoforestRowsIncidenceAudit_holds,
    d7Stage12CoforestRowsRootedAudit_holds,
    d7Stage12CoforestRowsIncidenceAudit_holds⟩

end TypeA

export TypeA
  (coforestRootedBoundaryAudit_direct
   coforestRootedBoundaryAudit_iterated
   coforestRootedBoundaryAudit_direct_child_iff
   coforestRootedBoundaryAudit_direct_parent_iff
   coforestRootedBoundaryAudit_iterated_child_iff
   coforestRootedBoundaryAudit_iterated_parent_iff
   coforestRootedBoundaryAudit_direct_child_mem_cell_iff
   coforestRootedBoundaryAudit_direct_parent_mem_cell_iff
   coforestRootedBoundaryAudit_iterated_child_mem_cell_iff
   coforestRootedBoundaryAudit_iterated_parent_mem_cell_iff
   coforestIncidenceAudit_self
   coforestIncidenceAudit_ne
   d5CoforestRowsRootedAudit_holds
   d5CoforestRowsIncidenceAudit_holds
   d7Stage12CoforestRowsRootedAudit_holds
   d7Stage12CoforestRowsIncidenceAudit_holds
   v28FiniteInputCoforestAudit_holds)

end EvenV11
