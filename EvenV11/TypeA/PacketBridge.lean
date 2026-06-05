import EvenV11.TypeA.AnchorBridge

namespace EvenV11
namespace TypeA

/-!
# Type-A packet/cell bridge

This file turns the rooted coforest boundary audit into the set-level
transversal facts used by later packet-splice instantiations: the row edge
crosses exactly its own descendant cell and is off-crossing for every other
cell.
-/

structure CellTransversal {Vertex Edge : Type*}
    (cell : Edge → Set Vertex) (tail head : Edge → Vertex) : Prop where
  head_mem_self : ∀ edge : Edge, head edge ∈ cell edge
  tail_not_mem_self : ∀ edge : Edge, tail edge ∉ cell edge
  head_mem_iff :
    ∀ cut edge : Edge,
      head edge ∈ cell cut ↔ cut = edge ∨ tail edge ∈ cell cut
  tail_mem_iff :
    ∀ cut edge : Edge,
      tail edge ∈ cell cut ↔ cut ≠ edge ∧ head edge ∈ cell cut

theorem CellTransversal.crosses_iff
    {Vertex Edge : Type*} {cell : Edge → Set Vertex}
    {tail head : Edge → Vertex}
    (T : CellTransversal cell tail head) (cut edge : Edge) :
    tail edge ∉ cell cut ∧ head edge ∈ cell cut ↔ cut = edge := by
  constructor
  · intro h
    rcases (T.head_mem_iff cut edge).mp h.2 with hcut | htail
    · exact hcut
    · exact False.elim (h.1 htail)
  · intro hcut
    subst cut
    exact ⟨T.tail_not_mem_self edge, T.head_mem_self edge⟩

theorem CellTransversal.head_mem_iff_tail_mem_of_ne
    {Vertex Edge : Type*} {cell : Edge → Set Vertex}
    {tail head : Edge → Vertex}
    (T : CellTransversal cell tail head) {cut edge : Edge}
    (hne : cut ≠ edge) :
    head edge ∈ cell cut ↔ tail edge ∈ cell cut := by
  constructor
  · intro hhead
    rcases (T.head_mem_iff cut edge).mp hhead with hcut | htail
    · exact False.elim (hne hcut)
    · exact htail
  · intro htail
    exact (T.head_mem_iff cut edge).mpr (Or.inr htail)

theorem CellTransversal.tail_mem_iff_head_mem_of_ne
    {Vertex Edge : Type*} {cell : Edge → Set Vertex}
    {tail head : Edge → Vertex}
    (T : CellTransversal cell tail head) {cut edge : Edge}
    (hne : cut ≠ edge) :
    tail edge ∈ cell cut ↔ head edge ∈ cell cut :=
  (T.head_mem_iff_tail_mem_of_ne hne).symm

def parentMapBoundary_cellTransversal
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child) :
    CellTransversal (descendantCell descendantCut) parent child where
  head_mem_self :=
    parentMapBoundary_child_mem_self_descendantCell hboundary
  tail_not_mem_self :=
    parentMapBoundary_parent_not_mem_self_descendantCell hboundary
  head_mem_iff :=
    parentMapBoundary_child_mem_descendantCell_iff hboundary
  tail_mem_iff :=
    parentMapBoundary_parent_mem_descendantCell_iff hboundary

theorem parentMapBoundary_crosses_descendantCell_iff
    {Vertex Edge : Type*}
    {descendantCut : Edge → Vertex → Prop}
    {parent child : Edge → Vertex}
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    parent edge ∉ descendantCell descendantCut cut ∧
      child edge ∈ descendantCell descendantCut cut ↔
      cut = edge :=
  (parentMapBoundary_cellTransversal hboundary).crosses_iff cut edge

def coforestRootedBoundaryAudit_direct_cellTransversal
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child) :
    CellTransversal (descendantCell desc) parent child :=
  parentMapBoundary_cellTransversal (coforestRootedBoundaryAudit_direct h)

def coforestRootedBoundaryAudit_iterated_cellTransversal
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child) :
    CellTransversal
      (descendantCell (iteratedParentDescendantCut parentStep child))
      parent child :=
  parentMapBoundary_cellTransversal (coforestRootedBoundaryAudit_iterated h)

theorem coforestRootedBoundaryAudit_direct_crosses_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∉ descendantCell desc cut ∧
      child edge ∈ descendantCell desc cut ↔
      cut = edge :=
  (coforestRootedBoundaryAudit_direct_cellTransversal h).crosses_iff cut edge

theorem coforestRootedBoundaryAudit_iterated_crosses_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∉
        descendantCell (iteratedParentDescendantCut parentStep child) cut ∧
      child edge ∈
        descendantCell (iteratedParentDescendantCut parentStep child) cut ↔
      cut = edge :=
  (coforestRootedBoundaryAudit_iterated_cellTransversal h).crosses_iff cut edge

structure CoforestRowCellBridge {Vertex Edge : Type*}
    (desc : Edge → Vertex → Prop)
    (parentStep : Vertex → Vertex)
    (parent child : Edge → Vertex) : Prop where
  directCellTransversal :
    CellTransversal (descendantCell desc) parent child
  iteratedCellTransversal :
    CellTransversal
      (descendantCell (iteratedParentDescendantCut parentStep child))
      parent child

def coforestRowCellBridge_of_rootedBoundaryAudit
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (h : coforestRootedBoundaryAudit desc parentStep parent child) :
    CoforestRowCellBridge desc parentStep parent child where
  directCellTransversal :=
    coforestRootedBoundaryAudit_direct_cellTransversal h
  iteratedCellTransversal :=
    coforestRootedBoundaryAudit_iterated_cellTransversal h

theorem CoforestRowCellBridge.direct_crosses_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (B : CoforestRowCellBridge desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∉ descendantCell desc cut ∧
      child edge ∈ descendantCell desc cut ↔
      cut = edge :=
  B.directCellTransversal.crosses_iff cut edge

theorem CoforestRowCellBridge.iterated_crosses_cell_iff
    {Vertex Edge : Type*}
    {desc : Edge → Vertex → Prop}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (B : CoforestRowCellBridge desc parentStep parent child)
    (cut edge : Edge) :
    parent edge ∉
        descendantCell (iteratedParentDescendantCut parentStep child) cut ∧
      child edge ∈
        descendantCell (iteratedParentDescendantCut parentStep child) cut ↔
      cut = edge :=
  B.iteratedCellTransversal.crosses_iff cut edge

structure D5CoforestRowsCellBridgeAudit : Prop where
  stage1 :
    CoforestRowCellBridge
      d5Stage1CoforestDescendantCut
      d5Stage1CoforestParentStep
      d5Stage1CoforestParent
      d5Stage1CoforestChild
  stage1Pair :
    CoforestRowCellBridge
      d5Stage1PairCoforestDescendantCut
      d5Stage1PairCoforestParentStep
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild
  stage2TripleColor0 :
    CoforestRowCellBridge
      d5Stage2TripleColor0CoforestDescendantCut
      d5Stage2TripleColor0CoforestParentStep
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild
  stage2TripleColor43 :
    CoforestRowCellBridge
      d5Stage2TripleColor43CoforestDescendantCut
      d5Stage2TripleColor43CoforestParentStep
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild
  stage2PairColor1 :
    CoforestRowCellBridge
      d5Stage2PairColor1CoforestDescendantCut
      d5Stage2PairColor1CoforestParentStep
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild
  stage2PairColor2 :
    CoforestRowCellBridge
      d5Stage2PairColor2CoforestDescendantCut
      d5Stage2PairColor2CoforestParentStep
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild
  stage3FinalPairColor0 :
    CoforestRowCellBridge
      d5Stage3FinalPairColor0CoforestDescendantCut
      d5Stage3FinalPairColor0CoforestParentStep
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild
  stage3FinalPairColor2 :
    CoforestRowCellBridge
      d5Stage3FinalPairColor2CoforestDescendantCut
      d5Stage3FinalPairColor2CoforestParentStep
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild

theorem d5CoforestRowsCellBridgeAudit_holds :
    D5CoforestRowsCellBridgeAudit := by
  rcases d5CoforestRowsRootedAudit_holds with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact
    { stage1 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h1
      stage1Pair :=
        coforestRowCellBridge_of_rootedBoundaryAudit h2
      stage2TripleColor0 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h3
      stage2TripleColor43 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h4
      stage2PairColor1 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h5
      stage2PairColor2 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h6
      stage3FinalPairColor0 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h7
      stage3FinalPairColor2 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h8 }

structure D7Stage12CoforestRowsCellBridgeAudit : Prop where
  stage1Triple :
    CoforestRowCellBridge
      d7Stage1TripleCoforestDescendantCut
      d7Stage1TripleCoforestParentStep
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild
  stage1Pair34 :
    CoforestRowCellBridge
      d7Stage1Pair34CoforestDescendantCut
      d7Stage1Pair34CoforestParentStep
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild
  stage1Pair56 :
    CoforestRowCellBridge
      d7Stage1Pair56CoforestDescendantCut
      d7Stage1Pair56CoforestParentStep
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild
  stage2 :
    CoforestRowCellBridge
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestParentStep
      d7Stage2CoforestParent
      d7Stage2CoforestChild
  stage2Packet134Color34 :
    CoforestRowCellBridge
      d7Stage2Packet134Color34CoforestDescendantCut
      d7Stage2Packet134Color34CoforestParentStep
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild
  stage2Pair02Color0 :
    CoforestRowCellBridge
      d7Stage2Pair02Color0CoforestDescendantCut
      d7Stage2Pair02Color0CoforestParentStep
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild
  stage2Pair02Color2 :
    CoforestRowCellBridge
      d7Stage2Pair02Color2CoforestDescendantCut
      d7Stage2Pair02Color2CoforestParentStep
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild
  stage2Pair56Color56 :
    CoforestRowCellBridge
      d7Stage2Pair56Color56CoforestDescendantCut
      d7Stage2Pair56Color56CoforestParentStep
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild

theorem d7Stage12CoforestRowsCellBridgeAudit_holds :
    D7Stage12CoforestRowsCellBridgeAudit := by
  rcases d7Stage12CoforestRowsRootedAudit_holds with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact
    { stage1Triple :=
        coforestRowCellBridge_of_rootedBoundaryAudit h1
      stage1Pair34 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h2
      stage1Pair56 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h3
      stage2 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h4
      stage2Packet134Color34 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h5
      stage2Pair02Color0 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h6
      stage2Pair02Color2 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h7
      stage2Pair56Color56 :=
        coforestRowCellBridge_of_rootedBoundaryAudit h8 }

def v28FiniteInputPacketCellBridgeAudit : Prop :=
  D5CoforestRowsCellBridgeAudit ∧
    D7Stage12CoforestRowsCellBridgeAudit

theorem v28FiniteInputPacketCellBridgeAudit_holds :
    v28FiniteInputPacketCellBridgeAudit :=
  ⟨d5CoforestRowsCellBridgeAudit_holds,
    d7Stage12CoforestRowsCellBridgeAudit_holds⟩

def d5Stage1CoforestDirectCellTransversal :
    CellTransversal
      (descendantCell d5Stage1CoforestDescendantCut)
      d5Stage1CoforestParent
      d5Stage1CoforestChild :=
  parentMapBoundary_cellTransversal d5Stage1CoforestParentMapBoundary

def d5Stage1CoforestIteratedCellTransversal :
    CellTransversal
      (descendantCell
        (iteratedParentDescendantCut d5Stage1CoforestParentStep
          d5Stage1CoforestChild))
      d5Stage1CoforestParent
      d5Stage1CoforestChild :=
  parentMapBoundary_cellTransversal d5Stage1CoforestIteratedParentMapBoundary

theorem d5Stage1Coforest_direct_crosses_cell_iff
    (cut edge : D5Stage1CoforestEdge) :
    d5Stage1CoforestParent edge ∉
        descendantCell d5Stage1CoforestDescendantCut cut ∧
      d5Stage1CoforestChild edge ∈
        descendantCell d5Stage1CoforestDescendantCut cut ↔
      cut = edge :=
  d5Stage1CoforestDirectCellTransversal.crosses_iff cut edge

theorem d5Stage1Coforest_iterated_crosses_cell_iff
    (cut edge : D5Stage1CoforestEdge) :
    d5Stage1CoforestParent edge ∉
        descendantCell
          (iteratedParentDescendantCut d5Stage1CoforestParentStep
            d5Stage1CoforestChild) cut ∧
      d5Stage1CoforestChild edge ∈
        descendantCell
          (iteratedParentDescendantCut d5Stage1CoforestParentStep
            d5Stage1CoforestChild) cut ↔
      cut = edge :=
  d5Stage1CoforestIteratedCellTransversal.crosses_iff cut edge

def d7Stage2Packet134Color34CoforestDirectCellTransversal :
    CellTransversal
      (descendantCell d7Stage2Packet134Color34CoforestDescendantCut)
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  parentMapBoundary_cellTransversal
    d7Stage2Packet134Color34CoforestParentMapBoundary

def d7Stage2Packet134Color34CoforestIteratedCellTransversal :
    CellTransversal
      (descendantCell
        (iteratedParentDescendantCut
          d7Stage2Packet134Color34CoforestParentStep
          d7Stage2Packet134Color34CoforestChild))
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  parentMapBoundary_cellTransversal
    d7Stage2Packet134Color34CoforestIteratedParentMapBoundary

theorem d7Stage2Packet134Color34Coforest_direct_crosses_cell_iff
    (cut edge : D7Stage2Packet134Color34CoforestEdge) :
    d7Stage2Packet134Color34CoforestParent edge ∉
        descendantCell d7Stage2Packet134Color34CoforestDescendantCut cut ∧
      d7Stage2Packet134Color34CoforestChild edge ∈
        descendantCell d7Stage2Packet134Color34CoforestDescendantCut cut ↔
      cut = edge :=
  d7Stage2Packet134Color34CoforestDirectCellTransversal.crosses_iff cut edge

theorem d7Stage2Packet134Color34Coforest_iterated_crosses_cell_iff
    (cut edge : D7Stage2Packet134Color34CoforestEdge) :
    d7Stage2Packet134Color34CoforestParent edge ∉
        descendantCell
          (iteratedParentDescendantCut
            d7Stage2Packet134Color34CoforestParentStep
            d7Stage2Packet134Color34CoforestChild) cut ∧
      d7Stage2Packet134Color34CoforestChild edge ∈
        descendantCell
          (iteratedParentDescendantCut
            d7Stage2Packet134Color34CoforestParentStep
            d7Stage2Packet134Color34CoforestChild) cut ↔
      cut = edge :=
  d7Stage2Packet134Color34CoforestIteratedCellTransversal.crosses_iff cut edge

end TypeA

export TypeA
  (CellTransversal
   CellTransversal.crosses_iff
   CellTransversal.head_mem_iff_tail_mem_of_ne
   CellTransversal.tail_mem_iff_head_mem_of_ne
   parentMapBoundary_cellTransversal
   parentMapBoundary_crosses_descendantCell_iff
   coforestRootedBoundaryAudit_direct_cellTransversal
   coforestRootedBoundaryAudit_iterated_cellTransversal
   coforestRootedBoundaryAudit_direct_crosses_cell_iff
   coforestRootedBoundaryAudit_iterated_crosses_cell_iff
   CoforestRowCellBridge
   coforestRowCellBridge_of_rootedBoundaryAudit
   CoforestRowCellBridge.direct_crosses_cell_iff
   CoforestRowCellBridge.iterated_crosses_cell_iff
   D5CoforestRowsCellBridgeAudit
   d5CoforestRowsCellBridgeAudit_holds
   D7Stage12CoforestRowsCellBridgeAudit
   d7Stage12CoforestRowsCellBridgeAudit_holds
   v28FiniteInputPacketCellBridgeAudit
   v28FiniteInputPacketCellBridgeAudit_holds
   d5Stage1CoforestDirectCellTransversal
   d5Stage1CoforestIteratedCellTransversal
   d5Stage1Coforest_direct_crosses_cell_iff
   d5Stage1Coforest_iterated_crosses_cell_iff
   d7Stage2Packet134Color34CoforestDirectCellTransversal
   d7Stage2Packet134Color34CoforestIteratedCellTransversal
   d7Stage2Packet134Color34Coforest_direct_crosses_cell_iff
   d7Stage2Packet134Color34Coforest_iterated_crosses_cell_iff)

end EvenV11
