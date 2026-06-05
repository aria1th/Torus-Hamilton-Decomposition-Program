import EvenV11.TypeA.RootedParentMap

namespace EvenV11
namespace TypeA

inductive D5Stage1CoforestVertex where
  | root0
  | v1
  | v2
  | v3
  deriving DecidableEq, Repr

inductive D5Stage1CoforestEdge where
  | e01
  | e02
  | e03
  deriving DecidableEq, Repr

def d5Stage1CoforestParent :
    D5Stage1CoforestEdge → D5Stage1CoforestVertex
  | D5Stage1CoforestEdge.e01 => D5Stage1CoforestVertex.root0
  | D5Stage1CoforestEdge.e02 => D5Stage1CoforestVertex.root0
  | D5Stage1CoforestEdge.e03 => D5Stage1CoforestVertex.root0

def d5Stage1CoforestChild :
    D5Stage1CoforestEdge → D5Stage1CoforestVertex
  | D5Stage1CoforestEdge.e01 => D5Stage1CoforestVertex.v1
  | D5Stage1CoforestEdge.e02 => D5Stage1CoforestVertex.v2
  | D5Stage1CoforestEdge.e03 => D5Stage1CoforestVertex.v3

def d5Stage1CoforestDescendantCut :
    D5Stage1CoforestEdge → D5Stage1CoforestVertex → Prop
  | D5Stage1CoforestEdge.e01, D5Stage1CoforestVertex.v1 => True
  | D5Stage1CoforestEdge.e02, D5Stage1CoforestVertex.v2 => True
  | D5Stage1CoforestEdge.e03, D5Stage1CoforestVertex.v3 => True
  | _, _ => False

def d5Stage1CoforestDescendantCutDecidable :
    (cut : D5Stage1CoforestEdge) →
      (vertex : D5Stage1CoforestVertex) →
        Decidable (d5Stage1CoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def d5Stage1CoforestParentStep :
    D5Stage1CoforestVertex → D5Stage1CoforestVertex
  | D5Stage1CoforestVertex.root0 => D5Stage1CoforestVertex.root0
  | D5Stage1CoforestVertex.v1 => D5Stage1CoforestVertex.root0
  | D5Stage1CoforestVertex.v2 => D5Stage1CoforestVertex.root0
  | D5Stage1CoforestVertex.v3 => D5Stage1CoforestVertex.root0

def d5Stage1CoforestRank : D5Stage1CoforestVertex → Nat
  | D5Stage1CoforestVertex.root0 => 0
  | D5Stage1CoforestVertex.v1 => 1
  | D5Stage1CoforestVertex.v2 => 1
  | D5Stage1CoforestVertex.v3 => 1

def d5Stage1CoforestEdgeTable : List D5Stage1CoforestEdge :=
  [D5Stage1CoforestEdge.e01, D5Stage1CoforestEdge.e02,
    D5Stage1CoforestEdge.e03]

def d5Stage1CoforestVertexTable : List D5Stage1CoforestVertex :=
  [D5Stage1CoforestVertex.root0, D5Stage1CoforestVertex.v1,
    D5Stage1CoforestVertex.v2, D5Stage1CoforestVertex.v3]

def d5Stage1CoforestParentTable : List D5Stage1CoforestVertex :=
  d5Stage1CoforestEdgeTable.map d5Stage1CoforestParent

def d5Stage1CoforestChildTable : List D5Stage1CoforestVertex :=
  d5Stage1CoforestEdgeTable.map d5Stage1CoforestChild

def d5Stage1CoforestParentStepTable : List D5Stage1CoforestVertex :=
  d5Stage1CoforestVertexTable.map d5Stage1CoforestParentStep

def d5Stage1CoforestRankTable : List Nat :=
  d5Stage1CoforestVertexTable.map d5Stage1CoforestRank

theorem d5Stage1CoforestEdgeTable_length :
    d5Stage1CoforestEdgeTable.length = 3 :=
  rfl

theorem d5Stage1CoforestVertexTable_length :
    d5Stage1CoforestVertexTable.length = 4 :=
  rfl

theorem d5Stage1CoforestEdgeTable_nodup :
    d5Stage1CoforestEdgeTable.Nodup := by
  decide

theorem d5Stage1CoforestVertexTable_nodup :
    d5Stage1CoforestVertexTable.Nodup := by
  decide

theorem d5Stage1CoforestParentTable_readout :
    d5Stage1CoforestParentTable =
      [D5Stage1CoforestVertex.root0, D5Stage1CoforestVertex.root0,
        D5Stage1CoforestVertex.root0] :=
  rfl

theorem d5Stage1CoforestChildTable_readout :
    d5Stage1CoforestChildTable =
      [D5Stage1CoforestVertex.v1, D5Stage1CoforestVertex.v2,
        D5Stage1CoforestVertex.v3] :=
  rfl

theorem d5Stage1CoforestParentStepTable_readout :
    d5Stage1CoforestParentStepTable =
      [D5Stage1CoforestVertex.root0, D5Stage1CoforestVertex.root0,
        D5Stage1CoforestVertex.root0, D5Stage1CoforestVertex.root0] :=
  rfl

theorem d5Stage1CoforestRankTable_readout :
    d5Stage1CoforestRankTable = [0, 1, 1, 1] :=
  rfl

def d5Stage1CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage1CoforestParentStep
      d5Stage1CoforestParent
      d5Stage1CoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [d5Stage1CoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := d5Stage1CoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem d5Stage1CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage1CoforestDescendantCut
      d5Stage1CoforestParent
      d5Stage1CoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [d5Stage1CoforestDescendantCut,
        d5Stage1CoforestChild]
  · intro edge
    cases edge <;>
      simp [d5Stage1CoforestDescendantCut,
        d5Stage1CoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [d5Stage1CoforestDescendantCut,
        d5Stage1CoforestParent, d5Stage1CoforestChild] at hne ⊢

theorem d5Stage1CoforestIncidence_eq_ite
    (cut edge : D5Stage1CoforestEdge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    D5Stage1CoforestVertex D5Stage1CoforestEdge inferInstance
    d5Stage1CoforestDescendantCut
    d5Stage1CoforestDescendantCutDecidable
    d5Stage1CoforestParent d5Stage1CoforestChild
    d5Stage1CoforestParentMapBoundary cut edge

theorem d5Stage1CoforestIncidence_self
    (edge : D5Stage1CoforestEdge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    D5Stage1CoforestVertex D5Stage1CoforestEdge
    d5Stage1CoforestDescendantCut
    d5Stage1CoforestDescendantCutDecidable
    d5Stage1CoforestParent d5Stage1CoforestChild
    d5Stage1CoforestParentMapBoundary edge

theorem d5Stage1CoforestIncidence_ne
    {cut edge : D5Stage1CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    D5Stage1CoforestVertex D5Stage1CoforestEdge
    d5Stage1CoforestDescendantCut
    d5Stage1CoforestDescendantCutDecidable
    d5Stage1CoforestParent d5Stage1CoforestChild
    d5Stage1CoforestParentMapBoundary cut edge hne

theorem d5Stage1CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d5Stage1CoforestParentStep
        d5Stage1CoforestChild)
      d5Stage1CoforestParent
      d5Stage1CoforestChild :=
  rankedRootedParentMapBoundary
    d5Stage1CoforestRankedParentMapData

inductive D5Stage1PairCoforestVertex where
  | root3
  | v0
  | v1
  | v4
  deriving DecidableEq, Repr

inductive D5Stage1PairCoforestEdge where
  | e03
  | e01
  | e34
  deriving DecidableEq, Repr

def d5Stage1PairCoforestParent :
    D5Stage1PairCoforestEdge → D5Stage1PairCoforestVertex
  | D5Stage1PairCoforestEdge.e03 =>
      D5Stage1PairCoforestVertex.root3
  | D5Stage1PairCoforestEdge.e01 =>
      D5Stage1PairCoforestVertex.v0
  | D5Stage1PairCoforestEdge.e34 =>
      D5Stage1PairCoforestVertex.root3

def d5Stage1PairCoforestChild :
    D5Stage1PairCoforestEdge → D5Stage1PairCoforestVertex
  | D5Stage1PairCoforestEdge.e03 =>
      D5Stage1PairCoforestVertex.v0
  | D5Stage1PairCoforestEdge.e01 =>
      D5Stage1PairCoforestVertex.v1
  | D5Stage1PairCoforestEdge.e34 =>
      D5Stage1PairCoforestVertex.v4

def d5Stage1PairCoforestDescendantCut :
    D5Stage1PairCoforestEdge →
      D5Stage1PairCoforestVertex → Prop
  | D5Stage1PairCoforestEdge.e03,
      D5Stage1PairCoforestVertex.v0 => True
  | D5Stage1PairCoforestEdge.e03,
      D5Stage1PairCoforestVertex.v1 => True
  | D5Stage1PairCoforestEdge.e01,
      D5Stage1PairCoforestVertex.v1 => True
  | D5Stage1PairCoforestEdge.e34,
      D5Stage1PairCoforestVertex.v4 => True
  | _, _ => False

def d5Stage1PairCoforestDescendantCutDecidable :
    (cut : D5Stage1PairCoforestEdge) →
      (vertex : D5Stage1PairCoforestVertex) →
        Decidable (d5Stage1PairCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def d5Stage1PairCoforestParentStep :
    D5Stage1PairCoforestVertex → D5Stage1PairCoforestVertex
  | D5Stage1PairCoforestVertex.root3 =>
      D5Stage1PairCoforestVertex.root3
  | D5Stage1PairCoforestVertex.v0 =>
      D5Stage1PairCoforestVertex.root3
  | D5Stage1PairCoforestVertex.v1 =>
      D5Stage1PairCoforestVertex.v0
  | D5Stage1PairCoforestVertex.v4 =>
      D5Stage1PairCoforestVertex.root3

def d5Stage1PairCoforestRank : D5Stage1PairCoforestVertex → Nat
  | D5Stage1PairCoforestVertex.root3 => 0
  | D5Stage1PairCoforestVertex.v0 => 1
  | D5Stage1PairCoforestVertex.v1 => 2
  | D5Stage1PairCoforestVertex.v4 => 1

def d5Stage1PairCoforestEdgeTable : List D5Stage1PairCoforestEdge :=
  [D5Stage1PairCoforestEdge.e03, D5Stage1PairCoforestEdge.e01,
    D5Stage1PairCoforestEdge.e34]

def d5Stage1PairCoforestVertexTable : List D5Stage1PairCoforestVertex :=
  [D5Stage1PairCoforestVertex.root3, D5Stage1PairCoforestVertex.v0,
    D5Stage1PairCoforestVertex.v1, D5Stage1PairCoforestVertex.v4]

def d5Stage1PairCoforestParentTable :
    List D5Stage1PairCoforestVertex :=
  d5Stage1PairCoforestEdgeTable.map d5Stage1PairCoforestParent

def d5Stage1PairCoforestChildTable :
    List D5Stage1PairCoforestVertex :=
  d5Stage1PairCoforestEdgeTable.map d5Stage1PairCoforestChild

def d5Stage1PairCoforestParentStepTable :
    List D5Stage1PairCoforestVertex :=
  d5Stage1PairCoforestVertexTable.map d5Stage1PairCoforestParentStep

def d5Stage1PairCoforestRankTable : List Nat :=
  d5Stage1PairCoforestVertexTable.map d5Stage1PairCoforestRank

theorem d5Stage1PairCoforestEdgeTable_length :
    d5Stage1PairCoforestEdgeTable.length = 3 :=
  rfl

theorem d5Stage1PairCoforestVertexTable_length :
    d5Stage1PairCoforestVertexTable.length = 4 :=
  rfl

theorem d5Stage1PairCoforestEdgeTable_nodup :
    d5Stage1PairCoforestEdgeTable.Nodup := by
  decide

theorem d5Stage1PairCoforestVertexTable_nodup :
    d5Stage1PairCoforestVertexTable.Nodup := by
  decide

theorem d5Stage1PairCoforestParentTable_readout :
    d5Stage1PairCoforestParentTable =
      [D5Stage1PairCoforestVertex.root3, D5Stage1PairCoforestVertex.v0,
        D5Stage1PairCoforestVertex.root3] :=
  rfl

theorem d5Stage1PairCoforestChildTable_readout :
    d5Stage1PairCoforestChildTable =
      [D5Stage1PairCoforestVertex.v0, D5Stage1PairCoforestVertex.v1,
        D5Stage1PairCoforestVertex.v4] :=
  rfl

theorem d5Stage1PairCoforestParentStepTable_readout :
    d5Stage1PairCoforestParentStepTable =
      [D5Stage1PairCoforestVertex.root3, D5Stage1PairCoforestVertex.root3,
        D5Stage1PairCoforestVertex.v0, D5Stage1PairCoforestVertex.root3] :=
  rfl

theorem d5Stage1PairCoforestRankTable_readout :
    d5Stage1PairCoforestRankTable = [0, 1, 2, 1] :=
  rfl

def d5Stage1PairCoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage1PairCoforestParentStep
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [d5Stage1PairCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := d5Stage1PairCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem d5Stage1PairCoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage1PairCoforestDescendantCut
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [d5Stage1PairCoforestDescendantCut,
        d5Stage1PairCoforestChild]
  · intro edge
    cases edge <;>
      simp [d5Stage1PairCoforestDescendantCut,
        d5Stage1PairCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [d5Stage1PairCoforestDescendantCut,
        d5Stage1PairCoforestParent,
        d5Stage1PairCoforestChild] at hne ⊢

theorem d5Stage1PairCoforestIncidence_eq_ite
    (cut edge : D5Stage1PairCoforestEdge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
    inferInstance
    d5Stage1PairCoforestDescendantCut
    d5Stage1PairCoforestDescendantCutDecidable
    d5Stage1PairCoforestParent d5Stage1PairCoforestChild
    d5Stage1PairCoforestParentMapBoundary cut edge

theorem d5Stage1PairCoforestIncidence_self
    (edge : D5Stage1PairCoforestEdge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
    d5Stage1PairCoforestDescendantCut
    d5Stage1PairCoforestDescendantCutDecidable
    d5Stage1PairCoforestParent d5Stage1PairCoforestChild
    d5Stage1PairCoforestParentMapBoundary edge

theorem d5Stage1PairCoforestIncidence_ne
    {cut edge : D5Stage1PairCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
    d5Stage1PairCoforestDescendantCut
    d5Stage1PairCoforestDescendantCutDecidable
    d5Stage1PairCoforestParent d5Stage1PairCoforestChild
    d5Stage1PairCoforestParentMapBoundary cut edge hne

theorem d5Stage1PairCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d5Stage1PairCoforestParentStep
        d5Stage1PairCoforestChild)
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild :=
  rankedRootedParentMapBoundary
    d5Stage1PairCoforestRankedParentMapData

inductive TwoLeafStarCoforestVertex where
  | root
  | left
  | right
  deriving DecidableEq, Repr

inductive TwoLeafStarCoforestEdge where
  | rootLeft
  | rootRight
  deriving DecidableEq, Repr

def twoLeafStarCoforestParent :
    TwoLeafStarCoforestEdge → TwoLeafStarCoforestVertex
  | TwoLeafStarCoforestEdge.rootLeft =>
      TwoLeafStarCoforestVertex.root
  | TwoLeafStarCoforestEdge.rootRight =>
      TwoLeafStarCoforestVertex.root

def twoLeafStarCoforestChild :
    TwoLeafStarCoforestEdge → TwoLeafStarCoforestVertex
  | TwoLeafStarCoforestEdge.rootLeft =>
      TwoLeafStarCoforestVertex.left
  | TwoLeafStarCoforestEdge.rootRight =>
      TwoLeafStarCoforestVertex.right

def twoLeafStarCoforestDescendantCut :
    TwoLeafStarCoforestEdge → TwoLeafStarCoforestVertex → Prop
  | TwoLeafStarCoforestEdge.rootLeft,
      TwoLeafStarCoforestVertex.left => True
  | TwoLeafStarCoforestEdge.rootRight,
      TwoLeafStarCoforestVertex.right => True
  | _, _ => False

def twoLeafStarCoforestDescendantCutDecidable :
    (cut : TwoLeafStarCoforestEdge) →
      (vertex : TwoLeafStarCoforestVertex) →
        Decidable (twoLeafStarCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def twoLeafStarCoforestParentStep :
    TwoLeafStarCoforestVertex → TwoLeafStarCoforestVertex
  | TwoLeafStarCoforestVertex.root =>
      TwoLeafStarCoforestVertex.root
  | TwoLeafStarCoforestVertex.left =>
      TwoLeafStarCoforestVertex.root
  | TwoLeafStarCoforestVertex.right =>
      TwoLeafStarCoforestVertex.root

def twoLeafStarCoforestRank : TwoLeafStarCoforestVertex → Nat
  | TwoLeafStarCoforestVertex.root => 0
  | TwoLeafStarCoforestVertex.left => 1
  | TwoLeafStarCoforestVertex.right => 1

def twoLeafStarCoforestEdgeTable : List TwoLeafStarCoforestEdge :=
  [TwoLeafStarCoforestEdge.rootLeft, TwoLeafStarCoforestEdge.rootRight]

def twoLeafStarCoforestVertexTable :
    List TwoLeafStarCoforestVertex :=
  [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.left,
    TwoLeafStarCoforestVertex.right]

def twoLeafStarCoforestParentTable :
    List TwoLeafStarCoforestVertex :=
  twoLeafStarCoforestEdgeTable.map twoLeafStarCoforestParent

def twoLeafStarCoforestChildTable :
    List TwoLeafStarCoforestVertex :=
  twoLeafStarCoforestEdgeTable.map twoLeafStarCoforestChild

def twoLeafStarCoforestParentStepTable :
    List TwoLeafStarCoforestVertex :=
  twoLeafStarCoforestVertexTable.map twoLeafStarCoforestParentStep

def twoLeafStarCoforestRankTable : List Nat :=
  twoLeafStarCoforestVertexTable.map twoLeafStarCoforestRank

theorem twoLeafStarCoforestEdgeTable_length :
    twoLeafStarCoforestEdgeTable.length = 2 :=
  rfl

theorem twoLeafStarCoforestVertexTable_length :
    twoLeafStarCoforestVertexTable.length = 3 :=
  rfl

theorem twoLeafStarCoforestEdgeTable_nodup :
    twoLeafStarCoforestEdgeTable.Nodup := by
  decide

theorem twoLeafStarCoforestVertexTable_nodup :
    twoLeafStarCoforestVertexTable.Nodup := by
  decide

theorem twoLeafStarCoforestParentTable_readout :
    twoLeafStarCoforestParentTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root] :=
  rfl

theorem twoLeafStarCoforestChildTable_readout :
    twoLeafStarCoforestChildTable =
      [TwoLeafStarCoforestVertex.left, TwoLeafStarCoforestVertex.right] :=
  rfl

theorem twoLeafStarCoforestParentStepTable_readout :
    twoLeafStarCoforestParentStepTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root,
        TwoLeafStarCoforestVertex.root] :=
  rfl

theorem twoLeafStarCoforestRankTable_readout :
    twoLeafStarCoforestRankTable = [0, 1, 1] :=
  rfl

def twoLeafStarCoforestRankedParentMapData :
    RankedRootedParentMapData
      twoLeafStarCoforestParentStep
      twoLeafStarCoforestParent
      twoLeafStarCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [twoLeafStarCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := twoLeafStarCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem twoLeafStarCoforestParentMapBoundary :
    ParentMapBoundary
      twoLeafStarCoforestDescendantCut
      twoLeafStarCoforestParent
      twoLeafStarCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [twoLeafStarCoforestDescendantCut,
        twoLeafStarCoforestChild]
  · intro edge
    cases edge <;>
      simp [twoLeafStarCoforestDescendantCut,
        twoLeafStarCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [twoLeafStarCoforestDescendantCut,
        twoLeafStarCoforestParent,
        twoLeafStarCoforestChild] at hne ⊢

theorem twoLeafStarCoforestIncidence_eq_ite
    (cut edge : TwoLeafStarCoforestEdge) :
    @parentMapIncidence
        TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
        twoLeafStarCoforestDescendantCut
        twoLeafStarCoforestDescendantCutDecidable
        twoLeafStarCoforestParent
        twoLeafStarCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
    inferInstance
    twoLeafStarCoforestDescendantCut
    twoLeafStarCoforestDescendantCutDecidable
    twoLeafStarCoforestParent twoLeafStarCoforestChild
    twoLeafStarCoforestParentMapBoundary cut edge

theorem twoLeafStarCoforestIncidence_self
    (edge : TwoLeafStarCoforestEdge) :
    @parentMapIncidence
        TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
        twoLeafStarCoforestDescendantCut
        twoLeafStarCoforestDescendantCutDecidable
        twoLeafStarCoforestParent
        twoLeafStarCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
    twoLeafStarCoforestDescendantCut
    twoLeafStarCoforestDescendantCutDecidable
    twoLeafStarCoforestParent twoLeafStarCoforestChild
    twoLeafStarCoforestParentMapBoundary edge

theorem twoLeafStarCoforestIncidence_ne
    {cut edge : TwoLeafStarCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
        twoLeafStarCoforestDescendantCut
        twoLeafStarCoforestDescendantCutDecidable
        twoLeafStarCoforestParent
        twoLeafStarCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    TwoLeafStarCoforestVertex TwoLeafStarCoforestEdge
    twoLeafStarCoforestDescendantCut
    twoLeafStarCoforestDescendantCutDecidable
    twoLeafStarCoforestParent twoLeafStarCoforestChild
    twoLeafStarCoforestParentMapBoundary cut edge hne

theorem twoLeafStarCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut twoLeafStarCoforestParentStep
        twoLeafStarCoforestChild)
      twoLeafStarCoforestParent
      twoLeafStarCoforestChild :=
  rankedRootedParentMapBoundary
    twoLeafStarCoforestRankedParentMapData

inductive TwoEdgePathCoforestVertex where
  | root
  | middle
  | leaf
  deriving DecidableEq, Repr

inductive TwoEdgePathCoforestEdge where
  | first
  | second
  deriving DecidableEq, Repr

def twoEdgePathCoforestParent :
    TwoEdgePathCoforestEdge → TwoEdgePathCoforestVertex
  | TwoEdgePathCoforestEdge.first =>
      TwoEdgePathCoforestVertex.root
  | TwoEdgePathCoforestEdge.second =>
      TwoEdgePathCoforestVertex.middle

def twoEdgePathCoforestChild :
    TwoEdgePathCoforestEdge → TwoEdgePathCoforestVertex
  | TwoEdgePathCoforestEdge.first =>
      TwoEdgePathCoforestVertex.middle
  | TwoEdgePathCoforestEdge.second =>
      TwoEdgePathCoforestVertex.leaf

def twoEdgePathCoforestDescendantCut :
    TwoEdgePathCoforestEdge → TwoEdgePathCoforestVertex → Prop
  | TwoEdgePathCoforestEdge.first,
      TwoEdgePathCoforestVertex.middle => True
  | TwoEdgePathCoforestEdge.first,
      TwoEdgePathCoforestVertex.leaf => True
  | TwoEdgePathCoforestEdge.second,
      TwoEdgePathCoforestVertex.leaf => True
  | _, _ => False

def twoEdgePathCoforestDescendantCutDecidable :
    (cut : TwoEdgePathCoforestEdge) →
      (vertex : TwoEdgePathCoforestVertex) →
        Decidable (twoEdgePathCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def twoEdgePathCoforestParentStep :
    TwoEdgePathCoforestVertex → TwoEdgePathCoforestVertex
  | TwoEdgePathCoforestVertex.root =>
      TwoEdgePathCoforestVertex.root
  | TwoEdgePathCoforestVertex.middle =>
      TwoEdgePathCoforestVertex.root
  | TwoEdgePathCoforestVertex.leaf =>
      TwoEdgePathCoforestVertex.middle

def twoEdgePathCoforestRank : TwoEdgePathCoforestVertex → Nat
  | TwoEdgePathCoforestVertex.root => 0
  | TwoEdgePathCoforestVertex.middle => 1
  | TwoEdgePathCoforestVertex.leaf => 2

def twoEdgePathCoforestEdgeTable : List TwoEdgePathCoforestEdge :=
  [TwoEdgePathCoforestEdge.first, TwoEdgePathCoforestEdge.second]

def twoEdgePathCoforestVertexTable :
    List TwoEdgePathCoforestVertex :=
  [TwoEdgePathCoforestVertex.root, TwoEdgePathCoforestVertex.middle,
    TwoEdgePathCoforestVertex.leaf]

def twoEdgePathCoforestParentTable :
    List TwoEdgePathCoforestVertex :=
  twoEdgePathCoforestEdgeTable.map twoEdgePathCoforestParent

def twoEdgePathCoforestChildTable :
    List TwoEdgePathCoforestVertex :=
  twoEdgePathCoforestEdgeTable.map twoEdgePathCoforestChild

def twoEdgePathCoforestParentStepTable :
    List TwoEdgePathCoforestVertex :=
  twoEdgePathCoforestVertexTable.map twoEdgePathCoforestParentStep

def twoEdgePathCoforestRankTable : List Nat :=
  twoEdgePathCoforestVertexTable.map twoEdgePathCoforestRank

theorem twoEdgePathCoforestEdgeTable_length :
    twoEdgePathCoforestEdgeTable.length = 2 :=
  rfl

theorem twoEdgePathCoforestVertexTable_length :
    twoEdgePathCoforestVertexTable.length = 3 :=
  rfl

theorem twoEdgePathCoforestEdgeTable_nodup :
    twoEdgePathCoforestEdgeTable.Nodup := by
  decide

theorem twoEdgePathCoforestVertexTable_nodup :
    twoEdgePathCoforestVertexTable.Nodup := by
  decide

theorem twoEdgePathCoforestParentTable_readout :
    twoEdgePathCoforestParentTable =
      [TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  rfl

theorem twoEdgePathCoforestChildTable_readout :
    twoEdgePathCoforestChildTable =
      [TwoEdgePathCoforestVertex.middle, TwoEdgePathCoforestVertex.leaf] :=
  rfl

theorem twoEdgePathCoforestParentStepTable_readout :
    twoEdgePathCoforestParentStepTable =
      [TwoEdgePathCoforestVertex.root, TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  rfl

theorem twoEdgePathCoforestRankTable_readout :
    twoEdgePathCoforestRankTable = [0, 1, 2] :=
  rfl

def twoEdgePathCoforestRankedParentMapData :
    RankedRootedParentMapData
      twoEdgePathCoforestParentStep
      twoEdgePathCoforestParent
      twoEdgePathCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [twoEdgePathCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := twoEdgePathCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem twoEdgePathCoforestParentMapBoundary :
    ParentMapBoundary
      twoEdgePathCoforestDescendantCut
      twoEdgePathCoforestParent
      twoEdgePathCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [twoEdgePathCoforestDescendantCut,
        twoEdgePathCoforestChild]
  · intro edge
    cases edge <;>
      simp [twoEdgePathCoforestDescendantCut,
        twoEdgePathCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [twoEdgePathCoforestDescendantCut,
        twoEdgePathCoforestParent,
        twoEdgePathCoforestChild] at hne ⊢

theorem twoEdgePathCoforestIncidence_eq_ite
    (cut edge : TwoEdgePathCoforestEdge) :
    @parentMapIncidence
        TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
        twoEdgePathCoforestDescendantCut
        twoEdgePathCoforestDescendantCutDecidable
        twoEdgePathCoforestParent
        twoEdgePathCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
    inferInstance
    twoEdgePathCoforestDescendantCut
    twoEdgePathCoforestDescendantCutDecidable
    twoEdgePathCoforestParent twoEdgePathCoforestChild
    twoEdgePathCoforestParentMapBoundary cut edge

theorem twoEdgePathCoforestIncidence_self
    (edge : TwoEdgePathCoforestEdge) :
    @parentMapIncidence
        TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
        twoEdgePathCoforestDescendantCut
        twoEdgePathCoforestDescendantCutDecidable
        twoEdgePathCoforestParent
        twoEdgePathCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
    twoEdgePathCoforestDescendantCut
    twoEdgePathCoforestDescendantCutDecidable
    twoEdgePathCoforestParent twoEdgePathCoforestChild
    twoEdgePathCoforestParentMapBoundary edge

theorem twoEdgePathCoforestIncidence_ne
    {cut edge : TwoEdgePathCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
        twoEdgePathCoforestDescendantCut
        twoEdgePathCoforestDescendantCutDecidable
        twoEdgePathCoforestParent
        twoEdgePathCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    TwoEdgePathCoforestVertex TwoEdgePathCoforestEdge
    twoEdgePathCoforestDescendantCut
    twoEdgePathCoforestDescendantCutDecidable
    twoEdgePathCoforestParent twoEdgePathCoforestChild
    twoEdgePathCoforestParentMapBoundary cut edge hne

theorem twoEdgePathCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut twoEdgePathCoforestParentStep
        twoEdgePathCoforestChild)
      twoEdgePathCoforestParent
      twoEdgePathCoforestChild :=
  rankedRootedParentMapBoundary
    twoEdgePathCoforestRankedParentMapData

inductive OneEdgeCoforestVertex where
  | root
  | leaf
  deriving DecidableEq, Repr

inductive OneEdgeCoforestEdge where
  | rootLeaf
  deriving DecidableEq, Repr

def oneEdgeCoforestParent :
    OneEdgeCoforestEdge → OneEdgeCoforestVertex
  | OneEdgeCoforestEdge.rootLeaf =>
      OneEdgeCoforestVertex.root

def oneEdgeCoforestChild :
    OneEdgeCoforestEdge → OneEdgeCoforestVertex
  | OneEdgeCoforestEdge.rootLeaf =>
      OneEdgeCoforestVertex.leaf

def oneEdgeCoforestDescendantCut :
    OneEdgeCoforestEdge → OneEdgeCoforestVertex → Prop
  | OneEdgeCoforestEdge.rootLeaf,
      OneEdgeCoforestVertex.leaf => True
  | _, _ => False

def oneEdgeCoforestDescendantCutDecidable :
    (cut : OneEdgeCoforestEdge) →
      (vertex : OneEdgeCoforestVertex) →
        Decidable (oneEdgeCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut
    cases vertex
    · exact isFalse (by intro h; exact h)
    · exact isTrue trivial

def oneEdgeCoforestParentStep :
    OneEdgeCoforestVertex → OneEdgeCoforestVertex
  | OneEdgeCoforestVertex.root =>
      OneEdgeCoforestVertex.root
  | OneEdgeCoforestVertex.leaf =>
      OneEdgeCoforestVertex.root

def oneEdgeCoforestRank : OneEdgeCoforestVertex → Nat
  | OneEdgeCoforestVertex.root => 0
  | OneEdgeCoforestVertex.leaf => 1

def oneEdgeCoforestEdgeTable : List OneEdgeCoforestEdge :=
  [OneEdgeCoforestEdge.rootLeaf]

def oneEdgeCoforestVertexTable : List OneEdgeCoforestVertex :=
  [OneEdgeCoforestVertex.root, OneEdgeCoforestVertex.leaf]

def oneEdgeCoforestParentTable : List OneEdgeCoforestVertex :=
  oneEdgeCoforestEdgeTable.map oneEdgeCoforestParent

def oneEdgeCoforestChildTable : List OneEdgeCoforestVertex :=
  oneEdgeCoforestEdgeTable.map oneEdgeCoforestChild

def oneEdgeCoforestParentStepTable : List OneEdgeCoforestVertex :=
  oneEdgeCoforestVertexTable.map oneEdgeCoforestParentStep

def oneEdgeCoforestRankTable : List Nat :=
  oneEdgeCoforestVertexTable.map oneEdgeCoforestRank

theorem oneEdgeCoforestEdgeTable_length :
    oneEdgeCoforestEdgeTable.length = 1 :=
  rfl

theorem oneEdgeCoforestVertexTable_length :
    oneEdgeCoforestVertexTable.length = 2 :=
  rfl

theorem oneEdgeCoforestEdgeTable_nodup :
    oneEdgeCoforestEdgeTable.Nodup := by
  decide

theorem oneEdgeCoforestVertexTable_nodup :
    oneEdgeCoforestVertexTable.Nodup := by
  decide

theorem oneEdgeCoforestParentTable_readout :
    oneEdgeCoforestParentTable = [OneEdgeCoforestVertex.root] :=
  rfl

theorem oneEdgeCoforestChildTable_readout :
    oneEdgeCoforestChildTable = [OneEdgeCoforestVertex.leaf] :=
  rfl

theorem oneEdgeCoforestParentStepTable_readout :
    oneEdgeCoforestParentStepTable =
      [OneEdgeCoforestVertex.root, OneEdgeCoforestVertex.root] :=
  rfl

theorem oneEdgeCoforestRankTable_readout :
    oneEdgeCoforestRankTable = [0, 1] :=
  rfl

def oneEdgeCoforestRankedParentMapData :
    RankedRootedParentMapData
      oneEdgeCoforestParentStep
      oneEdgeCoforestParent
      oneEdgeCoforestChild where
  child_injective := by
    intro left right hchild
    cases left
    cases right
    simp [oneEdgeCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge
    rfl
  rank := oneEdgeCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge
    decide

theorem oneEdgeCoforestParentMapBoundary :
    ParentMapBoundary
      oneEdgeCoforestDescendantCut
      oneEdgeCoforestParent
      oneEdgeCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge
    simp [oneEdgeCoforestDescendantCut,
      oneEdgeCoforestChild]
  · intro edge
    cases edge
    simp [oneEdgeCoforestDescendantCut,
      oneEdgeCoforestParent]
  · intro cut edge hne
    cases cut
    cases edge
    exact False.elim (hne rfl)

theorem oneEdgeCoforestIncidence_eq_ite
    (cut edge : OneEdgeCoforestEdge) :
    @parentMapIncidence
        OneEdgeCoforestVertex OneEdgeCoforestEdge
        oneEdgeCoforestDescendantCut
        oneEdgeCoforestDescendantCutDecidable
        oneEdgeCoforestParent
        oneEdgeCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    OneEdgeCoforestVertex OneEdgeCoforestEdge
    inferInstance
    oneEdgeCoforestDescendantCut
    oneEdgeCoforestDescendantCutDecidable
    oneEdgeCoforestParent oneEdgeCoforestChild
    oneEdgeCoforestParentMapBoundary cut edge

theorem oneEdgeCoforestIncidence_self
    (edge : OneEdgeCoforestEdge) :
    @parentMapIncidence
        OneEdgeCoforestVertex OneEdgeCoforestEdge
        oneEdgeCoforestDescendantCut
        oneEdgeCoforestDescendantCutDecidable
        oneEdgeCoforestParent
        oneEdgeCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    OneEdgeCoforestVertex OneEdgeCoforestEdge
    oneEdgeCoforestDescendantCut
    oneEdgeCoforestDescendantCutDecidable
    oneEdgeCoforestParent oneEdgeCoforestChild
    oneEdgeCoforestParentMapBoundary edge

theorem oneEdgeCoforestIncidence_ne
    {cut edge : OneEdgeCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        OneEdgeCoforestVertex OneEdgeCoforestEdge
        oneEdgeCoforestDescendantCut
        oneEdgeCoforestDescendantCutDecidable
        oneEdgeCoforestParent
        oneEdgeCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    OneEdgeCoforestVertex OneEdgeCoforestEdge
    oneEdgeCoforestDescendantCut
    oneEdgeCoforestDescendantCutDecidable
    oneEdgeCoforestParent oneEdgeCoforestChild
    oneEdgeCoforestParentMapBoundary cut edge hne

theorem oneEdgeCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut oneEdgeCoforestParentStep
        oneEdgeCoforestChild)
      oneEdgeCoforestParent
      oneEdgeCoforestChild :=
  rankedRootedParentMapBoundary
    oneEdgeCoforestRankedParentMapData

abbrev D5Stage2TripleColor0CoforestVertex :=
  TwoLeafStarCoforestVertex

abbrev D5Stage2TripleColor0CoforestEdge :=
  TwoLeafStarCoforestEdge

abbrev d5Stage2TripleColor0CoforestParent :
    D5Stage2TripleColor0CoforestEdge →
      D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestParent

abbrev d5Stage2TripleColor0CoforestChild :
    D5Stage2TripleColor0CoforestEdge →
      D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestChild

abbrev d5Stage2TripleColor0CoforestDescendantCut :
    D5Stage2TripleColor0CoforestEdge →
      D5Stage2TripleColor0CoforestVertex → Prop :=
  twoLeafStarCoforestDescendantCut

abbrev d5Stage2TripleColor0CoforestDescendantCutDecidable :
    (cut : D5Stage2TripleColor0CoforestEdge) →
      (vertex : D5Stage2TripleColor0CoforestVertex) →
        Decidable
          (d5Stage2TripleColor0CoforestDescendantCut cut vertex) :=
  twoLeafStarCoforestDescendantCutDecidable

abbrev d5Stage2TripleColor0CoforestParentStep :
    D5Stage2TripleColor0CoforestVertex →
      D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestParentStep

abbrev d5Stage2TripleColor0CoforestRank :
    D5Stage2TripleColor0CoforestVertex → Nat :=
  twoLeafStarCoforestRank

abbrev d5Stage2TripleColor0CoforestEdgeTable :
    List D5Stage2TripleColor0CoforestEdge :=
  twoLeafStarCoforestEdgeTable

abbrev d5Stage2TripleColor0CoforestVertexTable :
    List D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestVertexTable

abbrev d5Stage2TripleColor0CoforestParentTable :
    List D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestParentTable

abbrev d5Stage2TripleColor0CoforestChildTable :
    List D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestChildTable

abbrev d5Stage2TripleColor0CoforestParentStepTable :
    List D5Stage2TripleColor0CoforestVertex :=
  twoLeafStarCoforestParentStepTable

abbrev d5Stage2TripleColor0CoforestRankTable : List Nat :=
  twoLeafStarCoforestRankTable

theorem d5Stage2TripleColor0CoforestEdgeTable_length :
    d5Stage2TripleColor0CoforestEdgeTable.length = 2 :=
  twoLeafStarCoforestEdgeTable_length

theorem d5Stage2TripleColor0CoforestVertexTable_length :
    d5Stage2TripleColor0CoforestVertexTable.length = 3 :=
  twoLeafStarCoforestVertexTable_length

theorem d5Stage2TripleColor0CoforestEdgeTable_nodup :
    d5Stage2TripleColor0CoforestEdgeTable.Nodup :=
  twoLeafStarCoforestEdgeTable_nodup

theorem d5Stage2TripleColor0CoforestVertexTable_nodup :
    d5Stage2TripleColor0CoforestVertexTable.Nodup :=
  twoLeafStarCoforestVertexTable_nodup

theorem d5Stage2TripleColor0CoforestParentTable_readout :
    d5Stage2TripleColor0CoforestParentTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root] :=
  twoLeafStarCoforestParentTable_readout

theorem d5Stage2TripleColor0CoforestChildTable_readout :
    d5Stage2TripleColor0CoforestChildTable =
      [TwoLeafStarCoforestVertex.left, TwoLeafStarCoforestVertex.right] :=
  twoLeafStarCoforestChildTable_readout

theorem d5Stage2TripleColor0CoforestParentStepTable_readout :
    d5Stage2TripleColor0CoforestParentStepTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root,
        TwoLeafStarCoforestVertex.root] :=
  twoLeafStarCoforestParentStepTable_readout

theorem d5Stage2TripleColor0CoforestRankTable_readout :
    d5Stage2TripleColor0CoforestRankTable = [0, 1, 1] :=
  twoLeafStarCoforestRankTable_readout

abbrev d5Stage2TripleColor0CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage2TripleColor0CoforestParentStep
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild :=
  twoLeafStarCoforestRankedParentMapData

theorem d5Stage2TripleColor0CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage2TripleColor0CoforestDescendantCut
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild :=
  twoLeafStarCoforestParentMapBoundary

theorem d5Stage2TripleColor0CoforestIncidence_eq_ite
    (cut edge : D5Stage2TripleColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  twoLeafStarCoforestIncidence_eq_ite cut edge

theorem d5Stage2TripleColor0CoforestIncidence_self
    (edge : D5Stage2TripleColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild edge edge = 1 :=
  twoLeafStarCoforestIncidence_self edge

theorem d5Stage2TripleColor0CoforestIncidence_ne
    {cut edge : D5Stage2TripleColor0CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild cut edge = 0 :=
  twoLeafStarCoforestIncidence_ne hne

theorem d5Stage2TripleColor0CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2TripleColor0CoforestParentStep
        d5Stage2TripleColor0CoforestChild)
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild :=
  twoLeafStarCoforestIteratedParentMapBoundary

abbrev D5Stage2TripleColor43CoforestVertex :=
  TwoEdgePathCoforestVertex

abbrev D5Stage2TripleColor43CoforestEdge :=
  TwoEdgePathCoforestEdge

abbrev d5Stage2TripleColor43CoforestParent :
    D5Stage2TripleColor43CoforestEdge →
      D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestParent

abbrev d5Stage2TripleColor43CoforestChild :
    D5Stage2TripleColor43CoforestEdge →
      D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestChild

abbrev d5Stage2TripleColor43CoforestDescendantCut :
    D5Stage2TripleColor43CoforestEdge →
      D5Stage2TripleColor43CoforestVertex → Prop :=
  twoEdgePathCoforestDescendantCut

abbrev d5Stage2TripleColor43CoforestDescendantCutDecidable :
    (cut : D5Stage2TripleColor43CoforestEdge) →
      (vertex : D5Stage2TripleColor43CoforestVertex) →
        Decidable
          (d5Stage2TripleColor43CoforestDescendantCut cut vertex) :=
  twoEdgePathCoforestDescendantCutDecidable

abbrev d5Stage2TripleColor43CoforestParentStep :
    D5Stage2TripleColor43CoforestVertex →
      D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestParentStep

abbrev d5Stage2TripleColor43CoforestRank :
    D5Stage2TripleColor43CoforestVertex → Nat :=
  twoEdgePathCoforestRank

abbrev d5Stage2TripleColor43CoforestEdgeTable :
    List D5Stage2TripleColor43CoforestEdge :=
  twoEdgePathCoforestEdgeTable

abbrev d5Stage2TripleColor43CoforestVertexTable :
    List D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestVertexTable

abbrev d5Stage2TripleColor43CoforestParentTable :
    List D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestParentTable

abbrev d5Stage2TripleColor43CoforestChildTable :
    List D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestChildTable

abbrev d5Stage2TripleColor43CoforestParentStepTable :
    List D5Stage2TripleColor43CoforestVertex :=
  twoEdgePathCoforestParentStepTable

abbrev d5Stage2TripleColor43CoforestRankTable : List Nat :=
  twoEdgePathCoforestRankTable

theorem d5Stage2TripleColor43CoforestEdgeTable_length :
    d5Stage2TripleColor43CoforestEdgeTable.length = 2 :=
  twoEdgePathCoforestEdgeTable_length

theorem d5Stage2TripleColor43CoforestVertexTable_length :
    d5Stage2TripleColor43CoforestVertexTable.length = 3 :=
  twoEdgePathCoforestVertexTable_length

theorem d5Stage2TripleColor43CoforestEdgeTable_nodup :
    d5Stage2TripleColor43CoforestEdgeTable.Nodup :=
  twoEdgePathCoforestEdgeTable_nodup

theorem d5Stage2TripleColor43CoforestVertexTable_nodup :
    d5Stage2TripleColor43CoforestVertexTable.Nodup :=
  twoEdgePathCoforestVertexTable_nodup

theorem d5Stage2TripleColor43CoforestParentTable_readout :
    d5Stage2TripleColor43CoforestParentTable =
      [TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  twoEdgePathCoforestParentTable_readout

theorem d5Stage2TripleColor43CoforestChildTable_readout :
    d5Stage2TripleColor43CoforestChildTable =
      [TwoEdgePathCoforestVertex.middle,
        TwoEdgePathCoforestVertex.leaf] :=
  twoEdgePathCoforestChildTable_readout

theorem d5Stage2TripleColor43CoforestParentStepTable_readout :
    d5Stage2TripleColor43CoforestParentStepTable =
      [TwoEdgePathCoforestVertex.root, TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  twoEdgePathCoforestParentStepTable_readout

theorem d5Stage2TripleColor43CoforestRankTable_readout :
    d5Stage2TripleColor43CoforestRankTable = [0, 1, 2] :=
  twoEdgePathCoforestRankTable_readout

abbrev d5Stage2TripleColor43CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage2TripleColor43CoforestParentStep
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild :=
  twoEdgePathCoforestRankedParentMapData

theorem d5Stage2TripleColor43CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage2TripleColor43CoforestDescendantCut
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild :=
  twoEdgePathCoforestParentMapBoundary

theorem d5Stage2TripleColor43CoforestIncidence_eq_ite
    (cut edge : D5Stage2TripleColor43CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  twoEdgePathCoforestIncidence_eq_ite cut edge

theorem d5Stage2TripleColor43CoforestIncidence_self
    (edge : D5Stage2TripleColor43CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild edge edge = 1 :=
  twoEdgePathCoforestIncidence_self edge

theorem d5Stage2TripleColor43CoforestIncidence_ne
    {cut edge : D5Stage2TripleColor43CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild cut edge = 0 :=
  twoEdgePathCoforestIncidence_ne hne

theorem d5Stage2TripleColor43CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2TripleColor43CoforestParentStep
        d5Stage2TripleColor43CoforestChild)
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild :=
  twoEdgePathCoforestIteratedParentMapBoundary

abbrev D5Stage2PairColor1CoforestVertex :=
  TwoEdgePathCoforestVertex

abbrev D5Stage2PairColor1CoforestEdge :=
  TwoEdgePathCoforestEdge

abbrev d5Stage2PairColor1CoforestParent :
    D5Stage2PairColor1CoforestEdge →
      D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestParent

abbrev d5Stage2PairColor1CoforestChild :
    D5Stage2PairColor1CoforestEdge →
      D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestChild

abbrev d5Stage2PairColor1CoforestDescendantCut :
    D5Stage2PairColor1CoforestEdge →
      D5Stage2PairColor1CoforestVertex → Prop :=
  twoEdgePathCoforestDescendantCut

abbrev d5Stage2PairColor1CoforestDescendantCutDecidable :
    (cut : D5Stage2PairColor1CoforestEdge) →
      (vertex : D5Stage2PairColor1CoforestVertex) →
        Decidable
          (d5Stage2PairColor1CoforestDescendantCut cut vertex) :=
  twoEdgePathCoforestDescendantCutDecidable

abbrev d5Stage2PairColor1CoforestParentStep :
    D5Stage2PairColor1CoforestVertex →
      D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestParentStep

abbrev d5Stage2PairColor1CoforestRank :
    D5Stage2PairColor1CoforestVertex → Nat :=
  twoEdgePathCoforestRank

abbrev d5Stage2PairColor1CoforestEdgeTable :
    List D5Stage2PairColor1CoforestEdge :=
  twoEdgePathCoforestEdgeTable

abbrev d5Stage2PairColor1CoforestVertexTable :
    List D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestVertexTable

abbrev d5Stage2PairColor1CoforestParentTable :
    List D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestParentTable

abbrev d5Stage2PairColor1CoforestChildTable :
    List D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestChildTable

abbrev d5Stage2PairColor1CoforestParentStepTable :
    List D5Stage2PairColor1CoforestVertex :=
  twoEdgePathCoforestParentStepTable

abbrev d5Stage2PairColor1CoforestRankTable : List Nat :=
  twoEdgePathCoforestRankTable

theorem d5Stage2PairColor1CoforestEdgeTable_length :
    d5Stage2PairColor1CoforestEdgeTable.length = 2 :=
  twoEdgePathCoforestEdgeTable_length

theorem d5Stage2PairColor1CoforestVertexTable_length :
    d5Stage2PairColor1CoforestVertexTable.length = 3 :=
  twoEdgePathCoforestVertexTable_length

theorem d5Stage2PairColor1CoforestEdgeTable_nodup :
    d5Stage2PairColor1CoforestEdgeTable.Nodup :=
  twoEdgePathCoforestEdgeTable_nodup

theorem d5Stage2PairColor1CoforestVertexTable_nodup :
    d5Stage2PairColor1CoforestVertexTable.Nodup :=
  twoEdgePathCoforestVertexTable_nodup

theorem d5Stage2PairColor1CoforestParentTable_readout :
    d5Stage2PairColor1CoforestParentTable =
      [TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  twoEdgePathCoforestParentTable_readout

theorem d5Stage2PairColor1CoforestChildTable_readout :
    d5Stage2PairColor1CoforestChildTable =
      [TwoEdgePathCoforestVertex.middle,
        TwoEdgePathCoforestVertex.leaf] :=
  twoEdgePathCoforestChildTable_readout

theorem d5Stage2PairColor1CoforestParentStepTable_readout :
    d5Stage2PairColor1CoforestParentStepTable =
      [TwoEdgePathCoforestVertex.root, TwoEdgePathCoforestVertex.root,
        TwoEdgePathCoforestVertex.middle] :=
  twoEdgePathCoforestParentStepTable_readout

theorem d5Stage2PairColor1CoforestRankTable_readout :
    d5Stage2PairColor1CoforestRankTable = [0, 1, 2] :=
  twoEdgePathCoforestRankTable_readout

abbrev d5Stage2PairColor1CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage2PairColor1CoforestParentStep
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild :=
  twoEdgePathCoforestRankedParentMapData

theorem d5Stage2PairColor1CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage2PairColor1CoforestDescendantCut
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild :=
  twoEdgePathCoforestParentMapBoundary

theorem d5Stage2PairColor1CoforestIncidence_eq_ite
    (cut edge : D5Stage2PairColor1CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  twoEdgePathCoforestIncidence_eq_ite cut edge

theorem d5Stage2PairColor1CoforestIncidence_self
    (edge : D5Stage2PairColor1CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild edge edge = 1 :=
  twoEdgePathCoforestIncidence_self edge

theorem d5Stage2PairColor1CoforestIncidence_ne
    {cut edge : D5Stage2PairColor1CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild cut edge = 0 :=
  twoEdgePathCoforestIncidence_ne hne

theorem d5Stage2PairColor1CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2PairColor1CoforestParentStep
        d5Stage2PairColor1CoforestChild)
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild :=
  twoEdgePathCoforestIteratedParentMapBoundary

abbrev D5Stage2PairColor2CoforestVertex :=
  TwoLeafStarCoforestVertex

abbrev D5Stage2PairColor2CoforestEdge :=
  TwoLeafStarCoforestEdge

abbrev d5Stage2PairColor2CoforestParent :
    D5Stage2PairColor2CoforestEdge →
      D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestParent

abbrev d5Stage2PairColor2CoforestChild :
    D5Stage2PairColor2CoforestEdge →
      D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestChild

abbrev d5Stage2PairColor2CoforestDescendantCut :
    D5Stage2PairColor2CoforestEdge →
      D5Stage2PairColor2CoforestVertex → Prop :=
  twoLeafStarCoforestDescendantCut

abbrev d5Stage2PairColor2CoforestDescendantCutDecidable :
    (cut : D5Stage2PairColor2CoforestEdge) →
      (vertex : D5Stage2PairColor2CoforestVertex) →
        Decidable
          (d5Stage2PairColor2CoforestDescendantCut cut vertex) :=
  twoLeafStarCoforestDescendantCutDecidable

abbrev d5Stage2PairColor2CoforestParentStep :
    D5Stage2PairColor2CoforestVertex →
      D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestParentStep

abbrev d5Stage2PairColor2CoforestRank :
    D5Stage2PairColor2CoforestVertex → Nat :=
  twoLeafStarCoforestRank

abbrev d5Stage2PairColor2CoforestEdgeTable :
    List D5Stage2PairColor2CoforestEdge :=
  twoLeafStarCoforestEdgeTable

abbrev d5Stage2PairColor2CoforestVertexTable :
    List D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestVertexTable

abbrev d5Stage2PairColor2CoforestParentTable :
    List D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestParentTable

abbrev d5Stage2PairColor2CoforestChildTable :
    List D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestChildTable

abbrev d5Stage2PairColor2CoforestParentStepTable :
    List D5Stage2PairColor2CoforestVertex :=
  twoLeafStarCoforestParentStepTable

abbrev d5Stage2PairColor2CoforestRankTable : List Nat :=
  twoLeafStarCoforestRankTable

theorem d5Stage2PairColor2CoforestEdgeTable_length :
    d5Stage2PairColor2CoforestEdgeTable.length = 2 :=
  twoLeafStarCoforestEdgeTable_length

theorem d5Stage2PairColor2CoforestVertexTable_length :
    d5Stage2PairColor2CoforestVertexTable.length = 3 :=
  twoLeafStarCoforestVertexTable_length

theorem d5Stage2PairColor2CoforestEdgeTable_nodup :
    d5Stage2PairColor2CoforestEdgeTable.Nodup :=
  twoLeafStarCoforestEdgeTable_nodup

theorem d5Stage2PairColor2CoforestVertexTable_nodup :
    d5Stage2PairColor2CoforestVertexTable.Nodup :=
  twoLeafStarCoforestVertexTable_nodup

theorem d5Stage2PairColor2CoforestParentTable_readout :
    d5Stage2PairColor2CoforestParentTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root] :=
  twoLeafStarCoforestParentTable_readout

theorem d5Stage2PairColor2CoforestChildTable_readout :
    d5Stage2PairColor2CoforestChildTable =
      [TwoLeafStarCoforestVertex.left, TwoLeafStarCoforestVertex.right] :=
  twoLeafStarCoforestChildTable_readout

theorem d5Stage2PairColor2CoforestParentStepTable_readout :
    d5Stage2PairColor2CoforestParentStepTable =
      [TwoLeafStarCoforestVertex.root, TwoLeafStarCoforestVertex.root,
        TwoLeafStarCoforestVertex.root] :=
  twoLeafStarCoforestParentStepTable_readout

theorem d5Stage2PairColor2CoforestRankTable_readout :
    d5Stage2PairColor2CoforestRankTable = [0, 1, 1] :=
  twoLeafStarCoforestRankTable_readout

abbrev d5Stage2PairColor2CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage2PairColor2CoforestParentStep
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild :=
  twoLeafStarCoforestRankedParentMapData

theorem d5Stage2PairColor2CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage2PairColor2CoforestDescendantCut
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild :=
  twoLeafStarCoforestParentMapBoundary

theorem d5Stage2PairColor2CoforestIncidence_eq_ite
    (cut edge : D5Stage2PairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  twoLeafStarCoforestIncidence_eq_ite cut edge

theorem d5Stage2PairColor2CoforestIncidence_self
    (edge : D5Stage2PairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild edge edge = 1 :=
  twoLeafStarCoforestIncidence_self edge

theorem d5Stage2PairColor2CoforestIncidence_ne
    {cut edge : D5Stage2PairColor2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild cut edge = 0 :=
  twoLeafStarCoforestIncidence_ne hne

theorem d5Stage2PairColor2CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2PairColor2CoforestParentStep
        d5Stage2PairColor2CoforestChild)
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild :=
  twoLeafStarCoforestIteratedParentMapBoundary

abbrev D5Stage3FinalPairColor0CoforestVertex :=
  OneEdgeCoforestVertex

abbrev D5Stage3FinalPairColor0CoforestEdge :=
  OneEdgeCoforestEdge

abbrev d5Stage3FinalPairColor0CoforestParent :
    D5Stage3FinalPairColor0CoforestEdge →
      D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestParent

abbrev d5Stage3FinalPairColor0CoforestChild :
    D5Stage3FinalPairColor0CoforestEdge →
      D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestChild

abbrev d5Stage3FinalPairColor0CoforestDescendantCut :
    D5Stage3FinalPairColor0CoforestEdge →
      D5Stage3FinalPairColor0CoforestVertex → Prop :=
  oneEdgeCoforestDescendantCut

abbrev d5Stage3FinalPairColor0CoforestDescendantCutDecidable :
    (cut : D5Stage3FinalPairColor0CoforestEdge) →
      (vertex : D5Stage3FinalPairColor0CoforestVertex) →
        Decidable
          (d5Stage3FinalPairColor0CoforestDescendantCut cut vertex) :=
  oneEdgeCoforestDescendantCutDecidable

abbrev d5Stage3FinalPairColor0CoforestParentStep :
    D5Stage3FinalPairColor0CoforestVertex →
      D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestParentStep

abbrev d5Stage3FinalPairColor0CoforestRank :
    D5Stage3FinalPairColor0CoforestVertex → Nat :=
  oneEdgeCoforestRank

abbrev d5Stage3FinalPairColor0CoforestEdgeTable :
    List D5Stage3FinalPairColor0CoforestEdge :=
  oneEdgeCoforestEdgeTable

abbrev d5Stage3FinalPairColor0CoforestVertexTable :
    List D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestVertexTable

abbrev d5Stage3FinalPairColor0CoforestParentTable :
    List D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestParentTable

abbrev d5Stage3FinalPairColor0CoforestChildTable :
    List D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestChildTable

abbrev d5Stage3FinalPairColor0CoforestParentStepTable :
    List D5Stage3FinalPairColor0CoforestVertex :=
  oneEdgeCoforestParentStepTable

abbrev d5Stage3FinalPairColor0CoforestRankTable : List Nat :=
  oneEdgeCoforestRankTable

theorem d5Stage3FinalPairColor0CoforestEdgeTable_length :
    d5Stage3FinalPairColor0CoforestEdgeTable.length = 1 :=
  oneEdgeCoforestEdgeTable_length

theorem d5Stage3FinalPairColor0CoforestVertexTable_length :
    d5Stage3FinalPairColor0CoforestVertexTable.length = 2 :=
  oneEdgeCoforestVertexTable_length

theorem d5Stage3FinalPairColor0CoforestEdgeTable_nodup :
    d5Stage3FinalPairColor0CoforestEdgeTable.Nodup :=
  oneEdgeCoforestEdgeTable_nodup

theorem d5Stage3FinalPairColor0CoforestVertexTable_nodup :
    d5Stage3FinalPairColor0CoforestVertexTable.Nodup :=
  oneEdgeCoforestVertexTable_nodup

theorem d5Stage3FinalPairColor0CoforestParentTable_readout :
    d5Stage3FinalPairColor0CoforestParentTable =
      [OneEdgeCoforestVertex.root] :=
  oneEdgeCoforestParentTable_readout

theorem d5Stage3FinalPairColor0CoforestChildTable_readout :
    d5Stage3FinalPairColor0CoforestChildTable =
      [OneEdgeCoforestVertex.leaf] :=
  oneEdgeCoforestChildTable_readout

theorem d5Stage3FinalPairColor0CoforestParentStepTable_readout :
    d5Stage3FinalPairColor0CoforestParentStepTable =
      [OneEdgeCoforestVertex.root, OneEdgeCoforestVertex.root] :=
  oneEdgeCoforestParentStepTable_readout

theorem d5Stage3FinalPairColor0CoforestRankTable_readout :
    d5Stage3FinalPairColor0CoforestRankTable = [0, 1] :=
  oneEdgeCoforestRankTable_readout

abbrev d5Stage3FinalPairColor0CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage3FinalPairColor0CoforestParentStep
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild :=
  oneEdgeCoforestRankedParentMapData

theorem d5Stage3FinalPairColor0CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage3FinalPairColor0CoforestDescendantCut
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild :=
  oneEdgeCoforestParentMapBoundary

theorem d5Stage3FinalPairColor0CoforestIncidence_eq_ite
    (cut edge : D5Stage3FinalPairColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  oneEdgeCoforestIncidence_eq_ite cut edge

theorem d5Stage3FinalPairColor0CoforestIncidence_self
    (edge : D5Stage3FinalPairColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild edge edge = 1 :=
  oneEdgeCoforestIncidence_self edge

theorem d5Stage3FinalPairColor0CoforestIncidence_ne
    {cut edge : D5Stage3FinalPairColor0CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild cut edge = 0 :=
  oneEdgeCoforestIncidence_ne hne

theorem d5Stage3FinalPairColor0CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage3FinalPairColor0CoforestParentStep
        d5Stage3FinalPairColor0CoforestChild)
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild :=
  oneEdgeCoforestIteratedParentMapBoundary

abbrev D5Stage3FinalPairColor2CoforestVertex :=
  OneEdgeCoforestVertex

abbrev D5Stage3FinalPairColor2CoforestEdge :=
  OneEdgeCoforestEdge

abbrev d5Stage3FinalPairColor2CoforestParent :
    D5Stage3FinalPairColor2CoforestEdge →
      D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestParent

abbrev d5Stage3FinalPairColor2CoforestChild :
    D5Stage3FinalPairColor2CoforestEdge →
      D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestChild

abbrev d5Stage3FinalPairColor2CoforestDescendantCut :
    D5Stage3FinalPairColor2CoforestEdge →
      D5Stage3FinalPairColor2CoforestVertex → Prop :=
  oneEdgeCoforestDescendantCut

abbrev d5Stage3FinalPairColor2CoforestDescendantCutDecidable :
    (cut : D5Stage3FinalPairColor2CoforestEdge) →
      (vertex : D5Stage3FinalPairColor2CoforestVertex) →
        Decidable
          (d5Stage3FinalPairColor2CoforestDescendantCut cut vertex) :=
  oneEdgeCoforestDescendantCutDecidable

abbrev d5Stage3FinalPairColor2CoforestParentStep :
    D5Stage3FinalPairColor2CoforestVertex →
      D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestParentStep

abbrev d5Stage3FinalPairColor2CoforestRank :
    D5Stage3FinalPairColor2CoforestVertex → Nat :=
  oneEdgeCoforestRank

abbrev d5Stage3FinalPairColor2CoforestEdgeTable :
    List D5Stage3FinalPairColor2CoforestEdge :=
  oneEdgeCoforestEdgeTable

abbrev d5Stage3FinalPairColor2CoforestVertexTable :
    List D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestVertexTable

abbrev d5Stage3FinalPairColor2CoforestParentTable :
    List D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestParentTable

abbrev d5Stage3FinalPairColor2CoforestChildTable :
    List D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestChildTable

abbrev d5Stage3FinalPairColor2CoforestParentStepTable :
    List D5Stage3FinalPairColor2CoforestVertex :=
  oneEdgeCoforestParentStepTable

abbrev d5Stage3FinalPairColor2CoforestRankTable : List Nat :=
  oneEdgeCoforestRankTable

theorem d5Stage3FinalPairColor2CoforestEdgeTable_length :
    d5Stage3FinalPairColor2CoforestEdgeTable.length = 1 :=
  oneEdgeCoforestEdgeTable_length

theorem d5Stage3FinalPairColor2CoforestVertexTable_length :
    d5Stage3FinalPairColor2CoforestVertexTable.length = 2 :=
  oneEdgeCoforestVertexTable_length

theorem d5Stage3FinalPairColor2CoforestEdgeTable_nodup :
    d5Stage3FinalPairColor2CoforestEdgeTable.Nodup :=
  oneEdgeCoforestEdgeTable_nodup

theorem d5Stage3FinalPairColor2CoforestVertexTable_nodup :
    d5Stage3FinalPairColor2CoforestVertexTable.Nodup :=
  oneEdgeCoforestVertexTable_nodup

theorem d5Stage3FinalPairColor2CoforestParentTable_readout :
    d5Stage3FinalPairColor2CoforestParentTable =
      [OneEdgeCoforestVertex.root] :=
  oneEdgeCoforestParentTable_readout

theorem d5Stage3FinalPairColor2CoforestChildTable_readout :
    d5Stage3FinalPairColor2CoforestChildTable =
      [OneEdgeCoforestVertex.leaf] :=
  oneEdgeCoforestChildTable_readout

theorem d5Stage3FinalPairColor2CoforestParentStepTable_readout :
    d5Stage3FinalPairColor2CoforestParentStepTable =
      [OneEdgeCoforestVertex.root, OneEdgeCoforestVertex.root] :=
  oneEdgeCoforestParentStepTable_readout

theorem d5Stage3FinalPairColor2CoforestRankTable_readout :
    d5Stage3FinalPairColor2CoforestRankTable = [0, 1] :=
  oneEdgeCoforestRankTable_readout

abbrev d5Stage3FinalPairColor2CoforestRankedParentMapData :
    RankedRootedParentMapData
      d5Stage3FinalPairColor2CoforestParentStep
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild :=
  oneEdgeCoforestRankedParentMapData

theorem d5Stage3FinalPairColor2CoforestParentMapBoundary :
    ParentMapBoundary
      d5Stage3FinalPairColor2CoforestDescendantCut
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild :=
  oneEdgeCoforestParentMapBoundary

theorem d5Stage3FinalPairColor2CoforestIncidence_eq_ite
    (cut edge : D5Stage3FinalPairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  oneEdgeCoforestIncidence_eq_ite cut edge

theorem d5Stage3FinalPairColor2CoforestIncidence_self
    (edge : D5Stage3FinalPairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild edge edge = 1 :=
  oneEdgeCoforestIncidence_self edge

theorem d5Stage3FinalPairColor2CoforestIncidence_ne
    {cut edge : D5Stage3FinalPairColor2CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild cut edge = 0 :=
  oneEdgeCoforestIncidence_ne hne

theorem d5Stage3FinalPairColor2CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage3FinalPairColor2CoforestParentStep
        d5Stage3FinalPairColor2CoforestChild)
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild :=
  oneEdgeCoforestIteratedParentMapBoundary

inductive FiveLeafStarCoforestVertex where
  | root
  | leaf1
  | leaf2
  | leaf3
  | leaf4
  | leaf5
  deriving DecidableEq, Repr

inductive FiveLeafStarCoforestEdge where
  | root1
  | root2
  | root3
  | root4
  | root5
  deriving DecidableEq, Repr

def fiveLeafStarCoforestParent :
    FiveLeafStarCoforestEdge → FiveLeafStarCoforestVertex
  | FiveLeafStarCoforestEdge.root1 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestEdge.root2 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestEdge.root3 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestEdge.root4 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestEdge.root5 =>
      FiveLeafStarCoforestVertex.root

def fiveLeafStarCoforestChild :
    FiveLeafStarCoforestEdge → FiveLeafStarCoforestVertex
  | FiveLeafStarCoforestEdge.root1 =>
      FiveLeafStarCoforestVertex.leaf1
  | FiveLeafStarCoforestEdge.root2 =>
      FiveLeafStarCoforestVertex.leaf2
  | FiveLeafStarCoforestEdge.root3 =>
      FiveLeafStarCoforestVertex.leaf3
  | FiveLeafStarCoforestEdge.root4 =>
      FiveLeafStarCoforestVertex.leaf4
  | FiveLeafStarCoforestEdge.root5 =>
      FiveLeafStarCoforestVertex.leaf5

def fiveLeafStarCoforestDescendantCut :
    FiveLeafStarCoforestEdge → FiveLeafStarCoforestVertex → Prop
  | FiveLeafStarCoforestEdge.root1,
      FiveLeafStarCoforestVertex.leaf1 => True
  | FiveLeafStarCoforestEdge.root2,
      FiveLeafStarCoforestVertex.leaf2 => True
  | FiveLeafStarCoforestEdge.root3,
      FiveLeafStarCoforestVertex.leaf3 => True
  | FiveLeafStarCoforestEdge.root4,
      FiveLeafStarCoforestVertex.leaf4 => True
  | FiveLeafStarCoforestEdge.root5,
      FiveLeafStarCoforestVertex.leaf5 => True
  | _, _ => False

def fiveLeafStarCoforestDescendantCutDecidable :
    (cut : FiveLeafStarCoforestEdge) →
      (vertex : FiveLeafStarCoforestVertex) →
        Decidable (fiveLeafStarCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def fiveLeafStarCoforestParentStep :
    FiveLeafStarCoforestVertex → FiveLeafStarCoforestVertex
  | FiveLeafStarCoforestVertex.root =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestVertex.leaf1 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestVertex.leaf2 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestVertex.leaf3 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestVertex.leaf4 =>
      FiveLeafStarCoforestVertex.root
  | FiveLeafStarCoforestVertex.leaf5 =>
      FiveLeafStarCoforestVertex.root

def fiveLeafStarCoforestRank : FiveLeafStarCoforestVertex → Nat
  | FiveLeafStarCoforestVertex.root => 0
  | FiveLeafStarCoforestVertex.leaf1 => 1
  | FiveLeafStarCoforestVertex.leaf2 => 1
  | FiveLeafStarCoforestVertex.leaf3 => 1
  | FiveLeafStarCoforestVertex.leaf4 => 1
  | FiveLeafStarCoforestVertex.leaf5 => 1

def fiveLeafStarCoforestRankedParentMapData :
    RankedRootedParentMapData
      fiveLeafStarCoforestParentStep
      fiveLeafStarCoforestParent
      fiveLeafStarCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [fiveLeafStarCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := fiveLeafStarCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem fiveLeafStarCoforestParentMapBoundary :
    ParentMapBoundary
      fiveLeafStarCoforestDescendantCut
      fiveLeafStarCoforestParent
      fiveLeafStarCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [fiveLeafStarCoforestDescendantCut,
        fiveLeafStarCoforestChild]
  · intro edge
    cases edge <;>
      simp [fiveLeafStarCoforestDescendantCut,
        fiveLeafStarCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [fiveLeafStarCoforestDescendantCut,
        fiveLeafStarCoforestParent,
        fiveLeafStarCoforestChild] at hne ⊢

theorem fiveLeafStarCoforestIncidence_eq_ite
    (cut edge : FiveLeafStarCoforestEdge) :
    @parentMapIncidence
        FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
        fiveLeafStarCoforestDescendantCut
        fiveLeafStarCoforestDescendantCutDecidable
        fiveLeafStarCoforestParent
        fiveLeafStarCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
    inferInstance
    fiveLeafStarCoforestDescendantCut
    fiveLeafStarCoforestDescendantCutDecidable
    fiveLeafStarCoforestParent fiveLeafStarCoforestChild
    fiveLeafStarCoforestParentMapBoundary cut edge

theorem fiveLeafStarCoforestIncidence_self
    (edge : FiveLeafStarCoforestEdge) :
    @parentMapIncidence
        FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
        fiveLeafStarCoforestDescendantCut
        fiveLeafStarCoforestDescendantCutDecidable
        fiveLeafStarCoforestParent
        fiveLeafStarCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
    fiveLeafStarCoforestDescendantCut
    fiveLeafStarCoforestDescendantCutDecidable
    fiveLeafStarCoforestParent fiveLeafStarCoforestChild
    fiveLeafStarCoforestParentMapBoundary edge

theorem fiveLeafStarCoforestIncidence_ne
    {cut edge : FiveLeafStarCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
        fiveLeafStarCoforestDescendantCut
        fiveLeafStarCoforestDescendantCutDecidable
        fiveLeafStarCoforestParent
        fiveLeafStarCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    FiveLeafStarCoforestVertex FiveLeafStarCoforestEdge
    fiveLeafStarCoforestDescendantCut
    fiveLeafStarCoforestDescendantCutDecidable
    fiveLeafStarCoforestParent fiveLeafStarCoforestChild
    fiveLeafStarCoforestParentMapBoundary cut edge hne

theorem fiveLeafStarCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut fiveLeafStarCoforestParentStep
        fiveLeafStarCoforestChild)
      fiveLeafStarCoforestParent
      fiveLeafStarCoforestChild :=
  rankedRootedParentMapBoundary
    fiveLeafStarCoforestRankedParentMapData

inductive RootHubThreeLeafCoforestVertex where
  | root
  | hub
  | leaf1
  | leaf2
  | leaf3
  | mate
  deriving DecidableEq, Repr

inductive RootHubThreeLeafCoforestEdge where
  | rootHub
  | hub1
  | hub2
  | hub3
  | rootMate
  deriving DecidableEq, Repr

def rootHubThreeLeafCoforestParent :
    RootHubThreeLeafCoforestEdge → RootHubThreeLeafCoforestVertex
  | RootHubThreeLeafCoforestEdge.rootHub =>
      RootHubThreeLeafCoforestVertex.root
  | RootHubThreeLeafCoforestEdge.hub1 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestEdge.hub2 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestEdge.hub3 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestEdge.rootMate =>
      RootHubThreeLeafCoforestVertex.root

def rootHubThreeLeafCoforestChild :
    RootHubThreeLeafCoforestEdge → RootHubThreeLeafCoforestVertex
  | RootHubThreeLeafCoforestEdge.rootHub =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestEdge.hub1 =>
      RootHubThreeLeafCoforestVertex.leaf1
  | RootHubThreeLeafCoforestEdge.hub2 =>
      RootHubThreeLeafCoforestVertex.leaf2
  | RootHubThreeLeafCoforestEdge.hub3 =>
      RootHubThreeLeafCoforestVertex.leaf3
  | RootHubThreeLeafCoforestEdge.rootMate =>
      RootHubThreeLeafCoforestVertex.mate

def rootHubThreeLeafCoforestDescendantCut :
    RootHubThreeLeafCoforestEdge →
      RootHubThreeLeafCoforestVertex → Prop
  | RootHubThreeLeafCoforestEdge.rootHub,
      RootHubThreeLeafCoforestVertex.hub => True
  | RootHubThreeLeafCoforestEdge.rootHub,
      RootHubThreeLeafCoforestVertex.leaf1 => True
  | RootHubThreeLeafCoforestEdge.rootHub,
      RootHubThreeLeafCoforestVertex.leaf2 => True
  | RootHubThreeLeafCoforestEdge.rootHub,
      RootHubThreeLeafCoforestVertex.leaf3 => True
  | RootHubThreeLeafCoforestEdge.hub1,
      RootHubThreeLeafCoforestVertex.leaf1 => True
  | RootHubThreeLeafCoforestEdge.hub2,
      RootHubThreeLeafCoforestVertex.leaf2 => True
  | RootHubThreeLeafCoforestEdge.hub3,
      RootHubThreeLeafCoforestVertex.leaf3 => True
  | RootHubThreeLeafCoforestEdge.rootMate,
      RootHubThreeLeafCoforestVertex.mate => True
  | _, _ => False

def rootHubThreeLeafCoforestDescendantCutDecidable :
    (cut : RootHubThreeLeafCoforestEdge) →
      (vertex : RootHubThreeLeafCoforestVertex) →
        Decidable
          (rootHubThreeLeafCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def rootHubThreeLeafCoforestParentStep :
    RootHubThreeLeafCoforestVertex → RootHubThreeLeafCoforestVertex
  | RootHubThreeLeafCoforestVertex.root =>
      RootHubThreeLeafCoforestVertex.root
  | RootHubThreeLeafCoforestVertex.hub =>
      RootHubThreeLeafCoforestVertex.root
  | RootHubThreeLeafCoforestVertex.leaf1 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestVertex.leaf2 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestVertex.leaf3 =>
      RootHubThreeLeafCoforestVertex.hub
  | RootHubThreeLeafCoforestVertex.mate =>
      RootHubThreeLeafCoforestVertex.root

def rootHubThreeLeafCoforestRank :
    RootHubThreeLeafCoforestVertex → Nat
  | RootHubThreeLeafCoforestVertex.root => 0
  | RootHubThreeLeafCoforestVertex.hub => 1
  | RootHubThreeLeafCoforestVertex.leaf1 => 2
  | RootHubThreeLeafCoforestVertex.leaf2 => 2
  | RootHubThreeLeafCoforestVertex.leaf3 => 2
  | RootHubThreeLeafCoforestVertex.mate => 1

def rootHubThreeLeafCoforestRankedParentMapData :
    RankedRootedParentMapData
      rootHubThreeLeafCoforestParentStep
      rootHubThreeLeafCoforestParent
      rootHubThreeLeafCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [rootHubThreeLeafCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := rootHubThreeLeafCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem rootHubThreeLeafCoforestParentMapBoundary :
    ParentMapBoundary
      rootHubThreeLeafCoforestDescendantCut
      rootHubThreeLeafCoforestParent
      rootHubThreeLeafCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [rootHubThreeLeafCoforestDescendantCut,
        rootHubThreeLeafCoforestChild]
  · intro edge
    cases edge <;>
      simp [rootHubThreeLeafCoforestDescendantCut,
        rootHubThreeLeafCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [rootHubThreeLeafCoforestDescendantCut,
        rootHubThreeLeafCoforestParent,
        rootHubThreeLeafCoforestChild] at hne ⊢

theorem rootHubThreeLeafCoforestIncidence_eq_ite
    (cut edge : RootHubThreeLeafCoforestEdge) :
    @parentMapIncidence
        RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
        rootHubThreeLeafCoforestDescendantCut
        rootHubThreeLeafCoforestDescendantCutDecidable
        rootHubThreeLeafCoforestParent
        rootHubThreeLeafCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
    inferInstance
    rootHubThreeLeafCoforestDescendantCut
    rootHubThreeLeafCoforestDescendantCutDecidable
    rootHubThreeLeafCoforestParent rootHubThreeLeafCoforestChild
    rootHubThreeLeafCoforestParentMapBoundary cut edge

theorem rootHubThreeLeafCoforestIncidence_self
    (edge : RootHubThreeLeafCoforestEdge) :
    @parentMapIncidence
        RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
        rootHubThreeLeafCoforestDescendantCut
        rootHubThreeLeafCoforestDescendantCutDecidable
        rootHubThreeLeafCoforestParent
        rootHubThreeLeafCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
    rootHubThreeLeafCoforestDescendantCut
    rootHubThreeLeafCoforestDescendantCutDecidable
    rootHubThreeLeafCoforestParent rootHubThreeLeafCoforestChild
    rootHubThreeLeafCoforestParentMapBoundary edge

theorem rootHubThreeLeafCoforestIncidence_ne
    {cut edge : RootHubThreeLeafCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
        rootHubThreeLeafCoforestDescendantCut
        rootHubThreeLeafCoforestDescendantCutDecidable
        rootHubThreeLeafCoforestParent
        rootHubThreeLeafCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    RootHubThreeLeafCoforestVertex RootHubThreeLeafCoforestEdge
    rootHubThreeLeafCoforestDescendantCut
    rootHubThreeLeafCoforestDescendantCutDecidable
    rootHubThreeLeafCoforestParent rootHubThreeLeafCoforestChild
    rootHubThreeLeafCoforestParentMapBoundary cut edge hne

theorem rootHubThreeLeafCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut rootHubThreeLeafCoforestParentStep
        rootHubThreeLeafCoforestChild)
      rootHubThreeLeafCoforestParent
      rootHubThreeLeafCoforestChild :=
  rankedRootedParentMapBoundary
    rootHubThreeLeafCoforestRankedParentMapData

inductive FourLeafStarCoforestVertex where
  | root
  | leaf1
  | leaf2
  | leaf3
  | leaf4
  deriving DecidableEq, Repr

inductive FourLeafStarCoforestEdge where
  | root1
  | root2
  | root3
  | root4
  deriving DecidableEq, Repr

def fourLeafStarCoforestParent :
    FourLeafStarCoforestEdge → FourLeafStarCoforestVertex
  | FourLeafStarCoforestEdge.root1 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestEdge.root2 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestEdge.root3 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestEdge.root4 =>
      FourLeafStarCoforestVertex.root

def fourLeafStarCoforestChild :
    FourLeafStarCoforestEdge → FourLeafStarCoforestVertex
  | FourLeafStarCoforestEdge.root1 =>
      FourLeafStarCoforestVertex.leaf1
  | FourLeafStarCoforestEdge.root2 =>
      FourLeafStarCoforestVertex.leaf2
  | FourLeafStarCoforestEdge.root3 =>
      FourLeafStarCoforestVertex.leaf3
  | FourLeafStarCoforestEdge.root4 =>
      FourLeafStarCoforestVertex.leaf4

def fourLeafStarCoforestDescendantCut :
    FourLeafStarCoforestEdge → FourLeafStarCoforestVertex → Prop
  | FourLeafStarCoforestEdge.root1,
      FourLeafStarCoforestVertex.leaf1 => True
  | FourLeafStarCoforestEdge.root2,
      FourLeafStarCoforestVertex.leaf2 => True
  | FourLeafStarCoforestEdge.root3,
      FourLeafStarCoforestVertex.leaf3 => True
  | FourLeafStarCoforestEdge.root4,
      FourLeafStarCoforestVertex.leaf4 => True
  | _, _ => False

def fourLeafStarCoforestDescendantCutDecidable :
    (cut : FourLeafStarCoforestEdge) →
      (vertex : FourLeafStarCoforestVertex) →
        Decidable (fourLeafStarCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def fourLeafStarCoforestParentStep :
    FourLeafStarCoforestVertex → FourLeafStarCoforestVertex
  | FourLeafStarCoforestVertex.root =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestVertex.leaf1 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestVertex.leaf2 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestVertex.leaf3 =>
      FourLeafStarCoforestVertex.root
  | FourLeafStarCoforestVertex.leaf4 =>
      FourLeafStarCoforestVertex.root

def fourLeafStarCoforestRank :
    FourLeafStarCoforestVertex → Nat
  | FourLeafStarCoforestVertex.root => 0
  | FourLeafStarCoforestVertex.leaf1 => 1
  | FourLeafStarCoforestVertex.leaf2 => 1
  | FourLeafStarCoforestVertex.leaf3 => 1
  | FourLeafStarCoforestVertex.leaf4 => 1

def fourLeafStarCoforestRankedParentMapData :
    RankedRootedParentMapData
      fourLeafStarCoforestParentStep
      fourLeafStarCoforestParent
      fourLeafStarCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [fourLeafStarCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := fourLeafStarCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem fourLeafStarCoforestParentMapBoundary :
    ParentMapBoundary
      fourLeafStarCoforestDescendantCut
      fourLeafStarCoforestParent
      fourLeafStarCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [fourLeafStarCoforestDescendantCut,
        fourLeafStarCoforestChild]
  · intro edge
    cases edge <;>
      simp [fourLeafStarCoforestDescendantCut,
        fourLeafStarCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [fourLeafStarCoforestDescendantCut,
        fourLeafStarCoforestParent,
        fourLeafStarCoforestChild] at hne ⊢

theorem fourLeafStarCoforestIncidence_eq_ite
    (cut edge : FourLeafStarCoforestEdge) :
    @parentMapIncidence
        FourLeafStarCoforestVertex FourLeafStarCoforestEdge
        fourLeafStarCoforestDescendantCut
        fourLeafStarCoforestDescendantCutDecidable
        fourLeafStarCoforestParent
        fourLeafStarCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    FourLeafStarCoforestVertex FourLeafStarCoforestEdge
    inferInstance
    fourLeafStarCoforestDescendantCut
    fourLeafStarCoforestDescendantCutDecidable
    fourLeafStarCoforestParent fourLeafStarCoforestChild
    fourLeafStarCoforestParentMapBoundary cut edge

theorem fourLeafStarCoforestIncidence_self
    (edge : FourLeafStarCoforestEdge) :
    @parentMapIncidence
        FourLeafStarCoforestVertex FourLeafStarCoforestEdge
        fourLeafStarCoforestDescendantCut
        fourLeafStarCoforestDescendantCutDecidable
        fourLeafStarCoforestParent
        fourLeafStarCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    FourLeafStarCoforestVertex FourLeafStarCoforestEdge
    fourLeafStarCoforestDescendantCut
    fourLeafStarCoforestDescendantCutDecidable
    fourLeafStarCoforestParent fourLeafStarCoforestChild
    fourLeafStarCoforestParentMapBoundary edge

theorem fourLeafStarCoforestIncidence_ne
    {cut edge : FourLeafStarCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        FourLeafStarCoforestVertex FourLeafStarCoforestEdge
        fourLeafStarCoforestDescendantCut
        fourLeafStarCoforestDescendantCutDecidable
        fourLeafStarCoforestParent
        fourLeafStarCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    FourLeafStarCoforestVertex FourLeafStarCoforestEdge
    fourLeafStarCoforestDescendantCut
    fourLeafStarCoforestDescendantCutDecidable
    fourLeafStarCoforestParent fourLeafStarCoforestChild
    fourLeafStarCoforestParentMapBoundary cut edge hne

theorem fourLeafStarCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut fourLeafStarCoforestParentStep
        fourLeafStarCoforestChild)
      fourLeafStarCoforestParent
      fourLeafStarCoforestChild :=
  rankedRootedParentMapBoundary
    fourLeafStarCoforestRankedParentMapData

inductive TwoPathForkCoforestVertex where
  | root
  | left
  | leftLeaf
  | right
  | rightLeaf
  deriving DecidableEq, Repr

inductive TwoPathForkCoforestEdge where
  | rootLeft
  | leftLeaf
  | rootRight
  | rightLeaf
  deriving DecidableEq, Repr

def twoPathForkCoforestParent :
    TwoPathForkCoforestEdge → TwoPathForkCoforestVertex
  | TwoPathForkCoforestEdge.rootLeft =>
      TwoPathForkCoforestVertex.root
  | TwoPathForkCoforestEdge.leftLeaf =>
      TwoPathForkCoforestVertex.left
  | TwoPathForkCoforestEdge.rootRight =>
      TwoPathForkCoforestVertex.root
  | TwoPathForkCoforestEdge.rightLeaf =>
      TwoPathForkCoforestVertex.right

def twoPathForkCoforestChild :
    TwoPathForkCoforestEdge → TwoPathForkCoforestVertex
  | TwoPathForkCoforestEdge.rootLeft =>
      TwoPathForkCoforestVertex.left
  | TwoPathForkCoforestEdge.leftLeaf =>
      TwoPathForkCoforestVertex.leftLeaf
  | TwoPathForkCoforestEdge.rootRight =>
      TwoPathForkCoforestVertex.right
  | TwoPathForkCoforestEdge.rightLeaf =>
      TwoPathForkCoforestVertex.rightLeaf

def twoPathForkCoforestDescendantCut :
    TwoPathForkCoforestEdge → TwoPathForkCoforestVertex → Prop
  | TwoPathForkCoforestEdge.rootLeft,
      TwoPathForkCoforestVertex.left => True
  | TwoPathForkCoforestEdge.rootLeft,
      TwoPathForkCoforestVertex.leftLeaf => True
  | TwoPathForkCoforestEdge.leftLeaf,
      TwoPathForkCoforestVertex.leftLeaf => True
  | TwoPathForkCoforestEdge.rootRight,
      TwoPathForkCoforestVertex.right => True
  | TwoPathForkCoforestEdge.rootRight,
      TwoPathForkCoforestVertex.rightLeaf => True
  | TwoPathForkCoforestEdge.rightLeaf,
      TwoPathForkCoforestVertex.rightLeaf => True
  | _, _ => False

def twoPathForkCoforestDescendantCutDecidable :
    (cut : TwoPathForkCoforestEdge) →
      (vertex : TwoPathForkCoforestVertex) →
        Decidable (twoPathForkCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def twoPathForkCoforestParentStep :
    TwoPathForkCoforestVertex → TwoPathForkCoforestVertex
  | TwoPathForkCoforestVertex.root =>
      TwoPathForkCoforestVertex.root
  | TwoPathForkCoforestVertex.left =>
      TwoPathForkCoforestVertex.root
  | TwoPathForkCoforestVertex.leftLeaf =>
      TwoPathForkCoforestVertex.left
  | TwoPathForkCoforestVertex.right =>
      TwoPathForkCoforestVertex.root
  | TwoPathForkCoforestVertex.rightLeaf =>
      TwoPathForkCoforestVertex.right

def twoPathForkCoforestRank :
    TwoPathForkCoforestVertex → Nat
  | TwoPathForkCoforestVertex.root => 0
  | TwoPathForkCoforestVertex.left => 1
  | TwoPathForkCoforestVertex.leftLeaf => 2
  | TwoPathForkCoforestVertex.right => 1
  | TwoPathForkCoforestVertex.rightLeaf => 2

def twoPathForkCoforestRankedParentMapData :
    RankedRootedParentMapData
      twoPathForkCoforestParentStep
      twoPathForkCoforestParent
      twoPathForkCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [twoPathForkCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := twoPathForkCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem twoPathForkCoforestParentMapBoundary :
    ParentMapBoundary
      twoPathForkCoforestDescendantCut
      twoPathForkCoforestParent
      twoPathForkCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [twoPathForkCoforestDescendantCut,
        twoPathForkCoforestChild]
  · intro edge
    cases edge <;>
      simp [twoPathForkCoforestDescendantCut,
        twoPathForkCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [twoPathForkCoforestDescendantCut,
        twoPathForkCoforestParent,
        twoPathForkCoforestChild] at hne ⊢

theorem twoPathForkCoforestIncidence_eq_ite
    (cut edge : TwoPathForkCoforestEdge) :
    @parentMapIncidence
        TwoPathForkCoforestVertex TwoPathForkCoforestEdge
        twoPathForkCoforestDescendantCut
        twoPathForkCoforestDescendantCutDecidable
        twoPathForkCoforestParent
        twoPathForkCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    TwoPathForkCoforestVertex TwoPathForkCoforestEdge
    inferInstance
    twoPathForkCoforestDescendantCut
    twoPathForkCoforestDescendantCutDecidable
    twoPathForkCoforestParent twoPathForkCoforestChild
    twoPathForkCoforestParentMapBoundary cut edge

theorem twoPathForkCoforestIncidence_self
    (edge : TwoPathForkCoforestEdge) :
    @parentMapIncidence
        TwoPathForkCoforestVertex TwoPathForkCoforestEdge
        twoPathForkCoforestDescendantCut
        twoPathForkCoforestDescendantCutDecidable
        twoPathForkCoforestParent
        twoPathForkCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    TwoPathForkCoforestVertex TwoPathForkCoforestEdge
    twoPathForkCoforestDescendantCut
    twoPathForkCoforestDescendantCutDecidable
    twoPathForkCoforestParent twoPathForkCoforestChild
    twoPathForkCoforestParentMapBoundary edge

theorem twoPathForkCoforestIncidence_ne
    {cut edge : TwoPathForkCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        TwoPathForkCoforestVertex TwoPathForkCoforestEdge
        twoPathForkCoforestDescendantCut
        twoPathForkCoforestDescendantCutDecidable
        twoPathForkCoforestParent
        twoPathForkCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    TwoPathForkCoforestVertex TwoPathForkCoforestEdge
    twoPathForkCoforestDescendantCut
    twoPathForkCoforestDescendantCutDecidable
    twoPathForkCoforestParent twoPathForkCoforestChild
    twoPathForkCoforestParentMapBoundary cut edge hne

theorem twoPathForkCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut twoPathForkCoforestParentStep
        twoPathForkCoforestChild)
      twoPathForkCoforestParent
      twoPathForkCoforestChild :=
  rankedRootedParentMapBoundary
    twoPathForkCoforestRankedParentMapData

inductive RootHubThreeLeafNoMateCoforestVertex where
  | root
  | hub
  | leaf1
  | leaf2
  | leaf3
  deriving DecidableEq, Repr

inductive RootHubThreeLeafNoMateCoforestEdge where
  | rootHub
  | hub1
  | hub2
  | hub3
  deriving DecidableEq, Repr

def rootHubThreeLeafNoMateCoforestParent :
    RootHubThreeLeafNoMateCoforestEdge →
      RootHubThreeLeafNoMateCoforestVertex
  | RootHubThreeLeafNoMateCoforestEdge.rootHub =>
      RootHubThreeLeafNoMateCoforestVertex.root
  | RootHubThreeLeafNoMateCoforestEdge.hub1 =>
      RootHubThreeLeafNoMateCoforestVertex.hub
  | RootHubThreeLeafNoMateCoforestEdge.hub2 =>
      RootHubThreeLeafNoMateCoforestVertex.hub
  | RootHubThreeLeafNoMateCoforestEdge.hub3 =>
      RootHubThreeLeafNoMateCoforestVertex.hub

def rootHubThreeLeafNoMateCoforestChild :
    RootHubThreeLeafNoMateCoforestEdge →
      RootHubThreeLeafNoMateCoforestVertex
  | RootHubThreeLeafNoMateCoforestEdge.rootHub =>
      RootHubThreeLeafNoMateCoforestVertex.hub
  | RootHubThreeLeafNoMateCoforestEdge.hub1 =>
      RootHubThreeLeafNoMateCoforestVertex.leaf1
  | RootHubThreeLeafNoMateCoforestEdge.hub2 =>
      RootHubThreeLeafNoMateCoforestVertex.leaf2
  | RootHubThreeLeafNoMateCoforestEdge.hub3 =>
      RootHubThreeLeafNoMateCoforestVertex.leaf3

def rootHubThreeLeafNoMateCoforestDescendantCut :
    RootHubThreeLeafNoMateCoforestEdge →
      RootHubThreeLeafNoMateCoforestVertex → Prop
  | RootHubThreeLeafNoMateCoforestEdge.rootHub,
      RootHubThreeLeafNoMateCoforestVertex.hub => True
  | RootHubThreeLeafNoMateCoforestEdge.rootHub,
      RootHubThreeLeafNoMateCoforestVertex.leaf1 => True
  | RootHubThreeLeafNoMateCoforestEdge.rootHub,
      RootHubThreeLeafNoMateCoforestVertex.leaf2 => True
  | RootHubThreeLeafNoMateCoforestEdge.rootHub,
      RootHubThreeLeafNoMateCoforestVertex.leaf3 => True
  | RootHubThreeLeafNoMateCoforestEdge.hub1,
      RootHubThreeLeafNoMateCoforestVertex.leaf1 => True
  | RootHubThreeLeafNoMateCoforestEdge.hub2,
      RootHubThreeLeafNoMateCoforestVertex.leaf2 => True
  | RootHubThreeLeafNoMateCoforestEdge.hub3,
      RootHubThreeLeafNoMateCoforestVertex.leaf3 => True
  | _, _ => False

def rootHubThreeLeafNoMateCoforestDescendantCutDecidable :
    (cut : RootHubThreeLeafNoMateCoforestEdge) →
      (vertex : RootHubThreeLeafNoMateCoforestVertex) →
        Decidable
          (rootHubThreeLeafNoMateCoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def rootHubThreeLeafNoMateCoforestParentStep :
    RootHubThreeLeafNoMateCoforestVertex →
      RootHubThreeLeafNoMateCoforestVertex
  | RootHubThreeLeafNoMateCoforestVertex.root =>
      RootHubThreeLeafNoMateCoforestVertex.root
  | RootHubThreeLeafNoMateCoforestVertex.hub =>
      RootHubThreeLeafNoMateCoforestVertex.root
  | RootHubThreeLeafNoMateCoforestVertex.leaf1 =>
      RootHubThreeLeafNoMateCoforestVertex.hub
  | RootHubThreeLeafNoMateCoforestVertex.leaf2 =>
      RootHubThreeLeafNoMateCoforestVertex.hub
  | RootHubThreeLeafNoMateCoforestVertex.leaf3 =>
      RootHubThreeLeafNoMateCoforestVertex.hub

def rootHubThreeLeafNoMateCoforestRank :
    RootHubThreeLeafNoMateCoforestVertex → Nat
  | RootHubThreeLeafNoMateCoforestVertex.root => 0
  | RootHubThreeLeafNoMateCoforestVertex.hub => 1
  | RootHubThreeLeafNoMateCoforestVertex.leaf1 => 2
  | RootHubThreeLeafNoMateCoforestVertex.leaf2 => 2
  | RootHubThreeLeafNoMateCoforestVertex.leaf3 => 2

def rootHubThreeLeafNoMateCoforestRankedParentMapData :
    RankedRootedParentMapData
      rootHubThreeLeafNoMateCoforestParentStep
      rootHubThreeLeafNoMateCoforestParent
      rootHubThreeLeafNoMateCoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [rootHubThreeLeafNoMateCoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := rootHubThreeLeafNoMateCoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem rootHubThreeLeafNoMateCoforestParentMapBoundary :
    ParentMapBoundary
      rootHubThreeLeafNoMateCoforestDescendantCut
      rootHubThreeLeafNoMateCoforestParent
      rootHubThreeLeafNoMateCoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [rootHubThreeLeafNoMateCoforestDescendantCut,
        rootHubThreeLeafNoMateCoforestChild]
  · intro edge
    cases edge <;>
      simp [rootHubThreeLeafNoMateCoforestDescendantCut,
        rootHubThreeLeafNoMateCoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [rootHubThreeLeafNoMateCoforestDescendantCut,
        rootHubThreeLeafNoMateCoforestParent,
        rootHubThreeLeafNoMateCoforestChild] at hne ⊢

theorem rootHubThreeLeafNoMateCoforestIncidence_eq_ite
    (cut edge : RootHubThreeLeafNoMateCoforestEdge) :
    @parentMapIncidence
        RootHubThreeLeafNoMateCoforestVertex
        RootHubThreeLeafNoMateCoforestEdge
        rootHubThreeLeafNoMateCoforestDescendantCut
        rootHubThreeLeafNoMateCoforestDescendantCutDecidable
        rootHubThreeLeafNoMateCoforestParent
        rootHubThreeLeafNoMateCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    RootHubThreeLeafNoMateCoforestVertex
    RootHubThreeLeafNoMateCoforestEdge
    inferInstance
    rootHubThreeLeafNoMateCoforestDescendantCut
    rootHubThreeLeafNoMateCoforestDescendantCutDecidable
    rootHubThreeLeafNoMateCoforestParent
    rootHubThreeLeafNoMateCoforestChild
    rootHubThreeLeafNoMateCoforestParentMapBoundary cut edge

theorem rootHubThreeLeafNoMateCoforestIncidence_self
    (edge : RootHubThreeLeafNoMateCoforestEdge) :
    @parentMapIncidence
        RootHubThreeLeafNoMateCoforestVertex
        RootHubThreeLeafNoMateCoforestEdge
        rootHubThreeLeafNoMateCoforestDescendantCut
        rootHubThreeLeafNoMateCoforestDescendantCutDecidable
        rootHubThreeLeafNoMateCoforestParent
        rootHubThreeLeafNoMateCoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    RootHubThreeLeafNoMateCoforestVertex
    RootHubThreeLeafNoMateCoforestEdge
    rootHubThreeLeafNoMateCoforestDescendantCut
    rootHubThreeLeafNoMateCoforestDescendantCutDecidable
    rootHubThreeLeafNoMateCoforestParent
    rootHubThreeLeafNoMateCoforestChild
    rootHubThreeLeafNoMateCoforestParentMapBoundary edge

theorem rootHubThreeLeafNoMateCoforestIncidence_ne
    {cut edge : RootHubThreeLeafNoMateCoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        RootHubThreeLeafNoMateCoforestVertex
        RootHubThreeLeafNoMateCoforestEdge
        rootHubThreeLeafNoMateCoforestDescendantCut
        rootHubThreeLeafNoMateCoforestDescendantCutDecidable
        rootHubThreeLeafNoMateCoforestParent
        rootHubThreeLeafNoMateCoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    RootHubThreeLeafNoMateCoforestVertex
    RootHubThreeLeafNoMateCoforestEdge
    rootHubThreeLeafNoMateCoforestDescendantCut
    rootHubThreeLeafNoMateCoforestDescendantCutDecidable
    rootHubThreeLeafNoMateCoforestParent
    rootHubThreeLeafNoMateCoforestChild
    rootHubThreeLeafNoMateCoforestParentMapBoundary cut edge hne

theorem rootHubThreeLeafNoMateCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        rootHubThreeLeafNoMateCoforestParentStep
        rootHubThreeLeafNoMateCoforestChild)
      rootHubThreeLeafNoMateCoforestParent
      rootHubThreeLeafNoMateCoforestChild :=
  rankedRootedParentMapBoundary
    rootHubThreeLeafNoMateCoforestRankedParentMapData

abbrev D7Stage1TripleCoforestVertex :=
  FiveLeafStarCoforestVertex

abbrev D7Stage1TripleCoforestEdge :=
  FiveLeafStarCoforestEdge

abbrev d7Stage1TripleCoforestParent :
    D7Stage1TripleCoforestEdge → D7Stage1TripleCoforestVertex :=
  fiveLeafStarCoforestParent

abbrev d7Stage1TripleCoforestChild :
    D7Stage1TripleCoforestEdge → D7Stage1TripleCoforestVertex :=
  fiveLeafStarCoforestChild

abbrev d7Stage1TripleCoforestDescendantCut :
    D7Stage1TripleCoforestEdge →
      D7Stage1TripleCoforestVertex → Prop :=
  fiveLeafStarCoforestDescendantCut

abbrev d7Stage1TripleCoforestDescendantCutDecidable :
    (cut : D7Stage1TripleCoforestEdge) →
      (vertex : D7Stage1TripleCoforestVertex) →
        Decidable (d7Stage1TripleCoforestDescendantCut cut vertex) :=
  fiveLeafStarCoforestDescendantCutDecidable

abbrev d7Stage1TripleCoforestParentStep :
    D7Stage1TripleCoforestVertex → D7Stage1TripleCoforestVertex :=
  fiveLeafStarCoforestParentStep

abbrev d7Stage1TripleCoforestRank :
    D7Stage1TripleCoforestVertex → Nat :=
  fiveLeafStarCoforestRank

def d7Stage1TripleCoforestEdgeTable :
    List D7Stage1TripleCoforestEdge :=
  [FiveLeafStarCoforestEdge.root1, FiveLeafStarCoforestEdge.root2,
    FiveLeafStarCoforestEdge.root3, FiveLeafStarCoforestEdge.root4,
    FiveLeafStarCoforestEdge.root5]

def d7Stage1TripleCoforestVertexTable :
    List D7Stage1TripleCoforestVertex :=
  [FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.leaf1,
    FiveLeafStarCoforestVertex.leaf2, FiveLeafStarCoforestVertex.leaf3,
    FiveLeafStarCoforestVertex.leaf4, FiveLeafStarCoforestVertex.leaf5]

def d7Stage1TripleCoforestParentTable :
    List D7Stage1TripleCoforestVertex :=
  d7Stage1TripleCoforestEdgeTable.map d7Stage1TripleCoforestParent

def d7Stage1TripleCoforestChildTable :
    List D7Stage1TripleCoforestVertex :=
  d7Stage1TripleCoforestEdgeTable.map d7Stage1TripleCoforestChild

def d7Stage1TripleCoforestParentStepTable :
    List D7Stage1TripleCoforestVertex :=
  d7Stage1TripleCoforestVertexTable.map
    d7Stage1TripleCoforestParentStep

def d7Stage1TripleCoforestRankTable : List Nat :=
  d7Stage1TripleCoforestVertexTable.map d7Stage1TripleCoforestRank

theorem d7Stage1TripleCoforestEdgeTable_length :
    d7Stage1TripleCoforestEdgeTable.length = 5 :=
  rfl

theorem d7Stage1TripleCoforestVertexTable_length :
    d7Stage1TripleCoforestVertexTable.length = 6 :=
  rfl

theorem d7Stage1TripleCoforestEdgeTable_nodup :
    d7Stage1TripleCoforestEdgeTable.Nodup := by
  decide

theorem d7Stage1TripleCoforestVertexTable_nodup :
    d7Stage1TripleCoforestVertexTable.Nodup := by
  decide

theorem d7Stage1TripleCoforestParentTable_readout :
    d7Stage1TripleCoforestParentTable =
      [FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.root,
        FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.root,
        FiveLeafStarCoforestVertex.root] :=
  rfl

theorem d7Stage1TripleCoforestChildTable_readout :
    d7Stage1TripleCoforestChildTable =
      [FiveLeafStarCoforestVertex.leaf1, FiveLeafStarCoforestVertex.leaf2,
        FiveLeafStarCoforestVertex.leaf3, FiveLeafStarCoforestVertex.leaf4,
        FiveLeafStarCoforestVertex.leaf5] :=
  rfl

theorem d7Stage1TripleCoforestParentStepTable_readout :
    d7Stage1TripleCoforestParentStepTable =
      [FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.root,
        FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.root,
        FiveLeafStarCoforestVertex.root, FiveLeafStarCoforestVertex.root] :=
  rfl

theorem d7Stage1TripleCoforestRankTable_readout :
    d7Stage1TripleCoforestRankTable = [0, 1, 1, 1, 1, 1] :=
  rfl

abbrev d7Stage1TripleCoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage1TripleCoforestParentStep
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild :=
  fiveLeafStarCoforestRankedParentMapData

theorem d7Stage1TripleCoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage1TripleCoforestDescendantCut
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild :=
  fiveLeafStarCoforestParentMapBoundary

theorem d7Stage1TripleCoforestIncidence_eq_ite
    (cut edge : D7Stage1TripleCoforestEdge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  fiveLeafStarCoforestIncidence_eq_ite cut edge

theorem d7Stage1TripleCoforestIncidence_self
    (edge : D7Stage1TripleCoforestEdge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild edge edge = 1 :=
  fiveLeafStarCoforestIncidence_self edge

theorem d7Stage1TripleCoforestIncidence_ne
    {cut edge : D7Stage1TripleCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild cut edge = 0 :=
  fiveLeafStarCoforestIncidence_ne hne

theorem d7Stage1TripleCoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1TripleCoforestParentStep
        d7Stage1TripleCoforestChild)
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild :=
  fiveLeafStarCoforestIteratedParentMapBoundary

abbrev D7Stage1Pair34CoforestVertex :=
  RootHubThreeLeafCoforestVertex

abbrev D7Stage1Pair34CoforestEdge :=
  RootHubThreeLeafCoforestEdge

abbrev d7Stage1Pair34CoforestParent :
    D7Stage1Pair34CoforestEdge → D7Stage1Pair34CoforestVertex :=
  rootHubThreeLeafCoforestParent

abbrev d7Stage1Pair34CoforestChild :
    D7Stage1Pair34CoforestEdge → D7Stage1Pair34CoforestVertex :=
  rootHubThreeLeafCoforestChild

abbrev d7Stage1Pair34CoforestDescendantCut :
    D7Stage1Pair34CoforestEdge →
      D7Stage1Pair34CoforestVertex → Prop :=
  rootHubThreeLeafCoforestDescendantCut

abbrev d7Stage1Pair34CoforestDescendantCutDecidable :
    (cut : D7Stage1Pair34CoforestEdge) →
      (vertex : D7Stage1Pair34CoforestVertex) →
        Decidable (d7Stage1Pair34CoforestDescendantCut cut vertex) :=
  rootHubThreeLeafCoforestDescendantCutDecidable

abbrev d7Stage1Pair34CoforestParentStep :
    D7Stage1Pair34CoforestVertex → D7Stage1Pair34CoforestVertex :=
  rootHubThreeLeafCoforestParentStep

abbrev d7Stage1Pair34CoforestRank :
    D7Stage1Pair34CoforestVertex → Nat :=
  rootHubThreeLeafCoforestRank

def d7Stage1Pair34CoforestEdgeTable :
    List D7Stage1Pair34CoforestEdge :=
  [RootHubThreeLeafCoforestEdge.rootHub,
    RootHubThreeLeafCoforestEdge.hub1,
    RootHubThreeLeafCoforestEdge.hub2,
    RootHubThreeLeafCoforestEdge.hub3,
    RootHubThreeLeafCoforestEdge.rootMate]

def d7Stage1Pair34CoforestVertexTable :
    List D7Stage1Pair34CoforestVertex :=
  [RootHubThreeLeafCoforestVertex.root,
    RootHubThreeLeafCoforestVertex.hub,
    RootHubThreeLeafCoforestVertex.leaf1,
    RootHubThreeLeafCoforestVertex.leaf2,
    RootHubThreeLeafCoforestVertex.leaf3,
    RootHubThreeLeafCoforestVertex.mate]

def d7Stage1Pair34CoforestParentTable :
    List D7Stage1Pair34CoforestVertex :=
  d7Stage1Pair34CoforestEdgeTable.map d7Stage1Pair34CoforestParent

def d7Stage1Pair34CoforestChildTable :
    List D7Stage1Pair34CoforestVertex :=
  d7Stage1Pair34CoforestEdgeTable.map d7Stage1Pair34CoforestChild

def d7Stage1Pair34CoforestParentStepTable :
    List D7Stage1Pair34CoforestVertex :=
  d7Stage1Pair34CoforestVertexTable.map
    d7Stage1Pair34CoforestParentStep

def d7Stage1Pair34CoforestRankTable : List Nat :=
  d7Stage1Pair34CoforestVertexTable.map d7Stage1Pair34CoforestRank

theorem d7Stage1Pair34CoforestEdgeTable_length :
    d7Stage1Pair34CoforestEdgeTable.length = 5 :=
  rfl

theorem d7Stage1Pair34CoforestVertexTable_length :
    d7Stage1Pair34CoforestVertexTable.length = 6 :=
  rfl

theorem d7Stage1Pair34CoforestEdgeTable_nodup :
    d7Stage1Pair34CoforestEdgeTable.Nodup := by
  decide

theorem d7Stage1Pair34CoforestVertexTable_nodup :
    d7Stage1Pair34CoforestVertexTable.Nodup := by
  decide

theorem d7Stage1Pair34CoforestParentTable_readout :
    d7Stage1Pair34CoforestParentTable =
      [RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.root] :=
  rfl

theorem d7Stage1Pair34CoforestChildTable_readout :
    d7Stage1Pair34CoforestChildTable =
      [RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.leaf1,
        RootHubThreeLeafCoforestVertex.leaf2,
        RootHubThreeLeafCoforestVertex.leaf3,
        RootHubThreeLeafCoforestVertex.mate] :=
  rfl

theorem d7Stage1Pair34CoforestParentStepTable_readout :
    d7Stage1Pair34CoforestParentStepTable =
      [RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.root] :=
  rfl

theorem d7Stage1Pair34CoforestRankTable_readout :
    d7Stage1Pair34CoforestRankTable = [0, 1, 2, 2, 2, 1] :=
  rfl

abbrev d7Stage1Pair34CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage1Pair34CoforestParentStep
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild :=
  rootHubThreeLeafCoforestRankedParentMapData

theorem d7Stage1Pair34CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage1Pair34CoforestDescendantCut
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild :=
  rootHubThreeLeafCoforestParentMapBoundary

theorem d7Stage1Pair34CoforestIncidence_eq_ite
    (cut edge : D7Stage1Pair34CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rootHubThreeLeafCoforestIncidence_eq_ite cut edge

theorem d7Stage1Pair34CoforestIncidence_self
    (edge : D7Stage1Pair34CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild edge edge = 1 :=
  rootHubThreeLeafCoforestIncidence_self edge

theorem d7Stage1Pair34CoforestIncidence_ne
    {cut edge : D7Stage1Pair34CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild cut edge = 0 :=
  rootHubThreeLeafCoforestIncidence_ne hne

theorem d7Stage1Pair34CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1Pair34CoforestParentStep
        d7Stage1Pair34CoforestChild)
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild :=
  rootHubThreeLeafCoforestIteratedParentMapBoundary

abbrev D7Stage1Pair56CoforestVertex :=
  RootHubThreeLeafCoforestVertex

abbrev D7Stage1Pair56CoforestEdge :=
  RootHubThreeLeafCoforestEdge

abbrev d7Stage1Pair56CoforestParent :
    D7Stage1Pair56CoforestEdge → D7Stage1Pair56CoforestVertex :=
  rootHubThreeLeafCoforestParent

abbrev d7Stage1Pair56CoforestChild :
    D7Stage1Pair56CoforestEdge → D7Stage1Pair56CoforestVertex :=
  rootHubThreeLeafCoforestChild

abbrev d7Stage1Pair56CoforestDescendantCut :
    D7Stage1Pair56CoforestEdge →
      D7Stage1Pair56CoforestVertex → Prop :=
  rootHubThreeLeafCoforestDescendantCut

abbrev d7Stage1Pair56CoforestDescendantCutDecidable :
    (cut : D7Stage1Pair56CoforestEdge) →
      (vertex : D7Stage1Pair56CoforestVertex) →
        Decidable (d7Stage1Pair56CoforestDescendantCut cut vertex) :=
  rootHubThreeLeafCoforestDescendantCutDecidable

abbrev d7Stage1Pair56CoforestParentStep :
    D7Stage1Pair56CoforestVertex → D7Stage1Pair56CoforestVertex :=
  rootHubThreeLeafCoforestParentStep

abbrev d7Stage1Pair56CoforestRank :
    D7Stage1Pair56CoforestVertex → Nat :=
  rootHubThreeLeafCoforestRank

abbrev d7Stage1Pair56CoforestEdgeTable :
    List D7Stage1Pair56CoforestEdge :=
  d7Stage1Pair34CoforestEdgeTable

abbrev d7Stage1Pair56CoforestVertexTable :
    List D7Stage1Pair56CoforestVertex :=
  d7Stage1Pair34CoforestVertexTable

abbrev d7Stage1Pair56CoforestParentTable :
    List D7Stage1Pair56CoforestVertex :=
  d7Stage1Pair56CoforestEdgeTable.map d7Stage1Pair56CoforestParent

abbrev d7Stage1Pair56CoforestChildTable :
    List D7Stage1Pair56CoforestVertex :=
  d7Stage1Pair56CoforestEdgeTable.map d7Stage1Pair56CoforestChild

abbrev d7Stage1Pair56CoforestParentStepTable :
    List D7Stage1Pair56CoforestVertex :=
  d7Stage1Pair56CoforestVertexTable.map
    d7Stage1Pair56CoforestParentStep

abbrev d7Stage1Pair56CoforestRankTable : List Nat :=
  d7Stage1Pair56CoforestVertexTable.map d7Stage1Pair56CoforestRank

theorem d7Stage1Pair56CoforestEdgeTable_length :
    d7Stage1Pair56CoforestEdgeTable.length = 5 :=
  d7Stage1Pair34CoforestEdgeTable_length

theorem d7Stage1Pair56CoforestVertexTable_length :
    d7Stage1Pair56CoforestVertexTable.length = 6 :=
  d7Stage1Pair34CoforestVertexTable_length

theorem d7Stage1Pair56CoforestEdgeTable_nodup :
    d7Stage1Pair56CoforestEdgeTable.Nodup :=
  d7Stage1Pair34CoforestEdgeTable_nodup

theorem d7Stage1Pair56CoforestVertexTable_nodup :
    d7Stage1Pair56CoforestVertexTable.Nodup :=
  d7Stage1Pair34CoforestVertexTable_nodup

theorem d7Stage1Pair56CoforestParentTable_readout :
    d7Stage1Pair56CoforestParentTable =
      [RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.root] :=
  rfl

theorem d7Stage1Pair56CoforestChildTable_readout :
    d7Stage1Pair56CoforestChildTable =
      [RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.leaf1,
        RootHubThreeLeafCoforestVertex.leaf2,
        RootHubThreeLeafCoforestVertex.leaf3,
        RootHubThreeLeafCoforestVertex.mate] :=
  rfl

theorem d7Stage1Pair56CoforestParentStepTable_readout :
    d7Stage1Pair56CoforestParentStepTable =
      [RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.root,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.hub,
        RootHubThreeLeafCoforestVertex.root] :=
  rfl

theorem d7Stage1Pair56CoforestRankTable_readout :
    d7Stage1Pair56CoforestRankTable = [0, 1, 2, 2, 2, 1] :=
  rfl

abbrev d7Stage1Pair56CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage1Pair56CoforestParentStep
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild :=
  rootHubThreeLeafCoforestRankedParentMapData

theorem d7Stage1Pair56CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage1Pair56CoforestDescendantCut
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild :=
  rootHubThreeLeafCoforestParentMapBoundary

theorem d7Stage1Pair56CoforestIncidence_eq_ite
    (cut edge : D7Stage1Pair56CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rootHubThreeLeafCoforestIncidence_eq_ite cut edge

theorem d7Stage1Pair56CoforestIncidence_self
    (edge : D7Stage1Pair56CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild edge edge = 1 :=
  rootHubThreeLeafCoforestIncidence_self edge

theorem d7Stage1Pair56CoforestIncidence_ne
    {cut edge : D7Stage1Pair56CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild cut edge = 0 :=
  rootHubThreeLeafCoforestIncidence_ne hne

theorem d7Stage1Pair56CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1Pair56CoforestParentStep
        d7Stage1Pair56CoforestChild)
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild :=
  rootHubThreeLeafCoforestIteratedParentMapBoundary

inductive D7Stage2CoforestVertex where
  | root12
  | v0
  | v3
  | v4
  | v5
  deriving DecidableEq, Repr

inductive D7Stage2CoforestEdge where
  | e01
  | e03
  | e24
  | e25
  deriving DecidableEq, Repr

def d7Stage2CoforestParent :
    D7Stage2CoforestEdge → D7Stage2CoforestVertex
  | D7Stage2CoforestEdge.e01 => D7Stage2CoforestVertex.root12
  | D7Stage2CoforestEdge.e03 => D7Stage2CoforestVertex.v0
  | D7Stage2CoforestEdge.e24 => D7Stage2CoforestVertex.root12
  | D7Stage2CoforestEdge.e25 => D7Stage2CoforestVertex.root12

def d7Stage2CoforestChild :
    D7Stage2CoforestEdge → D7Stage2CoforestVertex
  | D7Stage2CoforestEdge.e01 => D7Stage2CoforestVertex.v0
  | D7Stage2CoforestEdge.e03 => D7Stage2CoforestVertex.v3
  | D7Stage2CoforestEdge.e24 => D7Stage2CoforestVertex.v4
  | D7Stage2CoforestEdge.e25 => D7Stage2CoforestVertex.v5

def d7Stage2CoforestDescendantCut :
    D7Stage2CoforestEdge → D7Stage2CoforestVertex → Prop
  | D7Stage2CoforestEdge.e01, D7Stage2CoforestVertex.v0 => True
  | D7Stage2CoforestEdge.e01, D7Stage2CoforestVertex.v3 => True
  | D7Stage2CoforestEdge.e03, D7Stage2CoforestVertex.v3 => True
  | D7Stage2CoforestEdge.e24, D7Stage2CoforestVertex.v4 => True
  | D7Stage2CoforestEdge.e25, D7Stage2CoforestVertex.v5 => True
  | _, _ => False

def d7Stage2CoforestDescendantCutDecidable :
    (cut : D7Stage2CoforestEdge) →
      (vertex : D7Stage2CoforestVertex) →
        Decidable (d7Stage2CoforestDescendantCut cut vertex) :=
  fun cut vertex => by
    cases cut <;> cases vertex <;>
      first
      | exact isTrue trivial
      | exact isFalse (by intro h; exact h)

def d7Stage2CoforestParentStep :
    D7Stage2CoforestVertex → D7Stage2CoforestVertex
  | D7Stage2CoforestVertex.root12 => D7Stage2CoforestVertex.root12
  | D7Stage2CoforestVertex.v0 => D7Stage2CoforestVertex.root12
  | D7Stage2CoforestVertex.v3 => D7Stage2CoforestVertex.v0
  | D7Stage2CoforestVertex.v4 => D7Stage2CoforestVertex.root12
  | D7Stage2CoforestVertex.v5 => D7Stage2CoforestVertex.root12

def d7Stage2CoforestRank : D7Stage2CoforestVertex → Nat
  | D7Stage2CoforestVertex.root12 => 0
  | D7Stage2CoforestVertex.v0 => 1
  | D7Stage2CoforestVertex.v3 => 2
  | D7Stage2CoforestVertex.v4 => 1
  | D7Stage2CoforestVertex.v5 => 1

def d7Stage2CoforestEdgeTable : List D7Stage2CoforestEdge :=
  [D7Stage2CoforestEdge.e01, D7Stage2CoforestEdge.e03,
    D7Stage2CoforestEdge.e24, D7Stage2CoforestEdge.e25]

def d7Stage2CoforestVertexTable : List D7Stage2CoforestVertex :=
  [D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.v0,
    D7Stage2CoforestVertex.v3, D7Stage2CoforestVertex.v4,
    D7Stage2CoforestVertex.v5]

def d7Stage2CoforestParentTable : List D7Stage2CoforestVertex :=
  d7Stage2CoforestEdgeTable.map d7Stage2CoforestParent

def d7Stage2CoforestChildTable : List D7Stage2CoforestVertex :=
  d7Stage2CoforestEdgeTable.map d7Stage2CoforestChild

def d7Stage2CoforestParentStepTable : List D7Stage2CoforestVertex :=
  d7Stage2CoforestVertexTable.map d7Stage2CoforestParentStep

def d7Stage2CoforestRankTable : List Nat :=
  d7Stage2CoforestVertexTable.map d7Stage2CoforestRank

theorem d7Stage2CoforestEdgeTable_length :
    d7Stage2CoforestEdgeTable.length = 4 :=
  rfl

theorem d7Stage2CoforestVertexTable_length :
    d7Stage2CoforestVertexTable.length = 5 :=
  rfl

theorem d7Stage2CoforestEdgeTable_nodup :
    d7Stage2CoforestEdgeTable.Nodup := by
  decide

theorem d7Stage2CoforestVertexTable_nodup :
    d7Stage2CoforestVertexTable.Nodup := by
  decide

theorem d7Stage2CoforestParentTable_readout :
    d7Stage2CoforestParentTable =
      [D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.v0,
        D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.root12] :=
  rfl

theorem d7Stage2CoforestChildTable_readout :
    d7Stage2CoforestChildTable =
      [D7Stage2CoforestVertex.v0, D7Stage2CoforestVertex.v3,
        D7Stage2CoforestVertex.v4, D7Stage2CoforestVertex.v5] :=
  rfl

theorem d7Stage2CoforestParentStepTable_readout :
    d7Stage2CoforestParentStepTable =
      [D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.root12,
        D7Stage2CoforestVertex.v0, D7Stage2CoforestVertex.root12,
        D7Stage2CoforestVertex.root12] :=
  rfl

theorem d7Stage2CoforestRankTable_readout :
    d7Stage2CoforestRankTable = [0, 1, 2, 1, 1] :=
  rfl

def d7Stage2CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage2CoforestParentStep
      d7Stage2CoforestParent
      d7Stage2CoforestChild where
  child_injective := by
    intro left right hchild
    cases left <;> cases right <;>
      simp [d7Stage2CoforestChild] at hchild ⊢
  parentStep_child := by
    intro edge
    cases edge <;>
      rfl
  rank := d7Stage2CoforestRank
  parentStep_rank_le := by
    intro vertex
    cases vertex <;>
      decide
  parent_child_rank_lt := by
    intro edge
    cases edge <;>
      decide

theorem d7Stage2CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestParent
      d7Stage2CoforestChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    cases edge <;>
      simp [d7Stage2CoforestDescendantCut,
        d7Stage2CoforestChild]
  · intro edge
    cases edge <;>
      simp [d7Stage2CoforestDescendantCut,
        d7Stage2CoforestParent]
  · intro cut edge hne
    cases cut <;> cases edge <;>
      simp [d7Stage2CoforestDescendantCut,
        d7Stage2CoforestParent, d7Stage2CoforestChild] at hne ⊢

theorem d7Stage2CoforestIncidence_eq_ite
    (cut edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidence_eq_ite
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestParentMapBoundary cut edge

theorem d7Stage2CoforestIncidence_self
    (edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild edge edge = 1 :=
  @parentMapIncidence_self
    D7Stage2CoforestVertex D7Stage2CoforestEdge
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestParentMapBoundary edge

theorem d7Stage2CoforestIncidence_ne
    {cut edge : D7Stage2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge = 0 :=
  @parentMapIncidence_ne
    D7Stage2CoforestVertex D7Stage2CoforestEdge
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestParentMapBoundary cut edge hne

theorem d7Stage2CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage2CoforestParentStep
        d7Stage2CoforestChild)
      d7Stage2CoforestParent
      d7Stage2CoforestChild :=
  rankedRootedParentMapBoundary
    d7Stage2CoforestRankedParentMapData

def d7Stage2CoforestIncidenceCertificate :
    @ParentMapIncidenceCertificate
      D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestDescendantCutDecidable
      d7Stage2CoforestParent d7Stage2CoforestChild :=
  @parentMapIncidenceCertificate_of_boundary
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestParentMapBoundary

theorem d7Stage2CoforestIncidenceCertificate_boundary :
    ParentMapBoundary
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestParent
      d7Stage2CoforestChild :=
  @parentMapIncidenceCertificate_boundary
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestIncidenceCertificate

theorem d7Stage2CoforestIncidenceCertificate_eq_ite
    (cut edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  @parentMapIncidenceCertificate_eq_ite
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestIncidenceCertificate cut edge

theorem d7Stage2CoforestIncidenceCertificate_self
    (edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild edge edge = 1 :=
  @parentMapIncidenceCertificate_self
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestIncidenceCertificate edge

theorem d7Stage2CoforestIncidenceCertificate_ne
    {cut edge : D7Stage2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge = 0 :=
  @parentMapIncidenceCertificate_ne
    D7Stage2CoforestVertex D7Stage2CoforestEdge inferInstance
    d7Stage2CoforestDescendantCut
    d7Stage2CoforestDescendantCutDecidable
    d7Stage2CoforestParent d7Stage2CoforestChild
    d7Stage2CoforestIncidenceCertificate cut edge hne

abbrev D7Stage2Packet134Color34CoforestVertex :=
  TwoPathForkCoforestVertex

abbrev D7Stage2Packet134Color34CoforestEdge :=
  TwoPathForkCoforestEdge

abbrev d7Stage2Packet134Color34CoforestParent :
    D7Stage2Packet134Color34CoforestEdge →
      D7Stage2Packet134Color34CoforestVertex :=
  twoPathForkCoforestParent

abbrev d7Stage2Packet134Color34CoforestChild :
    D7Stage2Packet134Color34CoforestEdge →
      D7Stage2Packet134Color34CoforestVertex :=
  twoPathForkCoforestChild

abbrev d7Stage2Packet134Color34CoforestDescendantCut :
    D7Stage2Packet134Color34CoforestEdge →
      D7Stage2Packet134Color34CoforestVertex → Prop :=
  twoPathForkCoforestDescendantCut

abbrev d7Stage2Packet134Color34CoforestDescendantCutDecidable :
    (cut : D7Stage2Packet134Color34CoforestEdge) →
      (vertex : D7Stage2Packet134Color34CoforestVertex) →
        Decidable
          (d7Stage2Packet134Color34CoforestDescendantCut cut vertex) :=
  twoPathForkCoforestDescendantCutDecidable

abbrev d7Stage2Packet134Color34CoforestParentStep :
    D7Stage2Packet134Color34CoforestVertex →
      D7Stage2Packet134Color34CoforestVertex :=
  twoPathForkCoforestParentStep

abbrev d7Stage2Packet134Color34CoforestRank :
    D7Stage2Packet134Color34CoforestVertex → Nat :=
  twoPathForkCoforestRank

def d7Stage2Packet134Color34CoforestEdgeTable :
    List D7Stage2Packet134Color34CoforestEdge :=
  [TwoPathForkCoforestEdge.rootLeft, TwoPathForkCoforestEdge.leftLeaf,
    TwoPathForkCoforestEdge.rootRight, TwoPathForkCoforestEdge.rightLeaf]

def d7Stage2Packet134Color34CoforestVertexTable :
    List D7Stage2Packet134Color34CoforestVertex :=
  [TwoPathForkCoforestVertex.root, TwoPathForkCoforestVertex.left,
    TwoPathForkCoforestVertex.leftLeaf, TwoPathForkCoforestVertex.right,
    TwoPathForkCoforestVertex.rightLeaf]

def d7Stage2Packet134Color34CoforestParentTable :
    List D7Stage2Packet134Color34CoforestVertex :=
  d7Stage2Packet134Color34CoforestEdgeTable.map
    d7Stage2Packet134Color34CoforestParent

def d7Stage2Packet134Color34CoforestChildTable :
    List D7Stage2Packet134Color34CoforestVertex :=
  d7Stage2Packet134Color34CoforestEdgeTable.map
    d7Stage2Packet134Color34CoforestChild

def d7Stage2Packet134Color34CoforestParentStepTable :
    List D7Stage2Packet134Color34CoforestVertex :=
  d7Stage2Packet134Color34CoforestVertexTable.map
    d7Stage2Packet134Color34CoforestParentStep

def d7Stage2Packet134Color34CoforestRankTable : List Nat :=
  d7Stage2Packet134Color34CoforestVertexTable.map
    d7Stage2Packet134Color34CoforestRank

theorem d7Stage2Packet134Color34CoforestEdgeTable_length :
    d7Stage2Packet134Color34CoforestEdgeTable.length = 4 :=
  rfl

theorem d7Stage2Packet134Color34CoforestVertexTable_length :
    d7Stage2Packet134Color34CoforestVertexTable.length = 5 :=
  rfl

theorem d7Stage2Packet134Color34CoforestEdgeTable_nodup :
    d7Stage2Packet134Color34CoforestEdgeTable.Nodup := by
  decide

theorem d7Stage2Packet134Color34CoforestVertexTable_nodup :
    d7Stage2Packet134Color34CoforestVertexTable.Nodup := by
  decide

theorem d7Stage2Packet134Color34CoforestParentTable_readout :
    d7Stage2Packet134Color34CoforestParentTable =
      [TwoPathForkCoforestVertex.root, TwoPathForkCoforestVertex.left,
        TwoPathForkCoforestVertex.root, TwoPathForkCoforestVertex.right] :=
  rfl

theorem d7Stage2Packet134Color34CoforestChildTable_readout :
    d7Stage2Packet134Color34CoforestChildTable =
      [TwoPathForkCoforestVertex.left, TwoPathForkCoforestVertex.leftLeaf,
        TwoPathForkCoforestVertex.right,
        TwoPathForkCoforestVertex.rightLeaf] :=
  rfl

theorem d7Stage2Packet134Color34CoforestParentStepTable_readout :
    d7Stage2Packet134Color34CoforestParentStepTable =
      [TwoPathForkCoforestVertex.root, TwoPathForkCoforestVertex.root,
        TwoPathForkCoforestVertex.left, TwoPathForkCoforestVertex.root,
        TwoPathForkCoforestVertex.right] :=
  rfl

theorem d7Stage2Packet134Color34CoforestRankTable_readout :
    d7Stage2Packet134Color34CoforestRankTable = [0, 1, 2, 1, 2] :=
  rfl

abbrev d7Stage2Packet134Color34CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage2Packet134Color34CoforestParentStep
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  twoPathForkCoforestRankedParentMapData

theorem d7Stage2Packet134Color34CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage2Packet134Color34CoforestDescendantCut
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  twoPathForkCoforestParentMapBoundary

theorem d7Stage2Packet134Color34CoforestIncidence_eq_ite
    (cut edge : D7Stage2Packet134Color34CoforestEdge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  twoPathForkCoforestIncidence_eq_ite cut edge

theorem d7Stage2Packet134Color34CoforestIncidence_self
    (edge : D7Stage2Packet134Color34CoforestEdge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild edge edge = 1 :=
  twoPathForkCoforestIncidence_self edge

theorem d7Stage2Packet134Color34CoforestIncidence_ne
    {cut edge : D7Stage2Packet134Color34CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild cut edge = 0 :=
  twoPathForkCoforestIncidence_ne hne

theorem d7Stage2Packet134Color34CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Packet134Color34CoforestParentStep
        d7Stage2Packet134Color34CoforestChild)
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  twoPathForkCoforestIteratedParentMapBoundary

abbrev D7Stage2Pair02Color0CoforestVertex :=
  FourLeafStarCoforestVertex

abbrev D7Stage2Pair02Color0CoforestEdge :=
  FourLeafStarCoforestEdge

abbrev d7Stage2Pair02Color0CoforestParent :
    D7Stage2Pair02Color0CoforestEdge →
      D7Stage2Pair02Color0CoforestVertex :=
  fourLeafStarCoforestParent

abbrev d7Stage2Pair02Color0CoforestChild :
    D7Stage2Pair02Color0CoforestEdge →
      D7Stage2Pair02Color0CoforestVertex :=
  fourLeafStarCoforestChild

abbrev d7Stage2Pair02Color0CoforestDescendantCut :
    D7Stage2Pair02Color0CoforestEdge →
      D7Stage2Pair02Color0CoforestVertex → Prop :=
  fourLeafStarCoforestDescendantCut

abbrev d7Stage2Pair02Color0CoforestDescendantCutDecidable :
    (cut : D7Stage2Pair02Color0CoforestEdge) →
      (vertex : D7Stage2Pair02Color0CoforestVertex) →
        Decidable
          (d7Stage2Pair02Color0CoforestDescendantCut cut vertex) :=
  fourLeafStarCoforestDescendantCutDecidable

abbrev d7Stage2Pair02Color0CoforestParentStep :
    D7Stage2Pair02Color0CoforestVertex →
      D7Stage2Pair02Color0CoforestVertex :=
  fourLeafStarCoforestParentStep

abbrev d7Stage2Pair02Color0CoforestRank :
    D7Stage2Pair02Color0CoforestVertex → Nat :=
  fourLeafStarCoforestRank

def d7Stage2Pair02Color0CoforestEdgeTable :
    List D7Stage2Pair02Color0CoforestEdge :=
  [FourLeafStarCoforestEdge.root1, FourLeafStarCoforestEdge.root2,
    FourLeafStarCoforestEdge.root3, FourLeafStarCoforestEdge.root4]

def d7Stage2Pair02Color0CoforestVertexTable :
    List D7Stage2Pair02Color0CoforestVertex :=
  [FourLeafStarCoforestVertex.root, FourLeafStarCoforestVertex.leaf1,
    FourLeafStarCoforestVertex.leaf2, FourLeafStarCoforestVertex.leaf3,
    FourLeafStarCoforestVertex.leaf4]

def d7Stage2Pair02Color0CoforestParentTable :
    List D7Stage2Pair02Color0CoforestVertex :=
  d7Stage2Pair02Color0CoforestEdgeTable.map
    d7Stage2Pair02Color0CoforestParent

def d7Stage2Pair02Color0CoforestChildTable :
    List D7Stage2Pair02Color0CoforestVertex :=
  d7Stage2Pair02Color0CoforestEdgeTable.map
    d7Stage2Pair02Color0CoforestChild

def d7Stage2Pair02Color0CoforestParentStepTable :
    List D7Stage2Pair02Color0CoforestVertex :=
  d7Stage2Pair02Color0CoforestVertexTable.map
    d7Stage2Pair02Color0CoforestParentStep

def d7Stage2Pair02Color0CoforestRankTable : List Nat :=
  d7Stage2Pair02Color0CoforestVertexTable.map
    d7Stage2Pair02Color0CoforestRank

theorem d7Stage2Pair02Color0CoforestEdgeTable_length :
    d7Stage2Pair02Color0CoforestEdgeTable.length = 4 :=
  rfl

theorem d7Stage2Pair02Color0CoforestVertexTable_length :
    d7Stage2Pair02Color0CoforestVertexTable.length = 5 :=
  rfl

theorem d7Stage2Pair02Color0CoforestEdgeTable_nodup :
    d7Stage2Pair02Color0CoforestEdgeTable.Nodup := by
  decide

theorem d7Stage2Pair02Color0CoforestVertexTable_nodup :
    d7Stage2Pair02Color0CoforestVertexTable.Nodup := by
  decide

theorem d7Stage2Pair02Color0CoforestParentTable_readout :
    d7Stage2Pair02Color0CoforestParentTable =
      [FourLeafStarCoforestVertex.root, FourLeafStarCoforestVertex.root,
        FourLeafStarCoforestVertex.root, FourLeafStarCoforestVertex.root] :=
  rfl

theorem d7Stage2Pair02Color0CoforestChildTable_readout :
    d7Stage2Pair02Color0CoforestChildTable =
      [FourLeafStarCoforestVertex.leaf1, FourLeafStarCoforestVertex.leaf2,
        FourLeafStarCoforestVertex.leaf3,
        FourLeafStarCoforestVertex.leaf4] :=
  rfl

theorem d7Stage2Pair02Color0CoforestParentStepTable_readout :
    d7Stage2Pair02Color0CoforestParentStepTable =
      [FourLeafStarCoforestVertex.root, FourLeafStarCoforestVertex.root,
        FourLeafStarCoforestVertex.root, FourLeafStarCoforestVertex.root,
        FourLeafStarCoforestVertex.root] :=
  rfl

theorem d7Stage2Pair02Color0CoforestRankTable_readout :
    d7Stage2Pair02Color0CoforestRankTable = [0, 1, 1, 1, 1] :=
  rfl

abbrev d7Stage2Pair02Color0CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage2Pair02Color0CoforestParentStep
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild :=
  fourLeafStarCoforestRankedParentMapData

theorem d7Stage2Pair02Color0CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage2Pair02Color0CoforestDescendantCut
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild :=
  fourLeafStarCoforestParentMapBoundary

theorem d7Stage2Pair02Color0CoforestIncidence_eq_ite
    (cut edge : D7Stage2Pair02Color0CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  fourLeafStarCoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair02Color0CoforestIncidence_self
    (edge : D7Stage2Pair02Color0CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild edge edge = 1 :=
  fourLeafStarCoforestIncidence_self edge

theorem d7Stage2Pair02Color0CoforestIncidence_ne
    {cut edge : D7Stage2Pair02Color0CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild cut edge = 0 :=
  fourLeafStarCoforestIncidence_ne hne

theorem d7Stage2Pair02Color0CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair02Color0CoforestParentStep
        d7Stage2Pair02Color0CoforestChild)
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild :=
  fourLeafStarCoforestIteratedParentMapBoundary

abbrev D7Stage2Pair02Color2CoforestVertex :=
  D7Stage2CoforestVertex

abbrev D7Stage2Pair02Color2CoforestEdge :=
  D7Stage2CoforestEdge

abbrev d7Stage2Pair02Color2CoforestParent :
    D7Stage2Pair02Color2CoforestEdge →
      D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2CoforestParent

abbrev d7Stage2Pair02Color2CoforestChild :
    D7Stage2Pair02Color2CoforestEdge →
      D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2CoforestChild

abbrev d7Stage2Pair02Color2CoforestDescendantCut :
    D7Stage2Pair02Color2CoforestEdge →
      D7Stage2Pair02Color2CoforestVertex → Prop :=
  d7Stage2CoforestDescendantCut

abbrev d7Stage2Pair02Color2CoforestDescendantCutDecidable :
    (cut : D7Stage2Pair02Color2CoforestEdge) →
      (vertex : D7Stage2Pair02Color2CoforestVertex) →
        Decidable
          (d7Stage2Pair02Color2CoforestDescendantCut cut vertex) :=
  d7Stage2CoforestDescendantCutDecidable

abbrev d7Stage2Pair02Color2CoforestParentStep :
    D7Stage2Pair02Color2CoforestVertex →
      D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2CoforestParentStep

abbrev d7Stage2Pair02Color2CoforestRank :
    D7Stage2Pair02Color2CoforestVertex → Nat :=
  d7Stage2CoforestRank

abbrev d7Stage2Pair02Color2CoforestEdgeTable :
    List D7Stage2Pair02Color2CoforestEdge :=
  d7Stage2CoforestEdgeTable

abbrev d7Stage2Pair02Color2CoforestVertexTable :
    List D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2CoforestVertexTable

abbrev d7Stage2Pair02Color2CoforestParentTable :
    List D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2Pair02Color2CoforestEdgeTable.map
    d7Stage2Pair02Color2CoforestParent

abbrev d7Stage2Pair02Color2CoforestChildTable :
    List D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2Pair02Color2CoforestEdgeTable.map
    d7Stage2Pair02Color2CoforestChild

abbrev d7Stage2Pair02Color2CoforestParentStepTable :
    List D7Stage2Pair02Color2CoforestVertex :=
  d7Stage2Pair02Color2CoforestVertexTable.map
    d7Stage2Pair02Color2CoforestParentStep

abbrev d7Stage2Pair02Color2CoforestRankTable : List Nat :=
  d7Stage2Pair02Color2CoforestVertexTable.map
    d7Stage2Pair02Color2CoforestRank

theorem d7Stage2Pair02Color2CoforestEdgeTable_length :
    d7Stage2Pair02Color2CoforestEdgeTable.length = 4 :=
  d7Stage2CoforestEdgeTable_length

theorem d7Stage2Pair02Color2CoforestVertexTable_length :
    d7Stage2Pair02Color2CoforestVertexTable.length = 5 :=
  d7Stage2CoforestVertexTable_length

theorem d7Stage2Pair02Color2CoforestEdgeTable_nodup :
    d7Stage2Pair02Color2CoforestEdgeTable.Nodup :=
  d7Stage2CoforestEdgeTable_nodup

theorem d7Stage2Pair02Color2CoforestVertexTable_nodup :
    d7Stage2Pair02Color2CoforestVertexTable.Nodup :=
  d7Stage2CoforestVertexTable_nodup

theorem d7Stage2Pair02Color2CoforestParentTable_readout :
    d7Stage2Pair02Color2CoforestParentTable =
      [D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.v0,
        D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.root12] :=
  rfl

theorem d7Stage2Pair02Color2CoforestChildTable_readout :
    d7Stage2Pair02Color2CoforestChildTable =
      [D7Stage2CoforestVertex.v0, D7Stage2CoforestVertex.v3,
        D7Stage2CoforestVertex.v4, D7Stage2CoforestVertex.v5] :=
  rfl

theorem d7Stage2Pair02Color2CoforestParentStepTable_readout :
    d7Stage2Pair02Color2CoforestParentStepTable =
      [D7Stage2CoforestVertex.root12, D7Stage2CoforestVertex.root12,
        D7Stage2CoforestVertex.v0, D7Stage2CoforestVertex.root12,
        D7Stage2CoforestVertex.root12] :=
  rfl

theorem d7Stage2Pair02Color2CoforestRankTable_readout :
    d7Stage2Pair02Color2CoforestRankTable = [0, 1, 2, 1, 1] :=
  rfl

abbrev d7Stage2Pair02Color2CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage2Pair02Color2CoforestParentStep
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild :=
  d7Stage2CoforestRankedParentMapData

theorem d7Stage2Pair02Color2CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage2Pair02Color2CoforestDescendantCut
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild :=
  d7Stage2CoforestParentMapBoundary

theorem d7Stage2Pair02Color2CoforestIncidence_eq_ite
    (cut edge : D7Stage2Pair02Color2CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2CoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair02Color2CoforestIncidence_self
    (edge : D7Stage2Pair02Color2CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild edge edge = 1 :=
  d7Stage2CoforestIncidence_self edge

theorem d7Stage2Pair02Color2CoforestIncidence_ne
    {cut edge : D7Stage2Pair02Color2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild cut edge = 0 :=
  d7Stage2CoforestIncidence_ne hne

theorem d7Stage2Pair02Color2CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair02Color2CoforestParentStep
        d7Stage2Pair02Color2CoforestChild)
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild :=
  d7Stage2CoforestIteratedParentMapBoundary

abbrev D7Stage2Pair56Color56CoforestVertex :=
  RootHubThreeLeafNoMateCoforestVertex

abbrev D7Stage2Pair56Color56CoforestEdge :=
  RootHubThreeLeafNoMateCoforestEdge

abbrev d7Stage2Pair56Color56CoforestParent :
    D7Stage2Pair56Color56CoforestEdge →
      D7Stage2Pair56Color56CoforestVertex :=
  rootHubThreeLeafNoMateCoforestParent

abbrev d7Stage2Pair56Color56CoforestChild :
    D7Stage2Pair56Color56CoforestEdge →
      D7Stage2Pair56Color56CoforestVertex :=
  rootHubThreeLeafNoMateCoforestChild

abbrev d7Stage2Pair56Color56CoforestDescendantCut :
    D7Stage2Pair56Color56CoforestEdge →
      D7Stage2Pair56Color56CoforestVertex → Prop :=
  rootHubThreeLeafNoMateCoforestDescendantCut

abbrev d7Stage2Pair56Color56CoforestDescendantCutDecidable :
    (cut : D7Stage2Pair56Color56CoforestEdge) →
      (vertex : D7Stage2Pair56Color56CoforestVertex) →
        Decidable
          (d7Stage2Pair56Color56CoforestDescendantCut cut vertex) :=
  rootHubThreeLeafNoMateCoforestDescendantCutDecidable

abbrev d7Stage2Pair56Color56CoforestParentStep :
    D7Stage2Pair56Color56CoforestVertex →
      D7Stage2Pair56Color56CoforestVertex :=
  rootHubThreeLeafNoMateCoforestParentStep

abbrev d7Stage2Pair56Color56CoforestRank :
    D7Stage2Pair56Color56CoforestVertex → Nat :=
  rootHubThreeLeafNoMateCoforestRank

def d7Stage2Pair56Color56CoforestEdgeTable :
    List D7Stage2Pair56Color56CoforestEdge :=
  [RootHubThreeLeafNoMateCoforestEdge.rootHub,
    RootHubThreeLeafNoMateCoforestEdge.hub1,
    RootHubThreeLeafNoMateCoforestEdge.hub2,
    RootHubThreeLeafNoMateCoforestEdge.hub3]

def d7Stage2Pair56Color56CoforestVertexTable :
    List D7Stage2Pair56Color56CoforestVertex :=
  [RootHubThreeLeafNoMateCoforestVertex.root,
    RootHubThreeLeafNoMateCoforestVertex.hub,
    RootHubThreeLeafNoMateCoforestVertex.leaf1,
    RootHubThreeLeafNoMateCoforestVertex.leaf2,
    RootHubThreeLeafNoMateCoforestVertex.leaf3]

def d7Stage2Pair56Color56CoforestParentTable :
    List D7Stage2Pair56Color56CoforestVertex :=
  d7Stage2Pair56Color56CoforestEdgeTable.map
    d7Stage2Pair56Color56CoforestParent

def d7Stage2Pair56Color56CoforestChildTable :
    List D7Stage2Pair56Color56CoforestVertex :=
  d7Stage2Pair56Color56CoforestEdgeTable.map
    d7Stage2Pair56Color56CoforestChild

def d7Stage2Pair56Color56CoforestParentStepTable :
    List D7Stage2Pair56Color56CoforestVertex :=
  d7Stage2Pair56Color56CoforestVertexTable.map
    d7Stage2Pair56Color56CoforestParentStep

def d7Stage2Pair56Color56CoforestRankTable : List Nat :=
  d7Stage2Pair56Color56CoforestVertexTable.map
    d7Stage2Pair56Color56CoforestRank

theorem d7Stage2Pair56Color56CoforestEdgeTable_length :
    d7Stage2Pair56Color56CoforestEdgeTable.length = 4 :=
  rfl

theorem d7Stage2Pair56Color56CoforestVertexTable_length :
    d7Stage2Pair56Color56CoforestVertexTable.length = 5 :=
  rfl

theorem d7Stage2Pair56Color56CoforestEdgeTable_nodup :
    d7Stage2Pair56Color56CoforestEdgeTable.Nodup := by
  decide

theorem d7Stage2Pair56Color56CoforestVertexTable_nodup :
    d7Stage2Pair56Color56CoforestVertexTable.Nodup := by
  decide

theorem d7Stage2Pair56Color56CoforestParentTable_readout :
    d7Stage2Pair56Color56CoforestParentTable =
      [RootHubThreeLeafNoMateCoforestVertex.root,
        RootHubThreeLeafNoMateCoforestVertex.hub,
        RootHubThreeLeafNoMateCoforestVertex.hub,
        RootHubThreeLeafNoMateCoforestVertex.hub] :=
  rfl

theorem d7Stage2Pair56Color56CoforestChildTable_readout :
    d7Stage2Pair56Color56CoforestChildTable =
      [RootHubThreeLeafNoMateCoforestVertex.hub,
        RootHubThreeLeafNoMateCoforestVertex.leaf1,
        RootHubThreeLeafNoMateCoforestVertex.leaf2,
        RootHubThreeLeafNoMateCoforestVertex.leaf3] :=
  rfl

theorem d7Stage2Pair56Color56CoforestParentStepTable_readout :
    d7Stage2Pair56Color56CoforestParentStepTable =
      [RootHubThreeLeafNoMateCoforestVertex.root,
        RootHubThreeLeafNoMateCoforestVertex.root,
        RootHubThreeLeafNoMateCoforestVertex.hub,
        RootHubThreeLeafNoMateCoforestVertex.hub,
        RootHubThreeLeafNoMateCoforestVertex.hub] :=
  rfl

theorem d7Stage2Pair56Color56CoforestRankTable_readout :
    d7Stage2Pair56Color56CoforestRankTable = [0, 1, 2, 2, 2] :=
  rfl

abbrev d7Stage2Pair56Color56CoforestRankedParentMapData :
    RankedRootedParentMapData
      d7Stage2Pair56Color56CoforestParentStep
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild :=
  rootHubThreeLeafNoMateCoforestRankedParentMapData

theorem d7Stage2Pair56Color56CoforestParentMapBoundary :
    ParentMapBoundary
      d7Stage2Pair56Color56CoforestDescendantCut
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild :=
  rootHubThreeLeafNoMateCoforestParentMapBoundary

theorem d7Stage2Pair56Color56CoforestIncidence_eq_ite
    (cut edge : D7Stage2Pair56Color56CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rootHubThreeLeafNoMateCoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair56Color56CoforestIncidence_self
    (edge : D7Stage2Pair56Color56CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild edge edge = 1 :=
  rootHubThreeLeafNoMateCoforestIncidence_self edge

theorem d7Stage2Pair56Color56CoforestIncidence_ne
    {cut edge : D7Stage2Pair56Color56CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild cut edge = 0 :=
  rootHubThreeLeafNoMateCoforestIncidence_ne hne

theorem d7Stage2Pair56Color56CoforestIteratedParentMapBoundary :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair56Color56CoforestParentStep
        d7Stage2Pair56Color56CoforestChild)
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild :=
  rootHubThreeLeafNoMateCoforestIteratedParentMapBoundary

end TypeA

export TypeA
  (D5Stage1CoforestVertex D5Stage1CoforestEdge
   d5Stage1CoforestParent
   d5Stage1CoforestChild
   d5Stage1CoforestDescendantCut
   d5Stage1CoforestDescendantCutDecidable
   d5Stage1CoforestParentStep
   d5Stage1CoforestRank
   d5Stage1CoforestEdgeTable
   d5Stage1CoforestVertexTable
   d5Stage1CoforestParentTable
   d5Stage1CoforestChildTable
   d5Stage1CoforestParentStepTable
   d5Stage1CoforestRankTable
   d5Stage1CoforestEdgeTable_length
   d5Stage1CoforestVertexTable_length
   d5Stage1CoforestEdgeTable_nodup
   d5Stage1CoforestVertexTable_nodup
   d5Stage1CoforestParentTable_readout
   d5Stage1CoforestChildTable_readout
   d5Stage1CoforestParentStepTable_readout
   d5Stage1CoforestRankTable_readout
   d5Stage1CoforestRankedParentMapData
   d5Stage1CoforestParentMapBoundary
   d5Stage1CoforestIncidence_eq_ite
   d5Stage1CoforestIncidence_self
   d5Stage1CoforestIncidence_ne
   d5Stage1CoforestIteratedParentMapBoundary
   D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
   d5Stage1PairCoforestParent
   d5Stage1PairCoforestChild
   d5Stage1PairCoforestDescendantCut
   d5Stage1PairCoforestDescendantCutDecidable
   d5Stage1PairCoforestParentStep
   d5Stage1PairCoforestRank
   d5Stage1PairCoforestEdgeTable
   d5Stage1PairCoforestVertexTable
   d5Stage1PairCoforestParentTable
   d5Stage1PairCoforestChildTable
   d5Stage1PairCoforestParentStepTable
   d5Stage1PairCoforestRankTable
   d5Stage1PairCoforestEdgeTable_length
   d5Stage1PairCoforestVertexTable_length
   d5Stage1PairCoforestEdgeTable_nodup
   d5Stage1PairCoforestVertexTable_nodup
   d5Stage1PairCoforestParentTable_readout
   d5Stage1PairCoforestChildTable_readout
   d5Stage1PairCoforestParentStepTable_readout
   d5Stage1PairCoforestRankTable_readout
   d5Stage1PairCoforestRankedParentMapData
   d5Stage1PairCoforestParentMapBoundary
   d5Stage1PairCoforestIncidence_eq_ite
   d5Stage1PairCoforestIncidence_self
   d5Stage1PairCoforestIncidence_ne
   d5Stage1PairCoforestIteratedParentMapBoundary
   D5Stage2TripleColor0CoforestVertex
   D5Stage2TripleColor0CoforestEdge
   d5Stage2TripleColor0CoforestParent
   d5Stage2TripleColor0CoforestChild
   d5Stage2TripleColor0CoforestDescendantCut
   d5Stage2TripleColor0CoforestDescendantCutDecidable
   d5Stage2TripleColor0CoforestParentStep
   d5Stage2TripleColor0CoforestRank
   d5Stage2TripleColor0CoforestEdgeTable
   d5Stage2TripleColor0CoforestVertexTable
   d5Stage2TripleColor0CoforestParentTable
   d5Stage2TripleColor0CoforestChildTable
   d5Stage2TripleColor0CoforestParentStepTable
   d5Stage2TripleColor0CoforestRankTable
   d5Stage2TripleColor0CoforestEdgeTable_length
   d5Stage2TripleColor0CoforestVertexTable_length
   d5Stage2TripleColor0CoforestEdgeTable_nodup
   d5Stage2TripleColor0CoforestVertexTable_nodup
   d5Stage2TripleColor0CoforestParentTable_readout
   d5Stage2TripleColor0CoforestChildTable_readout
   d5Stage2TripleColor0CoforestParentStepTable_readout
   d5Stage2TripleColor0CoforestRankTable_readout
   d5Stage2TripleColor0CoforestRankedParentMapData
   d5Stage2TripleColor0CoforestParentMapBoundary
   d5Stage2TripleColor0CoforestIncidence_eq_ite
   d5Stage2TripleColor0CoforestIncidence_self
   d5Stage2TripleColor0CoforestIncidence_ne
   d5Stage2TripleColor0CoforestIteratedParentMapBoundary
   D5Stage2TripleColor43CoforestVertex
   D5Stage2TripleColor43CoforestEdge
   d5Stage2TripleColor43CoforestParent
   d5Stage2TripleColor43CoforestChild
   d5Stage2TripleColor43CoforestDescendantCut
   d5Stage2TripleColor43CoforestDescendantCutDecidable
   d5Stage2TripleColor43CoforestParentStep
   d5Stage2TripleColor43CoforestRank
   d5Stage2TripleColor43CoforestEdgeTable
   d5Stage2TripleColor43CoforestVertexTable
   d5Stage2TripleColor43CoforestParentTable
   d5Stage2TripleColor43CoforestChildTable
   d5Stage2TripleColor43CoforestParentStepTable
   d5Stage2TripleColor43CoforestRankTable
   d5Stage2TripleColor43CoforestEdgeTable_length
   d5Stage2TripleColor43CoforestVertexTable_length
   d5Stage2TripleColor43CoforestEdgeTable_nodup
   d5Stage2TripleColor43CoforestVertexTable_nodup
   d5Stage2TripleColor43CoforestParentTable_readout
   d5Stage2TripleColor43CoforestChildTable_readout
   d5Stage2TripleColor43CoforestParentStepTable_readout
   d5Stage2TripleColor43CoforestRankTable_readout
   d5Stage2TripleColor43CoforestRankedParentMapData
   d5Stage2TripleColor43CoforestParentMapBoundary
   d5Stage2TripleColor43CoforestIncidence_eq_ite
   d5Stage2TripleColor43CoforestIncidence_self
   d5Stage2TripleColor43CoforestIncidence_ne
   d5Stage2TripleColor43CoforestIteratedParentMapBoundary
   D5Stage2PairColor1CoforestVertex
   D5Stage2PairColor1CoforestEdge
   d5Stage2PairColor1CoforestParent
   d5Stage2PairColor1CoforestChild
   d5Stage2PairColor1CoforestDescendantCut
   d5Stage2PairColor1CoforestDescendantCutDecidable
   d5Stage2PairColor1CoforestParentStep
   d5Stage2PairColor1CoforestRank
   d5Stage2PairColor1CoforestEdgeTable
   d5Stage2PairColor1CoforestVertexTable
   d5Stage2PairColor1CoforestParentTable
   d5Stage2PairColor1CoforestChildTable
   d5Stage2PairColor1CoforestParentStepTable
   d5Stage2PairColor1CoforestRankTable
   d5Stage2PairColor1CoforestEdgeTable_length
   d5Stage2PairColor1CoforestVertexTable_length
   d5Stage2PairColor1CoforestEdgeTable_nodup
   d5Stage2PairColor1CoforestVertexTable_nodup
   d5Stage2PairColor1CoforestParentTable_readout
   d5Stage2PairColor1CoforestChildTable_readout
   d5Stage2PairColor1CoforestParentStepTable_readout
   d5Stage2PairColor1CoforestRankTable_readout
   d5Stage2PairColor1CoforestRankedParentMapData
   d5Stage2PairColor1CoforestParentMapBoundary
   d5Stage2PairColor1CoforestIncidence_eq_ite
   d5Stage2PairColor1CoforestIncidence_self
   d5Stage2PairColor1CoforestIncidence_ne
   d5Stage2PairColor1CoforestIteratedParentMapBoundary
   D5Stage2PairColor2CoforestVertex
   D5Stage2PairColor2CoforestEdge
   d5Stage2PairColor2CoforestParent
   d5Stage2PairColor2CoforestChild
   d5Stage2PairColor2CoforestDescendantCut
   d5Stage2PairColor2CoforestDescendantCutDecidable
   d5Stage2PairColor2CoforestParentStep
   d5Stage2PairColor2CoforestRank
   d5Stage2PairColor2CoforestEdgeTable
   d5Stage2PairColor2CoforestVertexTable
   d5Stage2PairColor2CoforestParentTable
   d5Stage2PairColor2CoforestChildTable
   d5Stage2PairColor2CoforestParentStepTable
   d5Stage2PairColor2CoforestRankTable
   d5Stage2PairColor2CoforestEdgeTable_length
   d5Stage2PairColor2CoforestVertexTable_length
   d5Stage2PairColor2CoforestEdgeTable_nodup
   d5Stage2PairColor2CoforestVertexTable_nodup
   d5Stage2PairColor2CoforestParentTable_readout
   d5Stage2PairColor2CoforestChildTable_readout
   d5Stage2PairColor2CoforestParentStepTable_readout
   d5Stage2PairColor2CoforestRankTable_readout
   d5Stage2PairColor2CoforestRankedParentMapData
   d5Stage2PairColor2CoforestParentMapBoundary
   d5Stage2PairColor2CoforestIncidence_eq_ite
   d5Stage2PairColor2CoforestIncidence_self
   d5Stage2PairColor2CoforestIncidence_ne
   d5Stage2PairColor2CoforestIteratedParentMapBoundary
   D5Stage3FinalPairColor0CoforestVertex
   D5Stage3FinalPairColor0CoforestEdge
   d5Stage3FinalPairColor0CoforestParent
   d5Stage3FinalPairColor0CoforestChild
   d5Stage3FinalPairColor0CoforestDescendantCut
   d5Stage3FinalPairColor0CoforestDescendantCutDecidable
   d5Stage3FinalPairColor0CoforestParentStep
   d5Stage3FinalPairColor0CoforestRank
   d5Stage3FinalPairColor0CoforestEdgeTable
   d5Stage3FinalPairColor0CoforestVertexTable
   d5Stage3FinalPairColor0CoforestParentTable
   d5Stage3FinalPairColor0CoforestChildTable
   d5Stage3FinalPairColor0CoforestParentStepTable
   d5Stage3FinalPairColor0CoforestRankTable
   d5Stage3FinalPairColor0CoforestEdgeTable_length
   d5Stage3FinalPairColor0CoforestVertexTable_length
   d5Stage3FinalPairColor0CoforestEdgeTable_nodup
   d5Stage3FinalPairColor0CoforestVertexTable_nodup
   d5Stage3FinalPairColor0CoforestParentTable_readout
   d5Stage3FinalPairColor0CoforestChildTable_readout
   d5Stage3FinalPairColor0CoforestParentStepTable_readout
   d5Stage3FinalPairColor0CoforestRankTable_readout
   d5Stage3FinalPairColor0CoforestRankedParentMapData
   d5Stage3FinalPairColor0CoforestParentMapBoundary
   d5Stage3FinalPairColor0CoforestIncidence_eq_ite
   d5Stage3FinalPairColor0CoforestIncidence_self
   d5Stage3FinalPairColor0CoforestIncidence_ne
   d5Stage3FinalPairColor0CoforestIteratedParentMapBoundary
   D5Stage3FinalPairColor2CoforestVertex
   D5Stage3FinalPairColor2CoforestEdge
   d5Stage3FinalPairColor2CoforestParent
   d5Stage3FinalPairColor2CoforestChild
   d5Stage3FinalPairColor2CoforestDescendantCut
   d5Stage3FinalPairColor2CoforestDescendantCutDecidable
   d5Stage3FinalPairColor2CoforestParentStep
   d5Stage3FinalPairColor2CoforestRank
   d5Stage3FinalPairColor2CoforestEdgeTable
   d5Stage3FinalPairColor2CoforestVertexTable
   d5Stage3FinalPairColor2CoforestParentTable
   d5Stage3FinalPairColor2CoforestChildTable
   d5Stage3FinalPairColor2CoforestParentStepTable
   d5Stage3FinalPairColor2CoforestRankTable
   d5Stage3FinalPairColor2CoforestEdgeTable_length
   d5Stage3FinalPairColor2CoforestVertexTable_length
   d5Stage3FinalPairColor2CoforestEdgeTable_nodup
   d5Stage3FinalPairColor2CoforestVertexTable_nodup
   d5Stage3FinalPairColor2CoforestParentTable_readout
   d5Stage3FinalPairColor2CoforestChildTable_readout
   d5Stage3FinalPairColor2CoforestParentStepTable_readout
   d5Stage3FinalPairColor2CoforestRankTable_readout
   d5Stage3FinalPairColor2CoforestRankedParentMapData
   d5Stage3FinalPairColor2CoforestParentMapBoundary
   d5Stage3FinalPairColor2CoforestIncidence_eq_ite
   d5Stage3FinalPairColor2CoforestIncidence_self
   d5Stage3FinalPairColor2CoforestIncidence_ne
   d5Stage3FinalPairColor2CoforestIteratedParentMapBoundary
   D7Stage1TripleCoforestVertex
   D7Stage1TripleCoforestEdge
   d7Stage1TripleCoforestParent
   d7Stage1TripleCoforestChild
   d7Stage1TripleCoforestDescendantCut
   d7Stage1TripleCoforestDescendantCutDecidable
   d7Stage1TripleCoforestParentStep
   d7Stage1TripleCoforestRank
   d7Stage1TripleCoforestEdgeTable
   d7Stage1TripleCoforestVertexTable
   d7Stage1TripleCoforestParentTable
   d7Stage1TripleCoforestChildTable
   d7Stage1TripleCoforestParentStepTable
   d7Stage1TripleCoforestRankTable
   d7Stage1TripleCoforestEdgeTable_length
   d7Stage1TripleCoforestVertexTable_length
   d7Stage1TripleCoforestEdgeTable_nodup
   d7Stage1TripleCoforestVertexTable_nodup
   d7Stage1TripleCoforestParentTable_readout
   d7Stage1TripleCoforestChildTable_readout
   d7Stage1TripleCoforestParentStepTable_readout
   d7Stage1TripleCoforestRankTable_readout
   d7Stage1TripleCoforestRankedParentMapData
   d7Stage1TripleCoforestParentMapBoundary
   d7Stage1TripleCoforestIncidence_eq_ite
   d7Stage1TripleCoforestIncidence_self
   d7Stage1TripleCoforestIncidence_ne
   d7Stage1TripleCoforestIteratedParentMapBoundary
   D7Stage1Pair34CoforestVertex
   D7Stage1Pair34CoforestEdge
   d7Stage1Pair34CoforestParent
   d7Stage1Pair34CoforestChild
   d7Stage1Pair34CoforestDescendantCut
   d7Stage1Pair34CoforestDescendantCutDecidable
   d7Stage1Pair34CoforestParentStep
   d7Stage1Pair34CoforestRank
   d7Stage1Pair34CoforestEdgeTable
   d7Stage1Pair34CoforestVertexTable
   d7Stage1Pair34CoforestParentTable
   d7Stage1Pair34CoforestChildTable
   d7Stage1Pair34CoforestParentStepTable
   d7Stage1Pair34CoforestRankTable
   d7Stage1Pair34CoforestEdgeTable_length
   d7Stage1Pair34CoforestVertexTable_length
   d7Stage1Pair34CoforestEdgeTable_nodup
   d7Stage1Pair34CoforestVertexTable_nodup
   d7Stage1Pair34CoforestParentTable_readout
   d7Stage1Pair34CoforestChildTable_readout
   d7Stage1Pair34CoforestParentStepTable_readout
   d7Stage1Pair34CoforestRankTable_readout
   d7Stage1Pair34CoforestRankedParentMapData
   d7Stage1Pair34CoforestParentMapBoundary
   d7Stage1Pair34CoforestIncidence_eq_ite
   d7Stage1Pair34CoforestIncidence_self
   d7Stage1Pair34CoforestIncidence_ne
   d7Stage1Pair34CoforestIteratedParentMapBoundary
   D7Stage1Pair56CoforestVertex
   D7Stage1Pair56CoforestEdge
   d7Stage1Pair56CoforestParent
   d7Stage1Pair56CoforestChild
   d7Stage1Pair56CoforestDescendantCut
   d7Stage1Pair56CoforestDescendantCutDecidable
   d7Stage1Pair56CoforestParentStep
   d7Stage1Pair56CoforestRank
   d7Stage1Pair56CoforestEdgeTable
   d7Stage1Pair56CoforestVertexTable
   d7Stage1Pair56CoforestParentTable
   d7Stage1Pair56CoforestChildTable
   d7Stage1Pair56CoforestParentStepTable
   d7Stage1Pair56CoforestRankTable
   d7Stage1Pair56CoforestEdgeTable_length
   d7Stage1Pair56CoforestVertexTable_length
   d7Stage1Pair56CoforestEdgeTable_nodup
   d7Stage1Pair56CoforestVertexTable_nodup
   d7Stage1Pair56CoforestParentTable_readout
   d7Stage1Pair56CoforestChildTable_readout
   d7Stage1Pair56CoforestParentStepTable_readout
   d7Stage1Pair56CoforestRankTable_readout
   d7Stage1Pair56CoforestRankedParentMapData
   d7Stage1Pair56CoforestParentMapBoundary
   d7Stage1Pair56CoforestIncidence_eq_ite
   d7Stage1Pair56CoforestIncidence_self
   d7Stage1Pair56CoforestIncidence_ne
   d7Stage1Pair56CoforestIteratedParentMapBoundary
   D7Stage2CoforestVertex D7Stage2CoforestEdge
   d7Stage2CoforestParent
   d7Stage2CoforestChild
   d7Stage2CoforestDescendantCut
   d7Stage2CoforestDescendantCutDecidable
   d7Stage2CoforestParentStep
   d7Stage2CoforestRank
   d7Stage2CoforestEdgeTable
   d7Stage2CoforestVertexTable
   d7Stage2CoforestParentTable
   d7Stage2CoforestChildTable
   d7Stage2CoforestParentStepTable
   d7Stage2CoforestRankTable
   d7Stage2CoforestEdgeTable_length
   d7Stage2CoforestVertexTable_length
   d7Stage2CoforestEdgeTable_nodup
   d7Stage2CoforestVertexTable_nodup
   d7Stage2CoforestParentTable_readout
   d7Stage2CoforestChildTable_readout
   d7Stage2CoforestParentStepTable_readout
   d7Stage2CoforestRankTable_readout
   d7Stage2CoforestRankedParentMapData
   d7Stage2CoforestParentMapBoundary
   d7Stage2CoforestIncidence_eq_ite
   d7Stage2CoforestIncidence_self
   d7Stage2CoforestIncidence_ne
   d7Stage2CoforestIteratedParentMapBoundary
   d7Stage2CoforestIncidenceCertificate
   d7Stage2CoforestIncidenceCertificate_boundary
   d7Stage2CoforestIncidenceCertificate_eq_ite
   d7Stage2CoforestIncidenceCertificate_self
   d7Stage2CoforestIncidenceCertificate_ne
   D7Stage2Packet134Color34CoforestVertex
   D7Stage2Packet134Color34CoforestEdge
   d7Stage2Packet134Color34CoforestParent
   d7Stage2Packet134Color34CoforestChild
   d7Stage2Packet134Color34CoforestDescendantCut
   d7Stage2Packet134Color34CoforestDescendantCutDecidable
   d7Stage2Packet134Color34CoforestParentStep
   d7Stage2Packet134Color34CoforestRank
   d7Stage2Packet134Color34CoforestEdgeTable
   d7Stage2Packet134Color34CoforestVertexTable
   d7Stage2Packet134Color34CoforestParentTable
   d7Stage2Packet134Color34CoforestChildTable
   d7Stage2Packet134Color34CoforestParentStepTable
   d7Stage2Packet134Color34CoforestRankTable
   d7Stage2Packet134Color34CoforestEdgeTable_length
   d7Stage2Packet134Color34CoforestVertexTable_length
   d7Stage2Packet134Color34CoforestEdgeTable_nodup
   d7Stage2Packet134Color34CoforestVertexTable_nodup
   d7Stage2Packet134Color34CoforestParentTable_readout
   d7Stage2Packet134Color34CoforestChildTable_readout
   d7Stage2Packet134Color34CoforestParentStepTable_readout
   d7Stage2Packet134Color34CoforestRankTable_readout
   d7Stage2Packet134Color34CoforestRankedParentMapData
   d7Stage2Packet134Color34CoforestParentMapBoundary
   d7Stage2Packet134Color34CoforestIncidence_eq_ite
   d7Stage2Packet134Color34CoforestIncidence_self
   d7Stage2Packet134Color34CoforestIncidence_ne
   d7Stage2Packet134Color34CoforestIteratedParentMapBoundary
   D7Stage2Pair02Color0CoforestVertex
   D7Stage2Pair02Color0CoforestEdge
   d7Stage2Pair02Color0CoforestParent
   d7Stage2Pair02Color0CoforestChild
   d7Stage2Pair02Color0CoforestDescendantCut
   d7Stage2Pair02Color0CoforestDescendantCutDecidable
   d7Stage2Pair02Color0CoforestParentStep
   d7Stage2Pair02Color0CoforestRank
   d7Stage2Pair02Color0CoforestEdgeTable
   d7Stage2Pair02Color0CoforestVertexTable
   d7Stage2Pair02Color0CoforestParentTable
   d7Stage2Pair02Color0CoforestChildTable
   d7Stage2Pair02Color0CoforestParentStepTable
   d7Stage2Pair02Color0CoforestRankTable
   d7Stage2Pair02Color0CoforestEdgeTable_length
   d7Stage2Pair02Color0CoforestVertexTable_length
   d7Stage2Pair02Color0CoforestEdgeTable_nodup
   d7Stage2Pair02Color0CoforestVertexTable_nodup
   d7Stage2Pair02Color0CoforestParentTable_readout
   d7Stage2Pair02Color0CoforestChildTable_readout
   d7Stage2Pair02Color0CoforestParentStepTable_readout
   d7Stage2Pair02Color0CoforestRankTable_readout
   d7Stage2Pair02Color0CoforestRankedParentMapData
   d7Stage2Pair02Color0CoforestParentMapBoundary
   d7Stage2Pair02Color0CoforestIncidence_eq_ite
   d7Stage2Pair02Color0CoforestIncidence_self
   d7Stage2Pair02Color0CoforestIncidence_ne
   d7Stage2Pair02Color0CoforestIteratedParentMapBoundary
   D7Stage2Pair02Color2CoforestVertex
   D7Stage2Pair02Color2CoforestEdge
   d7Stage2Pair02Color2CoforestParent
   d7Stage2Pair02Color2CoforestChild
   d7Stage2Pair02Color2CoforestDescendantCut
   d7Stage2Pair02Color2CoforestDescendantCutDecidable
   d7Stage2Pair02Color2CoforestParentStep
   d7Stage2Pair02Color2CoforestRank
   d7Stage2Pair02Color2CoforestEdgeTable
   d7Stage2Pair02Color2CoforestVertexTable
   d7Stage2Pair02Color2CoforestParentTable
   d7Stage2Pair02Color2CoforestChildTable
   d7Stage2Pair02Color2CoforestParentStepTable
   d7Stage2Pair02Color2CoforestRankTable
   d7Stage2Pair02Color2CoforestEdgeTable_length
   d7Stage2Pair02Color2CoforestVertexTable_length
   d7Stage2Pair02Color2CoforestEdgeTable_nodup
   d7Stage2Pair02Color2CoforestVertexTable_nodup
   d7Stage2Pair02Color2CoforestParentTable_readout
   d7Stage2Pair02Color2CoforestChildTable_readout
   d7Stage2Pair02Color2CoforestParentStepTable_readout
   d7Stage2Pair02Color2CoforestRankTable_readout
   d7Stage2Pair02Color2CoforestRankedParentMapData
   d7Stage2Pair02Color2CoforestParentMapBoundary
   d7Stage2Pair02Color2CoforestIncidence_eq_ite
   d7Stage2Pair02Color2CoforestIncidence_self
   d7Stage2Pair02Color2CoforestIncidence_ne
   d7Stage2Pair02Color2CoforestIteratedParentMapBoundary
   D7Stage2Pair56Color56CoforestVertex
   D7Stage2Pair56Color56CoforestEdge
   d7Stage2Pair56Color56CoforestParent
   d7Stage2Pair56Color56CoforestChild
   d7Stage2Pair56Color56CoforestDescendantCut
   d7Stage2Pair56Color56CoforestDescendantCutDecidable
   d7Stage2Pair56Color56CoforestParentStep
   d7Stage2Pair56Color56CoforestRank
   d7Stage2Pair56Color56CoforestEdgeTable
   d7Stage2Pair56Color56CoforestVertexTable
   d7Stage2Pair56Color56CoforestParentTable
   d7Stage2Pair56Color56CoforestChildTable
   d7Stage2Pair56Color56CoforestParentStepTable
   d7Stage2Pair56Color56CoforestRankTable
   d7Stage2Pair56Color56CoforestEdgeTable_length
   d7Stage2Pair56Color56CoforestVertexTable_length
   d7Stage2Pair56Color56CoforestEdgeTable_nodup
   d7Stage2Pair56Color56CoforestVertexTable_nodup
   d7Stage2Pair56Color56CoforestParentTable_readout
   d7Stage2Pair56Color56CoforestChildTable_readout
   d7Stage2Pair56Color56CoforestParentStepTable_readout
   d7Stage2Pair56Color56CoforestRankTable_readout
   d7Stage2Pair56Color56CoforestRankedParentMapData
   d7Stage2Pair56Color56CoforestParentMapBoundary
   d7Stage2Pair56Color56CoforestIncidence_eq_ite
   d7Stage2Pair56Color56CoforestIncidence_self
   d7Stage2Pair56Color56CoforestIncidence_ne
   d7Stage2Pair56Color56CoforestIteratedParentMapBoundary)

end EvenV11
