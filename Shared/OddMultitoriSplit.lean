import Mathlib.Combinatorics.SimpleGraph.Metric
import Shared.TorusCayley
import Shared.SkewProductHolonomy

/-!
# Odd-modulus multitori splitting route

This file records the splitting proof for odd directed tori in a Lean-facing
form.  The hard mathematical input is isolated as the balancing/splitting
lemma.  The formalized part here is the multitorus model, the one-part base
decomposition, and the completion spine: if one may split any parallel class
`a >= 2` into `ceil(a/2), floor(a/2)`, then iterated splitting gives the
all-ones torus.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Shared
namespace OddMultitori

/-- Vertices of `T_m(parts)`: one `ZMod m` coordinate for every part. -/
abbrev Vertex (parts : List Nat) (m : Nat) : Type :=
  Fin parts.length -> ZMod m

/-- A directed arc-copy of `T_m(parts)`: a coordinate together with one of its
parallel copies. -/
abbrev Arc (parts : List Nat) : Type :=
  Sigma fun i : Fin parts.length => Fin (parts.get i)

/-- Unit step in one multitorus coordinate. -/
def basis (parts : List Nat) (m : Nat) (i : Fin parts.length) :
    Vertex parts m :=
  fun j => if j = i then 1 else 0

/-- The vertex map followed by one Hamilton colour in a multitorus
decomposition.  The second component of the selected arc records only the
parallel copy; the vertex move uses the first component. -/
def colorStep {parts : List Nat} {m : Nat}
    (colorArc : Arc parts -> Vertex parts m -> Arc parts)
    (c : Arc parts) : Vertex parts m -> Vertex parts m :=
  fun x => x + basis parts m (colorArc c x).1

/-- At each vertex every parallel arc-copy is used by exactly one Hamilton
colour. -/
def IsEdgePartition {parts : List Nat} {m : Nat}
    (colorArc : Arc parts -> Vertex parts m -> Arc parts) : Prop :=
  forall x : Vertex parts m, forall e : Arc parts,
    ∃! c : Arc parts, colorArc c x = e

/-- Every colour class is Hamiltonian on the multitorus vertex set. -/
def IsColorHamiltonian {parts : List Nat} {m : Nat}
    (colorArc : Arc parts -> Vertex parts m -> Arc parts) : Prop :=
  forall c : Arc parts, IsSingleCycleMap (colorStep colorArc c)

/-- Directed Hamilton decomposition of the multitorus `T_m(parts)`. -/
structure Decomposition (parts : List Nat) (m : Nat) where
  colorArc : Arc parts -> Vertex parts m -> Arc parts
  edgePartition : IsEdgePartition colorArc
  colorHamiltonian : IsColorHamiltonian colorArc

/-- Edge partition with an arbitrary colour type.  This is convenient for the
cyclic splitting lift, where the lifted Hamilton cycles are naturally indexed
by the old colours before being transported back to `Arc newParts`. -/
def IsColoredEdgePartition
    {parts : List Nat} {m : Nat} {Color : Type*}
    (colorArc : Color -> Vertex parts m -> Arc parts) : Prop :=
  forall x : Vertex parts m, forall e : Arc parts,
    ∃! c : Color, colorArc c x = e

/-- Hamiltonicity with an arbitrary colour type. -/
def IsColoredHamiltonian
    {parts : List Nat} {m : Nat} {Color : Type*}
    (colorArc : Color -> Vertex parts m -> Arc parts) : Prop :=
  forall c : Color,
    IsSingleCycleMap (fun x => x + basis parts m (colorArc c x).1)

/-- Directed Hamilton decomposition whose colours are not necessarily the arc
copy type. -/
structure ColoredDecomposition
    (parts : List Nat) (m : Nat) (Color : Type*) where
  colorArc : Color -> Vertex parts m -> Arc parts
  edgePartition : IsColoredEdgePartition colorArc
  colorHamiltonian : IsColoredHamiltonian colorArc

/-- Transport a coloured decomposition to the standard `Decomposition`
interface along a colour equivalence. -/
noncomputable def decompositionOfColored
    {parts : List Nat} {m : Nat} {Color : Type*}
    (E : Color ≃ Arc parts) (D : ColoredDecomposition parts m Color) :
    Decomposition parts m where
  colorArc := fun c x => D.colorArc (E.symm c) x
  edgePartition := by
    intro x e
    rcases D.edgePartition x e with ⟨c, hc, huniq⟩
    refine ⟨E c, ?_, ?_⟩
    · simpa using hc
    · intro c' hc'
      have hpre : E.symm c' = c := huniq (E.symm c') hc'
      calc
        c' = E (E.symm c') := by simp
        _ = E c := by rw [hpre]
  colorHamiltonian := by
    intro c
    simpa [colorStep, IsColoredHamiltonian] using
      D.colorHamiltonian (E.symm c)

/-- Existence of a directed Hamilton decomposition of `T_m(parts)`. -/
def HasDecomposition (parts : List Nat) (m : Nat) : Prop :=
  Nonempty (Decomposition parts m)

/-- A coloured decomposition gives an ordinary decomposition once its colour
type is identified with the arc-copy type. -/
theorem hasDecomposition_of_colored
    {parts : List Nat} {m : Nat} {Color : Type*}
    (E : Color ≃ Arc parts) :
    Nonempty (ColoredDecomposition parts m Color) ->
      HasDecomposition parts m := by
  rintro ⟨D⟩
  exact ⟨decompositionOfColored E D⟩

/-- A decomposition equipped with the extra invariant used by the replicated
balancing shortcut: vertices are partitioned into blocks of size `m`, and
inside each block the set of colours using any fixed direction is constant.

The partition is represented by an equivalence
`Σ _ : Block, Fin m ≃ Vertex parts m`; the theorem only needs the block
coordinate and row coordinate, not a canonical quotient type. -/
structure MFiberedDecomposition (parts : List Nat) (m : Nat) where
  toDecomposition : Decomposition parts m
  Block : Type
  blockFintype : Fintype Block
  blockEquiv : (Sigma fun _ : Block => Fin m) ≃ Vertex parts m
  sameDirectionColors :
    forall (b : Block) (z z' : Fin m) (dir : Fin parts.length)
      (color : Arc parts),
      (toDecomposition.colorArc color (blockEquiv ⟨b, z⟩)).1 = dir <->
        (toDecomposition.colorArc color (blockEquiv ⟨b, z'⟩)).1 = dir

/-- Existence of an `m`-fibered Hamilton decomposition. -/
def HasMFiberedDecomposition (parts : List Nat) (m : Nat) : Prop :=
  Nonempty (MFiberedDecomposition parts m)

/-- Forgetting the `m`-fibered invariant leaves an ordinary decomposition. -/
theorem hasDecomposition_of_mFibered {parts : List Nat} {m : Nat} :
    HasMFiberedDecomposition parts m -> HasDecomposition parts m := by
  rintro ⟨D⟩
  exact ⟨D.toDecomposition⟩

/-- The set of Hamilton colours whose outgoing arc at `x` uses direction
`dir`.  In the splitting proof this is the neighbour set of the incidence
row corresponding to `x`. -/
noncomputable def directionColorSet {parts : List Nat} {m : Nat}
    (D : Decomposition parts m) (x : Vertex parts m)
    (dir : Fin parts.length) : Finset (Arc parts) := by
  classical
  exact Finset.univ.filter fun c => (D.colorArc c x).1 = dir

/-- If an arc-copy equality in the `Sigma` arc type identifies both direction
and copy, then casting the copy coordinate along the direction equality gives
the stated copy. -/
theorem arc_copy_cast_eq_of_eq {parts : List Nat}
    {e : Arc parts} {dir : Fin parts.length} {copy : Fin (parts.get dir)}
    (h : e = ⟨dir, copy⟩) :
    cast (by rw [congrArg Sigma.fst h]) e.2 = copy := by
  cases h
  simp

/-- At a fixed vertex, exactly `parts.get dir` Hamilton colours use direction
`dir`.  This is the incidence left-degree calculation needed before applying
replicated balancing. -/
theorem directionColorSet_card {parts : List Nat} {m : Nat}
    (D : Decomposition parts m) (x : Vertex parts m)
    (dir : Fin parts.length) :
    (directionColorSet D x dir).card = parts.get dir := by
  classical
  let P : Arc parts -> Prop := fun c => (D.colorArc c x).1 = dir
  let edgeOfColor : {c : Arc parts // P c} -> Fin (parts.get dir) := fun c =>
    cast (by rw [c.2]) (D.colorArc c.1 x).2
  have hEdge : forall copy : Fin (parts.get dir),
      ∃! c : Arc parts, D.colorArc c x = ⟨dir, copy⟩ := by
    intro copy
    exact D.edgePartition x ⟨dir, copy⟩
  let colorOfEdge : Fin (parts.get dir) -> {c : Arc parts // P c} :=
    fun copy =>
      let c : Arc parts := Classical.choose (hEdge copy)
      have hc : D.colorArc c x = ⟨dir, copy⟩ :=
        (Classical.choose_spec (hEdge copy)).1
      ⟨c, by
        dsimp [P]
        exact congrArg Sigma.fst hc⟩
  let e : {c : Arc parts // P c} ≃ Fin (parts.get dir) :=
    { toFun := edgeOfColor
      invFun := colorOfEdge
      left_inv := by
        intro c
        apply Subtype.ext
        dsimp [edgeOfColor, colorOfEdge]
        have huniq := (Classical.choose_spec (hEdge (edgeOfColor c))).2
        exact (huniq c.1 (by
          dsimp [edgeOfColor]
          cases c with
          | mk color hcolor =>
              dsimp [P] at hcolor
              cases hcolor
              simp)).symm
      right_inv := by
        intro copy
        dsimp [edgeOfColor, colorOfEdge]
        have hc :
            D.colorArc (Classical.choose (hEdge copy)) x =
              ⟨dir, copy⟩ :=
          (Classical.choose_spec (hEdge copy)).1
        exact arc_copy_cast_eq_of_eq hc }
  have hcardSubtype : Fintype.card {c : Arc parts // P c} = parts.get dir := by
    calc
      Fintype.card {c : Arc parts // P c} =
          Fintype.card (Fin (parts.get dir)) :=
        Fintype.card_congr e
      _ = parts.get dir := Fintype.card_fin _
  have hfinset :
      (directionColorSet D x dir).card =
        Fintype.card {c : Arc parts // P c} := by
    rw [Fintype.card_subtype]
    rfl
  rw [hfinset, hcardSubtype]

@[simp]
theorem mem_directionColorSet {parts : List Nat} {m : Nat}
    (D : Decomposition parts m) (x : Vertex parts m)
    (dir : Fin parts.length) (color : Arc parts) :
    color ∈ directionColorSet D x dir <->
      (D.colorArc color x).1 = dir := by
  classical
  simp [directionColorSet]

/-- Direction-neighbour sets for rows in a fixed `m`-fibered block. -/
noncomputable def fiberDirectionColorSet {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (b : D.Block) (z : Fin m)
    (dir : Fin parts.length) : Finset (Arc parts) :=
  directionColorSet D.toDecomposition (D.blockEquiv ⟨b, z⟩) dir

/-- The `m`-fibered invariant is precisely the replicated-balancing row
condition: inside one block, all rows have the same direction-neighbour set. -/
theorem fiberDirectionColorSet_eq {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (b : D.Block) (z z' : Fin m)
    (dir : Fin parts.length) :
    fiberDirectionColorSet D b z dir =
      fiberDirectionColorSet D b z' dir := by
  classical
  ext color
  simp [fiberDirectionColorSet, D.sameDirectionColors b z z' dir color]

/-- Every row in a fibered incidence block has left degree equal to the number
of parallel copies in the split direction. -/
theorem fiberDirectionColorSet_card {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (b : D.Block) (z : Fin m)
    (dir : Fin parts.length) :
    (fiberDirectionColorSet D b z dir).card = parts.get dir :=
  directionColorSet_card D.toDecomposition (D.blockEquiv ⟨b, z⟩) dir

/-- If a colour does not use `dir` at `x`, then one step of that colour leaves
the `dir` coordinate unchanged. -/
theorem colorStep_coord_eq_of_ne_dir {parts : List Nat} {m : Nat}
    {colorArc : Arc parts -> Vertex parts m -> Arc parts}
    (color : Arc parts) (x : Vertex parts m) (dir : Fin parts.length)
    (hdir : (colorArc color x).1 ≠ dir) :
    colorStep colorArc color x dir = x dir := by
  simp [colorStep, basis, hdir.symm]

/-- If a colour never uses `dir`, then every iterate preserves the `dir`
coordinate. -/
theorem colorStep_iterate_coord_eq_of_forall_ne_dir
    {parts : List Nat} {m : Nat}
    {colorArc : Arc parts -> Vertex parts m -> Arc parts}
    (color : Arc parts) (dir : Fin parts.length)
    (hdir : forall x : Vertex parts m, (colorArc color x).1 ≠ dir) :
    forall n : Nat, forall x : Vertex parts m,
      (colorStep colorArc color)^[n] x dir = x dir := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      rw [colorStep_coord_eq_of_ne_dir color
        ((colorStep colorArc color)^[n] x) dir
        (hdir ((colorStep colorArc color)^[n] x))]
      exact ih x

/-- In `ZMod m`, `1` is nonzero as soon as `m >= 2`. -/
theorem zmod_one_ne_zero_of_two_le {m : Nat} (hm2 : 2 <= m) :
    (1 : ZMod m) ≠ 0 := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  intro h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_one m] at hval
  simp at hval

/-- Every Hamilton colour uses every direction at least once.  Otherwise the
corresponding coordinate would be invariant along the colour orbit, contradicting
single-cycle transitivity between the all-zero vertex and the vertex with that
coordinate equal to `1`. -/
theorem color_uses_direction_exists {parts : List Nat} {m : Nat}
    (D : Decomposition parts m) (hm2 : 2 <= m)
    (color : Arc parts) (dir : Fin parts.length) :
    ∃ x : Vertex parts m, (D.colorArc color x).1 = dir := by
  classical
  by_contra hnot
  have hdir : forall x : Vertex parts m, (D.colorArc color x).1 ≠ dir := by
    intro x hx
    exact hnot ⟨x, hx⟩
  let x0 : Vertex parts m := fun _ => 0
  let x1 : Vertex parts m := fun j => if j = dir then 1 else 0
  rcases (D.colorHamiltonian color).2 x0 x1 with ⟨n, hn⟩
  have hcoord := congrFun hn dir
  have hinv := colorStep_iterate_coord_eq_of_forall_ne_dir
    (colorArc := D.colorArc) color dir hdir n x0
  have hx0 : x0 dir = (0 : ZMod m) := rfl
  have hx1 : x1 dir = (1 : ZMod m) := by simp [x1]
  have h01 : (0 : ZMod m) = 1 := by
    calc
      (0 : ZMod m) = x0 dir := by rw [hx0]
      _ = (colorStep D.colorArc color)^[n] x0 dir := hinv.symm
      _ = x1 dir := hcoord
      _ = (1 : ZMod m) := hx1
  exact zmod_one_ne_zero_of_two_le hm2 h01.symm

/-- The no-isolated-right-vertex condition for the replicated incidence
hypergraph extracted from an `m`-fibered decomposition. -/
theorem fiberDirectionColorSet_no_isolated {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (hm2 : 2 <= m)
    (z0 : Fin m) (dir : Fin parts.length) (color : Arc parts) :
    ∃ b : D.Block, color ∈ fiberDirectionColorSet D b z0 dir := by
  classical
  rcases color_uses_direction_exists D.toDecomposition hm2 color dir with
    ⟨x, hx⟩
  rcases D.blockEquiv.surjective x with ⟨p, hp⟩
  refine ⟨p.1, ?_⟩
  have hmem : color ∈ fiberDirectionColorSet D p.1 p.2 dir := by
    simp [fiberDirectionColorSet, hp, hx]
  simpa [fiberDirectionColorSet_eq D p.1 p.2 z0 dir] using hmem

/-- The old list context before splitting one parallel class. -/
abbrev OldSplitParts (left : List Nat) (a : Nat) (right : List Nat) :
    List Nat :=
  left ++ a :: right

/-- The new list context after replacing one class by two child classes. -/
abbrev NewSplitParts (left : List Nat) (b c : Nat) (right : List Nat) :
    List Nat :=
  left ++ b :: c :: right

/-- In a list context `left ++ a :: right`, the direction selected for
splitting is the inserted `a` coordinate. -/
def contextSplitDir (left : List Nat) (a : Nat) (right : List Nat) :
    Fin (OldSplitParts left a right).length :=
  ⟨left.length, by simp⟩

@[simp]
theorem contextSplitDir_get (left : List Nat) (a : Nat) (right : List Nat) :
    (OldSplitParts left a right).get (contextSplitDir left a right) = a := by
  simp [contextSplitDir, OldSplitParts]

/-- First child direction after splitting the context coordinate. -/
def contextSplitFirstDir (left : List Nat) (b c : Nat) (right : List Nat) :
    Fin (NewSplitParts left b c right).length :=
  ⟨left.length, by simp [NewSplitParts]⟩

/-- Second child direction after splitting the context coordinate. -/
def contextSplitSecondDir (left : List Nat) (b c : Nat) (right : List Nat) :
    Fin (NewSplitParts left b c right).length :=
  ⟨left.length + 1, by simp [NewSplitParts]⟩

@[simp]
theorem contextSplitFirstDir_get
    (left : List Nat) (b c : Nat) (right : List Nat) :
    (NewSplitParts left b c right).get
      (contextSplitFirstDir left b c right) = b := by
  simp [contextSplitFirstDir, NewSplitParts]

@[simp]
theorem contextSplitSecondDir_get
    (left : List Nat) (b c : Nat) (right : List Nat) :
    (NewSplitParts left b c right).get
      (contextSplitSecondDir left b c right) = c := by
  simp [contextSplitSecondDir, NewSplitParts]

/-- Arc-copy in the first child split direction. -/
noncomputable def firstChildArc
    (left : List Nat) (b c : Nat) (right : List Nat) (copy : Fin b) :
    Arc (NewSplitParts left b c right) :=
  ⟨contextSplitFirstDir left b c right,
    cast (by rw [contextSplitFirstDir_get]) copy⟩

/-- Arc-copy in the second child split direction. -/
noncomputable def secondChildArc
    (left : List Nat) (b c : Nat) (right : List Nat) (copy : Fin c) :
    Arc (NewSplitParts left b c right) :=
  ⟨contextSplitSecondDir left b c right,
    cast (by rw [contextSplitSecondDir_get]) copy⟩

theorem firstChildArc_fst
    (left : List Nat) (b c : Nat) (right : List Nat) (copy : Fin b) :
    (firstChildArc left b c right copy).1 =
      contextSplitFirstDir left b c right := rfl

theorem secondChildArc_fst
    (left : List Nat) (b c : Nat) (right : List Nat) (copy : Fin c) :
    (secondChildArc left b c right copy).1 =
      contextSplitSecondDir left b c right := rfl

theorem firstChildArc_reconstruct
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (hdir : e.1 = contextSplitFirstDir left b c right) :
    firstChildArc left b c right
      (cast (by rw [hdir, contextSplitFirstDir_get]) e.2) = e := by
  cases e with
  | mk i copy =>
      change i = contextSplitFirstDir left b c right at hdir
      subst i
      simp [firstChildArc]

theorem secondChildArc_reconstruct
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (hdir : e.1 = contextSplitSecondDir left b c right) :
    secondChildArc left b c right
      (cast (by rw [hdir, contextSplitSecondDir_get]) e.2) = e := by
  cases e with
  | mk i copy =>
      change i = contextSplitSecondDir left b c right at hdir
      subst i
      simp [secondChildArc]

/-- A new direction before the split coordinate corresponds to the old
direction with the same index. -/
def oldDirOfNewBefore
    (left : List Nat) (b c : Nat) (right : List Nat)
    (j : Fin (NewSplitParts left b c right).length)
    (hj : j.val < left.length) :
    Fin (OldSplitParts left (b + c) right).length :=
  ⟨j.val, by simp [OldSplitParts]; omega⟩

/-- A new direction after the two split child directions corresponds to the old
direction one index to the left. -/
def oldDirOfNewAfter
    (left : List Nat) (b c : Nat) (right : List Nat)
    (j : Fin (NewSplitParts left b c right).length)
    (hj : left.length + 1 < j.val) :
    Fin (OldSplitParts left (b + c) right).length :=
  ⟨j.val - 1, by
    have hlt := j.isLt
    simp [OldSplitParts, NewSplitParts] at hlt ⊢
    omega⟩

/-- An old direction before the split coordinate corresponds to the new
direction with the same index. -/
def newDirOfOldBefore
    (left : List Nat) (b c : Nat) (right : List Nat)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (_hi : i.val < left.length) :
    Fin (NewSplitParts left b c right).length :=
  ⟨i.val, by simp [NewSplitParts]; omega⟩

/-- An old direction after the split coordinate corresponds to the new
direction one index to the right. -/
def newDirOfOldAfter
    (left : List Nat) (b c : Nat) (right : List Nat)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (_hi : left.length < i.val) :
    Fin (NewSplitParts left b c right).length :=
  ⟨i.val + 1, by
    have hlt := i.isLt
    simp [OldSplitParts, NewSplitParts] at hlt ⊢
    omega⟩

theorem oldDirOfNewBefore_get
    (left : List Nat) (b c : Nat) (right : List Nat)
    (j : Fin (NewSplitParts left b c right).length)
    (hj : j.val < left.length) :
    (OldSplitParts left (b + c) right).get
      (oldDirOfNewBefore left b c right j hj) =
      (NewSplitParts left b c right).get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp [oldDirOfNewBefore, OldSplitParts, NewSplitParts]
  rw [List.getElem_append_left (h := hj)]
  rw [List.getElem_append_left (h := hj)]

theorem oldDirOfNewAfter_get
    (left : List Nat) (b c : Nat) (right : List Nat)
    (j : Fin (NewSplitParts left b c right).length)
    (hj : left.length + 1 < j.val) :
    (OldSplitParts left (b + c) right).get
      (oldDirOfNewAfter left b c right j hj) =
      (NewSplitParts left b c right).get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp [oldDirOfNewAfter, OldSplitParts, NewSplitParts]
  grind

theorem newDirOfOldBefore_get
    (left : List Nat) (b c : Nat) (right : List Nat)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (hi : i.val < left.length) :
    (NewSplitParts left b c right).get
      (newDirOfOldBefore left b c right i hi) =
      (OldSplitParts left (b + c) right).get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp [newDirOfOldBefore, OldSplitParts, NewSplitParts]
  rw [List.getElem_append_left (h := hi)]
  rw [List.getElem_append_left (h := hi)]

theorem newDirOfOldAfter_get
    (left : List Nat) (b c : Nat) (right : List Nat)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (hi : left.length < i.val) :
    (NewSplitParts left b c right).get
      (newDirOfOldAfter left b c right i hi) =
      (OldSplitParts left (b + c) right).get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp [newDirOfOldAfter, OldSplitParts, NewSplitParts]
  grind

/-- Transport an old non-split arc before the split coordinate to the new
context. -/
noncomputable def newArcOfOldBefore
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (OldSplitParts left (b + c) right))
    (he : e.1.val < left.length) :
    Arc (NewSplitParts left b c right) :=
  ⟨newDirOfOldBefore left b c right e.1 he,
    cast (by rw [newDirOfOldBefore_get]) e.2⟩

/-- Transport an old non-split arc after the split coordinate to the new
context. -/
noncomputable def newArcOfOldAfter
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (OldSplitParts left (b + c) right))
    (he : left.length < e.1.val) :
    Arc (NewSplitParts left b c right) :=
  ⟨newDirOfOldAfter left b c right e.1 he,
    cast (by rw [newDirOfOldAfter_get]) e.2⟩

/-- Transport a new non-split arc before the split coordinate back to the old
context. -/
noncomputable def oldArcOfNewBefore
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (he : e.1.val < left.length) :
    Arc (OldSplitParts left (b + c) right) :=
  ⟨oldDirOfNewBefore left b c right e.1 he,
    cast (by rw [oldDirOfNewBefore_get]) e.2⟩

/-- Transport a new non-split arc after the split child directions back to the
old context. -/
noncomputable def oldArcOfNewAfter
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (he : left.length + 1 < e.1.val) :
    Arc (OldSplitParts left (b + c) right) :=
  ⟨oldDirOfNewAfter left b c right e.1 he,
    cast (by rw [oldDirOfNewAfter_get]) e.2⟩

theorem newArcOfOldBefore_oldArcOfNewBefore
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (he : e.1.val < left.length) :
    newArcOfOldBefore left b c right
      (oldArcOfNewBefore left b c right e he)
      (by simpa [oldArcOfNewBefore, oldDirOfNewBefore] using he) = e := by
  cases e with
  | mk i copy =>
      simp [oldArcOfNewBefore, newArcOfOldBefore,
        oldDirOfNewBefore, newDirOfOldBefore]

theorem newArcOfOldAfter_oldArcOfNewAfter
    (left : List Nat) (b c : Nat) (right : List Nat)
    (e : Arc (NewSplitParts left b c right))
    (he : left.length + 1 < e.1.val) :
    newArcOfOldAfter left b c right
      (oldArcOfNewAfter left b c right e he)
      (by
        simpa [oldArcOfNewAfter, oldDirOfNewAfter] using
          (Nat.lt_sub_of_add_lt he)) = e := by
  cases e with
  | mk i copy =>
      dsimp [oldArcOfNewAfter, newArcOfOldAfter]
      apply Sigma.ext
      · apply Fin.ext
        simp [oldDirOfNewAfter, newDirOfOldAfter]
        have he' : left.length + 1 < i.val := by simpa using he
        rw [Nat.sub_add_cancel (by omega : 1 <= i.val)]
      · simp

/-! ### Generic tuple contraction for the cyclic splitting lift -/

/-- Cast between finite function spaces with propositionally equal lengths. -/
noncomputable def finFunctionCast {n n' : Nat} {α : Type*} (h : n = n') :
    (Fin n -> α) ≃ (Fin n' -> α) where
  toFun f j := f (Fin.cast h.symm j)
  invFun g i := g (Fin.cast h i)
  left_inv := by
    intro f
    funext i
    simp
  right_inv := by
    intro g
    funext j
    simp

/-- The second child index associated to a non-last split index `j`. -/
def finSplitSecondIndex {n : Nat} (j : Fin (n + 1)) (hj : j.val < n) :
    Fin (n + 1) :=
  ⟨j.val + 1, by omega⟩

/-- Split a length-`n` tuple plus a sheet coordinate into a length-`n+1`
tuple: before `j` coordinates are unchanged, the `j` coordinate becomes
`old_j - sheet`, the next coordinate is `sheet`, and later coordinates are
shifted right. -/
def finSplitTuple {n m : Nat} (j : Fin (n + 1)) (hj : j.val < n) :
    ((Fin n -> ZMod m) × ZMod m) -> Fin (n + 1) -> ZMod m :=
  fun p l =>
    if hl : l.val < j.val then
      p.1 ⟨l.val, by omega⟩
    else if hF : l.val = j.val then
      p.1 ⟨j.val, hj⟩ - p.2
    else if hS : l.val = j.val + 1 then
      p.2
    else
      p.1 ⟨l.val - 1, by omega⟩

/-- Contract adjacent split coordinates by addition. -/
def finContractAdd {n m : Nat} (j : Fin (n + 1)) :
    (Fin (n + 1) -> ZMod m) -> Fin n -> ZMod m :=
  fun y => Fin.contractNth j (fun a b : ZMod m => a + b) y

theorem finSplitTuple_apply_lt {n m : Nat}
    (j : Fin (n + 1)) (hj : j.val < n)
    (p : (Fin n -> ZMod m) × ZMod m) (l : Fin (n + 1))
    (hl : l.val < j.val) :
    finSplitTuple j hj p l = p.1 ⟨l.val, by omega⟩ := by
  simp [finSplitTuple, hl]

theorem finSplitTuple_apply_first {n m : Nat}
    (j : Fin (n + 1)) (hj : j.val < n)
    (p : (Fin n -> ZMod m) × ZMod m) (l : Fin (n + 1))
    (hF : l.val = j.val) :
    finSplitTuple j hj p l = p.1 ⟨j.val, hj⟩ - p.2 := by
  simp [finSplitTuple, hF]

theorem finSplitTuple_apply_second {n m : Nat}
    (j : Fin (n + 1)) (hj : j.val < n)
    (p : (Fin n -> ZMod m) × ZMod m) (l : Fin (n + 1))
    (hS : l.val = j.val + 1) :
    finSplitTuple j hj p l = p.2 := by
  simp [finSplitTuple, hS]

theorem finSplitTuple_apply_gt_second {n m : Nat}
    (j : Fin (n + 1)) (hj : j.val < n)
    (p : (Fin n -> ZMod m) × ZMod m) (l : Fin (n + 1))
    (hgt : j.val + 1 < l.val) :
    finSplitTuple j hj p l = p.1 ⟨l.val - 1, by omega⟩ := by
  have hnotLt : ¬ l.val < j.val := by omega
  have hnotF : ¬ l.val = j.val := by omega
  have hnotS : ¬ l.val = j.val + 1 := by omega
  simp [finSplitTuple, hnotLt, hnotF, hnotS]

theorem finContractAdd_apply_lt {n m : Nat}
    (j : Fin (n + 1)) (y : Fin (n + 1) -> ZMod m)
    (k : Fin n) (hk : k.val < j.val) :
    finContractAdd j y k = y (Fin.castSucc k) := by
  exact Fin.contractNth_apply_of_lt j (fun a b : ZMod m => a + b) y k hk

theorem finContractAdd_apply_eq {n m : Nat}
    (j : Fin (n + 1)) (y : Fin (n + 1) -> ZMod m)
    (k : Fin n) (hk : k.val = j.val) :
    finContractAdd j y k = y (Fin.castSucc k) + y k.succ := by
  exact Fin.contractNth_apply_of_eq j (fun a b : ZMod m => a + b) y k hk

theorem finContractAdd_apply_gt {n m : Nat}
    (j : Fin (n + 1)) (y : Fin (n + 1) -> ZMod m)
    (k : Fin n) (hk : j.val < k.val) :
    finContractAdd j y k = y k.succ := by
  exact Fin.contractNth_apply_of_gt j (fun a b : ZMod m => a + b) y k hk

/-- Contracting two adjacent coordinates by addition, while remembering the
second coordinate as the sheet, is equivalent to the original tuple.  This is
the generic coordinate engine behind the `π(x,z)` map in the cyclic splitting
proof. -/
def finContractSplitEquiv (n m : Nat) (j : Fin (n + 1))
    (hj : j.val < n) :
    (Fin (n + 1) -> ZMod m) ≃ ((Fin n -> ZMod m) × ZMod m) where
  toFun y := (finContractAdd j y, y (finSplitSecondIndex j hj))
  invFun p := finSplitTuple j hj p
  left_inv := by
    intro y
    funext l
    change finSplitTuple j hj
        (finContractAdd j y, y (finSplitSecondIndex j hj)) l = y l
    rcases lt_trichotomy l.val j.val with hlt | heq | hgt
    · rw [finSplitTuple_apply_lt j hj _ _ hlt]
      calc
        (finContractAdd j y, y (finSplitSecondIndex j hj)).1
            ⟨l.val, by omega⟩
            = y (Fin.castSucc (⟨l.val, by omega⟩ : Fin n)) := by
              simpa using finContractAdd_apply_lt j y
                (⟨l.val, by omega⟩ : Fin n) (by simpa using hlt)
        _ = y l := by
              exact congrArg y (Fin.ext rfl)
    · rw [finSplitTuple_apply_first j hj _ _ heq]
      let k : Fin n := ⟨j.val, hj⟩
      have hC :
          (finContractAdd j y, y (finSplitSecondIndex j hj)).1 k =
            y (Fin.castSucc k) + y k.succ := by
        simpa [k] using finContractAdd_apply_eq j y k (by simp [k])
      have hcast : Fin.castSucc k = l := by
        apply Fin.ext
        simp [k, heq]
      have hsucc : k.succ = finSplitSecondIndex j hj := by
        apply Fin.ext
        simp [k, finSplitSecondIndex]
      rw [hC, hcast, hsucc]
      ring
    · by_cases hS : l.val = j.val + 1
      · rw [finSplitTuple_apply_second j hj _ _ hS]
        change y (finSplitSecondIndex j hj) = y l
        exact congrArg y (Fin.ext (by simp [finSplitSecondIndex, hS]))
      · have hgt2 : j.val + 1 < l.val := by omega
        rw [finSplitTuple_apply_gt_second j hj _ _ hgt2]
        let k : Fin n := ⟨l.val - 1, by omega⟩
        have hC :
            (finContractAdd j y, y (finSplitSecondIndex j hj)).1 k =
              y k.succ := by
          simpa [k] using finContractAdd_apply_gt j y k
            (by simp [k]; omega)
        have hsucc : k.succ = l := by
          apply Fin.ext
          simp [k]
          omega
        rw [hC, hsucc]
  right_inv := by
    intro p
    apply Prod.ext
    · funext k
      change finContractAdd j (finSplitTuple j hj p) k = p.1 k
      rcases lt_trichotomy k.val j.val with hlt | heq | hgt
      · rw [finContractAdd_apply_lt j (finSplitTuple j hj p) k hlt]
        rw [finSplitTuple_apply_lt j hj _ _ (by simpa using hlt)]
        exact congrArg p.1 (Fin.ext rfl)
      · rw [finContractAdd_apply_eq j (finSplitTuple j hj p) k heq]
        have hfirst :
            finSplitTuple j hj p (Fin.castSucc k) = p.1 k - p.2 := by
          rw [finSplitTuple_apply_first]
          · have hk : (⟨j.val, hj⟩ : Fin n) = k := by
              apply Fin.ext
              simpa using heq.symm
            rw [hk]
          · simp [heq]
        have hsecond : finSplitTuple j hj p k.succ = p.2 := by
          rw [finSplitTuple_apply_second]
          simp [heq]
        rw [hfirst, hsecond]
        ring
      · rw [finContractAdd_apply_gt j (finSplitTuple j hj p) k hgt]
        have hgt2 : j.val + 1 < (k.succ : Fin (n + 1)).val := by
          change j.val + 1 < k.val + 1
          omega
        rw [finSplitTuple_apply_gt_second j hj _ _ hgt2]
        exact congrArg p.1 (Fin.ext (by simp))
    · change finSplitTuple j hj p (finSplitSecondIndex j hj) = p.2
      rw [finSplitTuple_apply_second]
      simp [finSplitSecondIndex]

/-- Splitting one list-context coordinate increases the number of coordinates
by one. -/
theorem newSplitParts_length_eq_old_succ
    (left : List Nat) (b c : Nat) (right : List Nat) :
    (NewSplitParts left b c right).length =
      (OldSplitParts left (b + c) right).length + 1 := by
  simp [OldSplitParts, NewSplitParts]
  omega

/-- The generic contraction index corresponding to the split coordinate in a
list context. -/
def splitContractIndex (left : List Nat) (b c : Nat) (right : List Nat) :
    Fin ((OldSplitParts left (b + c) right).length + 1) :=
  ⟨left.length, by simp [OldSplitParts]⟩

theorem splitContractIndex_not_last
    (left : List Nat) (b c : Nat) (right : List Nat) :
    (splitContractIndex left b c right).val <
      (OldSplitParts left (b + c) right).length := by
  simp [splitContractIndex, OldSplitParts]

/-- Vertex equivalence for one cyclic splitting step: the new split torus
coordinate space is the old coordinate space together with the sheet
coordinate.  Under this equivalence the old split coordinate is the sum of the
two child coordinates. -/
noncomputable def contextSplitVertexEquiv
    (left : List Nat) (b c m : Nat) (right : List Nat) :
    Vertex (NewSplitParts left b c right) m ≃
      Vertex (OldSplitParts left (b + c) right) m × ZMod m :=
  (finFunctionCast (α := ZMod m)
      (newSplitParts_length_eq_old_succ left b c right)).trans
    (finContractSplitEquiv
      (OldSplitParts left (b + c) right).length m
      (splitContractIndex left b c right)
      (splitContractIndex_not_last left b c right))

theorem contextSplitVertexEquiv_add_secondChild
    (left : List Nat) (b c m : Nat) (right : List Nat)
    (p : Vertex (OldSplitParts left (b + c) right) m × ZMod m) :
    contextSplitVertexEquiv left b c m right
      ((contextSplitVertexEquiv left b c m right).symm p +
        basis (NewSplitParts left b c right) m
          (contextSplitSecondDir left b c right)) =
      (p.1 + basis (OldSplitParts left (b + c) right) m
        (contextSplitDir left (b + c) right), p.2 + 1) := by
  apply Prod.ext
  · funext k
    rcases lt_trichotomy k.val left.length with hlt | heq | hgt
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_lt, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitSecondDir, basis, hlt]
      simp [Fin.ext_iff]
      have h1 : ¬ k.val = left.length + 1 := by omega
      have h2 : ¬ k.val = left.length := by omega
      simp [h1, h2]
    · have hk : k = contextSplitDir left (b + c) right := by
        exact Fin.ext heq
      subst k
      simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_eq, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitSecondDir, basis]
      ring
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_gt, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitSecondDir, basis, hgt]
      simp [Fin.ext_iff]
      have h1 : ¬ k.val + 1 < left.length := by omega
      have h2 : ¬ k.val + 1 = left.length := by omega
      have h3 : ¬ k.val = left.length := by omega
      simp [h1, h2, h3]
  · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
      finSplitSecondIndex, basis, finSplitTuple, splitContractIndex,
      contextSplitSecondDir]

theorem contextSplitVertexEquiv_add_firstChild
    (left : List Nat) (b c m : Nat) (right : List Nat)
    (p : Vertex (OldSplitParts left (b + c) right) m × ZMod m) :
    contextSplitVertexEquiv left b c m right
      ((contextSplitVertexEquiv left b c m right).symm p +
        basis (NewSplitParts left b c right) m
          (contextSplitFirstDir left b c right)) =
      (p.1 + basis (OldSplitParts left (b + c) right) m
        (contextSplitDir left (b + c) right), p.2) := by
  apply Prod.ext
  · funext k
    rcases lt_trichotomy k.val left.length with hlt | heq | hgt
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_lt, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitFirstDir, basis, hlt]
      simp [Fin.ext_iff]
    · have hk : k = contextSplitDir left (b + c) right := by
        exact Fin.ext heq
      subst k
      simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_eq, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitFirstDir, basis]
      ring
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_gt, finSplitTuple, splitContractIndex,
        contextSplitDir, contextSplitFirstDir, basis, hgt]
      simp [Fin.ext_iff]
      have h1 : ¬ k.val + 1 < left.length := by omega
      have h2 : ¬ k.val + 1 = left.length := by omega
      have h3 : ¬ k.val = left.length := by omega
      simp [h1, h2, h3]
  · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
      finSplitSecondIndex, basis, finSplitTuple, splitContractIndex,
      contextSplitFirstDir]

theorem contextSplitVertexEquiv_add_oldBefore
    (left : List Nat) (b c m : Nat) (right : List Nat)
    (p : Vertex (OldSplitParts left (b + c) right) m × ZMod m)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (hi : i.val < left.length) :
    contextSplitVertexEquiv left b c m right
      ((contextSplitVertexEquiv left b c m right).symm p +
        basis (NewSplitParts left b c right) m
          (newDirOfOldBefore left b c right i hi)) =
      (p.1 + basis (OldSplitParts left (b + c) right) m i, p.2) := by
  apply Prod.ext
  · funext k
    rcases lt_trichotomy k.val left.length with hlt | heq | hgt
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_lt, finSplitTuple, splitContractIndex,
        newDirOfOldBefore, basis, hlt]
      simp [Fin.ext_iff]
    · have hk : k = contextSplitDir left (b + c) right := by
        exact Fin.ext heq
      subst k
      simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_eq, finSplitTuple, splitContractIndex,
        contextSplitDir, newDirOfOldBefore, basis]
      have hne : ¬ left.length = i.val := by omega
      have hne2 : ¬ left.length + 1 = i.val := by omega
      simp [Fin.ext_iff, hne, hne2]
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_gt, finSplitTuple, splitContractIndex,
        newDirOfOldBefore, basis, hgt]
      simp [Fin.ext_iff]
      have h1 : ¬ k.val + 1 < left.length := by omega
      have h2 : ¬ k.val + 1 = left.length := by omega
      have h3 : ¬ k.val = i.val := by omega
      have h4 : ¬ k.val + 1 = i.val := by omega
      have h5 : ¬ k.val = left.length := by omega
      simp [h1, h2, h3, h4, h5]
  · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
      finSplitSecondIndex, basis, finSplitTuple, splitContractIndex,
      newDirOfOldBefore]
    have hne : ¬ left.length + 1 = i.val := by omega
    simp [hne]

theorem contextSplitVertexEquiv_add_oldAfter
    (left : List Nat) (b c m : Nat) (right : List Nat)
    (p : Vertex (OldSplitParts left (b + c) right) m × ZMod m)
    (i : Fin (OldSplitParts left (b + c) right).length)
    (hi : left.length < i.val) :
    contextSplitVertexEquiv left b c m right
      ((contextSplitVertexEquiv left b c m right).symm p +
        basis (NewSplitParts left b c right) m
          (newDirOfOldAfter left b c right i hi)) =
      (p.1 + basis (OldSplitParts left (b + c) right) m i, p.2) := by
  apply Prod.ext
  · funext k
    rcases lt_trichotomy k.val left.length with hlt | heq | hgt
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_lt, finSplitTuple, splitContractIndex,
        newDirOfOldAfter, basis, hlt]
      simp [Fin.ext_iff]
      have hne : ¬ k.val = i.val := by omega
      have hne2 : ¬ k.val = i.val + 1 := by omega
      simp [hne, hne2]
    · have hk : k = contextSplitDir left (b + c) right := by
        exact Fin.ext heq
      subst k
      simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_eq, finSplitTuple, splitContractIndex,
        contextSplitDir, newDirOfOldAfter, basis]
      have hne : ¬ left.length = i.val := by omega
      have hne2 : ¬ left.length = i.val + 1 := by omega
      simp [Fin.ext_iff, hne, hne2]
    · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
        finContractAdd_apply_gt, finSplitTuple, splitContractIndex,
        newDirOfOldAfter, basis, hgt]
      simp [Fin.ext_iff]
      have h1 : ¬ k.val + 1 < left.length := by omega
      have h2 : ¬ k.val + 1 = left.length := by omega
      by_cases hk : k.val = i.val
      · have hkfin : k = i := Fin.ext hk
        subst k
        have h5 : ¬ i.val = left.length := by omega
        simp [h1, h2, h5]
      · have h5 : ¬ k.val = left.length := by omega
        simp [h1, h2, h5]
  · simp [contextSplitVertexEquiv, finFunctionCast, finContractSplitEquiv,
      finSplitSecondIndex, basis, finSplitTuple, splitContractIndex,
      newDirOfOldAfter]
    have hne : ¬ left.length = i.val := by omega
    simp [hne]

/-- The one-coordinate multitorus `T_m(d)` with `d` parallel copies of the same
directed `m`-cycle has the tautological decomposition. -/
noncomputable def onePartDecomposition (d m : Nat) [NeZero m] :
    Decomposition [d] m where
  colorArc := fun c _x => c
  edgePartition := by
    intro _x e
    exact ⟨e, rfl, by intro c hc; exact hc⟩
  colorHamiltonian := by
    intro c
    refine single_cycle_of_zmod_rank
      (f := colorStep (parts := [d]) (fun c _x => c) c)
      (rank := fun x : Vertex [d] m => x ⟨0, by simp⟩)
      ?_ ?_
    · constructor
      · intro x y hxy
        funext i
        fin_cases i
        exact hxy
      · intro z
        exact ⟨fun _ => z, rfl⟩
    · intro x
      have hc0 : c.1 = (⟨0, by simp⟩ : Fin [d].length) := by
        cases c.1 with
        | mk n hn =>
            simp at hn
            have hn0 : n = 0 := by omega
            subst n
            rfl
      simp [colorStep, basis, hc0]

theorem onePart_hasDecomposition (d m : Nat) [NeZero m] :
    HasDecomposition [d] m :=
  ⟨onePartDecomposition d m⟩

/-- The one-part base decomposition is `m`-fibered: all `m` vertices form one
block, and the direction used by a colour is independent of the vertex. -/
noncomputable def onePartMFiberedDecomposition (d m : Nat) [NeZero m] :
    MFiberedDecomposition [d] m where
  toDecomposition := onePartDecomposition d m
  Block := Unit
  blockFintype := inferInstance
  blockEquiv := Fintype.equivOfCardEq (by
    simp [Vertex, ZMod.card])
  sameDirectionColors := by
    intro b z z' dir color
    simp [onePartDecomposition]

theorem onePart_hasMFiberedDecomposition (d m : Nat) [NeZero m] :
    HasMFiberedDecomposition [d] m :=
  ⟨onePartMFiberedDecomposition d m⟩

/-- Splitting one part in a fixed list context.  This is the Lean-facing form of
the paper's splitting lemma. -/
def SplittingLemmaGoal : Prop :=
  forall {m : Nat}, Odd m -> 3 <= m ->
    forall (left : List Nat) (a : Nat) (right : List Nat), 2 <= a ->
      HasDecomposition (left ++ [a] ++ right) m ->
        HasDecomposition
          (left ++ [(a + 1) / 2, a / 2] ++ right) m

/-- Strengthened splitting target preserving the replicated `m`-fibered
invariant.  This is the Lean-facing target for the shortcut proof supplied
after the original balancing lemma was refuted. -/
def MFiberedSplittingLemmaGoal : Prop :=
  forall {m : Nat}, Odd m -> 3 <= m ->
    forall (left : List Nat) (a : Nat) (right : List Nat), 2 <= a ->
      HasMFiberedDecomposition (left ++ [a] ++ right) m ->
        HasMFiberedDecomposition
          (left ++ [(a + 1) / 2, a / 2] ++ right) m

/-- Abstract incidence graph used by the balancing lemma.  `Inc x y` is the
type of incidences between `x` and `y`; parallel incidences are represented by
multiple elements of this type. -/
structure IncidenceGraph (X Y : Type) where
  Inc : X -> Y -> Type

/-- Incidences adjacent to a left vertex. -/
abbrev LeftInc {X Y : Type} (B : IncidenceGraph X Y) (x : X) : Type :=
  Sigma fun y : Y => B.Inc x y

/-- Incidences adjacent to a right vertex. -/
abbrev RightInc {X Y : Type} (B : IncidenceGraph X Y) (y : Y) : Type :=
  Sigma fun x : X => B.Inc x y

/-- A selected subfamily of incidences.  The fields record exactly the output
needed by the splitting proof: `c` selected incidences at every left vertex and
unit selected/unselected right degrees modulo `m`. -/
structure IncidenceSelection
    {X Y : Type} [Fintype X] [Fintype Y]
    (B : IncidenceGraph X Y) (c m : Nat) where
  choose : forall x : X, Fin c -> LeftInc B x
  choose_injective : forall x : X, Function.Injective (choose x)
  selectedDegree : Y -> Nat
  unselectedDegree : Y -> Nat
  selectedDegree_coprime : forall y : Y, Nat.Coprime (selectedDegree y) m
  unselectedDegree_coprime : forall y : Y, Nat.Coprime (unselectedDegree y) m

/-- Formal target for the alternating-trail balancing lemma in the proof text.

This statement is intentionally a proof obligation, not an axiom.  The literal
balancing lemma from the proof text is refuted below: a future proof must add
the missing component-level feasibility hypothesis, or replace this target by a
corrected balancing statement. -/
def BalancingLemmaGoal : Prop :=
  forall {m a : Nat}, Odd m -> 2 <= a ->
    forall {X Y : Type} [Fintype X] [Fintype Y],
      forall B : IncidenceGraph X Y,
        forall leftDegree : X -> Nat,
        forall rightDegree : Y -> Nat,
        (forall x : X, leftDegree x = a) ->
        (forall y : Y, 0 < rightDegree y /\ m ∣ rightDegree y) ->
        m ∣ Fintype.card X ->
          Nonempty (IncidenceSelection B (a / 2) m)

/-! ## Replicated balancing targets and local finite-set facts -/

/-- In a block of size `a >= 2`, after reserving two distinct transfer
columns, there are enough remaining columns to fill every row up to
`floor(a/2)`. -/
theorem pairFiller_exists
    {Y : Type} {A : Finset Y} {a : Nat}
    {p q : Y} (ha : A.card = a) (ha2 : 2 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) :
    ∃ F : Finset Y, F ⊆ A ∧ p ∉ F ∧ q ∉ F ∧ F.card = a / 2 - 1 := by
  classical
  let R := (A.erase p).erase q
  have hRsub : R ⊆ A := by
    intro x hx
    dsimp [R] at hx
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
  have hpR : p ∉ R := by
    dsimp [R]
    simp
  have hqR : q ∉ R := by
    dsimp [R]
    simp
  have hcardR : R.card = a - 2 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem hp]
      omega
    · simpa [hpq.symm] using hq
  have hle : a / 2 - 1 <= R.card := by
    rw [hcardR]
    omega
  rcases Finset.exists_subset_card_eq hle with ⟨F, hFsubR, hFcard⟩
  refine ⟨F, ?_, ?_, ?_, hFcard⟩
  · exact hFsubR.trans hRsub
  · intro h
    exact hpR (hFsubR h)
  · intro h
    exact hqR (hFsubR h)

/-- For an active subset `S` of a block `A`, there are enough inactive columns
to fill every row from `floor(|S|/2)` up to `floor(|A|/2)`. -/
theorem subsetFiller_exists
    {Y : Type} [DecidableEq Y] {A S : Finset Y} {a : Nat}
    (ha : A.card = a) (hSsub : S ⊆ A) :
    ∃ F : Finset Y,
      F ⊆ A \ S ∧ F.card = a / 2 - S.card / 2 := by
  classical
  have hsum : (A \ S).card + S.card = a := by
    simpa [ha] using Finset.card_sdiff_add_card_eq_card hSsub
  have hle : a / 2 - S.card / 2 <= (A \ S).card := by
    omega
  exact Finset.exists_subset_card_eq hle

/-- Every active set size at least two is either all pairs or one triple plus
pairs.  This is the arithmetic spine behind the local pair/triple assembly. -/
theorem nat_pair_or_pair_plus_triple {n : Nat} (hn : 2 <= n) :
    (∃ k : Nat, n = 2 * k) ∨ ∃ k : Nat, n = 2 * k + 3 := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · exact Or.inl ⟨k, hk⟩
  · have hkpos : 1 <= k := by omega
    exact Or.inr ⟨k - 1, by omega⟩

/-- Union of a finite list of finite sets.  This lightweight wrapper keeps
the active-set pair/triple cover interface independent of a particular
indexing type. -/
def finsetListUnion {Y : Type} [DecidableEq Y] :
    List (Finset Y) -> Finset Y
  | [] => ∅
  | P :: Ps => P ∪ finsetListUnion Ps

@[simp] theorem finsetListUnion_nil {Y : Type} [DecidableEq Y] :
    finsetListUnion ([] : List (Finset Y)) = ∅ :=
  rfl

@[simp] theorem finsetListUnion_cons {Y : Type} [DecidableEq Y]
    (P : Finset Y) (Ps : List (Finset Y)) :
    finsetListUnion (P :: Ps) = P ∪ finsetListUnion Ps :=
  rfl

@[simp] theorem finsetListUnion_singleton {Y : Type} [DecidableEq Y]
    (P : Finset Y) :
    finsetListUnion [P] = P := by
  simp [finsetListUnion]

/-- A decomposition of an active set into disjoint pieces of size two or
three.  The full local assembly lemma will apply the pair reservoir to
two-pieces and the triple reservoir to three-pieces. -/
structure PairTripleCover {Y : Type} [DecidableEq Y] (S : Finset Y) where
  pieces : List (Finset Y)
  pieces_subset : forall P : Finset Y, P ∈ pieces -> P ⊆ S
  piece_card : forall P : Finset Y, P ∈ pieces -> P.card = 2 ∨ P.card = 3
  pairwise_disjoint : pieces.Pairwise Disjoint
  cover_eq : finsetListUnion pieces = S
  row_card_sum : (pieces.map fun P => P.card / 2).sum = S.card / 2

theorem pairTripleCover_of_card_two
    {Y : Type} [DecidableEq Y] {S : Finset Y} (hS : S.card = 2) :
    Nonempty (PairTripleCover S) := by
  refine ⟨
    { pieces := [S]
      pieces_subset := ?_
      piece_card := ?_
      pairwise_disjoint := ?_
      cover_eq := ?_
      row_card_sum := ?_ }⟩
  · intro P hP
    have hPS : P = S := by
      simpa using hP
    subst P
    exact subset_rfl
  · intro P hP
    have hPS : P = S := by
      simpa using hP
    subst P
    exact Or.inl hS
  · simp
  · simp
  · simp [hS]

theorem pairTripleCover_of_card_three
    {Y : Type} [DecidableEq Y] {S : Finset Y} (hS : S.card = 3) :
    Nonempty (PairTripleCover S) := by
  refine ⟨
    { pieces := [S]
      pieces_subset := ?_
      piece_card := ?_
      pairwise_disjoint := ?_
      cover_eq := ?_
      row_card_sum := ?_ }⟩
  · intro P hP
    have hPS : P = S := by
      simpa using hP
    subst P
    exact subset_rfl
  · intro P hP
    have hPS : P = S := by
      simpa using hP
    subst P
    exact Or.inr hS
  · simp
  · simp
  · simp [hS]

/-- Add one disjoint pair/triple piece to an existing cover.  This is the
inductive constructor used by the arbitrary active-set cover proof. -/
def PairTripleCover.cons
    {Y : Type} [DecidableEq Y] {P S : Finset Y}
    (C : PairTripleCover S) (hPS : Disjoint P S)
    (hPcard : P.card = 2 ∨ P.card = 3)
    (hRow : P.card / 2 + S.card / 2 = (P ∪ S).card / 2) :
    PairTripleCover (P ∪ S) where
  pieces := P :: C.pieces
  pieces_subset := by
    intro Q hQ x hx
    rw [List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact Finset.mem_union.mpr (Or.inl hx)
    · exact Finset.mem_union.mpr (Or.inr (C.pieces_subset Q hQ hx))
  piece_card := by
    intro Q hQ
    rw [List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact hPcard
    · exact C.piece_card Q hQ
  pairwise_disjoint := by
    rw [List.pairwise_cons]
    exact ⟨fun Q hQ => hPS.mono_right (C.pieces_subset Q hQ),
      C.pairwise_disjoint⟩
  cover_eq := by
    simp [C.cover_eq, finsetListUnion]
  row_card_sum := by
    simp [C.row_card_sum, hRow]

theorem pairTripleCover_exists
    {Y : Type} [DecidableEq Y] {S : Finset Y} (hS : 2 <= S.card) :
    Nonempty (PairTripleCover S) := by
  classical
  have H :
      forall n : Nat, forall T : Finset Y, T.card = n -> 2 <= n ->
        Nonempty (PairTripleCover T) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTcard hn2
      by_cases hn_two : n = 2
      · rw [hn_two] at hTcard
        exact pairTripleCover_of_card_two hTcard
      by_cases hn_three : n = 3
      · rw [hn_three] at hTcard
        exact pairTripleCover_of_card_three hTcard
      have hn4 : 4 <= n := by omega
      rcases Finset.exists_subset_card_eq (s := T) (n := 2) (by omega) with
        ⟨P, hPsub, hPcard⟩
      let R : Finset Y := T \ P
      have hRcard : R.card = n - 2 := by
        dsimp [R]
        rw [Finset.card_sdiff_of_subset hPsub, hTcard, hPcard]
      have hRge : 2 <= R.card := by
        rw [hRcard]
        omega
      have hRlt : R.card < n := by
        rw [hRcard]
        omega
      rcases ih R.card hRlt R rfl hRge with ⟨CR⟩
      have hPR : Disjoint P R := by
        dsimp [R]
        exact disjoint_sdiff_self_right
      have hCover : PairTripleCover (P ∪ R) :=
        PairTripleCover.cons CR hPR (Or.inl hPcard) (by
          have hUnionCard : (P ∪ R).card = P.card + R.card :=
            Finset.card_union_of_disjoint hPR
          rw [hPcard] at hUnionCard
          rw [hUnionCard]
          omega)
      have hUnion : P ∪ R = T := by
        dsimp [R]
        exact Finset.union_sdiff_of_subset hPsub
      exact ⟨hUnion ▸ hCover⟩
  exact H S.card S rfl hS

/-- Pair-transfer row choice: for `u` rows select `q`, and for the remaining
rows select `p`, always with the same filler `F`. -/
noncomputable def pairTransferChoice {Y : Type} [DecidableEq Y]
    (p q : Y) (F : Finset Y) (u : Nat) {m : Nat} : Fin m -> Finset Y :=
  fun z => if z.val < u then insert q F else insert p F

theorem pairTransferChoice_subset {Y : Type} [DecidableEq Y]
    {A F : Finset Y} {p q : Y} {u m : Nat}
    (hFsub : F ⊆ A) (hp : p ∈ A) (hq : q ∈ A) :
    forall z : Fin m, pairTransferChoice p q F u z ⊆ A := by
  intro z x hx
  dsimp [pairTransferChoice] at hx
  split at hx
  · rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hq
    · exact hFsub hx
  · rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hp
    · exact hFsub hx

theorem pairTransferChoice_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {a u m : Nat}
    (ha2 : 2 <= a) (hpF : p ∉ F) (hqF : q ∉ F)
    (hFcard : F.card = a / 2 - 1) :
    forall z : Fin m, (pairTransferChoice p q F u z).card = a / 2 := by
  intro z
  dsimp [pairTransferChoice]
  split
  · rw [Finset.card_insert_of_notMem hqF, hFcard]
    omega
  · rw [Finset.card_insert_of_notMem hpF, hFcard]
    omega

/-- The rows `z : Fin m` with `z.val < u` are canonically equivalent to
`Fin u` when `u <= m`. -/
noncomputable def finValLtEquiv (m u : Nat) (hu : u <= m) :
    {z : Fin m // z.val < u} ≃ Fin u where
  toFun z := ⟨z.1.val, z.2⟩
  invFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hu⟩, i.isLt⟩
  left_inv := by
    intro z
    cases z with
    | mk z hz =>
      cases z with
      | mk val isLt =>
        rfl
  right_inv := by
    intro i
    cases i
    rfl

theorem fintype_card_fin_val_lt (m u : Nat) (hu : u <= m) :
    Fintype.card {z : Fin m // z.val < u} = u := by
  classical
  simpa using Fintype.card_congr (finValLtEquiv m u hu)

theorem q_mem_pairTransferChoice_iff {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hpq : p ≠ q) (hqF : q ∉ F) (z : Fin m) :
    q ∈ pairTransferChoice p q F u z ↔ z.val < u := by
  dsimp [pairTransferChoice]
  by_cases hz : z.val < u
  · simp [hz]
  · simp [hz, hqF, hpq.symm]

theorem p_mem_pairTransferChoice_iff {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hpq : p ≠ q) (hpF : p ∉ F) (z : Fin m) :
    p ∈ pairTransferChoice p q F u z ↔ ¬ z.val < u := by
  dsimp [pairTransferChoice]
  by_cases hz : z.val < u
  · simp [hz, hpF, hpq]
  · simp [hz]

/-- Transport between subtypes defined by pointwise equivalent predicates. -/
noncomputable def subtypeEquivOfIff {α : Type} {P Q : α -> Prop}
    (h : forall x, P x <-> Q x) : {x : α // P x} ≃ {x : α // Q x} where
  toFun x := ⟨x.1, (h x.1).mp x.2⟩
  invFun x := ⟨x.1, (h x.1).mpr x.2⟩
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

/-- Trivial equivalence for an always-true subtype. -/
noncomputable def subtypeTrueEquiv (α : Type) :
    {_x : α // True} ≃ α where
  toFun x := x.1
  invFun x := ⟨x, trivial⟩
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

theorem fintype_card_subtype_true (α : Type) [Fintype α] :
    Fintype.card {_x : α // True} = Fintype.card α := by
  classical
  exact Fintype.card_congr (subtypeTrueEquiv α)

/-- Trivial equivalence for an impossible subtype. -/
noncomputable def subtypeFalseEquiv (α : Type) :
    {_x : α // False} ≃ PEmpty where
  toFun x := False.elim x.2
  invFun x := PEmpty.elim x
  left_inv := by
    intro x
    exact False.elim x.2
  right_inv := by
    intro x
    exact PEmpty.elim x

theorem fintype_card_subtype_false (α : Type) [Fintype α] :
    Fintype.card {_x : α // False} = 0 := by
  classical
  simp

theorem pairTransferChoice_q_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hu : u <= m) (hpq : p ≠ q) (hqF : q ∉ F) :
    Fintype.card {z : Fin m // q ∈ pairTransferChoice p q F u z} = u := by
  classical
  calc
    Fintype.card {z : Fin m // q ∈ pairTransferChoice p q F u z}
        = Fintype.card {z : Fin m // z.val < u} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff
              (fun z => q_mem_pairTransferChoice_iff hpq hqF z))
    _ = u := fintype_card_fin_val_lt m u hu

/-- The rows `z : Fin m` with `u <= z.val` are canonically equivalent to
`Fin (m-u)` when `u <= m`. -/
noncomputable def finValGeEquiv (m u : Nat) (hu : u <= m) :
    {z : Fin m // u <= z.val} ≃ Fin (m - u) where
  toFun z := ⟨z.1.val - u, by
    have hzlt : z.1.val < m := z.1.isLt
    have hzge : u <= z.1.val := z.2
    omega⟩
  invFun i := ⟨⟨u + i.val, by
    have hi : i.val < m - u := i.isLt
    omega⟩, by simp⟩
  left_inv := by
    intro z
    cases z with
    | mk z hzge =>
      cases z with
      | mk val isLt =>
        apply Subtype.ext
        apply Fin.ext
        have hzgeNat : u <= val := by simpa using hzge
        exact Nat.add_sub_of_le hzgeNat
  right_inv := by
    intro i
    cases i with
    | mk val isLt =>
      apply Fin.ext
      exact Nat.add_sub_cancel_left u val

theorem fintype_card_fin_val_ge (m u : Nat) (hu : u <= m) :
    Fintype.card {z : Fin m // u <= z.val} = m - u := by
  classical
  simpa using Fintype.card_congr (finValGeEquiv m u hu)

theorem pairTransferChoice_p_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hu : u <= m) (hpq : p ≠ q) (hpF : p ∉ F) :
    Fintype.card {z : Fin m // p ∈ pairTransferChoice p q F u z} = m - u := by
  classical
  calc
    Fintype.card {z : Fin m // p ∈ pairTransferChoice p q F u z}
        = Fintype.card {z : Fin m // u <= z.val} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff (fun z => by
              rw [p_mem_pairTransferChoice_iff hpq hpF z]
              omega))
    _ = m - u := fintype_card_fin_val_ge m u hu

theorem coprime_m_sub_of_coprime {u m : Nat} (hu : u <= m)
    (hcop : Nat.Coprime u m) : Nat.Coprime (m - u) m :=
  (Nat.coprime_self_sub_left hu).2 hcop

theorem pairTransferChoice_q_coprime {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hu : u <= m) (hpq : p ≠ q) (hqF : q ∉ F)
    (hcop : Nat.Coprime u m) :
    Nat.Coprime
      (Fintype.card {z : Fin m // q ∈ pairTransferChoice p q F u z}) m := by
  rw [pairTransferChoice_q_card hu hpq hqF]
  exact hcop

theorem pairTransferChoice_p_coprime {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q : Y} {u m : Nat}
    (hu : u <= m) (hpq : p ≠ q) (hpF : p ∉ F)
    (hcop : Nat.Coprime u m) :
    Nat.Coprime
      (Fintype.card {z : Fin m // p ∈ pairTransferChoice p q F u z}) m := by
  rw [pairTransferChoice_p_card hu hpq hpF]
  exact coprime_m_sub_of_coprime hu hcop

theorem pairTransferChoice_inactive_dvd {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q y : Y} {u m : Nat}
    (hyp : y ≠ p) (hyq : y ≠ q) :
    m ∣ Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z} := by
  classical
  by_cases hyF : y ∈ F
  · have hcard :
        Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z} = m := by
      calc
        Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z}
            = Fintype.card {z : Fin m // True} := by
              exact Fintype.card_congr
                (subtypeEquivOfIff (fun z => by
                  dsimp [pairTransferChoice]
                  by_cases hz : z.val < u <;> simp [hz, hyF]))
        _ = m := by
          rw [fintype_card_subtype_true]
          simp
    rw [hcard]
  · have hcard :
        Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z} = 0 := by
      calc
        Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z}
            = Fintype.card {z : Fin m // False} := by
              exact Fintype.card_congr
                (subtypeEquivOfIff (fun z => by
                  dsimp [pairTransferChoice]
                  by_cases hz : z.val < u <;> simp [hz, hyF, hyp, hyq]))
        _ = 0 := fintype_card_subtype_false (Fin m)
    rw [hcard]
    exact dvd_zero m

/-- In a block of size `a >= 3`, after reserving three distinct transfer
columns, there are enough remaining columns to fill every row up to
`floor(a/2)`. -/
theorem tripleFiller_exists
    {Y : Type} {A : Finset Y} {a : Nat}
    {p q r : Y} (ha : A.card = a) (ha3 : 3 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ F : Finset Y,
      F ⊆ A ∧ p ∉ F ∧ q ∉ F ∧ r ∉ F ∧ F.card = a / 2 - 1 := by
  classical
  let R := ((A.erase p).erase q).erase r
  have hRsub : R ⊆ A := by
    intro x hx
    dsimp [R] at hx
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2).2
  have hpR : p ∉ R := by
    dsimp [R]
    simp
  have hqR : q ∉ R := by
    dsimp [R]
    simp
  have hrR : r ∉ R := by
    dsimp [R]
    simp
  have hqAp : q ∈ A.erase p := by
    simp [hq, hpq.symm]
  have hrApq : r ∈ (A.erase p).erase q := by
    simp [hr, hpr.symm, hqr.symm]
  have hcardR : R.card = a - 3 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hrApq]
    rw [Finset.card_erase_of_mem hqAp]
    rw [Finset.card_erase_of_mem hp]
    omega
  have hle : a / 2 - 1 <= R.card := by
    rw [hcardR]
    omega
  rcases Finset.exists_subset_card_eq hle with ⟨F, hFsubR, hFcard⟩
  refine ⟨F, ?_, ?_, ?_, ?_, hFcard⟩
  · exact hFsubR.trans hRsub
  · intro h
    exact hpR (hFsubR h)
  · intro h
    exact hqR (hFsubR h)
  · intro h
    exact hrR (hFsubR h)

/-- Triple-transfer row choice: row `0` selects `p`, row `1` selects `q`, and
all remaining rows select `r`, always with the same filler `F`. -/
noncomputable def tripleTransferChoice {Y : Type} [DecidableEq Y]
    (p q r : Y) (F : Finset Y) {m : Nat} : Fin m -> Finset Y :=
  fun z =>
    if z.val = 0 then insert p F
    else if z.val = 1 then insert q F
    else insert r F

theorem tripleTransferChoice_subset {Y : Type} [DecidableEq Y]
    {A F : Finset Y} {p q r : Y} {m : Nat}
    (hFsub : F ⊆ A) (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) :
    forall z : Fin m, tripleTransferChoice p q r F z ⊆ A := by
  intro z x hx
  dsimp [tripleTransferChoice] at hx
  split at hx
  · rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hp
    · exact hFsub hx
  · split at hx
    · rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hq
      · exact hFsub hx
    · rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hr
      · exact hFsub hx

theorem tripleTransferChoice_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {a m : Nat}
    (ha3 : 3 <= a) (hpF : p ∉ F) (hqF : q ∉ F) (hrF : r ∉ F)
    (hFcard : F.card = a / 2 - 1) :
    forall z : Fin m, (tripleTransferChoice p q r F z).card = a / 2 := by
  intro z
  dsimp [tripleTransferChoice]
  split
  · rw [Finset.card_insert_of_notMem hpF, hFcard]
    omega
  · split
    · rw [Finset.card_insert_of_notMem hqF, hFcard]
      omega
    · rw [Finset.card_insert_of_notMem hrF, hFcard]
      omega

/-- The only row with value `0`. -/
noncomputable def finValEqZeroEquiv (m : Nat) (hmpos : 0 < m) :
    {z : Fin m // z.val = 0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨0, hmpos⟩, rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Fin.ext
    exact z.2.symm
  right_inv := by
    intro u
    cases u
    rfl

theorem fintype_card_fin_val_eq_zero (m : Nat) (hmpos : 0 < m) :
    Fintype.card {z : Fin m // z.val = 0} = 1 := by
  classical
  simpa using Fintype.card_congr (finValEqZeroEquiv m hmpos)

/-- The only row with value `1`. -/
noncomputable def finValEqOneEquiv (m : Nat) (hm2 : 1 < m) :
    {z : Fin m // z.val = 1} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨1, hm2⟩, rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Fin.ext
    exact z.2.symm
  right_inv := by
    intro u
    cases u
    rfl

theorem fintype_card_fin_val_eq_one (m : Nat) (hm2 : 1 < m) :
    Fintype.card {z : Fin m // z.val = 1} = 1 := by
  classical
  simpa using Fintype.card_congr (finValEqOneEquiv m hm2)

theorem p_mem_tripleTransferChoice_iff {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpF : p ∉ F) (z : Fin m) :
    p ∈ tripleTransferChoice p q r F z ↔ z.val = 0 := by
  dsimp [tripleTransferChoice]
  by_cases h0 : z.val = 0
  · simp [h0]
  · by_cases h1 : z.val = 1
    · simp [h1, hpq, hpF]
    · simp [h0, h1, hpr, hpF]

theorem q_mem_tripleTransferChoice_iff {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hpq : p ≠ q) (hqr : q ≠ r) (hqF : q ∉ F) (z : Fin m) :
    q ∈ tripleTransferChoice p q r F z ↔ z.val = 1 := by
  dsimp [tripleTransferChoice]
  by_cases h0 : z.val = 0
  · simp [h0, hpq.symm, hqF]
  · by_cases h1 : z.val = 1
    · simp [h1]
    · simp [h0, h1, hqr, hqF]

theorem r_mem_tripleTransferChoice_iff {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hpr : p ≠ r) (hqr : q ≠ r) (hrF : r ∉ F) (z : Fin m) :
    r ∈ tripleTransferChoice p q r F z ↔ 2 <= z.val := by
  dsimp [tripleTransferChoice]
  by_cases h0 : z.val = 0
  · simp [h0, hpr.symm, hrF]
  · by_cases h1 : z.val = 1
    · simp [h1, hqr.symm, hrF]
    · have hge : 2 <= z.val := by omega
      simp [h0, h1, hge]

theorem tripleTransferChoice_p_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hmpos : 0 < m) (hpq : p ≠ q) (hpr : p ≠ r) (hpF : p ∉ F) :
    Fintype.card {z : Fin m // p ∈ tripleTransferChoice p q r F z} = 1 := by
  classical
  calc
    Fintype.card {z : Fin m // p ∈ tripleTransferChoice p q r F z}
        = Fintype.card {z : Fin m // z.val = 0} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff
              (fun z => p_mem_tripleTransferChoice_iff hpq hpr hpF z))
    _ = 1 := fintype_card_fin_val_eq_zero m hmpos

theorem tripleTransferChoice_q_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hm2 : 1 < m) (hpq : p ≠ q) (hqr : q ≠ r) (hqF : q ∉ F) :
    Fintype.card {z : Fin m // q ∈ tripleTransferChoice p q r F z} = 1 := by
  classical
  calc
    Fintype.card {z : Fin m // q ∈ tripleTransferChoice p q r F z}
        = Fintype.card {z : Fin m // z.val = 1} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff
              (fun z => q_mem_tripleTransferChoice_iff hpq hqr hqF z))
    _ = 1 := fintype_card_fin_val_eq_one m hm2

theorem tripleTransferChoice_r_card {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hm2 : 2 <= m) (hpr : p ≠ r) (hqr : q ≠ r) (hrF : r ∉ F) :
    Fintype.card {z : Fin m // r ∈ tripleTransferChoice p q r F z} =
      m - 2 := by
  classical
  calc
    Fintype.card {z : Fin m // r ∈ tripleTransferChoice p q r F z}
        = Fintype.card {z : Fin m // 2 <= z.val} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff
              (fun z => r_mem_tripleTransferChoice_iff hpr hqr hrF z))
    _ = m - 2 := fintype_card_fin_val_ge m 2 hm2

theorem coprime_m_sub_two_of_odd {m : Nat} (hmOdd : Odd m) (hm2 : 2 <= m) :
    Nat.Coprime (m - 2) m := by
  have hcop2 : Nat.Coprime 2 m := by
    exact Nat.coprime_two_left.mpr hmOdd
  exact (Nat.coprime_self_sub_left hm2).2 hcop2

theorem tripleTransferChoice_r_coprime {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r : Y} {m : Nat}
    (hmOdd : Odd m) (hm2 : 2 <= m)
    (hpr : p ≠ r) (hqr : q ≠ r) (hrF : r ∉ F) :
    Nat.Coprime
      (Fintype.card {z : Fin m // r ∈ tripleTransferChoice p q r F z}) m := by
  rw [tripleTransferChoice_r_card hm2 hpr hqr hrF]
  exact coprime_m_sub_two_of_odd hmOdd hm2

theorem tripleTransferChoice_inactive_dvd {Y : Type} [DecidableEq Y]
    {F : Finset Y} {p q r y : Y} {m : Nat}
    (hyp : y ≠ p) (hyq : y ≠ q) (hyr : y ≠ r) :
    m ∣ Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z} := by
  classical
  by_cases hyF : y ∈ F
  · have hcard :
        Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z} = m := by
      calc
        Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z}
            = Fintype.card {z : Fin m // True} := by
              exact Fintype.card_congr
                (subtypeEquivOfIff (fun z => by
                  dsimp [tripleTransferChoice]
                  by_cases h0 : z.val = 0
                  · simp [h0, hyF]
                  · by_cases h1 : z.val = 1 <;> simp [h0, h1, hyF]))
        _ = m := by
          rw [fintype_card_subtype_true]
          simp
    rw [hcard]
  · have hcard :
        Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z} = 0 := by
      calc
        Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z}
            = Fintype.card {z : Fin m // False} := by
              exact Fintype.card_congr
                (subtypeEquivOfIff (fun z => by
                  dsimp [tripleTransferChoice]
                  by_cases h0 : z.val = 0
                  · simp [h0, hyF, hyp]
                  · by_cases h1 : z.val = 1
                    · simp [h1, hyF, hyq]
                    · simp [h0, h1, hyF, hyr]))
        _ = 0 := fintype_card_subtype_false (Fin m)
    rw [hcard]
    exact dvd_zero m

/-- A local replicated block choice: in every one of the `m` rows, choose
exactly `c` columns from the same neighbour set `A`. -/
structure ReplicatedBlockChoice
    {Y : Type} [DecidableEq Y] (A : Finset Y) (c m : Nat) where
  choose : Fin m -> Finset Y
  choose_subset : forall z, choose z ⊆ A
  choose_card : forall z, (choose z).card = c

/-- The column degree produced by one replicated block choice. -/
def replicatedBlockColumnDegree
    {Y : Type} [DecidableEq Y] {A : Finset Y} {c m : Nat}
    (C : ReplicatedBlockChoice A c m) (y : Y) : Nat :=
  Fintype.card {z : Fin m // y ∈ C.choose z}

theorem replicatedBlockColumnDegree_eq_zero_of_not_mem
    {Y : Type} [DecidableEq Y] {A : Finset Y} {c m : Nat}
    (C : ReplicatedBlockChoice A c m) {y : Y} (hyA : y ∉ A) :
    replicatedBlockColumnDegree C y = 0 := by
  classical
  change Fintype.card {z : Fin m // y ∈ C.choose z} = 0
  calc
    Fintype.card {z : Fin m // y ∈ C.choose z}
        = Fintype.card {z : Fin m // False} := by
          exact Fintype.card_congr
            (subtypeEquivOfIff (fun z => by
              have hyNot : y ∉ C.choose z := by
                intro hy
                exact hyA (C.choose_subset z hy)
              simp [hyNot]))
    _ = 0 := fintype_card_subtype_false (Fin m)

/-- A local residue pattern for one replicated block: active columns receive
unit selected degree modulo `m`, while inactive columns in the block receive
degree divisible by `m`. -/
structure ReplicatedBlockResiduePattern
    {Y : Type} [DecidableEq Y] (A S : Finset Y) (c m : Nat) where
  toChoice : ReplicatedBlockChoice A c m
  active_coprime :
    forall y : Y, y ∈ S -> Nat.Coprime (replicatedBlockColumnDegree toChoice y) m
  inactive_dvd :
    forall y : Y, y ∈ A -> y ∉ S -> m ∣ replicatedBlockColumnDegree toChoice y

theorem replicatedBlockResiduePattern_active_isUnit
    {Y : Type} [DecidableEq Y] {A S : Finset Y} {c m : Nat}
    (P : ReplicatedBlockResiduePattern A S c m)
    {y : Y} (hy : y ∈ S) :
    IsUnit ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) := by
  exact
    (ZMod.isUnit_iff_coprime (replicatedBlockColumnDegree P.toChoice y) m).mpr
      (P.active_coprime y hy)

theorem replicatedBlockResiduePattern_inactive_zmod_eq_zero
    {Y : Type} [DecidableEq Y] {A S : Finset Y} {c m : Nat}
    (P : ReplicatedBlockResiduePattern A S c m)
    {y : Y} (hyA : y ∈ A) (hyS : y ∉ S) :
    ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) = 0 := by
  exact
    (ZMod.natCast_eq_zero_iff
      (replicatedBlockColumnDegree P.toChoice y) m).mpr
      (P.inactive_dvd y hyA hyS)

theorem replicatedBlockResiduePattern_zmod_eq_if_active
    {Y : Type} [DecidableEq Y] {A S : Finset Y} {c m : Nat}
    (P : ReplicatedBlockResiduePattern A S c m)
    (y : Y) :
    ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) =
      if y ∈ S then
        ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m)
      else 0 := by
  classical
  by_cases hyS : y ∈ S
  · simp [hyS]
  · simp [hyS]
    by_cases hyA : y ∈ A
    · exact replicatedBlockResiduePattern_inactive_zmod_eq_zero P hyA hyS
    · rw [replicatedBlockColumnDegree_eq_zero_of_not_mem P.toChoice hyA]
      simp

theorem replicatedBlockResiduePattern_sum_zmod_eq_active_sum
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A S : Block -> Finset Y} {c m : Nat}
    (P : forall α : Block, ReplicatedBlockResiduePattern (A α) (S α) c m)
    (y : Y) :
    ((∑ α : Block, replicatedBlockColumnDegree (P α).toChoice y : Nat) : ZMod m) =
      ∑ α : Block,
        if y ∈ S α then
          ((replicatedBlockColumnDegree (P α).toChoice y : Nat) : ZMod m)
        else 0 := by
  classical
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro α _hα
  exact replicatedBlockResiduePattern_zmod_eq_if_active (P α) y

/-- Vertices of the finite incidence graph of a replicated hypergraph. -/
abbrev IncidenceVertex (Y Block : Type) : Type :=
  Sum Y Block

/-- The simple bipartite incidence graph associated to `A : Block -> Finset Y`. -/
def replicatedIncidenceGraph
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y) :
    SimpleGraph (IncidenceVertex Y Block) where
  Adj u v :=
    match u, v with
    | Sum.inl y, Sum.inr α => y ∈ A α
    | Sum.inr α, Sum.inl y => y ∈ A α
    | _, _ => False
  symm := by
    rintro (_ | _) (_ | _) h <;> simp_all
  loopless := ⟨by
    rintro (_ | _) <;> simp⟩

@[simp]
theorem replicatedIncidenceGraph_adj_left_right
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y)
    (y : Y) (α : Block) :
    (replicatedIncidenceGraph A).Adj
      (Sum.inl y : IncidenceVertex Y Block) (Sum.inr α) ↔
      y ∈ A α :=
  Iff.rfl

@[simp]
theorem replicatedIncidenceGraph_adj_right_left
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y)
    (α : Block) (y : Y) :
    (replicatedIncidenceGraph A).Adj
      (Sum.inr α : IncidenceVertex Y Block) (Sum.inl y) ↔
      y ∈ A α :=
  Iff.rfl

theorem replicatedIncidenceGraph_y_has_neighbor
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α) (y : Y) :
    ∃ v : IncidenceVertex Y Block,
      (replicatedIncidenceGraph A).Adj (Sum.inl y) v := by
  rcases hNoIso y with ⟨α, hyα⟩
  exact ⟨Sum.inr α, by simpa using hyα⟩

theorem replicatedIncidenceGraph_block_has_two_neighbors
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    (α : Block) :
    ∃ y z : Y, y ≠ z ∧
      (replicatedIncidenceGraph A).Adj (Sum.inr α) (Sum.inl y) ∧
      (replicatedIncidenceGraph A).Adj (Sum.inr α) (Sum.inl z) := by
  classical
  have hcard2 : 2 <= (A α).card := by
    rw [hA α]
    exact ha2
  have hpos : 0 < (A α).card := by omega
  rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
  have herasePos : 0 < ((A α).erase y).card := by
    rw [Finset.card_erase_of_mem hy]
    omega
  rcases Finset.card_pos.mp herasePos with ⟨z, hzErase⟩
  rcases Finset.mem_erase.mp hzErase with ⟨hzy, hz⟩
  refine ⟨y, z, ?_, ?_, ?_⟩
  · exact fun hyz => hzy hyz.symm
  · simpa using hy
  · simpa using hz

theorem replicatedIncidenceGraph_reachable_y_rep
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    (v : IncidenceVertex Y Block) :
    ∃ y : Y, (replicatedIncidenceGraph A).Reachable v (Sum.inl y) := by
  classical
  cases v with
  | inl y =>
      exact ⟨y, ⟨SimpleGraph.Walk.nil⟩⟩
  | inr α =>
      rcases replicatedIncidenceGraph_block_has_two_neighbors hA ha2 α with
        ⟨y, _z, _hyz, hyAdj, _hzAdj⟩
      exact ⟨y, hyAdj.reachable⟩

theorem replicatedIncidenceComponent_has_y
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent) :
    ∃ y : Y, (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp := by
  classical
  rcases C.exists_rep with ⟨v, hv⟩
  rcases replicatedIncidenceGraph_reachable_y_rep hA ha2 v with ⟨y, hvy⟩
  refine ⟨y, ?_⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [← hv]
  exact SimpleGraph.ConnectedComponent.sound hvy.symm

theorem replicatedIncidenceComponent_exists_isTree_le
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    (C : (replicatedIncidenceGraph A).ConnectedComponent) :
    ∃ T : SimpleGraph C, T ≤ C.toSimpleGraph ∧ T.IsTree :=
  C.connected_toSimpleGraph.exists_isTree_le

theorem replicatedIncidenceTree_adj_val
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {u v : C} (hAdj : T.Adj u v) :
    (replicatedIncidenceGraph A).Adj u.1 v.1 := by
  exact (C.toSimpleGraph_adj u.2 v.2).mp (hTle hAdj)

theorem replicatedIncidenceTree_not_adj_left_left
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {y z : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hz : (Sum.inl z : IncidenceVertex Y Block) ∈ C.supp} :
    ¬ T.Adj ⟨Sum.inl y, hy⟩ ⟨Sum.inl z, hz⟩ := by
  intro hAdj
  have hG := replicatedIncidenceTree_adj_val hTle hAdj
  simp [replicatedIncidenceGraph] at hG

theorem replicatedIncidenceTree_not_adj_right_right
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {α β : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {hβ : (Sum.inr β : IncidenceVertex Y Block) ∈ C.supp} :
    ¬ T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inr β, hβ⟩ := by
  intro hAdj
  have hG := replicatedIncidenceTree_adj_val hTle hAdj
  simp [replicatedIncidenceGraph] at hG

theorem replicatedIncidenceTree_adj_right_eq_left
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {v : C} (hAdj : T.Adj ⟨Sum.inr α, hα⟩ v) :
    ∃ y : Y, v.1 = Sum.inl y ∧ y ∈ A α := by
  have hG := replicatedIncidenceTree_adj_val hTle hAdj
  cases hv : v.1 with
  | inl y =>
      refine ⟨y, rfl, ?_⟩
      simpa [replicatedIncidenceGraph, hv] using hG
  | inr β =>
      simp [replicatedIncidenceGraph, hv] at hG

theorem replicatedIncidenceTree_adj_left_eq_right
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {v : C} (hAdj : T.Adj ⟨Sum.inl y, hy⟩ v) :
    ∃ α : Block, v.1 = Sum.inr α ∧ y ∈ A α := by
  have hG := replicatedIncidenceTree_adj_val hTle hAdj
  cases hv : v.1 with
  | inl z =>
      simp [replicatedIncidenceGraph, hv] at hG
  | inr α =>
      refine ⟨α, rfl, ?_⟩
      simpa [replicatedIncidenceGraph, hv] using hG

theorem replicatedIncidenceComponent_block_has_two_y_neighbors
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent)
    {α : Block} (hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp) :
    ∃ y z : Y, y ≠ z ∧
      (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp ∧
      (Sum.inl z : IncidenceVertex Y Block) ∈ C.supp ∧
      (replicatedIncidenceGraph A).Adj (Sum.inr α) (Sum.inl y) ∧
      (replicatedIncidenceGraph A).Adj (Sum.inr α) (Sum.inl z) := by
  classical
  rcases replicatedIncidenceGraph_block_has_two_neighbors hA ha2 α with
    ⟨y, z, hyz, hyAdj, hzAdj⟩
  refine ⟨y, z, hyz, ?_, ?_, hyAdj, hzAdj⟩
  · exact C.mem_supp_of_adj_mem_supp hα hyAdj
  · exact C.mem_supp_of_adj_mem_supp hα hzAdj

theorem replicatedIncidenceComponent_y_has_block_neighbor
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α)
    (C : (replicatedIncidenceGraph A).ConnectedComponent)
    {y : Y} (hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp) :
    ∃ α : Block,
      (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp ∧
      (replicatedIncidenceGraph A).Adj (Sum.inl y) (Sum.inr α) := by
  rcases hNoIso y with ⟨α, hyα⟩
  have hadj :
      (replicatedIncidenceGraph A).Adj
        (Sum.inl y : IncidenceVertex Y Block) (Sum.inr α) := by
    simpa using hyα
  exact ⟨α, C.mem_supp_of_adj_mem_supp hy hadj, hadj⟩

theorem replicatedIncidenceComponent_has_other_y
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a)
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent)
    {ρ : Y} (hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp) :
    ∃ y : Y, y ≠ ρ ∧
      (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp := by
  rcases replicatedIncidenceComponent_y_has_block_neighbor hNoIso C hρ with
    ⟨α, hα, _hAdj⟩
  rcases replicatedIncidenceComponent_block_has_two_y_neighbors hA ha2 C hα with
    ⟨y, z, hyz, hyC, hzC, _hyAdj, _hzAdj⟩
  by_cases hyρ : y = ρ
  · refine ⟨z, ?_, hzC⟩
    intro hzρ
    exact hyz (by rw [hyρ, hzρ])
  · exact ⟨y, hyρ, hyC⟩

/-- A rooted parent relation: `parent` is adjacent to `child` and is exactly
one step closer to `root`. -/
def IsRootParent {V : Type} (G : SimpleGraph V) (root parent child : V) : Prop :=
  G.Adj child parent ∧ G.dist root parent + 1 = G.dist root child

theorem isRootParent_root_of_adj
    {V : Type} {G : SimpleGraph V} {root child : V}
    (hAdj : G.Adj root child) :
    IsRootParent G root root child := by
  refine ⟨hAdj.symm, ?_⟩
  rw [SimpleGraph.dist_self]
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hAdj]

theorem connected_exists_rootParent
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    {root child : V} (hchild : child ≠ root) :
    ∃ parent : V, IsRootParent G root parent child := by
  classical
  have hreach : G.Reachable child root := hconn child root
  rcases hreach.exists_walk_length_eq_dist with ⟨p, hp⟩
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hchild p with
    ⟨parent, hAdj, p', hpEq⟩
  subst p
  have hdistPath : p'.length + 1 = G.dist root child := by
    rw [SimpleGraph.dist_comm]
    simpa using hp
  have hleParent : G.dist root parent <= p'.length := by
    have h := SimpleGraph.dist_le p'.reverse
    simpa [SimpleGraph.Walk.length_reverse, SimpleGraph.dist_comm] using h
  have hleChild : G.dist root child <= G.dist root parent + 1 := by
    have htri := hAdj.symm.reachable.dist_triangle_right root
    have hdist : G.dist parent child = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hAdj.symm
    simpa [hdist] using htri
  refine ⟨parent, hAdj, ?_⟩
  omega

noncomputable def rootParent
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (child : {v : V // v ≠ root}) : V :=
  Classical.choose (connected_exists_rootParent hconn child.2)

theorem rootParent_spec
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (child : {v : V // v ≠ root}) :
    IsRootParent G root (rootParent hconn root child) child.1 :=
  Classical.choose_spec (connected_exists_rootParent hconn child.2)

theorem rootParent_adj
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (child : {v : V // v ≠ root}) :
    G.Adj child.1 (rootParent hconn root child) :=
  (rootParent_spec hconn root child).1

theorem rootParent_dist_add_one
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (child : {v : V // v ≠ root}) :
    G.dist root (rootParent hconn root child) + 1 =
      G.dist root child.1 :=
  (rootParent_spec hconn root child).2

theorem rootParent_dist_lt
    {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (child : {v : V // v ≠ root}) :
    G.dist root (rootParent hconn root child) < G.dist root child.1 := by
  have h := rootParent_dist_add_one hconn root child
  omega

theorem isRootParent_unique
    {V : Type} {G : SimpleGraph V} (hTree : G.IsTree)
    {root parent₁ parent₂ child : V}
    (h₁ : IsRootParent G root parent₁ child)
    (h₂ : IsRootParent G root parent₂ child) :
    parent₁ = parent₂ := by
  classical
  rcases hTree.connected.exists_path_of_dist root parent₁ with
    ⟨p₁, _hp₁Path, hp₁Len⟩
  rcases hTree.connected.exists_path_of_dist root parent₂ with
    ⟨p₂, _hp₂Path, hp₂Len⟩
  have hP₁ :
      (p₁.concat h₁.1.symm).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [SimpleGraph.Walk.length_concat, hp₁Len]
    exact h₁.2
  have hP₂ :
      (p₂.concat h₂.1.symm).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [SimpleGraph.Walk.length_concat, hp₂Len]
    exact h₂.2
  have hWalkEq : p₁.concat h₁.1.symm = p₂.concat h₂.1.symm :=
    (hTree.existsUnique_path root child).unique hP₁ hP₂
  rcases SimpleGraph.Walk.concat_inj hWalkEq with ⟨hEq, _hPathEq⟩
  exact hEq

theorem rootParent_eq_of_isRootParent
    {V : Type} {G : SimpleGraph V} (hTree : G.IsTree)
    (root : V) (child : {v : V // v ≠ root}) {parent : V}
    (hParent : IsRootParent G root parent child.1) :
    rootParent hTree.connected root child = parent :=
  isRootParent_unique hTree
    (rootParent_spec hTree.connected root child) hParent

theorem incidenceRootParent_left_eq_right
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {root : C} {child : {v : C // v ≠ root}} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    (hchild : child.1 = ⟨Sum.inl y, hy⟩) :
    ∃ α : Block,
    ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
      rootParent hTtree.connected root child = ⟨Sum.inr α, hα⟩ ∧
        y ∈ A α := by
  classical
  have hAdj : T.Adj child.1 (rootParent hTtree.connected root child) :=
    rootParent_adj hTtree.connected root child
  have hAdj' :
      T.Adj ⟨Sum.inl y, hy⟩
        (rootParent hTtree.connected root child) := by
    simpa [hchild] using hAdj
  rcases replicatedIncidenceTree_adj_left_eq_right hTle hAdj' with
    ⟨α, hEq, hyA⟩
  have hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp := by
    simpa [hEq] using (rootParent hTtree.connected root child).2
  refine ⟨α, hα, ?_, hyA⟩
  apply Subtype.ext
  exact hEq

theorem incidenceRootParent_right_eq_left
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {root : C} {child : {v : C // v ≠ root}} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hchild : child.1 = ⟨Sum.inr α, hα⟩) :
    ∃ y : Y,
    ∃ hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
      rootParent hTtree.connected root child = ⟨Sum.inl y, hy⟩ ∧
        y ∈ A α := by
  classical
  have hAdj : T.Adj child.1 (rootParent hTtree.connected root child) :=
    rootParent_adj hTtree.connected root child
  have hAdj' :
      T.Adj ⟨Sum.inr α, hα⟩
        (rootParent hTtree.connected root child) := by
    simpa [hchild] using hAdj
  rcases replicatedIncidenceTree_adj_right_eq_left hTle hAdj' with
    ⟨y, hEq, hyA⟩
  have hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp := by
    simpa [hEq] using (rootParent hTtree.connected root child).2
  refine ⟨y, hy, ?_, hyA⟩
  apply Subtype.ext
  exact hEq

theorem incidenceYParentBlock_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    (hyρ : y ≠ ρ) :
    ∃ α : Block,
    ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
      IsRootParent T ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩ ∧
        y ∈ A α := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let child : {v : C // v ≠ root} :=
    ⟨⟨Sum.inl y, hy⟩, by
      intro h
      have hval := congrArg Subtype.val h
      simp [root] at hval
      exact hyρ hval⟩
  rcases incidenceRootParent_left_eq_right (A := A) hTle hTtree
      (root := root) (child := child) (hy := hy) (hchild := rfl) with
    ⟨α, hα, hparentEq, hyA⟩
  refine ⟨α, hα, ?_, hyA⟩
  have hspec := rootParent_spec hTtree.connected root child
  simpa [root, child, hparentEq] using hspec

theorem incidenceBlockParentY_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp} :
    ∃ y : Y,
    ∃ hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
      IsRootParent T ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩ ∧
        y ∈ A α := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let child : {v : C // v ≠ root} :=
    ⟨⟨Sum.inr α, hα⟩, by
      intro h
      have hval := congrArg Subtype.val h
      simp [root] at hval⟩
  rcases incidenceRootParent_right_eq_left (A := A) hTle hTtree
      (root := root) (child := child) (hα := hα) (hchild := rfl) with
    ⟨y, hy, hparentEq, hyA⟩
  refine ⟨y, hy, ?_, hyA⟩
  have hspec := rootParent_spec hTtree.connected root child
  simpa [root, child, hparentEq] using hspec

theorem incidenceYParentBlock_unique
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTtree : T.IsTree)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α β : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {hβ : (Sum.inr β : IncidenceVertex Y Block) ∈ C.supp}
    (hParentα :
      IsRootParent T root ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩)
    (hParentβ :
      IsRootParent T root ⟨Sum.inr β, hβ⟩ ⟨Sum.inl y, hy⟩) :
    α = β := by
  have hEq :
      (⟨Sum.inr α, hα⟩ : C) = ⟨Sum.inr β, hβ⟩ :=
    isRootParent_unique hTtree hParentα hParentβ
  have hval := congrArg Subtype.val hEq
  simpa using hval

theorem incidenceBlockParentY_unique
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent} {T : SimpleGraph C}
    (hTtree : T.IsTree)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {y z : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hz : (Sum.inl z : IncidenceVertex Y Block) ∈ C.supp}
    (hParentY :
      IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩)
    (hParentZ :
      IsRootParent T root ⟨Sum.inl z, hz⟩ ⟨Sum.inr α, hα⟩) :
    y = z := by
  have hEq :
      (⟨Sum.inl y, hy⟩ : C) = ⟨Sum.inl z, hz⟩ :=
    isRootParent_unique hTtree hParentY hParentZ
  have hval := congrArg Subtype.val hEq
  simpa using hval

noncomputable def rootChildrenFinset
    {V : Type} [Fintype V] (G : SimpleGraph V) (root parent : V) :
    Finset V := by
  classical
  exact Finset.univ.filter fun child => IsRootParent G root parent child

theorem mem_rootChildrenFinset
    {V : Type} [Fintype V] (G : SimpleGraph V) (root parent child : V) :
    child ∈ rootChildrenFinset G root parent ↔
      IsRootParent G root parent child := by
  classical
  simp [rootChildrenFinset]

noncomputable def incidenceBlockChildren
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (y : Y) (hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp) :
    Finset Block := by
  classical
  exact Finset.univ.filter fun α =>
    ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
      IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩

theorem mem_incidenceBlockChildren
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (y : Y) (hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp)
    (α : Block) :
    α ∈ incidenceBlockChildren T root y hy ↔
      ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
        IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩ := by
  classical
  simp [incidenceBlockChildren]

theorem incidenceBlockChildren_mem_incidence
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} (hmem : α ∈ incidenceBlockChildren T root y hy) :
    y ∈ A α := by
  classical
  rcases (mem_incidenceBlockChildren T root y hy α).mp hmem with
    ⟨hα, hparent⟩
  have hG := replicatedIncidenceTree_adj_val hTle hparent.1
  simpa [replicatedIncidenceGraph] using hG

theorem incidenceBlockChildren_parentY_unique
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {root : C} {α : Block}
    {y z : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hz : (Sum.inl z : IncidenceVertex Y Block) ∈ C.supp}
    (hαy : α ∈ incidenceBlockChildren T root y hy)
    (hαz : α ∈ incidenceBlockChildren T root z hz) :
    y = z := by
  classical
  rcases (mem_incidenceBlockChildren T root y hy α).mp hαy with
    ⟨hα₁, hParentY⟩
  rcases (mem_incidenceBlockChildren T root z hz α).mp hαz with
    ⟨hα₂, hParentZ⟩
  have hBlockEq :
      (⟨Sum.inr α, hα₂⟩ : C) = ⟨Sum.inr α, hα₁⟩ := by
    apply Subtype.ext
    rfl
  have hParentZ' :
      IsRootParent T root ⟨Sum.inl z, hz⟩ ⟨Sum.inr α, hα₁⟩ := by
    simpa [hBlockEq] using hParentZ
  exact incidenceBlockParentY_unique hTtree hParentY hParentZ'

theorem incidenceRootBlock_mem_blockChildren
    {Y Block : Type} [Fintype Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C}
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩) :
    α ∈ incidenceBlockChildren T ⟨Sum.inl ρ, hρ⟩ ρ hρ := by
  classical
  rw [mem_incidenceBlockChildren]
  exact ⟨hα, isRootParent_root_of_adj hRootAlpha⟩

noncomputable def incidenceYChildren
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (α : Block) (hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp) :
    Finset Y := by
  classical
  exact Finset.univ.filter fun y =>
    ∃ hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
      IsRootParent T root ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩

theorem mem_incidenceYChildren
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (α : Block) (hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)
    (y : Y) :
    y ∈ incidenceYChildren T root α hα ↔
      ∃ hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
        IsRootParent T root ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩ := by
  classical
  simp [incidenceYChildren]

theorem incidenceYChildren_mem_incidence
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {y : Y} (hmem : y ∈ incidenceYChildren T root α hα) :
    y ∈ A α := by
  classical
  rcases (mem_incidenceYChildren T root α hα y).mp hmem with
    ⟨hy, hparent⟩
  have hG := replicatedIncidenceTree_adj_val hTle hparent.1
  simpa [replicatedIncidenceGraph] using hG

theorem incidenceYChildren_parentBlock_unique
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {root : C} {y : Y}
    {α β : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {hβ : (Sum.inr β : IncidenceVertex Y Block) ∈ C.supp}
    (hyα : y ∈ incidenceYChildren T root α hα)
    (hyβ : y ∈ incidenceYChildren T root β hβ) :
    α = β := by
  classical
  rcases (mem_incidenceYChildren T root α hα y).mp hyα with
    ⟨hy₁, hParentα⟩
  rcases (mem_incidenceYChildren T root β hβ y).mp hyβ with
    ⟨hy₂, hParentβ⟩
  have hYEq :
      (⟨Sum.inl y, hy₂⟩ : C) = ⟨Sum.inl y, hy₁⟩ := by
    apply Subtype.ext
    rfl
  have hParentβ' :
      IsRootParent T root ⟨Sum.inr β, hβ⟩ ⟨Sum.inl y, hy₁⟩ := by
    simpa [hYEq] using hParentβ
  exact incidenceYParentBlock_unique hTtree hParentα hParentβ'

theorem incidenceYChildren_subset
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp} :
    incidenceYChildren T root α hα ⊆ A α := by
  intro y hy
  exact incidenceYChildren_mem_incidence hTle hy

theorem incidenceRootBlockActiveSet_subset
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩) :
    insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα) ⊆ A α := by
  classical
  have hρA : ρ ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hRootAlpha
    simpa [replicatedIncidenceGraph] using hG
  intro y hy
  rw [Finset.mem_insert] at hy
  rcases hy with rfl | hyChild
  · exact hρA
  · exact incidenceYChildren_subset hTle hyChild

theorem incidenceYChildren_card_le
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp} :
    (incidenceYChildren T root α hα).card <= (A α).card :=
  Finset.card_le_card (incidenceYChildren_subset hTle)

noncomputable def incidenceUnaryBlockChildren
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (y : Y) (hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp) :
    Finset Block := by
  classical
  exact Finset.univ.filter fun α =>
    ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
      IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩ ∧
        (incidenceYChildren T root α hα).card = 1

theorem mem_incidenceUnaryBlockChildren
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    (T : SimpleGraph C) (root : C)
    (y : Y) (hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp)
    (α : Block) :
    α ∈ incidenceUnaryBlockChildren T root y hy ↔
      ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
        IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩ ∧
          (incidenceYChildren T root α hα).card = 1 := by
  classical
  simp [incidenceUnaryBlockChildren]

theorem incidenceRootBlock_mem_unaryBlockChildren_of_card_eq_one
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C}
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα).card = 1) :
    α ∈ incidenceUnaryBlockChildren T ⟨Sum.inl ρ, hρ⟩ ρ hρ := by
  classical
  rw [mem_incidenceUnaryBlockChildren]
  exact ⟨hα, isRootParent_root_of_adj hRootAlpha, hUnary⟩

theorem incidenceBlockParentY_mem_unaryBlockChildren_of_card_eq_one
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hParent : IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩)
    (hUnary : (incidenceYChildren T root α hα).card = 1) :
    α ∈ incidenceUnaryBlockChildren T root y hy := by
  classical
  rw [mem_incidenceUnaryBlockChildren]
  exact ⟨hα, hParent, hUnary⟩

theorem incidenceUnaryBlockChildren_subset_blockChildren
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp} :
    incidenceUnaryBlockChildren T root y hy ⊆
      incidenceBlockChildren T root y hy := by
  classical
  intro α hαUnary
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hαUnary with
    ⟨hα, hParent, _hUnary⟩
  rw [mem_incidenceBlockChildren]
  exact ⟨hα, hParent⟩

theorem incidenceUnaryBlockChildren_block_mem_component
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y hy) :
    (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp := by
  classical
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hαUnary with
    ⟨hα, _hParent, _hUnary⟩
  exact hα

theorem incidenceUnaryBlockChildren_parent
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y hy) :
    IsRootParent T root ⟨Sum.inl y, hy⟩
      ⟨Sum.inr α,
        incidenceUnaryBlockChildren_block_mem_component
          (A := A) hαUnary⟩ := by
  classical
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hαUnary with
    ⟨hα, hParent, _hUnary⟩
  have hBlockEq :
      (⟨Sum.inr α, hα⟩ : C) =
        ⟨Sum.inr α,
          incidenceUnaryBlockChildren_block_mem_component
            (A := A) hαUnary⟩ := by
    apply Subtype.ext
    rfl
  simpa [hBlockEq]
    using hParent

theorem incidenceUnaryBlockChildren_child_card_eq_one
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y hy) :
    (incidenceYChildren T root α
      (incidenceUnaryBlockChildren_block_mem_component
        (A := A) hαUnary)).card = 1 := by
  classical
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hαUnary with
    ⟨hα, _hParent, hUnary⟩
  have hArg :
      incidenceYChildren T root α
          (incidenceUnaryBlockChildren_block_mem_component
            (A := A) hαUnary) =
        incidenceYChildren T root α hα := by
    have hproof :
        incidenceUnaryBlockChildren_block_mem_component
            (A := A) hαUnary = hα :=
      Subsingleton.elim _ _
    rw [hproof]
  simpa [hArg]
    using hUnary

theorem incidenceUnaryBlockChildren_parentY_unique
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {root : C} {α : Block}
    {y z : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hz : (Sum.inl z : IncidenceVertex Y Block) ∈ C.supp}
    (hαy : α ∈ incidenceUnaryBlockChildren T root y hy)
    (hαz : α ∈ incidenceUnaryBlockChildren T root z hz) :
    y = z :=
  incidenceBlockChildren_parentY_unique (A := A) hTtree
    (incidenceUnaryBlockChildren_subset_blockChildren hαy)
    (incidenceUnaryBlockChildren_subset_blockChildren hαz)

theorem incidenceUnaryBlockChildren_parent_dist_lt_child
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y hy)
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {q : Y}
    (hqChild : q ∈ incidenceYChildren T root α hα) :
    ∃ hq : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
      T.dist root ⟨Sum.inl y, hy⟩ <
        T.dist root ⟨Sum.inl q, hq⟩ := by
  classical
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hαUnary with
    ⟨hαParent, hParent, _hUnary⟩
  rcases (mem_incidenceYChildren T root α hα q).mp hqChild with
    ⟨hq, hChild⟩
  have hBlockEq :
      (⟨Sum.inr α, hαParent⟩ : C) = ⟨Sum.inr α, hα⟩ := by
    apply Subtype.ext
    rfl
  have hParent' :
      IsRootParent T root ⟨Sum.inl y, hy⟩ ⟨Sum.inr α, hα⟩ := by
    simpa [hBlockEq] using hParent
  refine ⟨hq, ?_⟩
  have hParentDist := hParent'.2
  have hChildDist := hChild.2
  omega

theorem incidenceUnaryBlockPair_subset
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C}
    {y : Y} {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y hy)
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    {q : Y}
    (hqChild : q ∈ incidenceYChildren T root α hα) :
    ({y, q} : Finset Y) ⊆ A α := by
  classical
  have hyA : y ∈ A α := by
    have hParent := incidenceUnaryBlockChildren_parent (A := A) hαUnary
    have hG := replicatedIncidenceTree_adj_val hTle hParent.1
    simpa [replicatedIncidenceGraph] using hG
  have hqA : q ∈ A α :=
    incidenceYChildren_subset (A := A) hTle hqChild
  intro z hz
  simp at hz
  rcases hz with rfl | rfl
  · exact hyA
  · exact hqA

theorem root_not_mem_incidenceYChildren
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C}
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp} :
    ρ ∉ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα := by
  classical
  intro hmem
  rcases (mem_incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα ρ).mp hmem with
    ⟨hρ', hparent⟩
  have hrootEq :
      (⟨Sum.inl ρ, hρ'⟩ : C) = ⟨Sum.inl ρ, hρ⟩ := by
    apply Subtype.ext
    rfl
  have hdist := hparent.2
  rw [hrootEq, SimpleGraph.dist_self] at hdist
  omega

theorem incidenceYChildren_mem_of_root_branch
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block} {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩)
    (hyρ : y ≠ ρ)
    (hAlphaY : T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩) :
    y ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα := by
  classical
  have hrootBlockDist :
      T.dist ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩ = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hRootAlpha
  have hblockYDist :
      T.dist ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩ = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hAlphaY
  have hle :
      T.dist ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inl y, hy⟩ <= 2 := by
    have htri := hAlphaY.reachable.dist_triangle_right ⟨Sum.inl ρ, hρ⟩
    rw [hrootBlockDist, hblockYDist] at htri
    exact htri
  have hrootYNe :
      (⟨Sum.inl ρ, hρ⟩ : C) ≠ ⟨Sum.inl y, hy⟩ := by
    intro h
    have hval := congrArg Subtype.val h
    simp at hval
    exact hyρ hval.symm
  have hnotAdjRootY :
      ¬ T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inl y, hy⟩ :=
    replicatedIncidenceTree_not_adj_left_left hTle
  have hlt :
      1 < T.dist ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inl y, hy⟩ :=
    hTtree.connected.one_lt_dist_of_ne_of_not_adj hrootYNe hnotAdjRootY
  have hdist :
      T.dist ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inl y, hy⟩ = 2 := by
    omega
  rw [mem_incidenceYChildren]
  refine ⟨hy, ?_⟩
  exact ⟨hAlphaY.symm, by rw [hrootBlockDist, hdist]⟩

theorem replicatedIncidenceComponent_rooted_tree_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a)
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent) :
    ∃ ρ : Y,
    ∃ _ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
    ∃ T : SimpleGraph C,
      T ≤ C.toSimpleGraph ∧ T.IsTree ∧
      ∃ α : Block,
        (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp ∧
        (replicatedIncidenceGraph A).Adj (Sum.inl ρ) (Sum.inr α) := by
  classical
  rcases replicatedIncidenceComponent_has_y hA ha2 C with ⟨ρ, hρ⟩
  rcases replicatedIncidenceComponent_exists_isTree_le C with ⟨T, hTle, hTtree⟩
  rcases replicatedIncidenceComponent_y_has_block_neighbor hNoIso C hρ with
    ⟨α, hα, hAdj⟩
  exact ⟨ρ, hρ, T, hTle, hTtree, α, hα, hAdj⟩

theorem replicatedIncidenceComponent_rooted_tree_with_tree_neighbor_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a)
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent) :
    ∃ ρ : Y,
    ∃ hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
    ∃ T : SimpleGraph C,
      T ≤ C.toSimpleGraph ∧ T.IsTree ∧
      ∃ α : Block,
      ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
        T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩ := by
  classical
  rcases replicatedIncidenceComponent_rooted_tree_exists hA hNoIso ha2 C with
    ⟨ρ, hρ, T, hTle, hTtree, α, hα, _hAdj⟩
  let u : C := ⟨Sum.inl ρ, hρ⟩
  let v : C := ⟨Sum.inr α, hα⟩
  have huv : u ≠ v := by
    intro h
    have hval := congrArg Subtype.val h
    simp [u, v] at hval
  have hreach : T.Reachable u v := hTtree.connected u v
  rcases hreach.nonempty_neighborSet_left huv with ⟨w, hwAdj⟩
  rcases replicatedIncidenceTree_adj_left_eq_right hTle hwAdj with
    ⟨β, hwEq, _hyw⟩
  have hβ : (Sum.inr β : IncidenceVertex Y Block) ∈ C.supp := by
    simpa [hwEq] using w.2
  have hw : w = ⟨Sum.inr β, hβ⟩ := by
    apply Subtype.ext
    exact hwEq
  refine ⟨ρ, hρ, T, hTle, hTtree, β, hβ, ?_⟩
  simpa [u, hw] using hwAdj

theorem replicatedIncidenceComponent_rooted_tree_with_branch_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {a : Nat} (hA : forall α : Block, (A α).card = a)
    (hNoIso : forall y : Y, exists α : Block, y ∈ A α) (ha2 : 2 <= a)
    (C : (replicatedIncidenceGraph A).ConnectedComponent) :
    ∃ ρ : Y,
    ∃ hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
    ∃ T : SimpleGraph C,
      T ≤ C.toSimpleGraph ∧ T.IsTree ∧
      ∃ α : Block,
      ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
        T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩ ∧
        ∃ y : Y,
        ∃ hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
          y ≠ ρ ∧ T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩ := by
  classical
  rcases replicatedIncidenceComponent_has_y hA ha2 C with ⟨ρ, hρ⟩
  rcases replicatedIncidenceComponent_exists_isTree_le C with ⟨T, hTle, hTtree⟩
  rcases replicatedIncidenceComponent_has_other_y hA hNoIso ha2 C hρ with
    ⟨yTarget, hyTarget_ne, hyTargetC⟩
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let target : C := ⟨Sum.inl yTarget, hyTargetC⟩
  have hRootTarget : root ≠ target := by
    intro h
    have hval := congrArg Subtype.val h
    simp [root, target] at hval
    exact hyTarget_ne hval.symm
  have hreach : T.Reachable root target := hTtree.connected root target
  rcases hreach.exists_walk_length_eq_dist with ⟨p, hp⟩
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hRootTarget p with
    ⟨w, hRootW, pTail, hpEq⟩
  subst p
  rcases replicatedIncidenceTree_adj_left_eq_right hTle hRootW with
    ⟨α, hWval, _hρA⟩
  have hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp := by
    simpa [hWval] using w.2
  have hwEq : w = ⟨Sum.inr α, hα⟩ := by
    apply Subtype.ext
    exact hWval
  have hWTarget : w ≠ target := by
    intro h
    have hval := congrArg Subtype.val h
    rw [hWval] at hval
    simp [target] at hval
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hWTarget pTail with
    ⟨z, hWZ, pRest, hpTailEq⟩
  subst pTail
  have hWZ' : T.Adj ⟨Sum.inr α, hα⟩ z := by
    simpa [hwEq] using hWZ
  rcases replicatedIncidenceTree_adj_right_eq_left hTle hWZ' with
    ⟨yNext, hZval, _hyA⟩
  have hyNextC : (Sum.inl yNext : IncidenceVertex Y Block) ∈ C.supp := by
    simpa [hZval] using z.2
  have hzEq : z = ⟨Sum.inl yNext, hyNextC⟩ := by
    apply Subtype.ext
    exact hZval
  have hNext_ne : yNext ≠ ρ := by
    intro hnext
    have hzroot : z = root := by
      apply Subtype.ext
      simp [root, hZval, hnext]
    have hle0 : T.dist z target <= pRest.length := SimpleGraph.dist_le pRest
    have hle : T.dist root target <= pRest.length := by
      simpa [hzroot] using hle0
    simp at hp
    omega
  have hAlphaY : T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inl yNext, hyNextC⟩ := by
    simpa [hzEq] using hWZ'
  have hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩ := by
    simpa [root, hwEq] using hRootW
  exact
    ⟨ρ, hρ, T, hTle, hTtree, α, hα, hRootAlpha,
      yNext, hyNextC, hNext_ne, hAlphaY⟩

abbrev IncidenceComponent
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y) : Type :=
  (replicatedIncidenceGraph A).ConnectedComponent

abbrev ComponentBlock
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y)
    (C : IncidenceComponent A) : Type :=
  {α : Block // (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}

abbrev ComponentY
    {Y Block : Type} [DecidableEq Y] (A : Block -> Finset Y)
    (C : IncidenceComponent A) : Type :=
  {y : Y // (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}

noncomputable instance componentBlockFintype
    {Y Block : Type} [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y} (C : IncidenceComponent A) :
    Fintype (ComponentBlock A C) :=
  Fintype.ofFinite _

noncomputable instance componentYFintype
    {Y Block : Type} [DecidableEq Y] [Fintype Y]
    {A : Block -> Finset Y} (C : IncidenceComponent A) :
    Fintype (ComponentY A C) :=
  Fintype.ofFinite _

def componentYVertex
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : IncidenceComponent A} (y : ComponentY A C) : C :=
  ⟨Sum.inl y.1, y.2⟩

noncomputable def componentYRootDist
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : IncidenceComponent A} (T : SimpleGraph C) (root : C)
    (y : ComponentY A C) : Nat :=
  T.dist root (componentYVertex y)

theorem componentYRootDist_lt_of_unary_child
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {y q : ComponentY A C} {α : Block}
    (hαUnary : α ∈ incidenceUnaryBlockChildren T root y.1 y.2)
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hqChild : q.1 ∈ incidenceYChildren T root α hα) :
    componentYRootDist T root y < componentYRootDist T root q := by
  classical
  rcases incidenceUnaryBlockChildren_parent_dist_lt_child
      (A := A) hαUnary hqChild with
    ⟨hq, hlt⟩
  have hqEq :
      (⟨Sum.inl q.1, hq⟩ : C) = ⟨Sum.inl q.1, q.2⟩ := by
    apply Subtype.ext
    rfl
  simpa [componentYRootDist, componentYVertex, hqEq]
    using hlt

theorem componentYRootDist_lt_of_parentBlock_child
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {p q : ComponentY A C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hParent :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α, hα⟩)
    (hqChild : q.1 ∈ incidenceYChildren T root α hα) :
    componentYRootDist T root p < componentYRootDist T root q := by
  classical
  rcases (mem_incidenceYChildren T root α hα q.1).mp hqChild with
    ⟨hq, hChild⟩
  have hqEq :
      (⟨Sum.inl q.1, hq⟩ : C) = ⟨Sum.inl q.1, q.2⟩ := by
    apply Subtype.ext
    rfl
  have hParentDist := hParent.2
  have hChildDist := hChild.2
  have hdist :
      T.dist root (componentYVertex p) + 1 + 1 =
        T.dist root (componentYVertex q) := by
    calc
      T.dist root (componentYVertex p) + 1 + 1
          = T.dist root ⟨Sum.inr α, hα⟩ + 1 := by
              rw [hParentDist]
      _ = T.dist root (componentYVertex q) := by
              simpa [componentYVertex, hqEq] using hChildDist
  unfold componentYRootDist
  rw [← hdist]
  omega

theorem componentBlockParentY_exists
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (α : ComponentBlock A C) :
    ∃ y : ComponentY A C,
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        (componentYVertex y) ⟨Sum.inr α.1, α.2⟩ ∧
      y.1 ∈ A α.1 := by
  classical
  rcases incidenceBlockParentY_exists (A := A) hTle hTtree
      (hρ := hρ) (hα := α.2) with
    ⟨y, hy, hParent, hyA⟩
  refine ⟨⟨y, hy⟩, ?_, hyA⟩
  simpa [componentYVertex]
    using hParent

theorem componentYParentBlock_exists
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (y : ComponentY A C) (hyρ : y.1 ≠ ρ) :
    ∃ α : ComponentBlock A C,
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) ∧
      y.1 ∈ A α.1 := by
  classical
  rcases incidenceYParentBlock_exists (A := A) hTle hTtree
      (hρ := hρ) (hy := y.2) hyρ with
    ⟨α, hα, hParent, hyA⟩
  refine ⟨⟨α, hα⟩, ?_, hyA⟩
  simpa [componentYVertex]
    using hParent

/-- Named choice of the parent block of a non-root component `Y` vertex. -/
noncomputable def componentYParentBlockChoice
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (y : ComponentY A C) (hyρ : y.1 ≠ ρ) :
    ComponentBlock A C :=
  Classical.choose
    (componentYParentBlock_exists (A := A) hTle hTtree (hρ := hρ) y hyρ)

theorem componentYParentBlockChoice_spec
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (y : ComponentY A C) (hyρ : y.1 ≠ ρ) :
    IsRootParent T ⟨Sum.inl ρ, hρ⟩
        ⟨Sum.inr
          (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree y hyρ).1,
          (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree y hyρ).2⟩
        (componentYVertex y) ∧
      y.1 ∈ A (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ).1 := by
  classical
  simpa [componentYParentBlockChoice] using
    Classical.choose_spec
      (componentYParentBlock_exists (A := A) hTle hTtree (hρ := hρ) y hyρ)

theorem componentYParentBlockChoice_parent
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (y : ComponentY A C) (hyρ : y.1 ≠ ρ) :
    IsRootParent T ⟨Sum.inl ρ, hρ⟩
      ⟨Sum.inr
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).1,
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).2⟩
      (componentYVertex y) :=
  (componentYParentBlockChoice_spec (A := A) (ρ := ρ) (hρ := hρ)
    hTle hTtree y hyρ).1

theorem componentYParentBlock_unique
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {root : C} {y : ComponentY A C}
    {α β : ComponentBlock A C}
    (hParentα :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y))
    (hParentβ :
      IsRootParent T root ⟨Sum.inr β.1, β.2⟩ (componentYVertex y)) :
    α = β := by
  classical
  have hαβ :
      α.1 = β.1 :=
    incidenceYParentBlock_unique (A := A) hTtree hParentα hParentβ
  exact Subtype.ext hαβ

theorem componentBlockParentY_unique
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {root : C} {α : ComponentBlock A C}
    {p q : ComponentY A C}
    (hParentP :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩)
    (hParentQ :
      IsRootParent T root (componentYVertex q) ⟨Sum.inr α.1, α.2⟩) :
    p = q := by
  classical
  have hpq :
      p.1 = q.1 :=
    incidenceBlockParentY_unique (A := A) hTtree hParentP hParentQ
  exact Subtype.ext hpq

theorem componentYParentBlockChoice_eq_of_parent
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {y : ComponentY A C} (hyρ : y.1 ≠ ρ)
    {α : ComponentBlock A C}
    (hParent :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        ⟨Sum.inr α.1, α.2⟩ (componentYVertex y)) :
    componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree y hyρ = α := by
  classical
  exact componentYParentBlock_unique (A := A) hTtree
    (componentYParentBlockChoice_parent (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree y hyρ)
    hParent

/-- Named choice of the parent `Y` vertex of a component block. -/
noncomputable def componentBlockParentYChoice
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (α : ComponentBlock A C) :
    ComponentY A C :=
  Classical.choose
    (componentBlockParentY_exists (A := A) hTle hTtree (hρ := hρ) α)

theorem componentBlockParentYChoice_spec
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (α : ComponentBlock A C) :
    IsRootParent T ⟨Sum.inl ρ, hρ⟩
        (componentYVertex
          (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree α))
        ⟨Sum.inr α.1, α.2⟩ ∧
      (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree α).1 ∈ A α.1 := by
  classical
  simpa [componentBlockParentYChoice] using
    Classical.choose_spec
      (componentBlockParentY_exists (A := A) hTle hTtree (hρ := hρ) α)

theorem componentBlockParentYChoice_parent
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (α : ComponentBlock A C) :
    IsRootParent T ⟨Sum.inl ρ, hρ⟩
      (componentYVertex
        (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree α))
      ⟨Sum.inr α.1, α.2⟩ :=
  (componentBlockParentYChoice_spec (A := A) (ρ := ρ) (hρ := hρ)
    hTle hTtree α).1

theorem componentBlockParentYChoice_eq_of_parent
    {Y Block : Type} [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {α : ComponentBlock A C} {p : ComponentY A C}
    (hParent :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        (componentYVertex p) ⟨Sum.inr α.1, α.2⟩) :
    componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree α = p := by
  classical
  exact componentBlockParentY_unique (A := A) hTtree
    (componentBlockParentYChoice_parent (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree α)
    hParent

noncomputable def componentBlockYChildren
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C)
    (α : ComponentBlock A C) : Finset (ComponentY A C) := by
  classical
  exact Finset.univ.filter fun y : ComponentY A C =>
    y.1 ∈ incidenceYChildren T root α.1 α.2

theorem mem_componentBlockYChildren
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C)
    (α : ComponentBlock A C) (y : ComponentY A C) :
    y ∈ componentBlockYChildren T root α ↔
      y.1 ∈ incidenceYChildren T root α.1 α.2 := by
  classical
  simp [componentBlockYChildren]

theorem componentYParentBlock_mem_children
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {y : ComponentY A C} {α : ComponentBlock A C}
    (hParent :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y)) :
    y ∈ componentBlockYChildren T root α := by
  classical
  rw [mem_componentBlockYChildren]
  rw [mem_incidenceYChildren]
  exact ⟨y.2, by simpa [componentYVertex] using hParent⟩

theorem componentBlockYChildren_mk_mem
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {α : ComponentBlock A C} {y : Y}
    (hy : y ∈ incidenceYChildren T root α.1 α.2) :
    ∃ hyC : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp,
      (⟨y, hyC⟩ : ComponentY A C) ∈
        componentBlockYChildren T root α := by
  classical
  rcases (mem_incidenceYChildren T root α.1 α.2 y).mp hy with
    ⟨hyC, _hParent⟩
  refine ⟨hyC, ?_⟩
  rw [mem_componentBlockYChildren]
  exact hy

theorem componentBlockYChildren_dist_lt_of_parent
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {p : ComponentY A C} {α : ComponentBlock A C}
    (hParent :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩)
    {q : ComponentY A C}
    (hq : q ∈ componentBlockYChildren T root α) :
    componentYRootDist T root p < componentYRootDist T root q := by
  classical
  exact
    componentYRootDist_lt_of_parentBlock_child
      (A := A) hParent
      ((mem_componentBlockYChildren T root α q).mp hq)

theorem componentBlockYChildren_eq_of_card_one
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {α : ComponentBlock A C}
    (hUnary : (incidenceYChildren T root α.1 α.2).card = 1)
    {p q : ComponentY A C}
    (hp : p ∈ componentBlockYChildren T root α)
    (hq : q ∈ componentBlockYChildren T root α) :
    p = q := by
  classical
  have hpChild := (mem_componentBlockYChildren T root α p).mp hp
  have hqChild := (mem_componentBlockYChildren T root α q).mp hq
  rcases Finset.card_eq_one.mp hUnary with ⟨z, hz⟩
  have hpz : p.1 = z := by
    simpa [hz] using hpChild
  have hqz : q.1 = z := by
    simpa [hz] using hqChild
  have hpq : p.1 = q.1 := by
    rw [hpz, hqz]
  exact Subtype.ext hpq

/-- Component-local form of the remaining residue assignment.  For each
connected component of the incidence graph, choose local residue patterns on
the block vertices in that component so that every `Y`-vertex in the component
receives a unit total contribution. -/
def ComponentResiduePatternUnitAssignmentGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          forall C : IncidenceComponent A,
            ∃ S : Block -> Finset Y,
            ∃ P : forall α : Block,
                ReplicatedBlockResiduePattern (A α) (S α) (a / 2) m,
              (forall α : Block, S α ⊆ A α) ∧
              (forall α : Block,
                (Sum.inr α : IncidenceVertex Y Block) ∉ C.supp -> S α = ∅) ∧
              forall y : Y,
                (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp ->
                  IsUnit
                    (∑ α : Block,
                      if y ∈ S α then
                        ((replicatedBlockColumnDegree (P α).toChoice y : Nat) :
                          ZMod m)
                      else 0)

/-- Rooted-tree form of the remaining component assignment.  This is the
target that should be proved by the top-down construction: the root has a
specified first tree-neighbour block, and the proof may orient the spanning
tree away from that root. -/
def RootedTreeResiduePatternUnitAssignmentGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          forall C : IncidenceComponent A,
          forall ρ : Y,
          forall hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
          forall T : SimpleGraph C,
            T ≤ C.toSimpleGraph -> T.IsTree ->
              forall α0 : Block,
              forall hα0 : (Sum.inr α0 : IncidenceVertex Y Block) ∈ C.supp,
                T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α0, hα0⟩ ->
                  ∃ S : Block -> Finset Y,
                  ∃ P : forall α : Block,
                      ReplicatedBlockResiduePattern (A α) (S α) (a / 2) m,
                    (forall α : Block, S α ⊆ A α) ∧
                    (forall α : Block,
                      (Sum.inr α : IncidenceVertex Y Block) ∉ C.supp ->
                        S α = ∅) ∧
                    forall y : Y,
                      (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp ->
                        IsUnit
                          (∑ α : Block,
                            if y ∈ S α then
                              ((replicatedBlockColumnDegree
                                (P α).toChoice y : Nat) : ZMod m)
                            else 0)

/-- Branch-rooted version of the remaining component assignment.  This matches
the constructive shortcut more closely than an arbitrary root-neighbour block:
the chosen root block is required to have a non-root left child in the rooted
spanning tree, so the root block can use the active set
`{root} ∪ children(rootBlock)`. -/
def RootedBranchResiduePatternUnitAssignmentGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          forall C : IncidenceComponent A,
          forall ρ : Y,
          forall hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
          forall T : SimpleGraph C,
            T ≤ C.toSimpleGraph -> T.IsTree ->
              forall α0 : Block,
              forall hα0 : (Sum.inr α0 : IncidenceVertex Y Block) ∈ C.supp,
                T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α0, hα0⟩ ->
                  forall y0 : Y,
                  forall hy0 :
                    (Sum.inl y0 : IncidenceVertex Y Block) ∈ C.supp,
                    y0 ≠ ρ ->
                    T.Adj ⟨Sum.inr α0, hα0⟩ ⟨Sum.inl y0, hy0⟩ ->
                      ∃ S : Block -> Finset Y,
                      ∃ P : forall α : Block,
                          ReplicatedBlockResiduePattern (A α) (S α)
                            (a / 2) m,
                        (forall α : Block, S α ⊆ A α) ∧
                        (forall α : Block,
                          (Sum.inr α : IncidenceVertex Y Block) ∉ C.supp ->
                            S α = ∅) ∧
                        forall y : Y,
                          (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp ->
                            IsUnit
                              (∑ α : Block,
                                if y ∈ S α then
                                  ((replicatedBlockColumnDegree
                                    (P α).toChoice y : Nat) : ZMod m)
                                else 0)

/-- Component-subtype version of the branch-rooted assignment goal.  This is
the clean target for the actual top-down construction: it only chooses
patterns on block vertices lying in the connected component under discussion.
The bridge below extends those patterns to all blocks by idle patterns. -/
def RootedBranchComponentBlockResiduePatternUnitAssignmentGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          forall C : IncidenceComponent A,
          forall ρ : Y,
          forall hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp,
          forall T : SimpleGraph C,
            T ≤ C.toSimpleGraph -> T.IsTree ->
              forall α0 : Block,
              forall hα0 : (Sum.inr α0 : IncidenceVertex Y Block) ∈ C.supp,
                T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α0, hα0⟩ ->
                  forall y0 : Y,
                  forall hy0 :
                    (Sum.inl y0 : IncidenceVertex Y Block) ∈ C.supp,
                    y0 ≠ ρ ->
                    T.Adj ⟨Sum.inr α0, hα0⟩ ⟨Sum.inl y0, hy0⟩ ->
                      ∃ S : ComponentBlock A C -> Finset Y,
                      ∃ P : forall α : ComponentBlock A C,
                          ReplicatedBlockResiduePattern (A α.1) (S α)
                            (a / 2) m,
                        (forall α : ComponentBlock A C, S α ⊆ A α.1) ∧
                        forall y : Y,
                          (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp ->
                            IsUnit
                              (∑ α : ComponentBlock A C,
                                if y ∈ S α then
                                  ((replicatedBlockColumnDegree
                                    (P α).toChoice y : Nat) : ZMod m)
                                else 0)

theorem componentResiduePatternUnitAssignmentGoal_of_rootedTree
    (hRooted : RootedTreeResiduePatternUnitAssignmentGoal) :
    ComponentResiduePatternUnitAssignmentGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso C
  letI := instY
  letI := instDec
  letI := instBlock
  classical
  rcases replicatedIncidenceComponent_rooted_tree_with_tree_neighbor_exists
      hA hNoIso ha2 C with
    ⟨ρ, hρ, T, hTle, hTtree, α0, hα0, hTAdj⟩
  exact hRooted hmOdd hm3 ha2 A hA hNoIso C ρ hρ T hTle hTtree
    α0 hα0 hTAdj

theorem componentResiduePatternUnitAssignmentGoal_of_rootedBranch
    (hRooted : RootedBranchResiduePatternUnitAssignmentGoal) :
    ComponentResiduePatternUnitAssignmentGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso C
  letI := instY
  letI := instDec
  letI := instBlock
  classical
  rcases replicatedIncidenceComponent_rooted_tree_with_branch_exists
      hA hNoIso ha2 C with
    ⟨ρ, hρ, T, hTle, hTtree, α0, hα0, hRootAlpha,
      y0, hy0, hy0ρ, hAlphaY⟩
  exact hRooted hmOdd hm3 ha2 A hA hNoIso C ρ hρ T hTle hTtree
    α0 hα0 hRootAlpha y0 hy0 hy0ρ hAlphaY

/-- Pure residue-assignment form of the remaining replicated balancing
construction.  It forgets row-level choices except through already-closed
local residue patterns; the remaining task is to choose active sets and local
patterns so that each right vertex receives a unit total contribution. -/
def ReplicatedResiduePatternUnitAssignmentGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          ∃ S : Block -> Finset Y,
          ∃ P : forall α : Block,
              ReplicatedBlockResiduePattern (A α) (S α) (a / 2) m,
            forall y : Y,
              IsUnit
                (∑ α : Block,
                  if y ∈ S α then
                    ((replicatedBlockColumnDegree (P α).toChoice y : Nat) :
                      ZMod m)
                  else 0)

theorem replicatedResiduePatternUnitAssignmentGoal_of_component
    (hComponent : ComponentResiduePatternUnitAssignmentGoal) :
    ReplicatedResiduePatternUnitAssignmentGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
  letI := instY
  letI := instDec
  letI := instBlock
  classical
  let G : SimpleGraph (IncidenceVertex Y Block) := replicatedIncidenceGraph A
  let compOfBlock : Block -> IncidenceComponent A :=
    fun α => G.connectedComponentMk (Sum.inr α)
  have hBlockMem :
      forall α : Block,
        (Sum.inr α : IncidenceVertex Y Block) ∈ (compOfBlock α).supp := by
    intro α
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hLocal := hComponent hmOdd hm3 ha2 A hA hNoIso
  choose SComp hSComp using hLocal
  choose PComp hPComp using hSComp
  let S : Block -> Finset Y :=
    fun α => SComp (compOfBlock α) α
  let P : forall α : Block,
      ReplicatedBlockResiduePattern (A α) (S α) (a / 2) m :=
    fun α => PComp (compOfBlock α) α
  refine ⟨S, P, ?_⟩
  intro y
  let Cy : IncidenceComponent A := G.connectedComponentMk (Sum.inl y)
  have hyCy : (Sum.inl y : IncidenceVertex Y Block) ∈ Cy.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  let globalTerm : Block -> ZMod m := fun α =>
    if y ∈ S α then
      ((replicatedBlockColumnDegree (P α).toChoice y : Nat) : ZMod m)
    else 0
  let localTerm : Block -> ZMod m := fun α =>
    if y ∈ SComp Cy α then
      ((replicatedBlockColumnDegree (PComp Cy α).toChoice y : Nat) : ZMod m)
    else 0
  have hTermEq : forall α : Block, globalTerm α = localTerm α := by
    intro α
    by_cases hαCy : (Sum.inr α : IncidenceVertex Y Block) ∈ Cy.supp
    · have hEq : compOfBlock α = Cy := by
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff Cy
          (Sum.inr α : IncidenceVertex Y Block)).mp hαCy
      simp only [globalTerm, localTerm, S, P]
      rw [hEq]
    · have hGlobalZero : globalTerm α = 0 := by
        by_cases hyS : y ∈ S α
        · have hyA : y ∈ A α := by
            exact (hPComp (compOfBlock α)).1 α hyS
          have hadj : G.Adj (Sum.inl y) (Sum.inr α) := by
            simpa [G, replicatedIncidenceGraph] using hyA
          have hmem : (Sum.inr α : IncidenceVertex Y Block) ∈ Cy.supp :=
            Cy.mem_supp_of_adj_mem_supp hyCy hadj
          exact False.elim (hαCy hmem)
        · simp [globalTerm, hyS]
      have hLocalZero : localTerm α = 0 := by
        have hEmpty : SComp Cy α = ∅ := (hPComp Cy).2.1 α hαCy
        simp [localTerm, hEmpty]
      rw [hGlobalZero, hLocalZero]
  have hSumEq :
      (∑ α : Block, globalTerm α) =
        ∑ α : Block, localTerm α := by
    apply Finset.sum_congr rfl
    intro α _hα
    exact hTermEq α
  change IsUnit (∑ α : Block, globalTerm α)
  rw [hSumEq]
  exact (hPComp Cy).2.2 y hyCy

/-- The closed local unary-transfer reservoir used by the replicated shortcut.
For two distinct active columns `p,q` in a block of size `a`, and any unit
`u <= m`, one can choose `floor(a/2)` columns in every row so that the `q`
column receives exactly `u` rows and the `p` column receives exactly `m-u`
rows.  Both column degrees are units modulo `m`. -/
theorem pairTransferBlockChoice_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a u m : Nat}
    {p q : Y} (ha : A.card = a) (ha2 : 2 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q)
    (hu : u <= m) (hcop : Nat.Coprime u m) :
    ∃ C : ReplicatedBlockChoice A (a / 2) m,
      replicatedBlockColumnDegree C q = u /\
        replicatedBlockColumnDegree C p = m - u /\
        Nat.Coprime (replicatedBlockColumnDegree C q) m /\
        Nat.Coprime (replicatedBlockColumnDegree C p) m := by
  classical
  rcases pairFiller_exists ha ha2 hp hq hpq with
    ⟨F, hFsub, hpF, hqF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := pairTransferChoice p q F u
      choose_subset := pairTransferChoice_subset hFsub hp hq
      choose_card := pairTransferChoice_card ha2 hpF hqF hFcard }
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · change Fintype.card
      {z : Fin m // q ∈ pairTransferChoice p q F u z} = u
    exact pairTransferChoice_q_card hu hpq hqF
  · change Fintype.card
      {z : Fin m // p ∈ pairTransferChoice p q F u z} = m - u
    exact pairTransferChoice_p_card hu hpq hpF
  · change Nat.Coprime
      (Fintype.card {z : Fin m // q ∈ pairTransferChoice p q F u z}) m
    exact pairTransferChoice_q_coprime hu hpq hqF hcop
  · change Nat.Coprime
      (Fintype.card {z : Fin m // p ∈ pairTransferChoice p q F u z}) m
    exact pairTransferChoice_p_coprime hu hpq hpF hcop

/-- The pair reservoir as a local residue pattern: the active set `{p,q}`
gets unit selected degrees, and every other block column has selected degree
divisible by `m`. -/
theorem pairResiduePattern_nonempty
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q : Y} (hmpos : 0 < m)
    (ha : A.card = a) (ha2 : 2 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) :
    Nonempty
      (ReplicatedBlockResiduePattern A ({p, q} : Finset Y) (a / 2) m) := by
  classical
  have hOneLe : 1 <= m := by omega
  rcases pairFiller_exists ha ha2 hp hq hpq with
    ⟨F, hFsub, hpF, hqF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := pairTransferChoice p q F 1
      choose_subset := pairTransferChoice_subset hFsub hp hq
      choose_card := pairTransferChoice_card ha2 hpF hqF hFcard }
  refine ⟨
    { toChoice := C
      active_coprime := ?_
      inactive_dvd := ?_ }⟩
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyP | hyQ
    · subst y
      change Nat.Coprime
        (Fintype.card {z : Fin m // p ∈ pairTransferChoice p q F 1 z}) m
      rw [pairTransferChoice_p_card hOneLe hpq hpF]
      exact coprime_m_sub_of_coprime hOneLe (by simp)
    · subst y
      change Nat.Coprime
        (Fintype.card {z : Fin m // q ∈ pairTransferChoice p q F 1 z}) m
      rw [pairTransferChoice_q_card hOneLe hpq hqF]
      simp
  · intro y _hyA hyInactive
    have hyp : y ≠ p := by
      intro h
      apply hyInactive
      simp [h]
    have hyq : y ≠ q := by
      intro h
      apply hyInactive
      simp [h]
    change m ∣
      Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F 1 z}
    exact pairTransferChoice_inactive_dvd hyp hyq

theorem pairResiduePatternWithUnit_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a u m : Nat}
    {p q : Y} (ha : A.card = a) (ha2 : 2 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q)
    (hu : u <= m) (hcop : Nat.Coprime u m) :
    ∃ P : ReplicatedBlockResiduePattern A ({p, q} : Finset Y) (a / 2) m,
      replicatedBlockColumnDegree P.toChoice q = u ∧
      replicatedBlockColumnDegree P.toChoice p = m - u := by
  classical
  rcases pairFiller_exists ha ha2 hp hq hpq with
    ⟨F, hFsub, hpF, hqF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := pairTransferChoice p q F u
      choose_subset := pairTransferChoice_subset hFsub hp hq
      choose_card := pairTransferChoice_card ha2 hpF hqF hFcard }
  have hqdeg : replicatedBlockColumnDegree C q = u := by
    change Fintype.card
      {z : Fin m // q ∈ pairTransferChoice p q F u z} = u
    exact pairTransferChoice_q_card hu hpq hqF
  have hpdeg : replicatedBlockColumnDegree C p = m - u := by
    change Fintype.card
      {z : Fin m // p ∈ pairTransferChoice p q F u z} = m - u
    exact pairTransferChoice_p_card hu hpq hpF
  refine ⟨
    { toChoice := C
      active_coprime := ?_
      inactive_dvd := ?_ }, hqdeg, hpdeg⟩
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyP | hyQ
    · subst y
      rw [hpdeg]
      exact coprime_m_sub_of_coprime hu hcop
    · subst y
      rw [hqdeg]
      exact hcop
  · intro y _hyA hyInactive
    have hyp : y ≠ p := by
      intro h
      apply hyInactive
      simp [h]
    have hyq : y ≠ q := by
      intro h
      apply hyInactive
      simp [h]
    change m ∣
      Fintype.card {z : Fin m // y ∈ pairTransferChoice p q F u z}
    exact pairTransferChoice_inactive_dvd hyp hyq

theorem pairResiduePatternWithZModUnit_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q : Y} (hmpos : 0 < m)
    (ha : A.card = a) (ha2 : 2 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q)
    (u : ZMod m) (hu : IsUnit u) :
    ∃ P : ReplicatedBlockResiduePattern A ({p, q} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) = u ∧
      ((replicatedBlockColumnDegree P.toChoice p : Nat) : ZMod m) = -u := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have huLe : u.val <= m := le_of_lt (ZMod.val_lt u)
  have hcop : Nat.Coprime u.val m := by
    exact
      (ZMod.isUnit_iff_coprime u.val m).mp
        (by simpa [ZMod.natCast_zmod_val u] using hu)
  rcases pairResiduePatternWithUnit_exists
      (A := A) (a := a) (u := u.val) (m := m) (p := p) (q := q)
      ha ha2 hp hq hpq huLe hcop with
    ⟨P, hqdeg, hpdeg⟩
  refine ⟨P, ?_, ?_⟩
  · rw [hqdeg]
    exact ZMod.natCast_zmod_val u
  · rw [hpdeg]
    have hsub :
        ((m - u.val : Nat) : ZMod m) =
          (m : ZMod m) - (u.val : ZMod m) := by
      exact Nat.cast_sub huLe
    rw [hsub]
    simp [ZMod.natCast_zmod_val u]

theorem incidenceUnaryPairResiduePatternWithZModUnit_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    {root : C} {p q : Y} {α : Block}
    {hp : (Sum.inl p : IncidenceVertex Y Block) ∈ C.supp}
    {hq : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a) (ha2 : 2 <= a)
    (hParent : IsRootParent T root ⟨Sum.inl p, hp⟩ ⟨Sum.inr α, hα⟩)
    (hChild : IsRootParent T root ⟨Sum.inr α, hα⟩ ⟨Sum.inl q, hq⟩)
    (u : ZMod m) (hu : IsUnit u) :
    ∃ P : ReplicatedBlockResiduePattern (A α) ({p, q} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) = u ∧
      ((replicatedBlockColumnDegree P.toChoice p : Nat) : ZMod m) = -u := by
  classical
  have hpA : p ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hParent.1
    simpa [replicatedIncidenceGraph] using hG
  have hqA : q ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hChild.1
    simpa [replicatedIncidenceGraph] using hG
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hEq :
        (⟨Sum.inl p, hq⟩ : C) = ⟨Sum.inl p, hp⟩ := by
      apply Subtype.ext
      rfl
    have hParentDist := hParent.2
    have hChildDist := hChild.2
    rw [hEq] at hChildDist
    omega
  exact
    pairResiduePatternWithZModUnit_exists hmpos ha ha2 hpA hqA hpq u hu

theorem incidenceChildTransferResiduePatternWithZModUnit_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    {ρ q : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a) (ha2 : 2 <= a)
    (hqChild :
      q ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα)
    (u : ZMod m) (hu : IsUnit u) :
    ∃ p : Y,
    ∃ _ : (Sum.inl p : IncidenceVertex Y Block) ∈ C.supp,
    ∃ P : ReplicatedBlockResiduePattern (A α) ({p, q} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) = u ∧
      ((replicatedBlockColumnDegree P.toChoice p : Nat) : ZMod m) = -u := by
  classical
  rcases (mem_incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα q).mp hqChild with
    ⟨hq, hChild⟩
  rcases incidenceBlockParentY_exists (A := A) hTle hTtree
      (hρ := hρ) (hα := hα) with
    ⟨p, hp, hParent, _hpA⟩
  rcases incidenceUnaryPairResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos ha ha2 hParent hChild u hu with
    ⟨P, hqdeg, hpdeg⟩
  exact ⟨p, hp, P, hqdeg, hpdeg⟩

/-- The closed local triple reservoir used by the replicated shortcut.  For
three distinct active columns `p,q,r`, one can choose `floor(a/2)` columns in
every row so that the three active columns receive row counts `1,1,m-2`.
When `m` is odd, all three counts are units modulo `m`. -/
theorem tripleTransferBlockChoice_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q r : Y} (hmOdd : Odd m) (hm3 : 3 <= m)
    (ha : A.card = a) (ha3 : 3 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ C : ReplicatedBlockChoice A (a / 2) m,
      replicatedBlockColumnDegree C p = 1 /\
        replicatedBlockColumnDegree C q = 1 /\
        replicatedBlockColumnDegree C r = m - 2 /\
        Nat.Coprime (replicatedBlockColumnDegree C p) m /\
        Nat.Coprime (replicatedBlockColumnDegree C q) m /\
        Nat.Coprime (replicatedBlockColumnDegree C r) m := by
  classical
  have hmpos : 0 < m := by omega
  have hm2lt : 1 < m := by omega
  have hm2 : 2 <= m := by omega
  rcases tripleFiller_exists ha ha3 hp hq hr hpq hpr hqr with
    ⟨F, hFsub, hpF, hqF, hrF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := tripleTransferChoice p q r F
      choose_subset := tripleTransferChoice_subset hFsub hp hq hr
      choose_card := tripleTransferChoice_card ha3 hpF hqF hrF hFcard }
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Fintype.card
      {z : Fin m // p ∈ tripleTransferChoice p q r F z} = 1
    exact tripleTransferChoice_p_card hmpos hpq hpr hpF
  · change Fintype.card
      {z : Fin m // q ∈ tripleTransferChoice p q r F z} = 1
    exact tripleTransferChoice_q_card hm2lt hpq hqr hqF
  · change Fintype.card
      {z : Fin m // r ∈ tripleTransferChoice p q r F z} = m - 2
    exact tripleTransferChoice_r_card hm2 hpr hqr hrF
  · change Nat.Coprime
      (Fintype.card {z : Fin m // p ∈ tripleTransferChoice p q r F z}) m
    rw [tripleTransferChoice_p_card hmpos hpq hpr hpF]
    simp
  · change Nat.Coprime
      (Fintype.card {z : Fin m // q ∈ tripleTransferChoice p q r F z}) m
    rw [tripleTransferChoice_q_card hm2lt hpq hqr hqF]
    simp
  · change Nat.Coprime
      (Fintype.card {z : Fin m // r ∈ tripleTransferChoice p q r F z}) m
    exact tripleTransferChoice_r_coprime hmOdd hm2 hpr hqr hrF

/-- The triple reservoir as a local residue pattern: the active set `{p,q,r}`
gets unit selected degrees, and every other block column has selected degree
divisible by `m`. -/
theorem tripleResiduePattern_nonempty
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q r : Y} (hmOdd : Odd m) (hm3 : 3 <= m)
    (ha : A.card = a) (ha3 : 3 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Nonempty
      (ReplicatedBlockResiduePattern A ({p, q, r} : Finset Y) (a / 2) m) := by
  classical
  have hmpos : 0 < m := by omega
  have hm2lt : 1 < m := by omega
  have hm2 : 2 <= m := by omega
  rcases tripleFiller_exists ha ha3 hp hq hr hpq hpr hqr with
    ⟨F, hFsub, hpF, hqF, hrF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := tripleTransferChoice p q r F
      choose_subset := tripleTransferChoice_subset hFsub hp hq hr
      choose_card := tripleTransferChoice_card ha3 hpF hqF hrF hFcard }
  refine ⟨
    { toChoice := C
      active_coprime := ?_
      inactive_dvd := ?_ }⟩
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyP | hyQ | hyR
    · subst y
      change Nat.Coprime
        (Fintype.card {z : Fin m // p ∈ tripleTransferChoice p q r F z}) m
      rw [tripleTransferChoice_p_card hmpos hpq hpr hpF]
      simp
    · subst y
      change Nat.Coprime
        (Fintype.card {z : Fin m // q ∈ tripleTransferChoice p q r F z}) m
      rw [tripleTransferChoice_q_card hm2lt hpq hqr hqF]
      simp
    · subst y
      change Nat.Coprime
        (Fintype.card {z : Fin m // r ∈ tripleTransferChoice p q r F z}) m
      exact tripleTransferChoice_r_coprime hmOdd hm2 hpr hqr hrF
  · intro y _hyA hyInactive
    have hyp : y ≠ p := by
      intro h
      apply hyInactive
      simp [h]
    have hyq : y ≠ q := by
      intro h
      apply hyInactive
      simp [h]
    have hyr : y ≠ r := by
      intro h
      apply hyInactive
      simp [h]
    change m ∣
      Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z}
    exact tripleTransferChoice_inactive_dvd hyp hyq hyr

theorem tripleResiduePatternWithDegrees_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q r : Y} (hmOdd : Odd m) (hm3 : 3 <= m)
    (ha : A.card = a) (ha3 : 3 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ P : ReplicatedBlockResiduePattern A ({p, q, r} : Finset Y) (a / 2) m,
      replicatedBlockColumnDegree P.toChoice p = 1 ∧
      replicatedBlockColumnDegree P.toChoice q = 1 ∧
      replicatedBlockColumnDegree P.toChoice r = m - 2 := by
  classical
  have hmpos : 0 < m := by omega
  have hm2lt : 1 < m := by omega
  have hm2 : 2 <= m := by omega
  rcases tripleFiller_exists ha ha3 hp hq hr hpq hpr hqr with
    ⟨F, hFsub, hpF, hqF, hrF, hFcard⟩
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := tripleTransferChoice p q r F
      choose_subset := tripleTransferChoice_subset hFsub hp hq hr
      choose_card := tripleTransferChoice_card ha3 hpF hqF hrF hFcard }
  have hpdeg : replicatedBlockColumnDegree C p = 1 := by
    change Fintype.card
      {z : Fin m // p ∈ tripleTransferChoice p q r F z} = 1
    exact tripleTransferChoice_p_card hmpos hpq hpr hpF
  have hqdeg : replicatedBlockColumnDegree C q = 1 := by
    change Fintype.card
      {z : Fin m // q ∈ tripleTransferChoice p q r F z} = 1
    exact tripleTransferChoice_q_card hm2lt hpq hqr hqF
  have hrdeg : replicatedBlockColumnDegree C r = m - 2 := by
    change Fintype.card
      {z : Fin m // r ∈ tripleTransferChoice p q r F z} = m - 2
    exact tripleTransferChoice_r_card hm2 hpr hqr hrF
  refine ⟨
    { toChoice := C
      active_coprime := ?_
      inactive_dvd := ?_ }, hpdeg, hqdeg, hrdeg⟩
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyP | hyQ | hyR
    · subst y
      rw [hpdeg]
      simp
    · subst y
      rw [hqdeg]
      simp
    · subst y
      rw [hrdeg]
      exact coprime_m_sub_two_of_odd hmOdd hm2
  · intro y _hyA hyInactive
    have hyp : y ≠ p := by
      intro h
      apply hyInactive
      simp [h]
    have hyq : y ≠ q := by
      intro h
      apply hyInactive
      simp [h]
    have hyr : y ≠ r := by
      intro h
      apply hyInactive
      simp [h]
    change m ∣
      Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r F z}
    exact tripleTransferChoice_inactive_dvd hyp hyq hyr

theorem tripleResiduePatternWithZModDegrees_exists
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    {p q r : Y} (hmOdd : Odd m) (hm3 : 3 <= m)
    (ha : A.card = a) (ha3 : 3 <= a)
    (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ P : ReplicatedBlockResiduePattern A ({p, q, r} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice p : Nat) : ZMod m) = 1 ∧
      ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) = 1 ∧
      ((replicatedBlockColumnDegree P.toChoice r : Nat) : ZMod m) =
        -(2 : ZMod m) := by
  classical
  have hmpos : 0 < m := by omega
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hm2 : 2 <= m := by omega
  rcases tripleResiduePatternWithDegrees_exists
      (A := A) (a := a) (m := m) (p := p) (q := q) (r := r)
      hmOdd hm3 ha ha3 hp hq hr hpq hpr hqr with
    ⟨P, hpdeg, hqdeg, hrdeg⟩
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hpdeg]
    simp
  · rw [hqdeg]
    simp
  · rw [hrdeg]
    have hsub :
        ((m - 2 : Nat) : ZMod m) = (m : ZMod m) - (2 : ZMod m) := by
      exact Nat.cast_sub hm2
    rw [hsub]
    simp

/-- A partial block choice for one piece of a pair/triple cover.  Unlike
`ReplicatedBlockChoice`, this does not fill the whole row up to `a/2`; it only
chooses inside one active piece.  Disjoint partial choices are the correct
objects to union row-wise before adding the inactive filler. -/
structure PartialBlockChoice
    {Y : Type} [DecidableEq Y] (P : Finset Y) (m : Nat) where
  choose : Fin m -> Finset Y
  choose_subset : forall z, choose z ⊆ P
  choose_card : forall z, (choose z).card = P.card / 2
  selectedDegree : Y -> Nat
  selectedDegree_eq : forall y : Y,
    selectedDegree y =
      Fintype.card {z : Fin m // y ∈ choose z}
  active_coprime : forall y : Y, y ∈ P -> Nat.Coprime (selectedDegree y) m
  inactive_zero : forall y : Y, y ∉ P -> selectedDegree y = 0

theorem partialPairChoice_nonempty
    {Y : Type} [DecidableEq Y] {m : Nat} (hm3 : 3 <= m)
    {p q : Y} (hpq : p ≠ q) :
    Nonempty (PartialBlockChoice ({p, q} : Finset Y) m) := by
  classical
  have hOneLe : 1 <= m := by omega
  let C : PartialBlockChoice ({p, q} : Finset Y) m :=
    { choose := pairTransferChoice p q ∅ 1
      choose_subset := by
        exact pairTransferChoice_subset
          (A := ({p, q} : Finset Y)) (F := ∅) (p := p) (q := q)
          (by simp) (by simp) (by simp)
      choose_card := by
        intro z
        have hz :
            (pairTransferChoice p q (∅ : Finset Y) 1 z).card = 2 / 2 :=
          pairTransferChoice_card
            (a := 2) (u := 1) (m := m) (p := p) (q := q)
            (F := (∅ : Finset Y)) (by norm_num) (by simp) (by simp)
            (by norm_num) z
        simpa [Finset.card_pair hpq] using hz
      selectedDegree := fun y =>
        Fintype.card {z : Fin m // y ∈ pairTransferChoice p q ∅ 1 z}
      selectedDegree_eq := by
        intro y
        rfl
      active_coprime := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with hyP | hyQ
        · subst y
          rw [pairTransferChoice_p_card hOneLe hpq (by simp)]
          exact coprime_m_sub_of_coprime hOneLe (by simp)
        · subst y
          rw [pairTransferChoice_q_card hOneLe hpq (by simp)]
          simp
      inactive_zero := by
        intro y hy
        have hyp : y ≠ p := by
          intro h
          apply hy
          simp [h]
        have hyq : y ≠ q := by
          intro h
          apply hy
          simp [h]
        change
          Fintype.card
            {z : Fin m // y ∈ pairTransferChoice p q (∅ : Finset Y) 1 z} = 0
        calc
          Fintype.card
              {z : Fin m // y ∈ pairTransferChoice p q (∅ : Finset Y) 1 z}
              = Fintype.card {z : Fin m // False} := by
                exact Fintype.card_congr
                  (subtypeEquivOfIff (fun z => by
                    dsimp [pairTransferChoice]
                    by_cases hz : z.val < 1 <;> simp [hz, hyp, hyq]))
          _ = 0 := fintype_card_subtype_false (Fin m) }
  exact ⟨C⟩

theorem card_triple_of_ne {Y : Type} [DecidableEq Y]
    {p q r : Y} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ({p, q, r} : Finset Y).card = 3 := by
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_pair hqr]
  · simp [hpq, hpr]

theorem partialTripleChoice_nonempty
    {Y : Type} [DecidableEq Y] {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {p q r : Y} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Nonempty (PartialBlockChoice ({p, q, r} : Finset Y) m) := by
  classical
  have hmpos : 0 < m := by omega
  have hm2lt : 1 < m := by omega
  have hm2 : 2 <= m := by omega
  let C : PartialBlockChoice ({p, q, r} : Finset Y) m :=
    { choose := tripleTransferChoice p q r ∅
      choose_subset := by
        exact tripleTransferChoice_subset
          (A := ({p, q, r} : Finset Y)) (F := ∅)
          (p := p) (q := q) (r := r)
          (by simp) (by simp) (by simp) (by simp)
      choose_card := by
        intro z
        have hz :
            (tripleTransferChoice p q r (∅ : Finset Y) z).card = 3 / 2 :=
          tripleTransferChoice_card
            (a := 3) (m := m) (p := p) (q := q) (r := r)
            (F := (∅ : Finset Y)) (by norm_num) (by simp) (by simp)
            (by simp) (by norm_num) z
        simpa [card_triple_of_ne hpq hpr hqr] using hz
      selectedDegree := fun y =>
        Fintype.card {z : Fin m // y ∈ tripleTransferChoice p q r ∅ z}
      selectedDegree_eq := by
        intro y
        rfl
      active_coprime := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with hyP | hyQ | hyR
        · subst y
          rw [tripleTransferChoice_p_card hmpos hpq hpr (by simp)]
          simp
        · subst y
          rw [tripleTransferChoice_q_card hm2lt hpq hqr (by simp)]
          simp
        · subst y
          exact tripleTransferChoice_r_coprime hmOdd hm2 hpr hqr (by simp)
      inactive_zero := by
        intro y hy
        have hyp : y ≠ p := by
          intro h
          apply hy
          simp [h]
        have hyq : y ≠ q := by
          intro h
          apply hy
          simp [h]
        have hyr : y ≠ r := by
          intro h
          apply hy
          simp [h]
        change
          Fintype.card
            {z : Fin m // y ∈ tripleTransferChoice p q r (∅ : Finset Y) z} = 0
        calc
          Fintype.card
              {z : Fin m // y ∈ tripleTransferChoice p q r (∅ : Finset Y) z}
              = Fintype.card {z : Fin m // False} := by
                exact Fintype.card_congr
                  (subtypeEquivOfIff (fun z => by
                    dsimp [tripleTransferChoice]
                    by_cases h0 : z.val = 0
                    · simp [h0, hyp]
                    · by_cases h1 : z.val = 1
                      · simp [h1, hyq]
                      · simp [h0, h1, hyr]))
          _ = 0 := fintype_card_subtype_false (Fin m) }
  exact ⟨C⟩

theorem partialChoice_of_pairTriple_piece
    {Y : Type} [DecidableEq Y] {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {P : Finset Y} (hP : P.card = 2 ∨ P.card = 3) :
    Nonempty (PartialBlockChoice P m) := by
  classical
  rcases hP with hP | hP
  · rcases Finset.card_eq_two.mp hP with ⟨p, q, hpq, hPset⟩
    rw [hPset]
    exact partialPairChoice_nonempty hm3 hpq
  · rcases Finset.card_eq_three.mp hP with
      ⟨p, q, r, hpq, hpr, hqr, hPset⟩
    rw [hPset]
    exact partialTripleChoice_nonempty hmOdd hm3 hpq hpr hqr

theorem disjoint_finsetListUnion_of_forall
    {Y : Type} [DecidableEq Y] {P : Finset Y} {Ps : List (Finset Y)}
    (h : forall Q : Finset Y, Q ∈ Ps -> Disjoint P Q) :
    Disjoint P (finsetListUnion Ps) := by
  induction Ps with
  | nil =>
      simp [finsetListUnion]
  | cons Q Qs ih =>
      rw [finsetListUnion_cons, Finset.disjoint_union_right]
      constructor
      · exact h Q (by simp)
      · exact ih (by
          intro R hR
          exact h R (by simp [hR]))

/-- A raw partial choice for a list of disjoint pair/triple pieces.  The row
size is the sum of the piece row sizes, not yet rewritten as
`(finsetListUnion Ps).card / 2`; that rewrite is supplied by
`PairTripleCover.row_card_sum`. -/
structure PartialListChoice
    {Y : Type} [DecidableEq Y] (Ps : List (Finset Y)) (m : Nat) where
  choose : Fin m -> Finset Y
  choose_subset : forall z, choose z ⊆ finsetListUnion Ps
  choose_card : forall z, (choose z).card =
    (Ps.map fun P => P.card / 2).sum
  selectedDegree : Y -> Nat
  selectedDegree_eq : forall y : Y,
    selectedDegree y =
      Fintype.card {z : Fin m // y ∈ choose z}
  active_coprime :
    forall y : Y, y ∈ finsetListUnion Ps -> Nat.Coprime (selectedDegree y) m
  inactive_zero :
    forall y : Y, y ∉ finsetListUnion Ps -> selectedDegree y = 0

theorem partialListChoice_nil
    {Y : Type} [DecidableEq Y] {m : Nat} :
    Nonempty (PartialListChoice ([] : List (Finset Y)) m) := by
  classical
  refine ⟨
    { choose := fun _ => ∅
      choose_subset := ?_
      choose_card := ?_
      selectedDegree := fun _ => 0
      selectedDegree_eq := ?_
      active_coprime := ?_
      inactive_zero := ?_ }⟩
  · intro z
    simp [finsetListUnion]
  · intro z
    simp
  · intro y
    calc
      0 = Fintype.card {z : Fin m // False} := by
        rw [fintype_card_subtype_false]
      _ = Fintype.card {z : Fin m // y ∈ (∅ : Finset Y)} := by
        simp
  · intro y hy
    simp [finsetListUnion] at hy
  · intro y hy
    rfl

theorem partialListChoice_cons
    {Y : Type} [DecidableEq Y] {m : Nat}
    {P : Finset Y} {Ps : List (Finset Y)}
    (hPU : Disjoint P (finsetListUnion Ps))
    (CP : PartialBlockChoice P m)
    (CL : PartialListChoice Ps m) :
    Nonempty (PartialListChoice (P :: Ps) m) := by
  classical
  let C : PartialListChoice (P :: Ps) m :=
    { choose := fun z => CP.choose z ∪ CL.choose z
      choose_subset := by
        intro z y hy
        rw [Finset.mem_union] at hy
        rcases hy with hyP | hyL
        · exact Finset.mem_union.mpr (Or.inl (CP.choose_subset z hyP))
        · exact Finset.mem_union.mpr (Or.inr (CL.choose_subset z hyL))
      choose_card := by
        intro z
        have hDisj : Disjoint (CP.choose z) (CL.choose z) :=
          (hPU.mono_left (CP.choose_subset z)).mono_right (CL.choose_subset z)
        rw [Finset.card_union_of_disjoint hDisj, CP.choose_card z,
          CL.choose_card z]
        simp
      selectedDegree := fun y =>
        Fintype.card {z : Fin m // y ∈ CP.choose z ∪ CL.choose z}
      selectedDegree_eq := by
        intro y
        rfl
      active_coprime := by
        intro y hy
        rw [finsetListUnion_cons, Finset.mem_union] at hy
        rcases hy with hyP | hyU
        · have hyNotU : y ∉ finsetListUnion Ps := by
            intro hyU
            exact (Finset.disjoint_left.mp hPU) hyP hyU
          have hEq :
              Fintype.card
                  {z : Fin m // y ∈ CP.choose z ∪ CL.choose z} =
                CP.selectedDegree y := by
            rw [CP.selectedDegree_eq y]
            exact Fintype.card_congr
              (subtypeEquivOfIff (fun z => by
                have hyNotCL : y ∉ CL.choose z := by
                  intro hyCL
                  exact hyNotU (CL.choose_subset z hyCL)
                simp [hyNotCL]))
          rw [hEq]
          exact CP.active_coprime y hyP
        · have hyNotP : y ∉ P := by
            intro hyP
            exact (Finset.disjoint_left.mp hPU) hyP hyU
          have hEq :
              Fintype.card
                  {z : Fin m // y ∈ CP.choose z ∪ CL.choose z} =
                CL.selectedDegree y := by
            rw [CL.selectedDegree_eq y]
            exact Fintype.card_congr
              (subtypeEquivOfIff (fun z => by
                have hyNotCP : y ∉ CP.choose z := by
                  intro hyCP
                  exact hyNotP (CP.choose_subset z hyCP)
                simp [hyNotCP]))
          rw [hEq]
          exact CL.active_coprime y hyU
      inactive_zero := by
        intro y hy
        rw [finsetListUnion_cons, Finset.mem_union] at hy
        have hyP : y ∉ P := by
          intro hyP
          exact hy (Or.inl hyP)
        have hyU : y ∉ finsetListUnion Ps := by
          intro hyU
          exact hy (Or.inr hyU)
        change
          Fintype.card {z : Fin m // y ∈ CP.choose z ∪ CL.choose z} = 0
        calc
          Fintype.card {z : Fin m // y ∈ CP.choose z ∪ CL.choose z}
              = Fintype.card {z : Fin m // False} := by
                exact Fintype.card_congr
                  (subtypeEquivOfIff (fun z => by
                    have hyNotCP : y ∉ CP.choose z := by
                      intro hyCP
                      exact hyP (CP.choose_subset z hyCP)
                    have hyNotCL : y ∉ CL.choose z := by
                      intro hyCL
                      exact hyU (CL.choose_subset z hyCL)
                    simp [hyNotCP, hyNotCL]))
          _ = 0 := fintype_card_subtype_false (Fin m) }
  exact ⟨C⟩

theorem partialListChoice_of_pairTriplePieces
    {Y : Type} [DecidableEq Y] {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Ps : List (Finset Y)}
    (hCards : forall P : Finset Y, P ∈ Ps -> P.card = 2 ∨ P.card = 3)
    (hDisj : Ps.Pairwise Disjoint) :
    Nonempty (PartialListChoice Ps m) := by
  classical
  induction Ps with
  | nil =>
      exact partialListChoice_nil
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hDisj
      have hHeadCards : P.card = 2 ∨ P.card = 3 :=
        hCards P (by simp)
      have hTailCards :
          forall Q : Finset Y, Q ∈ Ps -> Q.card = 2 ∨ Q.card = 3 := by
        intro Q hQ
        exact hCards Q (by simp [hQ])
      rcases partialChoice_of_pairTriple_piece hmOdd hm3 hHeadCards with ⟨CP⟩
      rcases ih hTailCards hDisj.2 with ⟨CL⟩
      have hPU : Disjoint P (finsetListUnion Ps) :=
        disjoint_finsetListUnion_of_forall hDisj.1
      exact partialListChoice_cons hPU CP CL

theorem partialChoice_of_pairTripleCover
    {Y : Type} [DecidableEq Y] {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {S : Finset Y} (C : PairTripleCover S) :
    Nonempty (PartialBlockChoice S m) := by
  classical
  rcases partialListChoice_of_pairTriplePieces hmOdd hm3
      C.piece_card C.pairwise_disjoint with ⟨L⟩
  let P : PartialBlockChoice S m :=
    { choose := L.choose
      choose_subset := by
        intro z
        simpa [C.cover_eq] using L.choose_subset z
      choose_card := by
        intro z
        rw [L.choose_card, C.row_card_sum]
      selectedDegree := L.selectedDegree
      selectedDegree_eq := L.selectedDegree_eq
      active_coprime := by
        intro y hy
        exact L.active_coprime y (by simpa [C.cover_eq] using hy)
      inactive_zero := by
        intro y hy
        exact L.inactive_zero y (by
          intro hyU
          exact hy (by simpa [C.cover_eq] using hyU)) }
  exact ⟨P⟩

theorem partialBlockChoice_empty
    {Y : Type} [DecidableEq Y] {m : Nat} :
    Nonempty (PartialBlockChoice (∅ : Finset Y) m) := by
  classical
  refine ⟨
    { choose := fun _ => ∅
      choose_subset := ?_
      choose_card := ?_
      selectedDegree := fun _ => 0
      selectedDegree_eq := ?_
      active_coprime := ?_
      inactive_zero := ?_ }⟩
  · intro z
    simp
  · intro z
    simp
  · intro y
    calc
      0 = Fintype.card {z : Fin m // False} := by
        rw [fintype_card_subtype_false]
      _ = Fintype.card {z : Fin m // y ∈ (∅ : Finset Y)} := by
        simp
  · intro y hy
    simp at hy
  · intro y hy
    rfl

theorem replicatedBlockResiduePattern_of_partialChoice
    {Y : Type} [DecidableEq Y] {m a : Nat} {A S : Finset Y}
    (ha : A.card = a) (hSsub : S ⊆ A)
    (PC : PartialBlockChoice S m) :
    Nonempty (ReplicatedBlockResiduePattern A S (a / 2) m) := by
  classical
  rcases subsetFiller_exists ha hSsub with ⟨F, hFsub, hFcard⟩
  have hFsubA : F ⊆ A := by
    intro y hy
    exact (Finset.mem_sdiff.mp (hFsub hy)).1
  have hSdisjF : Disjoint S F := by
    rw [Finset.disjoint_left]
    intro y hyS hyF
    exact (Finset.mem_sdiff.mp (hFsub hyF)).2 hyS
  have hHalfLe : S.card / 2 <= a / 2 := by
    rw [← ha]
    exact Nat.div_le_div_right (Finset.card_le_card hSsub)
  let C : ReplicatedBlockChoice A (a / 2) m :=
    { choose := fun z => PC.choose z ∪ F
      choose_subset := by
        intro z y hy
        rw [Finset.mem_union] at hy
        rcases hy with hyPC | hyF
        · exact hSsub (PC.choose_subset z hyPC)
        · exact hFsubA hyF
      choose_card := by
        intro z
        have hDisj : Disjoint (PC.choose z) F :=
          hSdisjF.mono_left (PC.choose_subset z)
        rw [Finset.card_union_of_disjoint hDisj, PC.choose_card z, hFcard]
        omega }
  refine ⟨
    { toChoice := C
      active_coprime := ?_
      inactive_dvd := ?_ }⟩
  · intro y hyS
    have hyNotF : y ∉ F := by
      intro hyF
      exact (Finset.mem_sdiff.mp (hFsub hyF)).2 hyS
    have hEq : replicatedBlockColumnDegree C y = PC.selectedDegree y := by
      change
        Fintype.card {z : Fin m // y ∈ PC.choose z ∪ F} =
          PC.selectedDegree y
      rw [PC.selectedDegree_eq y]
      exact Fintype.card_congr
        (subtypeEquivOfIff (fun z => by
          simp [hyNotF]))
    rw [hEq]
    exact PC.active_coprime y hyS
  · intro y _hyA hyNotS
    by_cases hyF : y ∈ F
    · have hEq : replicatedBlockColumnDegree C y = m := by
        change Fintype.card {z : Fin m // y ∈ PC.choose z ∪ F} = m
        calc
          Fintype.card {z : Fin m // y ∈ PC.choose z ∪ F}
              = Fintype.card {z : Fin m // True} := by
                exact Fintype.card_congr
                  (subtypeEquivOfIff (fun z => by
                    simp [hyF]))
          _ = m := by
            rw [fintype_card_subtype_true]
            simp
      rw [hEq]
    · have hEq : replicatedBlockColumnDegree C y = 0 := by
        change Fintype.card {z : Fin m // y ∈ PC.choose z ∪ F} = 0
        calc
          Fintype.card {z : Fin m // y ∈ PC.choose z ∪ F}
              = Fintype.card {z : Fin m // False} := by
                exact Fintype.card_congr
                  (subtypeEquivOfIff (fun z => by
                    have hyNotPC : y ∉ PC.choose z := by
                      intro hyPC
                      exact hyNotS (PC.choose_subset z hyPC)
                    simp [hyF, hyNotPC]))
          _ = 0 := fintype_card_subtype_false (Fin m)
      rw [hEq]
      exact dvd_zero m

theorem replicatedBlockResiduePattern_empty_nonempty
    {Y : Type} [DecidableEq Y] {A : Finset Y} {a m : Nat}
    (ha : A.card = a) :
    Nonempty (ReplicatedBlockResiduePattern A ∅ (a / 2) m) := by
  classical
  rcases (partialBlockChoice_empty :
    Nonempty (PartialBlockChoice (∅ : Finset Y) m)) with ⟨PC⟩
  exact replicatedBlockResiduePattern_of_partialChoice ha (by simp) PC

theorem rootedBranchResiduePatternUnitAssignmentGoal_of_componentBlock
    (hComp : RootedBranchComponentBlockResiduePatternUnitAssignmentGoal) :
    RootedBranchResiduePatternUnitAssignmentGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
    C ρ hρ T hTle hTtree α0 hα0 hRootAlpha y0 hy0 hy0ρ hAlphaY
  letI := instY
  letI := instDec
  letI := instBlock
  classical
  rcases hComp hmOdd hm3 ha2 A hA hNoIso C ρ hρ T hTle hTtree
      α0 hα0 hRootAlpha y0 hy0 hy0ρ hAlphaY with
    ⟨SComp, PComp, hSComp_subset, hUnitComp⟩
  let S : Block -> Finset Y := fun α =>
    if hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp then
      SComp ⟨α, hα⟩
    else
      ∅
  let P : forall α : Block,
      ReplicatedBlockResiduePattern (A α) (S α) (a / 2) m := by
    intro α
    by_cases hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp
    · have hαeq :
          (replicatedIncidenceGraph A).connectedComponentMk
              (Sum.inr α : IncidenceVertex Y Block) = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C
          (Sum.inr α : IncidenceVertex Y Block)).mp hα
      refine
        { toChoice := (PComp ⟨α, hα⟩).toChoice
          active_coprime := ?_
          inactive_dvd := ?_ }
      · intro y hyS
        have hySComp : y ∈ SComp ⟨α, hα⟩ := by
          simpa [S, hαeq] using hyS
        exact (PComp ⟨α, hα⟩).active_coprime y hySComp
      · intro y hyA hyS
        have hySComp : y ∉ SComp ⟨α, hα⟩ := by
          intro hy
          exact hyS (by simpa [S, hαeq] using hy)
        exact (PComp ⟨α, hα⟩).inactive_dvd y hyA hySComp
    · have hαeq :
          (replicatedIncidenceGraph A).connectedComponentMk
              (Sum.inr α : IncidenceVertex Y Block) ≠ C := by
        intro hEq
        exact hα ((SimpleGraph.ConnectedComponent.mem_supp_iff C
          (Sum.inr α : IncidenceVertex Y Block)).mpr hEq)
      let P0 : ReplicatedBlockResiduePattern (A α) ∅ (a / 2) m :=
        Classical.choice
          (replicatedBlockResiduePattern_empty_nonempty
            (A := A α) (a := a) (m := m) (hA α))
      refine
        { toChoice := P0.toChoice
          active_coprime := ?_
          inactive_dvd := ?_ }
      · intro y hyS
        have hyFalse : False := by
          simp [S, hαeq] at hyS
        exact False.elim hyFalse
      · intro y hyA _hyS
        exact P0.inactive_dvd y hyA (by simp)
  refine ⟨S, P, ?_, ?_, ?_⟩
  · intro α
    by_cases hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp
    · have hαeq :
          (replicatedIncidenceGraph A).connectedComponentMk
              (Sum.inr α : IncidenceVertex Y Block) = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C
          (Sum.inr α : IncidenceVertex Y Block)).mp hα
      simpa [S, hαeq] using hSComp_subset ⟨α, hα⟩
    · have hαeq :
          (replicatedIncidenceGraph A).connectedComponentMk
              (Sum.inr α : IncidenceVertex Y Block) ≠ C := by
        intro hEq
        exact hα ((SimpleGraph.ConnectedComponent.mem_supp_iff C
          (Sum.inr α : IncidenceVertex Y Block)).mpr hEq)
      simp [S, hαeq]
  · intro α hα
    have hαeq :
        (replicatedIncidenceGraph A).connectedComponentMk
            (Sum.inr α : IncidenceVertex Y Block) ≠ C := by
      intro hEq
      exact hα ((SimpleGraph.ConnectedComponent.mem_supp_iff C
        (Sum.inr α : IncidenceVertex Y Block)).mpr hEq)
    simp [S, hαeq]
  · intro y hy
    let globalTerm : Block -> ZMod m := fun α =>
      if y ∈ S α then
        ((replicatedBlockColumnDegree (P α).toChoice y : Nat) : ZMod m)
      else 0
    let compTerm : ComponentBlock A C -> ZMod m := fun α =>
      if y ∈ SComp α then
        ((replicatedBlockColumnDegree (PComp α).toChoice y : Nat) : ZMod m)
      else 0
    let fullCompTerm : Block -> ZMod m := fun α =>
      if hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp then
        compTerm ⟨α, hα⟩
      else 0
    have hTermEq : forall α : Block, globalTerm α = fullCompTerm α := by
      intro α
      by_cases hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp
      · have hαeq :
            (replicatedIncidenceGraph A).connectedComponentMk
                (Sum.inr α : IncidenceVertex Y Block) = C :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff C
            (Sum.inr α : IncidenceVertex Y Block)).mp hα
        simp [globalTerm, fullCompTerm, compTerm, S, P, hαeq]
      · have hαeq :
            (replicatedIncidenceGraph A).connectedComponentMk
                (Sum.inr α : IncidenceVertex Y Block) ≠ C := by
          intro hEq
          exact hα ((SimpleGraph.ConnectedComponent.mem_supp_iff C
            (Sum.inr α : IncidenceVertex Y Block)).mpr hEq)
        simp [globalTerm, fullCompTerm, S, hαeq]
    have hSumEq :
        (∑ α : Block, globalTerm α) =
          ∑ α : Block, fullCompTerm α := by
      apply Finset.sum_congr rfl
      intro α _hα
      exact hTermEq α
    have hSubtype :
        (∑ α : Block, fullCompTerm α) =
          ∑ α : ComponentBlock A C, compTerm α := by
      let p : Block -> Prop := fun α =>
        (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp
      have hFilter :
          (∑ α : Block, fullCompTerm α) =
            ∑ α ∈ (Finset.univ.filter p), fullCompTerm α := by
        symm
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro α _hα
        by_cases hα : p α
        · have hαeq :
              (replicatedIncidenceGraph A).connectedComponentMk
                  (Sum.inr α : IncidenceVertex Y Block) = C :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff C
              (Sum.inr α : IncidenceVertex Y Block)).mp hα
          simp [fullCompTerm, hαeq]
        · have hαeq :
              (replicatedIncidenceGraph A).connectedComponentMk
                  (Sum.inr α : IncidenceVertex Y Block) ≠ C := by
            intro hEq
            exact hα ((SimpleGraph.ConnectedComponent.mem_supp_iff C
              (Sum.inr α : IncidenceVertex Y Block)).mpr hEq)
          simp [fullCompTerm, hαeq]
      have hFilter' :
          (∑ α : Block, fullCompTerm α) =
            ∑ α ∈ (Finset.univ.filter
              (fun α : Block =>
                (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)),
              fullCompTerm α := by
        simpa [p] using hFilter
      have h := Finset.sum_subtype
        (F := componentBlockFintype (A := A) C)
        (s := (Finset.univ.filter
          (fun α : Block =>
            (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)))
        (p := fun α : Block =>
          (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)
        (h := fun α => by simp)
        (f := fullCompTerm)
      have hSubToComp :
          (∑ α : ComponentBlock A C, fullCompTerm α.1) =
            ∑ α : ComponentBlock A C, compTerm α := by
        apply Finset.sum_congr rfl
        intro α _hα
        have hαeq :
            (replicatedIncidenceGraph A).connectedComponentMk
                (Sum.inr α.1 : IncidenceVertex Y Block) = C :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff C
            (Sum.inr α.1 : IncidenceVertex Y Block)).mp α.2
        simp [fullCompTerm, compTerm, hαeq]
      exact hFilter'.trans (h.trans hSubToComp)
    change IsUnit (∑ α : Block, globalTerm α)
    rw [hSumEq, hSubtype]
    exact hUnitComp y hy

/-- Local arbitrary-active-set target for the replicated shortcut.  This is
the next assembly obligation after the pair/triple cover theorem: for every
active subset `S` of a block `A`, build one block choice whose active columns
receive unit selected degree and whose inactive columns receive zero residue
modulo `m`. -/
def LocalSubsetResiduePatternGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m ->
    forall {Y : Type} [DecidableEq Y],
      forall {A S : Finset Y},
        A.card = a -> S ⊆ A -> 2 <= S.card ->
          Nonempty (ReplicatedBlockResiduePattern A S (a / 2) m)

/-- The remaining local assembly obligation once an active set has been
partitioned into pair/triple pieces. -/
def PairTripleCoverAssemblyGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m ->
    forall {Y : Type} [DecidableEq Y],
      forall {A S : Finset Y},
        A.card = a -> S ⊆ A -> PairTripleCover S ->
          Nonempty (ReplicatedBlockResiduePattern A S (a / 2) m)

theorem pairTripleCoverAssemblyGoal_closed :
    PairTripleCoverAssemblyGoal := by
  intro m a hmOdd hm3 Y inst A S ha hSsub C
  letI := inst
  rcases partialChoice_of_pairTripleCover hmOdd hm3 C with ⟨PC⟩
  exact replicatedBlockResiduePattern_of_partialChoice ha hSsub PC

theorem localSubsetResiduePatternGoal_of_pairTripleCoverAssembly
    (hAssembly : PairTripleCoverAssemblyGoal) :
    LocalSubsetResiduePatternGoal := by
  intro m a hmOdd hm3 Y inst A S ha hSsub hScard
  letI := inst
  rcases pairTripleCover_exists hScard with ⟨C⟩
  exact hAssembly hmOdd hm3 ha hSsub C

theorem localSubsetResiduePatternGoal_closed :
    LocalSubsetResiduePatternGoal :=
  localSubsetResiduePatternGoal_of_pairTripleCoverAssembly
    pairTripleCoverAssemblyGoal_closed

theorem rootBranchPairResiduePattern_nonempty
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {ρ y : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a) (hyρ : y ≠ ρ)
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩)
    (hAlphaY : T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩) :
    Nonempty
      (ReplicatedBlockResiduePattern (A α) ({ρ, y} : Finset Y) (a / 2) m) := by
  classical
  have hρA : ρ ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hRootAlpha
    simpa [replicatedIncidenceGraph] using hG
  have hyA : y ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hAlphaY
    simpa [replicatedIncidenceGraph] using hG
  have hSub : ({ρ, y} : Finset Y) ⊆ A α := by
    intro z hz
    simp at hz
    rcases hz with rfl | rfl
    · exact hρA
    · exact hyA
  have hCard : 2 <= ({ρ, y} : Finset Y).card := by
    rw [Finset.card_pair hyρ.symm]
  exact localSubsetResiduePatternGoal_closed hmOdd hm3 ha hSub hCard

theorem incidenceRootBlockResiduePattern_nonempty
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {ρ : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a)
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩)
    (hChildNonempty :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα).Nonempty) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α)
        (insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα))
        (a / 2) m) := by
  classical
  have hρA : ρ ∈ A α := by
    have hG := replicatedIncidenceTree_adj_val hTle hRootAlpha
    simpa [replicatedIncidenceGraph] using hG
  have hSub :
      insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα) ⊆ A α := by
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hyChild
    · exact hρA
    · exact incidenceYChildren_subset hTle hyChild
  have hρnot :
      ρ ∉ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα :=
    root_not_mem_incidenceYChildren
  have hCard :
      2 <= (insert ρ
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα)).card := by
    rw [Finset.card_insert_of_notMem hρnot]
    have hpos :
        0 < (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα).card :=
      Finset.card_pos.mpr hChildNonempty
    omega
  exact localSubsetResiduePatternGoal_closed hmOdd hm3 ha hSub hCard

theorem incidenceRootBlockResiduePattern_nonempty_of_branch
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a)
    (hRootAlpha : T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α, hα⟩)
    (hyρ : y ≠ ρ)
    (hAlphaY : T.Adj ⟨Sum.inr α, hα⟩ ⟨Sum.inl y, hy⟩) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α)
        (insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα))
        (a / 2) m) := by
  classical
  have hyChild :
      y ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα :=
    incidenceYChildren_mem_of_root_branch
      (A := A) hTle hTtree hRootAlpha hyρ hAlphaY
  exact
    incidenceRootBlockResiduePattern_nonempty
      hmOdd hm3 hTle ha hRootAlpha ⟨y, hyChild⟩

theorem incidenceMultiChildResiduePattern_nonempty
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a)
    (hMulti : 2 <= (incidenceYChildren T root α hα).card) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α) (incidenceYChildren T root α hα) (a / 2) m) := by
  exact localSubsetResiduePatternGoal_closed hmOdd hm3 ha
    (incidenceYChildren_subset hTle) hMulti

theorem finset_card_zero_or_one_or_two_le
    {α : Type} (S : Finset α) :
    S.card = 0 ∨ S.card = 1 ∨ 2 <= S.card := by
  omega

theorem incidenceZeroOrMultiChildResiduePattern_nonempty
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a)
    (hZeroOrMulti :
      (incidenceYChildren T root α hα).card = 0 ∨
        2 <= (incidenceYChildren T root α hα).card) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α) (incidenceYChildren T root α hα) (a / 2) m) := by
  classical
  rcases hZeroOrMulti with hZero | hMulti
  · have hEmpty : incidenceYChildren T root α hα = ∅ :=
      Finset.card_eq_zero.mp hZero
    rw [hEmpty]
    exact replicatedBlockResiduePattern_empty_nonempty ha
  · exact incidenceMultiChildResiduePattern_nonempty
      hmOdd hm3 hTle ha hMulti

theorem incidenceNonUnaryChildResiduePattern_nonempty
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a)
    (hNotUnary : (incidenceYChildren T root α hα).card ≠ 1) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α) (incidenceYChildren T root α hα) (a / 2) m) := by
  classical
  have hSplit := finset_card_zero_or_one_or_two_le
    (incidenceYChildren T root α hα)
  rcases hSplit with hZero | hOne | hMulti
  · exact incidenceZeroOrMultiChildResiduePattern_nonempty
      hmOdd hm3 hTle ha (Or.inl hZero)
  · exact False.elim (hNotUnary hOne)
  · exact incidenceZeroOrMultiChildResiduePattern_nonempty
      hmOdd hm3 hTle ha (Or.inr hMulti)

theorem incidenceUnaryChild_singleton
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hUnary : (incidenceYChildren T root α hα).card = 1) :
    ∃ y : Y, incidenceYChildren T root α hα = {y} :=
  Finset.card_eq_one.mp hUnary

theorem incidenceYChildren_eq_of_card_one
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} {root : C} {α : Block}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hUnary : (incidenceYChildren T root α hα).card = 1)
    {p q : Y}
    (hp : p ∈ incidenceYChildren T root α hα)
    (hq : q ∈ incidenceYChildren T root α hα) :
    p = q := by
  classical
  rcases incidenceUnaryChild_singleton (A := A) hUnary with ⟨z, hz⟩
  rw [hz] at hp hq
  have hpz : p = z := by
    simpa using hp
  have hqz : q = z := by
    simpa using hq
  rw [hpz, hqz]

theorem incidenceUnaryBlockResiduePatternWithZModUnit_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {α : Block}
    (hUnaryBlock : α ∈ incidenceUnaryBlockChildren T root y hy)
    (u : ZMod m) (hu : IsUnit u) :
    ∃ q : Y,
    ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
    ∃ hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp,
    ∃ P : ReplicatedBlockResiduePattern
        (A α) ({y, q} : Finset Y) (a / 2) m,
      q ∈ incidenceYChildren T root α hα ∧
      ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) = u ∧
      ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) = -u := by
  classical
  rcases (mem_incidenceUnaryBlockChildren T root y hy α).mp hUnaryBlock with
    ⟨hα, hParent, hUnary⟩
  rcases incidenceUnaryChild_singleton (A := A) hUnary with ⟨q, hqSet⟩
  have hqChild : q ∈ incidenceYChildren T root α hα := by
    rw [hqSet]
    simp
  rcases (mem_incidenceYChildren T root α hα q).mp hqChild with
    ⟨hq, hChild⟩
  rcases incidenceUnaryPairResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos (hA α) ha2 hParent hChild u hu with
    ⟨P, hqdeg, hydeg⟩
  exact ⟨q, hq, hα, P, hqChild, hqdeg, hydeg⟩

theorem localSubsetResiduePattern_card_two
    {m a : Nat} (hm3 : 3 <= m)
    {Y : Type} [DecidableEq Y] {A S : Finset Y}
    (ha : A.card = a) (hSsub : S ⊆ A) (hScard : S.card = 2) :
    Nonempty (ReplicatedBlockResiduePattern A S (a / 2) m) := by
  classical
  rcases Finset.card_eq_two.mp hScard with ⟨p, q, hpq, hS⟩
  have hpA : p ∈ A := by
    apply hSsub
    rw [hS]
    simp
  have hqA : q ∈ A := by
    apply hSsub
    rw [hS]
    simp
  have ha2 : 2 <= a := by
    have hle : S.card <= A.card := Finset.card_le_card hSsub
    omega
  have hmpos : 0 < m := by omega
  rw [hS]
  exact pairResiduePattern_nonempty hmpos ha ha2 hpA hqA hpq

theorem localSubsetResiduePattern_card_three
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y : Type} [DecidableEq Y] {A S : Finset Y}
    (ha : A.card = a) (hSsub : S ⊆ A) (hScard : S.card = 3) :
    Nonempty (ReplicatedBlockResiduePattern A S (a / 2) m) := by
  classical
  rcases Finset.card_eq_three.mp hScard with
    ⟨p, q, r, hpq, hpr, hqr, hS⟩
  have hpA : p ∈ A := by
    apply hSsub
    rw [hS]
    simp
  have hqA : q ∈ A := by
    apply hSsub
    rw [hS]
    simp
  have hrA : r ∈ A := by
    apply hSsub
    rw [hS]
    simp
  have ha3 : 3 <= a := by
    have hle : S.card <= A.card := Finset.card_le_card hSsub
    omega
  rw [hS]
  exact tripleResiduePattern_nonempty
    hmOdd hm3 ha ha3 hpA hqA hrA hpq hpr hqr

/-! ### Unit-splitting arithmetic for the tree assignment -/

theorem zmod_primePower_isUnit_of_cast_ne_zero
    {p e : Nat} (hp : Nat.Prime p) (he : e ≠ 0)
    (x : ZMod (p ^ e))
    (hx : (ZMod.castHom (dvd_pow_self p he) (ZMod p) x) ≠ 0) :
    IsUnit x := by
  classical
  have hq0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  haveI : NeZero (p ^ e) := ⟨hq0⟩
  have hnotdvd : ¬ p ∣ x.val := by
    intro hd
    apply hx
    calc
      ZMod.castHom (dvd_pow_self p he) (ZMod p) x
          = ZMod.castHom (dvd_pow_self p he) (ZMod p)
              ((x.val : Nat) : ZMod (p ^ e)) := by
            rw [ZMod.natCast_zmod_val x]
      _ = ((x.val : Nat) : ZMod p) := by
            rw [ZMod.castHom_apply]
            exact ZMod.cast_natCast (dvd_pow_self p he) x.val
      _ = 0 := (ZMod.natCast_eq_zero_iff x.val p).mpr hd
  have hcop : Nat.Coprime x.val (p ^ e) :=
    hp.coprime_pow_of_not_dvd hnotdvd
  have hxunit_nat : IsUnit ((x.val : Nat) : ZMod (p ^ e)) :=
    (ZMod.isUnit_iff_coprime x.val (p ^ e)).mpr hcop
  simpa [ZMod.natCast_zmod_val x] using hxunit_nat

theorem zmod_primePower_unit_split
    {p e : Nat} (hp : Nat.Prime p) (hpne2 : p ≠ 2) (he : e ≠ 0)
    (x : ZMod (p ^ e)) :
    ∃ u : ZMod (p ^ e), IsUnit u ∧ IsUnit (x - u) := by
  classical
  let f : ZMod (p ^ e) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p he) (ZMod p)
  have hp3 : 3 <= p := by
    have hp2le : 2 <= p := hp.two_le
    omega
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hone_ne_two : (1 : ZMod p) ≠ 2 := by
    intro h
    have hval := congrArg ZMod.val h
    have htwoVal : ZMod.val (2 : ZMod p) = 2 := by
      change (((2 : Nat) : ZMod p).val = 2)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [ZMod.val_one p, htwoVal] at hval
    omega
  have htwoUnit : IsUnit (2 : ZMod (p ^ e)) := by
    have hpOdd : Odd p := hp.odd_of_ne_two hpne2
    have hOddPow : Odd (p ^ e) := hpOdd.pow
    have hcop : Nat.Coprime 2 (p ^ e) :=
      Nat.coprime_two_left.mpr hOddPow
    exact (ZMod.isUnit_iff_coprime 2 (p ^ e)).mpr hcop
  have hf_one : f (1 : ZMod (p ^ e)) = (1 : ZMod p) :=
    map_one f
  have hf_two : f (2 : ZMod (p ^ e)) = (2 : ZMod p) := by
    change (ZMod.castHom (dvd_pow_self p he) (ZMod p))
        (((2 : Nat) : ZMod (p ^ e))) = ((2 : Nat) : ZMod p)
    rw [ZMod.castHom_apply]
    exact ZMod.cast_natCast (dvd_pow_self p he) 2
  by_cases hx1 : f x = 1
  · refine ⟨2, htwoUnit, ?_⟩
    apply zmod_primePower_isUnit_of_cast_ne_zero hp he
    intro hzero
    have hx2 : f x = (2 : ZMod p) := by
      have hmap : f (x - 2) = f x - f (2 : ZMod (p ^ e)) :=
        RingHom.map_sub f x 2
      rw [hmap, hf_two] at hzero
      exact sub_eq_zero.mp hzero
    exact hone_ne_two (hx1.symm.trans hx2)
  · refine ⟨1, isUnit_one, ?_⟩
    apply zmod_primePower_isUnit_of_cast_ne_zero hp he
    intro hzero
    apply hx1
    have hmap : f (x - 1) = f x - f (1 : ZMod (p ^ e)) :=
      RingHom.map_sub f x 1
    rw [hmap, hf_one] at hzero
    exact sub_eq_zero.mp hzero

theorem zmod_unit_split_of_odd
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (x : ZMod m) :
    ∃ u : ZMod m, IsUnit u ∧ IsUnit (x - u) := by
  classical
  have hm0 : m ≠ 0 := by omega
  let E := ZMod.equivPi m hm0
  have hsplit : forall p : m.primeFactors,
      ∃ u : ZMod ((p : Nat) ^ m.factorization (p : Nat)),
        IsUnit u ∧ IsUnit ((E x) p - u) := by
    intro p
    have hp : Nat.Prime (p : Nat) :=
      Nat.prime_of_mem_primeFactors p.property
    have hdvd : (p : Nat) ∣ m :=
      Nat.dvd_of_mem_primeFactors p.property
    have hepos : 0 < m.factorization (p : Nat) :=
      hp.factorization_pos_of_dvd hm0 hdvd
    have he : m.factorization (p : Nat) ≠ 0 := by omega
    have hpne2 : (p : Nat) ≠ 2 := by
      intro hp2
      have hnotEven : ¬ Even m := (Nat.not_even_iff_odd).mpr hmOdd
      apply hnotEven
      rw [even_iff_two_dvd]
      simpa [hp2] using hdvd
    exact zmod_primePower_unit_split hp hpne2 he ((E x) p)
  choose uP hPunit hPsub using hsplit
  let uPi : (p : m.primeFactors) ->
      ZMod ((p : Nat) ^ m.factorization (p : Nat)) :=
    fun p => uP p
  let u : ZMod m := E.symm uPi
  refine ⟨u, ?_, ?_⟩
  · apply (isUnit_map_iff E u).mp
    have hEu : E u = uPi := by
      dsimp [u]
      exact E.apply_symm_apply uPi
    rw [hEu, Pi.isUnit_iff]
    intro p
    exact hPunit p
  · apply (isUnit_map_iff E (x - u)).mp
    have hEu : E u = uPi := by
      dsimp [u]
      exact E.apply_symm_apply uPi
    rw [map_sub, hEu, Pi.isUnit_iff]
    intro p
    exact hPsub p

theorem zmod_unit_sub_sum_units
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {r : ZMod m} (hr : IsUnit r) :
    forall t : Nat, ∃ us : Fin t -> ZMod m,
      (forall i : Fin t, IsUnit (us i)) ∧
        IsUnit (r - ∑ i, us i) := by
  intro t
  induction t generalizing r with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simpa using hr
  | succ t ih =>
      rcases zmod_unit_split_of_odd hmOdd hm3 r with ⟨u0, hu0, hrem⟩
      rcases ih hrem with ⟨us, hus, hfinal⟩
      let us' : Fin (t + 1) -> ZMod m := Fin.cons u0 us
      refine ⟨us', ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
            simpa [us'] using hu0
        | succ i =>
            simpa [us'] using hus i
      · rw [Fin.sum_univ_succ]
        change IsUnit (r - (u0 + ∑ i : Fin t, us i))
        convert hfinal using 1
        ring

theorem zmod_unit_sub_sum_units_finset
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {ι : Type} (s : Finset ι)
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us : {i : ι // i ∈ s} -> ZMod m,
      (forall i : {i : ι // i ∈ s}, IsUnit (us i)) ∧
        IsUnit (r - ∑ i : {i : ι // i ∈ s}, us i) := by
  classical
  rcases zmod_unit_sub_sum_units hmOdd hm3 hr s.card with
    ⟨usFin, husFin, hfinal⟩
  let E : Fin s.card ≃ {i : ι // i ∈ s} := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin]
    rw [Fintype.card_coe]
  let us : {i : ι // i ∈ s} -> ZMod m := fun i => usFin (E.symm i)
  refine ⟨us, ?_, ?_⟩
  · intro i
    exact husFin (E.symm i)
  · have hsum :
        (∑ i : {i : ι // i ∈ s}, us i) =
          ∑ i : Fin s.card, usFin i := by
      simpa [us] using (E.symm.sum_comp usFin)
    rw [hsum]
    exact hfinal

theorem incidenceChildTransferPatternsWithUnitLabels_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    {ρ : Y} {α : Block}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (ha : (A α).card = a) (ha2 : 2 <= a)
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us :
        {q : Y // q ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα} ->
          ZMod m,
      (forall q, IsUnit (us q)) ∧
      IsUnit (r - ∑ q, us q) ∧
      forall q,
        ∃ p : Y,
        ∃ _ : (Sum.inl p : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α) ({p, q.1} : Finset Y) (a / 2) m,
          ((replicatedBlockColumnDegree P.toChoice q.1 : Nat) : ZMod m) =
            us q ∧
          ((replicatedBlockColumnDegree P.toChoice p : Nat) : ZMod m) =
            -us q := by
  classical
  let S : Finset Y := incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α hα
  rcases zmod_unit_sub_sum_units_finset hmOdd hm3 S hr with
    ⟨us, hus, hfinal⟩
  refine ⟨us, hus, hfinal, ?_⟩
  intro q
  exact
    incidenceChildTransferResiduePatternWithZModUnit_exists
      (A := A) hTle hTtree hmpos ha ha2 q.2 (us q) (hus q)

theorem incidenceUnaryBlockTransferPatternsWithUnitLabelsOn_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    (U : Finset Block)
    (hU :
      U ⊆ incidenceUnaryBlockChildren T root y hy)
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us : {α : Block // α ∈ U} -> ZMod m,
      (forall α, IsUnit (us α)) ∧
      IsUnit (r - ∑ α : {α : Block // α ∈ U}, us α) ∧
      forall α : {α : Block // α ∈ U},
        ∃ q : Y,
        ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
        ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α.1) ({y, q} : Finset Y) (a / 2) m,
          q ∈ incidenceYChildren T root α.1 hα ∧
          ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
            us α ∧
          ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) =
            -us α := by
  classical
  rcases zmod_unit_sub_sum_units_finset hmOdd hm3 U hr with
    ⟨us, hus, hfinal⟩
  refine ⟨us, hus, hfinal, ?_⟩
  intro α
  exact
    incidenceUnaryBlockResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos hA ha2 (hU α.2) (us α) (hus α)

noncomputable def classicalFinsetErase {α : Type} (s : Finset α) (a : α) :
    Finset α := by
  classical
  exact s.erase a

theorem mem_classicalFinsetErase
    {α : Type} {s : Finset α} {a b : α} :
    b ∈ classicalFinsetErase s a ↔ b ∈ s ∧ b ≠ a := by
  classical
  simp [classicalFinsetErase, and_comm]

theorem classicalFinsetErase_subset
    {α : Type} {s : Finset α} {a : α} :
    classicalFinsetErase s a ⊆ s := by
  intro b hb
  exact ((mem_classicalFinsetErase).mp hb).1

theorem incidenceUnaryBlockTransferPatternsExceptWithUnitLabels_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    (β : Block)
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us :
        {α : Block //
          α ∈ classicalFinsetErase
            (incidenceUnaryBlockChildren T root y hy) β} ->
          ZMod m,
      (forall α, IsUnit (us α)) ∧
      IsUnit
        (r - ∑ α :
          {α : Block //
            α ∈ classicalFinsetErase
              (incidenceUnaryBlockChildren T root y hy) β},
          us α) ∧
      forall α :
        {α : Block //
          α ∈ classicalFinsetErase
            (incidenceUnaryBlockChildren T root y hy) β},
        ∃ q : Y,
        ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
        ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α.1) ({y, q} : Finset Y) (a / 2) m,
          q ∈ incidenceYChildren T root α.1 hα ∧
          ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
            us α ∧
          ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) =
            -us α := by
  classical
  exact
    incidenceUnaryBlockTransferPatternsWithUnitLabelsOn_exists
      (A := A) hTle hmOdd hm3 hmpos hA ha2
      (classicalFinsetErase (incidenceUnaryBlockChildren T root y hy) β)
      classicalFinsetErase_subset
      hr

theorem incidenceUnaryBlockTransferPatternsWithUnitLabels_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : (replicatedIncidenceGraph A).ConnectedComponent}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {y : Y}
    {hy : (Sum.inl y : IncidenceVertex Y Block) ∈ C.supp}
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us :
        {α : Block // α ∈ incidenceUnaryBlockChildren T root y hy} ->
          ZMod m,
      (forall α, IsUnit (us α)) ∧
      IsUnit (r - ∑ α, us α) ∧
      forall α,
        ∃ q : Y,
        ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
        ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α.1) ({y, q} : Finset Y) (a / 2) m,
          q ∈ incidenceYChildren T root α.1 hα ∧
          ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
            us α ∧
          ((replicatedBlockColumnDegree P.toChoice y : Nat) : ZMod m) =
            -us α := by
  classical
  let U : Finset Block := incidenceUnaryBlockChildren T root y hy
  rcases zmod_unit_sub_sum_units_finset hmOdd hm3 U hr with
    ⟨us, hus, hfinal⟩
  refine ⟨us, hus, hfinal, ?_⟩
  intro α
  exact
    incidenceUnaryBlockResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos hA ha2 α.2 (us α) (hus α)

/-- Unary child blocks to be handled at one component `Y`-vertex.  At the
root we remove the distinguished root block `α0`, since that block is already
handled by the root reservoir.  Away from the root this is just the full unary
child set. -/
noncomputable def componentYUnaryBlockChildrenExceptRoot
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y) (α0 : Block)
    (y : ComponentY A C) : Finset Block := by
  classical
  exact
    if y.1 = ρ then
      classicalFinsetErase (incidenceUnaryBlockChildren T root y.1 y.2) α0
    else
      incidenceUnaryBlockChildren T root y.1 y.2

theorem mem_componentYUnaryBlockChildrenExceptRoot
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y) (α0 : Block)
    (y : ComponentY A C) (α : Block) :
    α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y ↔
      α ∈ incidenceUnaryBlockChildren T root y.1 y.2 ∧
        (y.1 = ρ -> α ≠ α0) := by
  classical
  by_cases hyρ : y.1 = ρ
  · simp [componentYUnaryBlockChildrenExceptRoot, hyρ,
      mem_classicalFinsetErase]
  · simp [componentYUnaryBlockChildrenExceptRoot, hyρ]

theorem componentYUnaryBlockChildrenExceptRoot_root_not_mem
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (α0 : Block) :
    α0 ∉ componentYUnaryBlockChildrenExceptRoot T ⟨Sum.inl ρ, hρ⟩ ρ α0
      (⟨ρ, hρ⟩ : ComponentY A C) := by
  classical
  rw [mem_componentYUnaryBlockChildrenExceptRoot]
  intro h
  exact h.2 rfl rfl

theorem componentYUnaryBlockChildrenExceptRoot_subset
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y) (α0 : Block)
    (y : ComponentY A C) :
    componentYUnaryBlockChildrenExceptRoot T root ρ α0 y ⊆
      incidenceUnaryBlockChildren T root y.1 y.2 := by
  classical
  by_cases hyρ : y.1 = ρ
  · intro α hα
    have hα' :
        α ∈ classicalFinsetErase
          (incidenceUnaryBlockChildren T root y.1 y.2) α0 := by
      simpa [componentYUnaryBlockChildrenExceptRoot, hyρ] using hα
    exact classicalFinsetErase_subset hα'
  · intro α hα
    simpa [componentYUnaryBlockChildrenExceptRoot, hyρ] using hα

theorem componentYUnaryBlockChildrenExceptRoot_mem_of_parent
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {ρ : Y} {α0 α : Block} {p : ComponentY A C}
    {hα : (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp}
    (hParent :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α, hα⟩)
    (hUnary : (incidenceYChildren T root α hα).card = 1)
    (hNotRootException : p.1 = ρ -> α ≠ α0) :
    α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 p := by
  classical
  have hUnaryMem :
      α ∈ incidenceUnaryBlockChildren T root p.1 p.2 :=
    incidenceBlockParentY_mem_unaryBlockChildren_of_card_eq_one
      (A := A) hParent hUnary
  by_cases hpρ : p.1 = ρ
  · have hne : α ≠ α0 := hNotRootException hpρ
    have hmem :
        α ∈ classicalFinsetErase
          (incidenceUnaryBlockChildren T root p.1 p.2) α0 := by
      rw [mem_classicalFinsetErase]
      exact ⟨hUnaryMem, hne⟩
    simpa [componentYUnaryBlockChildrenExceptRoot, hpρ] using hmem
  · simpa [componentYUnaryBlockChildrenExceptRoot, hpρ] using hUnaryMem

/-- Canonical local data attached to an ordinary unary block of a rooted
component: its parent `Y`-vertex, its unique child `Y`-vertex, and the fact
that the block appears in the parent vertex's ordinary-unary outgoing set. -/
structure ComponentOrdinaryUnaryBlockData
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y)
    (αRoot α : ComponentBlock A C) where
  not_root : α.1 ≠ αRoot.1
  unary : (incidenceYChildren T root α.1 α.2).card = 1
  parent : ComponentY A C
  child : ComponentY A C
  parent_rel :
    IsRootParent T root (componentYVertex parent) ⟨Sum.inr α.1, α.2⟩
  child_rel :
    IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex child)
  ordinary_mem :
    α.1 ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 parent
  child_mem : child ∈ componentBlockYChildren T root α

theorem componentOrdinaryUnaryBlockData_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hNotRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1) :
    Nonempty
      (ComponentOrdinaryUnaryBlockData T ⟨Sum.inl ρ, hρ⟩ ρ αRoot α) := by
  classical
  rcases componentBlockParentY_exists (A := A) hTle hTtree
      (hρ := hρ) α with
    ⟨p, hParent, _hpA⟩
  rcases Finset.card_eq_one.mp hUnary with ⟨q, hqEq⟩
  have hqChild : q ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 := by
    simp [hqEq]
  rcases (mem_incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 q).mp hqChild with
    ⟨hqC, hChild⟩
  let child : ComponentY A C := ⟨q, hqC⟩
  have hChild' :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α.1, α.2⟩
        (componentYVertex child) := by
    simpa [componentYVertex, child] using hChild
  have hChildMem : child ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α := by
    rw [mem_componentBlockYChildren]
    simpa [child] using hqChild
  have hOrdinary :
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 p :=
    componentYUnaryBlockChildrenExceptRoot_mem_of_parent
      (A := A) hParent hUnary (fun _ => hNotRoot)
  exact
    ⟨
      { not_root := hNotRoot
        unary := hUnary
        parent := p
        child := child
        parent_rel := hParent
        child_rel := hChild'
        ordinary_mem := hOrdinary
        child_mem := hChildMem }⟩

theorem componentOrdinaryUnaryBlockData_pair_subset
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C} (hTle : T ≤ C.toSimpleGraph)
    {ρ : Y} {αRoot α : ComponentBlock A C}
    (D : ComponentOrdinaryUnaryBlockData T root ρ αRoot α) :
    ({D.parent.1, D.child.1} : Finset Y) ⊆ A α.1 := by
  classical
  have hParentA : D.parent.1 ∈ A α.1 := by
    have hG := replicatedIncidenceTree_adj_val hTle D.parent_rel.1
    simpa [replicatedIncidenceGraph, componentYVertex] using hG
  have hChildA : D.child.1 ∈ A α.1 := by
    have hG := replicatedIncidenceTree_adj_val hTle D.child_rel.1
    simpa [replicatedIncidenceGraph, componentYVertex] using hG
  intro y hy
  rw [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact hParentA
  · exact hChildA

/-- The possible source of the incoming unit at a component `Y`-vertex in the
rooted top-down construction.  The root receives its source from the
distinguished root block at the root column.  A non-root vertex receives it
from its parent block: from the distinguished root block, from a non-unary
child-set reservoir, or from the unary transfer label chosen at the parent
`Y`-vertex. -/
inductive ComponentIncomingSource
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y)
    (αRoot : ComponentBlock A C) :
    ComponentY A C -> Prop where
  | root (y : ComponentY A C) :
      y.1 = ρ -> ComponentIncomingSource T root ρ αRoot y
  | rootBlock (y : ComponentY A C) :
      y.1 ≠ ρ ->
      y ∈ componentBlockYChildren T root αRoot ->
        ComponentIncomingSource T root ρ αRoot y
  | nonUnary (y : ComponentY A C) (α : ComponentBlock A C) :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) ->
      α.1 ≠ αRoot.1 ->
      (incidenceYChildren T root α.1 α.2).card ≠ 1 ->
        ComponentIncomingSource T root ρ αRoot y
  | unary (y p : ComponentY A C) (α : ComponentBlock A C) :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩ ->
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) ->
      α.1 ≠ αRoot.1 ->
      (incidenceYChildren T root α.1 α.2).card = 1 ->
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 p ->
        ComponentIncomingSource T root ρ αRoot y

theorem componentIncomingSource_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (αRoot : ComponentBlock A C) (y : ComponentY A C) :
    ComponentIncomingSource T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y := by
  classical
  by_cases hyρ : y.1 = ρ
  · exact ComponentIncomingSource.root y hyρ
  · rcases componentYParentBlock_exists (A := A) hTle hTtree
        (hρ := hρ) y hyρ with
      ⟨α, hParentChild, _hyA⟩
    by_cases hαRoot : α.1 = αRoot.1
    · have hαeq : α = αRoot := Subtype.ext hαRoot
      subst α
      exact ComponentIncomingSource.rootBlock y hyρ
        (componentYParentBlock_mem_children hParentChild)
    · by_cases hUnary :
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1
      · rcases componentBlockParentY_exists (A := A) hTle hTtree
            (hρ := hρ) α with
          ⟨p, hParentY, _hpA⟩
        have hOrdinary :
            α.1 ∈ componentYUnaryBlockChildrenExceptRoot
              T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 p :=
          componentYUnaryBlockChildrenExceptRoot_mem_of_parent
            (A := A) hParentY hUnary (fun _ => hαRoot)
        exact ComponentIncomingSource.unary y p α hParentY hParentChild
          hαRoot hUnary hOrdinary
      · exact ComponentIncomingSource.nonUnary y α hParentChild hαRoot hUnary

theorem componentRootPattern_root_isUnit
    {m a : Nat}
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {ρ : Y}
    {α0 : Block} {hα0 : (Sum.inr α0 : IncidenceVertex Y Block) ∈ C.supp}
    (P :
      ReplicatedBlockResiduePattern
        (A α0)
        (insert ρ (incidenceYChildren T root α0 hα0))
        (a / 2) m) :
    IsUnit
      ((replicatedBlockColumnDegree P.toChoice ρ : Nat) : ZMod m) := by
  classical
  exact replicatedBlockResiduePattern_active_isUnit P (by simp)

theorem componentRootPattern_child_isUnit
    {m a : Nat}
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {ρ : Y}
    {αRoot : ComponentBlock A C}
    (P :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ (incidenceYChildren T root αRoot.1 αRoot.2))
        (a / 2) m)
    {y : ComponentY A C}
    (hy : y ∈ componentBlockYChildren T root αRoot) :
    IsUnit
      ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) := by
  classical
  have hyChild :
      y.1 ∈ incidenceYChildren T root αRoot.1 αRoot.2 :=
    (mem_componentBlockYChildren T root αRoot y).mp hy
  exact replicatedBlockResiduePattern_active_isUnit P (by simp [hyChild])

theorem componentNonUnaryPattern_child_isUnit
    {m a : Nat}
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C}
    {α : ComponentBlock A C}
    (P :
      ReplicatedBlockResiduePattern
        (A α.1) (incidenceYChildren T root α.1 α.2) (a / 2) m)
    {y : ComponentY A C}
    (hy : y ∈ componentBlockYChildren T root α) :
    IsUnit
      ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) := by
  classical
  have hyChild :
      y.1 ∈ incidenceYChildren T root α.1 α.2 :=
    (mem_componentBlockYChildren T root α y).mp hy
  exact replicatedBlockResiduePattern_active_isUnit P hyChild

theorem componentUnaryPairResiduePatternWithZModUnit_exists
    {Y Block : Type} [DecidableEq Y] {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {p y : ComponentY A C} {α : ComponentBlock A C}
    (hParent :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩)
    (hChild :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y))
    (u : ZMod m) (hu : IsUnit u) :
    ∃ P : ReplicatedBlockResiduePattern
        (A α.1) ({p.1, y.1} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) = u ∧
      ((replicatedBlockColumnDegree P.toChoice p.1 : Nat) : ZMod m) = -u := by
  classical
  exact
    incidenceUnaryPairResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos (hA α.1) ha2
      (by simpa [componentYVertex] using hParent)
      (by simpa [componentYVertex] using hChild)
      u hu

/-- A relation saying that `r` is the incoming contribution at a component
`Y`-vertex, read from the already chosen root/non-unary reservoirs or from the
unary label chosen at the parent `Y`-vertex.  This is intentionally relational:
later constructions can choose an actual incoming function by classical choice
after proving existence of a unit contribution at every vertex. -/
inductive ComponentIncomingContribution
    {m a : Nat}
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y)
    (αRoot : ComponentBlock A C)
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ (incidenceYChildren T root αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T root α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1) (incidenceYChildren T root α.1 α.2) (a / 2) m)
    (us :
      forall p : ComponentY A C,
        {α : Block //
          α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 p} ->
          ZMod m) :
    ComponentY A C -> ZMod m -> Prop where
  | root (y : ComponentY A C) :
      y.1 = ρ ->
      r = ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m) ->
        ComponentIncomingContribution T root ρ αRoot PRoot PNonUnary us y r
  | rootBlock (y : ComponentY A C) :
      y.1 ≠ ρ ->
      y ∈ componentBlockYChildren T root αRoot ->
      r = ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) : ZMod m) ->
        ComponentIncomingContribution T root ρ αRoot PRoot PNonUnary us y r
  | nonUnary (y : ComponentY A C) (α : ComponentBlock A C) :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) ->
      (hαRoot : α.1 ≠ αRoot.1) ->
      (hNotUnary : (incidenceYChildren T root α.1 α.2).card ≠ 1) ->
      r =
        ((replicatedBlockColumnDegree
          ((PNonUnary α hαRoot hNotUnary).toChoice) y.1 : Nat) : ZMod m) ->
        ComponentIncomingContribution T root ρ αRoot PRoot PNonUnary us y r
  | unary (y p : ComponentY A C) (α : ComponentBlock A C) :
      IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩ ->
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) ->
      α.1 ≠ αRoot.1 ->
      (incidenceYChildren T root α.1 α.2).card = 1 ->
      (hOrdinary :
        α.1 ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 p) ->
      r = us p ⟨α.1, hOrdinary⟩ ->
        ComponentIncomingContribution T root ρ αRoot PRoot PNonUnary us y r

theorem componentIncomingContribution_exists_of_source
    {m a : Nat}
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} {root : C} {ρ : Y}
    {αRoot : ComponentBlock A C}
    {PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ (incidenceYChildren T root αRoot.1 αRoot.2))
        (a / 2) m}
    {PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T root α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1) (incidenceYChildren T root α.1 α.2) (a / 2) m}
    {us :
      forall p : ComponentY A C,
        {α : Block //
          α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 p} ->
          ZMod m}
    (hus : forall p α, IsUnit (us p α))
    {y : ComponentY A C}
    (hSource : ComponentIncomingSource T root ρ αRoot y) :
    ∃ r : ZMod m,
      ComponentIncomingContribution T root ρ αRoot PRoot PNonUnary us y r ∧
        IsUnit r := by
  classical
  cases hSource with
  | root hyρ =>
      refine
        ⟨((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m),
          ?_, ?_⟩
      · exact ComponentIncomingContribution.root y hyρ rfl
      · exact componentRootPattern_root_isUnit PRoot
  | rootBlock hyρ hyChild =>
      refine
        ⟨((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) : ZMod m),
          ?_, ?_⟩
      · exact ComponentIncomingContribution.rootBlock y hyρ hyChild rfl
      · exact componentRootPattern_child_isUnit PRoot hyChild
  | nonUnary α hParent hαRoot hNotUnary =>
      refine
        ⟨((replicatedBlockColumnDegree
            ((PNonUnary α hαRoot hNotUnary).toChoice) y.1 : Nat) : ZMod m),
          ?_, ?_⟩
      · exact ComponentIncomingContribution.nonUnary y α hParent hαRoot
          hNotUnary rfl
      · exact componentNonUnaryPattern_child_isUnit
          (PNonUnary α hαRoot hNotUnary)
          (componentYParentBlock_mem_children hParent)
  | unary p α hParent hChild hαRoot hUnary hOrdinary =>
      refine ⟨us p ⟨α.1, hOrdinary⟩, ?_, ?_⟩
      · exact ComponentIncomingContribution.unary y p α hParent hChild
          hαRoot hUnary hOrdinary rfl
      · exact hus p ⟨α.1, hOrdinary⟩

/-- One top-down unit-flow step at a component `Y`-vertex: given a unit incoming
residue `r`, choose unit labels on all ordinary unary child blocks (with the
root block exception above) so that the final residue at this `Y`-vertex is
still a unit, and realize every chosen label by a local unary transfer pattern.
This is the reusable step for the remaining component-tree recursion. -/
theorem componentYUnaryTransferPatternsExceptRootWithUnitLabels_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} (ρ : Y) (α0 : Block) (y : ComponentY A C)
    {r : ZMod m} (hr : IsUnit r) :
    ∃ us :
        {α : Block //
          α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y} ->
          ZMod m,
      (forall α, IsUnit (us α)) ∧
      IsUnit
        (r - ∑ α :
          {α : Block //
            α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y},
          us α) ∧
      forall α :
        {α : Block //
          α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y},
        ∃ q : Y,
        ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
        ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α.1) ({y.1, q} : Finset Y) (a / 2) m,
          q ∈ incidenceYChildren T root α.1 hα ∧
          ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
            us α ∧
          ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) =
            -us α := by
  classical
  exact
    incidenceUnaryBlockTransferPatternsWithUnitLabelsOn_exists
      (A := A) hTle hmOdd hm3 hmpos hA ha2
      (componentYUnaryBlockChildrenExceptRoot T root ρ α0 y)
      (componentYUnaryBlockChildrenExceptRoot_subset T root ρ α0 y)
      hr

/-- Simultaneous version of
`componentYUnaryTransferPatternsExceptRootWithUnitLabels_exists` over all
`Y`-vertices in the component.  This packages the local step by finite choice;
the remaining global proof must still supply an incoming unit residue function
compatible with the rooted tree. -/
theorem componentYUnaryTransferPatternFamilyExceptRootWithUnitLabels_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} (ρ : Y) (α0 : Block)
    (incoming : ComponentY A C -> ZMod m)
    (hincoming : forall y : ComponentY A C, IsUnit (incoming y)) :
    ∃ us :
        forall y : ComponentY A C,
          {α : Block //
            α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y} ->
            ZMod m,
      (forall y α, IsUnit (us y α)) ∧
      (forall y,
        IsUnit
          (incoming y - ∑ α :
            {α : Block //
              α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y},
            us y α)) ∧
      forall y α,
        ∃ q : Y,
        ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
        ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
        ∃ P : ReplicatedBlockResiduePattern
            (A α.1) ({y.1, q} : Finset Y) (a / 2) m,
          q ∈ incidenceYChildren T root α.1 hα ∧
          ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
            us y α ∧
          ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) =
            -us y α := by
  classical
  have hLocal :
      forall y : ComponentY A C,
        ∃ us :
            {α : Block //
              α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y} ->
              ZMod m,
          (forall α, IsUnit (us α)) ∧
          IsUnit
            (incoming y - ∑ α :
              {α : Block //
                α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y},
              us α) ∧
          forall α :
            {α : Block //
              α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ α0 y},
            ∃ q : Y,
            ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
            ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
            ∃ P : ReplicatedBlockResiduePattern
                (A α.1) ({y.1, q} : Finset Y) (a / 2) m,
              q ∈ incidenceYChildren T root α.1 hα ∧
              ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
                us α ∧
              ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) =
                -us α := by
    intro y
    exact
      componentYUnaryTransferPatternsExceptRootWithUnitLabels_exists
        (A := A) hTle hmOdd hm3 hmpos hA ha2 ρ α0 y
        (hincoming y)
  choose us hus hfinal hpatterns using hLocal
  exact ⟨us, hus, hfinal, hpatterns⟩

/-- The local data produced at one component `Y`-vertex once its incoming
unit residue is known: unit labels on all ordinary unary child blocks, the
unit final residue after subtracting those labels, and local pair-transfer
patterns realizing every label. -/
structure ComponentYFlowData
    {m a : Nat}
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y) (αRoot : ComponentBlock A C)
    (y : ComponentY A C) (incoming : ZMod m) where
  label :
    {α : Block //
      α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y} ->
      ZMod m
  label_unit : forall α, IsUnit (label α)
  final_unit :
    IsUnit
      (incoming - ∑ α :
        {α : Block //
          α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y},
        label α)
  transfer_pattern :
    forall α :
      {α : Block //
        α ∈ componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y},
      ∃ q : Y,
      ∃ _ : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp,
      ∃ hα : (Sum.inr α.1 : IncidenceVertex Y Block) ∈ C.supp,
      ∃ P : ReplicatedBlockResiduePattern
          (A α.1) ({y.1, q} : Finset Y) (a / 2) m,
        q ∈ incidenceYChildren T root α.1 hα ∧
        ((replicatedBlockColumnDegree P.toChoice q : Nat) : ZMod m) =
          label α ∧
        ((replicatedBlockColumnDegree P.toChoice y.1 : Nat) : ZMod m) =
          -label α

theorem componentYFlowData_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot : ComponentBlock A C}
    (y : ComponentY A C) {incoming : ZMod m}
    (hincoming : IsUnit incoming) :
    Nonempty
      (ComponentYFlowData (m := m) (a := a) T root ρ αRoot y incoming) := by
  classical
  rcases componentYUnaryTransferPatternsExceptRootWithUnitLabels_exists
      (A := A) hTle hmOdd hm3 hmpos hA ha2 ρ αRoot.1 y hincoming with
    ⟨label, hLabelUnit, hFinal, hPattern⟩
  exact
    ⟨
      { label := label
        label_unit := hLabelUnit
        final_unit := hFinal
        transfer_pattern := hPattern }⟩

theorem componentYFlowDataFamily_exists
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot : ComponentBlock A C}
    (incoming : ComponentY A C -> ZMod m)
    (hincoming : forall y : ComponentY A C, IsUnit (incoming y)) :
    Nonempty
      (forall y : ComponentY A C,
        ComponentYFlowData (m := m) (a := a) T root ρ αRoot y (incoming y)) := by
  classical
  have hLocal :
      forall y : ComponentY A C,
        Nonempty
      (ComponentYFlowData (m := m) (a := a) T root ρ αRoot y (incoming y)) := by
    intro y
    exact componentYFlowData_exists
      (A := A) hTle hmOdd hm3 hmpos hA ha2 y (hincoming y)
  exact ⟨fun y => Classical.choice (hLocal y)⟩

/-- A parent flow label on an ordinary unary block can be realized on that
block's actual parent-child pair.  This is the unary case needed when the
global component assignment later defines `S α = {parent, child}`. -/
theorem componentOrdinaryUnaryBlockData_flowTransferPattern_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot α : ComponentBlock A C}
    (D : ComponentOrdinaryUnaryBlockData T root ρ αRoot α)
    {incoming : ZMod m}
    (F :
      ComponentYFlowData (m := m) (a := a) T root ρ αRoot D.parent
        incoming) :
    ∃ P : ReplicatedBlockResiduePattern
        (A α.1) ({D.parent.1, D.child.1} : Finset Y) (a / 2) m,
      ((replicatedBlockColumnDegree P.toChoice D.child.1 : Nat) : ZMod m) =
        F.label ⟨α.1, D.ordinary_mem⟩ ∧
      ((replicatedBlockColumnDegree P.toChoice D.parent.1 : Nat) : ZMod m) =
        -F.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  exact
    componentUnaryPairResiduePatternWithZModUnit_exists
      (A := A) hTle hmpos hA ha2 D.parent_rel D.child_rel
      (F.label ⟨α.1, D.ordinary_mem⟩)
      (F.label_unit ⟨α.1, D.ordinary_mem⟩)

/-- The concrete unary-transfer pattern chosen for an ordinary unary block
from the already constructed parent flow data. -/
noncomputable def componentOrdinaryUnaryBlockPattern
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot α : ComponentBlock A C}
    (D : ComponentOrdinaryUnaryBlockData T root ρ αRoot α)
    {incoming : ZMod m}
    (F :
      ComponentYFlowData (m := m) (a := a) T root ρ αRoot D.parent
        incoming) :
    ReplicatedBlockResiduePattern
      (A α.1) ({D.parent.1, D.child.1} : Finset Y) (a / 2) m :=
  Classical.choose
    (componentOrdinaryUnaryBlockData_flowTransferPattern_exists
      (A := A) hTle hmpos hA ha2 D F)

theorem componentOrdinaryUnaryBlockPattern_child_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot α : ComponentBlock A C}
    (D : ComponentOrdinaryUnaryBlockData T root ρ αRoot α)
    {incoming : ZMod m}
    (F :
      ComponentYFlowData (m := m) (a := a) T root ρ αRoot D.parent
        incoming) :
    ((replicatedBlockColumnDegree
      ((componentOrdinaryUnaryBlockPattern
        (A := A) hTle hmpos hA ha2 D F).toChoice)
      D.child.1 : Nat) : ZMod m) =
        F.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  simpa [componentOrdinaryUnaryBlockPattern] using
    (Classical.choose_spec
      (componentOrdinaryUnaryBlockData_flowTransferPattern_exists
        (A := A) hTle hmpos hA ha2 D F)).1

theorem componentOrdinaryUnaryBlockPattern_parent_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {root : C} {ρ : Y} {αRoot α : ComponentBlock A C}
    (D : ComponentOrdinaryUnaryBlockData T root ρ αRoot α)
    {incoming : ZMod m}
    (F :
      ComponentYFlowData (m := m) (a := a) T root ρ αRoot D.parent
        incoming) :
    ((replicatedBlockColumnDegree
      ((componentOrdinaryUnaryBlockPattern
        (A := A) hTle hmpos hA ha2 D F).toChoice)
      D.parent.1 : Nat) : ZMod m) =
        -F.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  simpa [componentOrdinaryUnaryBlockPattern] using
    (Classical.choose_spec
      (componentOrdinaryUnaryBlockData_flowTransferPattern_exists
        (A := A) hTle hmpos hA ha2 D F)).2

/-- The top-down local flow data at a component `Y`-vertex.  The `incoming`
residue is a unit, and `flow` chooses unit outgoing labels on the ordinary
unary child blocks of this vertex. -/
structure ComponentVertexFlowData
    {m a : Nat}
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    (T : SimpleGraph C) (root : C) (ρ : Y) (αRoot : ComponentBlock A C)
    (y : ComponentY A C) where
  incoming : ZMod m
  incoming_unit : IsUnit incoming
  flow :
    ComponentYFlowData (m := m) (a := a) T root ρ αRoot y incoming

/-- Named version of the top-down well-founded flow family.  The older
existence theorem below hides this construction behind `Nonempty`; this
definition exposes the recursion so later proofs can derive case equations
from `WellFounded.fix_eq`. -/
noncomputable def componentVertexFlowDataFamily
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m) :
    forall y : ComponentY A C,
      ComponentVertexFlowData (m := m) (a := a)
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let depth : ComponentY A C -> Nat := fun y => componentYRootDist T root y
  exact
    WellFounded.fix (InvImage.wf depth Nat.lt_wfRel.2)
      (fun y rec => by
        by_cases hyρ : y.1 = ρ
        · let r : ZMod m :=
            ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m)
          have hr : IsUnit r := by
            exact componentRootPattern_root_isUnit PRoot
          exact
            { incoming := r
              incoming_unit := hr
              flow := Classical.choice
                (componentYFlowData_exists
                  (A := A) hTle hmOdd hm3 hmpos hA ha2 y hr) }
        · let α : ComponentBlock A C :=
            componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree y hyρ
          have hParentChild :
              IsRootParent T root
                ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) :=
            componentYParentBlockChoice_parent (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree y hyρ
          by_cases hαRoot : α.1 = αRoot.1
          · have hαeq : α = αRoot := Subtype.ext hαRoot
            have hyChild : y ∈ componentBlockYChildren T root αRoot := by
              simpa [hαeq] using
                componentYParentBlock_mem_children hParentChild
            let r : ZMod m :=
              ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) :
                ZMod m)
            have hr : IsUnit r := by
              exact componentRootPattern_child_isUnit PRoot hyChild
            exact
              { incoming := r
                incoming_unit := hr
                flow := Classical.choice
                  (componentYFlowData_exists
                    (A := A) hTle hmOdd hm3 hmpos hA ha2 y hr) }
          · by_cases hUnary :
              (incidenceYChildren T root α.1 α.2).card = 1
            · let p : ComponentY A C :=
                componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
                  hTle hTtree α
              have hParentY :
                  IsRootParent T root
                    (componentYVertex p) ⟨Sum.inr α.1, α.2⟩ :=
                componentBlockParentYChoice_parent (A := A) (ρ := ρ) (hρ := hρ)
                  hTle hTtree α
              have hOrdinary :
                  α.1 ∈ componentYUnaryBlockChildrenExceptRoot
                    T root ρ αRoot.1 p :=
                componentYUnaryBlockChildrenExceptRoot_mem_of_parent
                  (A := A) hParentY hUnary (fun _ => hαRoot)
              have hyChild : y.1 ∈ incidenceYChildren T root α.1 α.2 := by
                rw [mem_incidenceYChildren]
                exact ⟨y.2, by simpa [componentYVertex] using hParentChild⟩
              have hlt : depth p < depth y := by
                simpa [depth] using
                  componentYRootDist_lt_of_parentBlock_child
                    (A := A) hParentY hyChild
              let parentData := rec p hlt
              let r : ZMod m :=
                parentData.flow.label ⟨α.1, hOrdinary⟩
              have hr : IsUnit r := by
                exact parentData.flow.label_unit ⟨α.1, hOrdinary⟩
              exact
                { incoming := r
                  incoming_unit := hr
                  flow := Classical.choice
                    (componentYFlowData_exists
                      (A := A) hTle hmOdd hm3 hmpos hA ha2 y hr) }
            · let r : ZMod m :=
                ((replicatedBlockColumnDegree
                  ((PNonUnary α hαRoot hUnary).toChoice) y.1 : Nat) :
                    ZMod m)
              have hr : IsUnit r := by
                exact componentNonUnaryPattern_child_isUnit
                  (PNonUnary α hαRoot hUnary)
                  (componentYParentBlock_mem_children hParentChild)
              exact
                { incoming := r
                  incoming_unit := hr
                  flow := Classical.choice
                    (componentYFlowData_exists
                      (A := A) hTle hmOdd hm3 hmpos hA ha2 y hr) })

theorem componentVertexFlowDataFamily_root_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    {y : ComponentY A C} (hyρ : y.1 = ρ) :
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).incoming =
        ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m) := by
  classical
  unfold componentVertexFlowDataFamily
  rw [WellFounded.fix_eq]
  simp [hyρ]

theorem componentVertexFlowDataFamily_rootBlock_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    {y : ComponentY A C}
    (hyρ : y.1 ≠ ρ)
    (hyChild :
      y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot) :
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).incoming =
        ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) :
          ZMod m) := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  have hRootParent :
      IsRootParent T root
        ⟨Sum.inr αRoot.1, αRoot.2⟩ (componentYVertex y) := by
    have hyRaw :
        y.1 ∈ incidenceYChildren T root αRoot.1 αRoot.2 :=
      (mem_componentBlockYChildren T root αRoot y).mp hyChild
    rcases (mem_incidenceYChildren T root αRoot.1 αRoot.2 y.1).mp hyRaw
      with ⟨_hyC, hParent⟩
    simpa [componentYVertex] using hParent
  have hαeq :
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ = αRoot :=
    componentYParentBlockChoice_eq_of_parent
      (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hRootParent
  have hαRootVal :
      (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ).1 = αRoot.1 :=
    congrArg Subtype.val hαeq
  unfold componentVertexFlowDataFamily
  rw [WellFounded.fix_eq]
  simp [hyρ, hαRootVal]

theorem componentVertexFlowDataFamily_nonUnary_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    {y : ComponentY A C}
    (hyρ : y.1 ≠ ρ)
    (hParent :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        ⟨Sum.inr α.1, α.2⟩ (componentYVertex y))
    (hRoot : α.1 ≠ αRoot.1)
    (hNotUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1) :
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).incoming =
        ((replicatedBlockColumnDegree
          ((PNonUnary α hRoot hNotUnary).toChoice) y.1 : Nat) :
          ZMod m) := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  have hβα :
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ = α :=
    componentYParentBlockChoice_eq_of_parent
      (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hParent
  unfold componentVertexFlowDataFamily
  rw [WellFounded.fix_eq]
  simp [hyρ, hβα, hRoot, hNotUnary]
  congr
  all_goals first
    | exact proof_irrel_heq _ _
    | simp [hβα, hRoot, hNotUnary]

theorem componentVertexFlowDataFamily_unary_choice_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    {y : ComponentY A C}
    (hyρ : y.1 ≠ ρ)
    (hRoot :
      (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ).1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).1
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).2).card = 1) :
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).incoming =
        (componentVertexFlowDataFamily
          (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
          (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree
            (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree y hyρ))).flow.label
          ⟨(componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree y hyρ).1,
            componentYUnaryBlockChildrenExceptRoot_mem_of_parent
              (A := A)
              (componentBlockParentYChoice_parent
                (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree
                (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
                  hTle hTtree y hyρ))
              hUnary (fun _ => hRoot)⟩ := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let αc : ComponentBlock A C :=
    componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree y hyρ
  have hRootc : αc.1 ≠ αRoot.1 := by
    simpa [αc] using hRoot
  have hUnaryc :
      (incidenceYChildren T root αc.1 αc.2).card = 1 := by
    simpa [root, αc] using hUnary
  let pc : ComponentY A C :=
    componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αc
  have hParentY :
      IsRootParent T root (componentYVertex pc) ⟨Sum.inr αc.1, αc.2⟩ := by
    simpa [root, αc, pc] using
      componentBlockParentYChoice_parent
        (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree αc
  have hOrdinary :
      αc.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T root ρ αRoot.1 pc :=
    componentYUnaryBlockChildrenExceptRoot_mem_of_parent
      (A := A) hParentY hUnaryc (fun _ => hRootc)
  let parentTarget : ZMod m :=
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      pc).flow.label ⟨αc.1, hOrdinary⟩
  change
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).incoming = parentTarget
  unfold componentVertexFlowDataFamily
  rw [WellFounded.fix_eq]
  simp [root, αc, pc, parentTarget, componentVertexFlowDataFamily, hyρ,
    hRootc, hUnaryc]

/-- Well-founded construction of the vertex-local top-down flow data.  The
recursive call is used only in the unary-source case, where the parent
`Y`-vertex is strictly closer to the root. -/
theorem componentVertexFlowDataFamily_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m) :
    Nonempty
      (forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y) := by
  classical
  exact
    ⟨componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary⟩

/-- The parts of the component-block assignment that do not depend on the
top-down unary labels can be selected up front: the distinguished root block
uses the active set `{root} ∪ children(rootBlock)`, while every other
non-unary block uses its full child set. -/
theorem componentRootAndNonUnaryResiduePatterns_exists
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    {Y Block : Type} [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    (hA : forall α : Block, (A α).card = a)
    {ρ y0 : Y}
    {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {hy0 : (Sum.inl y0 : IncidenceVertex Y Block) ∈ C.supp}
    {α0 : Block}
    {hα0 : (Sum.inr α0 : IncidenceVertex Y Block) ∈ C.supp}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr α0, hα0⟩)
    (hy0ρ : y0 ≠ ρ)
    (hAlphaY :
      T.Adj ⟨Sum.inr α0, hα0⟩ ⟨Sum.inl y0, hy0⟩) :
    ∃ _ :
        ReplicatedBlockResiduePattern
          (A α0)
          (insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α0 hα0))
          (a / 2) m,
    ∃ _ :
        forall α : ComponentBlock A C,
          α.1 ≠ α0 ->
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
            ReplicatedBlockResiduePattern
              (A α.1)
              (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
              (a / 2) m,
      True := by
  classical
  rcases incidenceRootBlockResiduePattern_nonempty_of_branch
      (A := A) hmOdd hm3 hTle hTtree (hA α0)
      hRootAlpha hy0ρ hAlphaY with
    ⟨PRoot⟩
  let PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ α0 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m :=
    fun α _ hNotUnary =>
      Classical.choice
        (incidenceNonUnaryChildResiduePattern_nonempty
          (A := A) hmOdd hm3 hTle (hA α.1) hNotUnary)
  exact ⟨PRoot, PNonUnary, trivial⟩

/-- Choice wrapper for the ordinary-unary block data. -/
noncomputable def componentOrdinaryUnaryBlockDataChoice
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hNotRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1) :
    ComponentOrdinaryUnaryBlockData T ⟨Sum.inl ρ, hρ⟩ ρ αRoot α :=
  by
    classical
    let root : C := ⟨Sum.inl ρ, hρ⟩
    let p : ComponentY A C :=
      componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree α
    have hParent :
        IsRootParent T root (componentYVertex p) ⟨Sum.inr α.1, α.2⟩ := by
      simpa [root, p] using
        componentBlockParentYChoice_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree α
    let q : Y :=
      Classical.choose
        (Finset.card_eq_one.mp (by simpa [root] using hUnary))
    have hqEq : incidenceYChildren T root α.1 α.2 = {q} :=
      Classical.choose_spec
        (Finset.card_eq_one.mp (by simpa [root] using hUnary))
    have hqChild : q ∈ incidenceYChildren T root α.1 α.2 := by
      simp [root, hqEq]
    let hqData := (mem_incidenceYChildren T root α.1 α.2 q).mp hqChild
    let hqC : (Sum.inl q : IncidenceVertex Y Block) ∈ C.supp :=
      Classical.choose hqData
    have hChild :
        IsRootParent T root ⟨Sum.inr α.1, α.2⟩ ⟨Sum.inl q, hqC⟩ :=
      Classical.choose_spec hqData
    let child : ComponentY A C := ⟨q, hqC⟩
    have hChild' :
        IsRootParent T root ⟨Sum.inr α.1, α.2⟩
          (componentYVertex child) := by
      simpa [componentYVertex, child] using hChild
    have hChildMem : child ∈ componentBlockYChildren T root α := by
      rw [mem_componentBlockYChildren]
      simpa [child] using hqChild
    have hOrdinary :
        α.1 ∈ componentYUnaryBlockChildrenExceptRoot
          T root ρ αRoot.1 p :=
      componentYUnaryBlockChildrenExceptRoot_mem_of_parent
        (A := A) hParent (by simpa [root] using hUnary)
        (fun _ => hNotRoot)
    exact
      { not_root := hNotRoot
        unary := by simpa [root] using hUnary
        parent := p
        child := child
        parent_rel := hParent
        child_rel := hChild'
        ordinary_mem := hOrdinary
        child_mem := hChildMem }

theorem componentOrdinaryUnaryBlockDataChoice_parent_eq_of_mem
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (hNotRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hOrdinary :
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    (componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hNotRoot hUnary).parent = y := by
  classical
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hNotRoot hUnary
  have hUnaryMem :
      α.1 ∈ incidenceUnaryBlockChildren
        T ⟨Sum.inl ρ, hρ⟩ y.1 y.2 :=
    componentYUnaryBlockChildrenExceptRoot_subset
      T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y hOrdinary
  have hParentY :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        (componentYVertex y) ⟨Sum.inr α.1, α.2⟩ := by
    have h :=
      incidenceUnaryBlockChildren_parent (A := A) hUnaryMem
    simpa [componentYVertex] using h
  exact componentBlockParentY_unique (A := A) hTtree D.parent_rel hParentY

theorem componentOrdinaryUnaryBlockDataChoice_child_eq_of_child
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (hNotRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    (componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hNotRoot hUnary).child = y := by
  classical
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hNotRoot hUnary
  exact componentBlockYChildren_eq_of_card_one
    (A := A) hUnary D.child_mem hyChild

/-- The active set assigned to a component block by the top-down shortcut:
the distinguished root block uses `{root} ∪ children`, ordinary unary blocks
use their parent-child pair, and all other blocks use their child set. -/
noncomputable def componentBlockActiveSet
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (αRoot : ComponentBlock A C) (α : ComponentBlock A C) :
    Finset Y := by
  classical
  by_cases hRoot : α.1 = αRoot.1
  · exact insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
  · by_cases hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1
    · let D :=
        componentOrdinaryUnaryBlockDataChoice
          (A := A) hTle hTtree hRoot hUnary
      exact ({D.parent.1, D.child.1} : Finset Y)
    · exact incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2

theorem componentBlockActiveSet_root_eq
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 = αRoot.1) :
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α =
        insert ρ (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2) := by
  classical
  unfold componentBlockActiveSet
  simp [hRoot]

theorem componentBlockActiveSet_nonunary_eq
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hNotUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1) :
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α =
        incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 := by
  classical
  unfold componentBlockActiveSet
  simp [hRoot, hNotUnary]

theorem componentBlockActiveSet_unary_eq
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1) :
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α =
        ({D.parent.1, D.child.1} : Finset Y) := by
  classical
  dsimp
  unfold componentBlockActiveSet
  simp [hRoot, hUnary]

theorem mem_componentBlockActiveSet_root
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 = αRoot.1) :
    y ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α ↔
        y = ρ ∨ y ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 := by
  classical
  rw [componentBlockActiveSet_root_eq (A := A) hTle hTtree hRoot]
  simp

theorem mem_componentBlockActiveSet_nonunary
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hNotUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1) :
    y ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α ↔
        y ∈ incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 := by
  classical
  rw [componentBlockActiveSet_nonunary_eq
    (A := A) hTle hTtree hRoot hNotUnary]

theorem mem_componentBlockActiveSet_unary
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ y : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1) :
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    y ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α ↔ y = D.parent.1 ∨ y = D.child.1 := by
  classical
  dsimp
  rw [componentBlockActiveSet_unary_eq (A := A) hTle hTtree hRoot hUnary]
  simp

theorem componentBlockActiveSet_mem_of_ordinary_parent
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hOrdinary :
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    y.1 ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α := by
  classical
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hRoot hUnary
  have hParent :
      D.parent = y :=
    componentOrdinaryUnaryBlockDataChoice_parent_eq_of_mem
      (A := A) hTle hTtree hRoot hUnary hOrdinary
  rw [componentBlockActiveSet_unary_eq (A := A) hTle hTtree hRoot hUnary]
  simp [D, hParent]

theorem componentBlockActiveSet_mem_of_unary_child
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    y.1 ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α := by
  classical
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hRoot hUnary
  have hChild :
      D.child = y :=
    componentOrdinaryUnaryBlockDataChoice_child_eq_of_child
      (A := A) hTle hTtree hRoot hUnary hyChild
  rw [componentBlockActiveSet_unary_eq (A := A) hTle hTtree hRoot hUnary]
  simp [D, hChild]

theorem componentOrdinaryUnaryBlockPattern_child_zmod_of_child
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    ((replicatedBlockColumnDegree
      ((componentOrdinaryUnaryBlockPattern
        (A := A) hTle hmpos hA ha2 D (flow D.parent).flow).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow D.parent).flow.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  dsimp
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hRoot hUnary
  have hChild : D.child = y :=
    componentOrdinaryUnaryBlockDataChoice_child_eq_of_child
      (A := A) hTle hTtree hRoot hUnary hyChild
  have h :=
    componentOrdinaryUnaryBlockPattern_child_zmod
      (A := A) hTle hmpos hA ha2 D (flow D.parent).flow
  simpa [D, hChild] using h

theorem componentOrdinaryUnaryBlockPattern_parent_zmod_of_mem
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hOrdinary :
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    ((replicatedBlockColumnDegree
      ((componentOrdinaryUnaryBlockPattern
        (A := A) hTle hmpos hA ha2 D (flow D.parent).flow).toChoice)
      y.1 : Nat) : ZMod m) =
        -(flow y).flow.label ⟨α.1, hOrdinary⟩ := by
  classical
  dsimp
  let D :=
    componentOrdinaryUnaryBlockDataChoice
      (A := A) hTle hTtree hRoot hUnary
  have hParent : D.parent = y :=
    componentOrdinaryUnaryBlockDataChoice_parent_eq_of_mem
      (A := A) hTle hTtree hRoot hUnary hOrdinary
  subst hParent
  have hLabel :
      (flow D.parent).flow.label ⟨α.1, D.ordinary_mem⟩ =
        (flow D.parent).flow.label ⟨α.1, hOrdinary⟩ := by
    congr
  have h :=
    componentOrdinaryUnaryBlockPattern_parent_zmod
      (A := A) hTle hmpos hA ha2 D (flow D.parent).flow
  simpa [D, hLabel] using h

theorem componentBlockActiveSet_subset
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    (α : ComponentBlock A C) :
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α ⊆ A α.1 := by
  classical
  unfold componentBlockActiveSet
  by_cases hRoot : α.1 = αRoot.1
  · have hαeq : α = αRoot := Subtype.ext hRoot
    subst α
    simpa [hRoot] using
      incidenceRootBlockActiveSet_subset (A := A) hTle hRootAlpha
  · by_cases hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1
    · let D :=
        componentOrdinaryUnaryBlockDataChoice
          (A := A) hTle hTtree hRoot hUnary
      simpa [hRoot, hUnary, D] using
        componentOrdinaryUnaryBlockData_pair_subset (A := A) hTle D
    · simpa [hRoot, hUnary] using
        (incidenceYChildren_subset (A := A) hTle :
          incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2 ⊆ A α.1)

/-- Each active set supplied by `componentBlockActiveSet` has an already
constructed local residue pattern, once the root/non-unary reservoirs and the
top-down vertex flow family have been chosen. -/
theorem componentBlockActivePattern_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (α : ComponentBlock A C) :
    Nonempty
      (ReplicatedBlockResiduePattern
        (A α.1)
        (componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot α)
        (a / 2) m) := by
  classical
  unfold componentBlockActiveSet
  by_cases hRoot : α.1 = αRoot.1
  · have hαeq : α = αRoot := Subtype.ext hRoot
    subst α
    exact ⟨by simpa [hRoot] using PRoot⟩
  · by_cases hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1
    · let D :=
        componentOrdinaryUnaryBlockDataChoice
          (A := A) hTle hTtree hRoot hUnary
      rcases componentOrdinaryUnaryBlockData_flowTransferPattern_exists
          (A := A) hTle hmpos hA ha2 D (flow D.parent).flow with
        ⟨P, _hChild, _hParent⟩
      exact ⟨by simpa [hRoot, hUnary, D] using P⟩
    · exact ⟨by simpa [hRoot, hUnary] using PNonUnary α hRoot hUnary⟩

/-- The concrete local residue pattern assigned to one component block by the
top-down construction.  This preserves the case distinction needed for the
final contribution-sum proof. -/
noncomputable def componentBlockActivePattern
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (α : ComponentBlock A C) :
    ReplicatedBlockResiduePattern
      (A α.1)
      (componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot α)
      (a / 2) m := by
  classical
  by_cases hRoot : α.1 = αRoot.1
  · have hαeq : α = αRoot := Subtype.ext hRoot
    subst α
    refine
      { toChoice := PRoot.toChoice
        active_coprime := ?_
        inactive_dvd := ?_ }
    · intro y hy
      exact PRoot.active_coprime y
        (by simpa [componentBlockActiveSet] using hy)
    · intro y hyA hyS
      exact PRoot.inactive_dvd y hyA (by
        intro hy
        exact hyS (by simpa [componentBlockActiveSet] using hy))
  · by_cases hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1
    · let D :=
        componentOrdinaryUnaryBlockDataChoice
          (A := A) hTle hTtree hRoot hUnary
      let PU :=
        componentOrdinaryUnaryBlockPattern
          (A := A) hTle hmpos hA ha2 D (flow D.parent).flow
      refine
        { toChoice := PU.toChoice
          active_coprime := ?_
          inactive_dvd := ?_ }
      · intro y hy
        exact PU.active_coprime y
          (by simpa [componentBlockActiveSet, hRoot, hUnary, D, PU] using hy)
      · intro y hyA hyS
        exact PU.inactive_dvd y hyA (by
          intro hy
          exact hyS
            (by simpa [componentBlockActiveSet, hRoot, hUnary, D, PU] using hy))
    · let PN := PNonUnary α hRoot hUnary
      refine
        { toChoice := PN.toChoice
          active_coprime := ?_
          inactive_dvd := ?_ }
      · intro y hy
        exact PN.active_coprime y
          (by simpa [componentBlockActiveSet, hRoot, hUnary, PN] using hy)
      · intro y hyA hyS
        exact PN.inactive_dvd y hyA (by
          intro hy
          exact hyS
            (by simpa [componentBlockActiveSet, hRoot, hUnary, PN] using hy))

theorem componentBlockActivePattern_root_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y) :
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        αRoot).toChoice)
      ρ : Nat) : ZMod m) =
        ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m) := by
  classical
  simp [componentBlockActivePattern, componentBlockActiveSet]

theorem componentBlockActivePattern_root_child_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (y : ComponentY A C) :
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        αRoot).toChoice)
      y.1 : Nat) : ZMod m) =
        ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) : ZMod m) := by
  classical
  simp [componentBlockActivePattern, componentBlockActiveSet]

theorem componentBlockActivePattern_nonunary_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (hRoot : α.1 ≠ αRoot.1)
    (hNotUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1)
    (y : Y) :
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y : Nat) : ZMod m) =
        ((replicatedBlockColumnDegree
          ((PNonUnary α hRoot hNotUnary).toChoice) y : Nat) : ZMod m) := by
  classical
  simp [componentBlockActivePattern, componentBlockActiveSet, hRoot, hNotUnary]

theorem componentBlockActivePattern_unary_child_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow D.parent).flow.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  dsimp
  simpa [componentBlockActivePattern, componentBlockActiveSet, hRoot, hUnary]
    using
      componentOrdinaryUnaryBlockPattern_child_zmod_of_child
        (A := A) hTle hTtree hmpos hA ha2 flow hRoot hUnary hyChild

theorem componentBlockActivePattern_unary_parent_zmod
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hOrdinary :
      α.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y.1 : Nat) : ZMod m) =
        -(flow y).flow.label ⟨α.1, hOrdinary⟩ := by
  classical
  simpa [componentBlockActivePattern, componentBlockActiveSet, hRoot, hUnary]
    using
      componentOrdinaryUnaryBlockPattern_parent_zmod_of_mem
        (A := A) hTle hTtree hmpos hA ha2 flow hRoot hUnary hOrdinary

theorem componentBlockActivePattern_unary_child_zmod_eq_parent_flow_label
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    let D :=
      componentOrdinaryUnaryBlockDataChoice
        (A := A) hTle hTtree hRoot hUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow D.parent).flow.label ⟨α.1, D.ordinary_mem⟩ := by
  classical
  dsimp
  let flow :=
    componentVertexFlowDataFamily
      (A := A) (ρ := ρ) (hρ := hρ) (αRoot := αRoot)
      hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  simpa [flow] using
    componentBlockActivePattern_unary_child_zmod
      (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
      hRoot hUnary hyChild

theorem componentBlockActivePattern_unary_child_zmod_eq_flow_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hRoot : α.1 ≠ αRoot.1)
    (hUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card = 1)
    (hyChild : y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ α) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming := by
  classical
  dsimp
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) (ρ := ρ) (hρ := hρ) (αRoot := αRoot)
      hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  have hChildRaw :
      y.1 ∈ incidenceYChildren T root α.1 α.2 :=
    (mem_componentBlockYChildren T root α y).mp hyChild
  have hyρ : y.1 ≠ ρ := by
    intro hyEq
    exact root_not_mem_incidenceYChildren
      (A := A) (T := T) (hρ := hρ) (hα := α.2)
      (by simpa [root, hyEq] using hChildRaw)
  have hChildParent :
      IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) := by
    rcases (mem_incidenceYChildren T root α.1 α.2 y.1).mp hChildRaw with
      ⟨_hyC, hParent⟩
    simpa [root, componentYVertex] using hParent
  have hChoice :
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ = α :=
    componentYParentBlockChoice_eq_of_parent
      (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hChildParent
  have hChoiceRoot :
      (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ).1 ≠ αRoot.1 := by
    simpa [hChoice] using hRoot
  have hChoiceUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).1
        (componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree y hyρ).2).card = 1 := by
    simpa [hChoice] using hUnary
  have hIncoming :
      (flow y).incoming =
        (flow
          (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree α)).flow.label
          ⟨α.1,
            componentYUnaryBlockChildrenExceptRoot_mem_of_parent
              (A := A)
              (componentBlockParentYChoice_parent
                (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree α)
              hUnary (fun _ => hRoot)⟩ := by
    have h :=
      componentVertexFlowDataFamily_unary_choice_incoming
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hyρ hChoiceRoot hChoiceUnary
    cases hChoice
    simpa [flow] using h
  have hActive :
      ((replicatedBlockColumnDegree
        ((componentBlockActivePattern
          (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
          α).toChoice)
        y.1 : Nat) : ZMod m) =
          (flow
            (componentBlockParentYChoice (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree α)).flow.label
            ⟨α.1,
              componentYUnaryBlockChildrenExceptRoot_mem_of_parent
                (A := A)
                (componentBlockParentYChoice_parent
                  (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree α)
                hUnary (fun _ => hRoot)⟩ := by
    simpa [flow, componentOrdinaryUnaryBlockDataChoice, root] using
      componentBlockActivePattern_unary_child_zmod_eq_parent_flow_label
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hRoot hUnary hyChild
  exact hActive.trans hIncoming.symm

theorem componentBlockActivePattern_root_zmod_eq_flow_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hyρ : y.1 = ρ) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        αRoot).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming := by
  classical
  dsimp
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  have hActive :
      ((replicatedBlockColumnDegree
        ((componentBlockActivePattern
          (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
          αRoot).toChoice)
        y.1 : Nat) : ZMod m) =
          ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m) := by
    simpa [flow, hyρ] using
      componentBlockActivePattern_root_zmod
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
  have hIncoming :
      (flow y).incoming =
        ((replicatedBlockColumnDegree PRoot.toChoice ρ : Nat) : ZMod m) := by
    simpa [flow] using
      componentVertexFlowDataFamily_root_incoming
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hyρ
  exact hActive.trans hIncoming.symm

theorem componentBlockActivePattern_root_child_zmod_eq_flow_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hyρ : y.1 ≠ ρ)
    (hyChild :
      y ∈ componentBlockYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        αRoot).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming := by
  classical
  dsimp
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  have hActive :
      ((replicatedBlockColumnDegree
        ((componentBlockActivePattern
          (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
          αRoot).toChoice)
        y.1 : Nat) : ZMod m) =
          ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) :
            ZMod m) := by
    simpa [flow] using
      componentBlockActivePattern_root_child_zmod
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow y
  have hIncoming :
      (flow y).incoming =
        ((replicatedBlockColumnDegree PRoot.toChoice y.1 : Nat) :
          ZMod m) := by
    simpa [flow] using
      componentVertexFlowDataFamily_rootBlock_incoming
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hyρ hyChild
  exact hActive.trans hIncoming.symm

theorem componentBlockActivePattern_nonunary_zmod_eq_flow_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot α : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hyρ : y.1 ≠ ρ)
    (hParent :
      IsRootParent T ⟨Sum.inl ρ, hρ⟩
        ⟨Sum.inr α.1, α.2⟩ (componentYVertex y))
    (hRoot : α.1 ≠ αRoot.1)
    (hNotUnary :
      (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        α).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming := by
  classical
  dsimp
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  have hActive :
      ((replicatedBlockColumnDegree
        ((componentBlockActivePattern
          (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
          α).toChoice)
        y.1 : Nat) : ZMod m) =
          ((replicatedBlockColumnDegree
            ((PNonUnary α hRoot hNotUnary).toChoice) y.1 : Nat) :
            ZMod m) := by
    simpa [flow] using
      componentBlockActivePattern_nonunary_zmod
        (A := A) hTle hTtree hmpos hA ha2
        PRoot PNonUnary flow hRoot hNotUnary y.1
  have hIncoming :
      (flow y).incoming =
        ((replicatedBlockColumnDegree
          ((PNonUnary α hRoot hNotUnary).toChoice) y.1 : Nat) :
          ZMod m) := by
    simpa [flow] using
      componentVertexFlowDataFamily_nonUnary_incoming
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hyρ hParent hRoot hNotUnary
  exact hActive.trans hIncoming.symm

/-- The unique block supplying the incoming contribution at a component
`Y`-vertex: the distinguished root block at the root vertex, and otherwise
the rooted-tree parent block. -/
noncomputable def componentYIncomingBlock
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    (αRoot : ComponentBlock A C) (y : ComponentY A C) :
    ComponentBlock A C := by
  classical
  by_cases hyρ : y.1 = ρ
  · exact αRoot
  · exact componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree y hyρ

theorem componentYIncomingBlock_active_zmod_eq_flow_incoming
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        (componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y)).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  change
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        (componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y)).toChoice)
      y.1 : Nat) : ZMod m) =
        (flow y).incoming
  by_cases hyρ : y.1 = ρ
  · have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = αRoot := by
      unfold componentYIncomingBlock
      simp [hyρ]
    rw [hSource]
    exact
      componentBlockActivePattern_root_zmod_eq_flow_incoming
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        PRoot PNonUnary hyρ
  · let α : ComponentBlock A C :=
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ
    have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = α := by
      unfold componentYIncomingBlock
      simp [hyρ, α]
    have hParent :
        IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) := by
      simpa [root, α] using
        componentYParentBlockChoice_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree y hyρ
    by_cases hRootVal : α.1 = αRoot.1
    · have hαeq : α = αRoot := Subtype.ext hRootVal
      have hyChild : y ∈ componentBlockYChildren T root αRoot := by
        simpa [root, hαeq] using componentYParentBlock_mem_children hParent
      rw [hSource, hαeq]
      exact
        componentBlockActivePattern_root_child_zmod_eq_flow_incoming
          (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
          PRoot PNonUnary hyρ hyChild
    · by_cases hUnary :
        (incidenceYChildren T root α.1 α.2).card = 1
      · have hyChild : y ∈ componentBlockYChildren T root α := by
          simpa [root] using componentYParentBlock_mem_children hParent
        rw [hSource]
        exact
          componentBlockActivePattern_unary_child_zmod_eq_flow_incoming
            (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
            PRoot PNonUnary hRootVal (by simpa [root] using hUnary)
            hyChild
      · rw [hSource]
        exact
          componentBlockActivePattern_nonunary_zmod_eq_flow_incoming
            (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
            PRoot PNonUnary hyρ (by simpa [root] using hParent)
            hRootVal (by simpa [root] using hUnary)

theorem componentYIncomingBlock_mem_activeSet
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C} :
    y.1 ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot
      (componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot y) := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  by_cases hyρ : y.1 = ρ
  · have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = αRoot := by
      unfold componentYIncomingBlock
      simp [hyρ]
    rw [hSource]
    have hmem :
        y.1 = ρ ∨
          y.1 ∈ incidenceYChildren T root αRoot.1 αRoot.2 :=
      Or.inl hyρ
    exact
      (mem_componentBlockActiveSet_root
        (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
        (y := y.1) (αRoot := αRoot) (α := αRoot) rfl).mpr
        (by simpa [root] using hmem)
  · let α : ComponentBlock A C :=
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ
    have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = α := by
      unfold componentYIncomingBlock
      simp [hyρ, α]
    have hParent :
        IsRootParent T root ⟨Sum.inr α.1, α.2⟩ (componentYVertex y) := by
      simpa [root, α] using
        componentYParentBlockChoice_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree y hyρ
    have hyChild : y ∈ componentBlockYChildren T root α :=
      componentYParentBlock_mem_children hParent
    rw [hSource]
    by_cases hRootVal : α.1 = αRoot.1
    · have hαeq : α = αRoot := Subtype.ext hRootVal
      have hyChildRoot : y ∈ componentBlockYChildren T root αRoot := by
        simpa [hαeq] using hyChild
      have hmem :
          y.1 = ρ ∨
            y.1 ∈ incidenceYChildren T root αRoot.1 αRoot.2 :=
        Or.inr ((mem_componentBlockYChildren T root αRoot y).mp hyChildRoot)
      have hTarget :
          y.1 ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot αRoot :=
        (mem_componentBlockActiveSet_root
          (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
          (y := y.1) (αRoot := αRoot) (α := αRoot) rfl).mpr
          (by simpa [root] using hmem)
      simpa [hαeq] using hTarget
    · by_cases hUnary :
        (incidenceYChildren T root α.1 α.2).card = 1
      · exact componentBlockActiveSet_mem_of_unary_child
          (A := A) hTle hTtree hRootVal (by simpa [root] using hUnary)
          (by simpa [root] using hyChild)
      · exact
          (mem_componentBlockActiveSet_nonunary
            (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
            (y := y.1) (αRoot := αRoot) (α := α)
            hRootVal (by simpa [root] using hUnary)).mpr
            ((mem_componentBlockYChildren T root α y).mp hyChild)

theorem componentBlockActiveSet_mem_source_or_unaryChild
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot β : ComponentBlock A C} {y : ComponentY A C}
    (hmem :
      y.1 ∈ componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot β) :
    β = componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot y ∨
      β.1 ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  by_cases hβRoot : β.1 = αRoot.1
  · have hβeq : β = αRoot := Subtype.ext hβRoot
    have hmemRoot :
        y.1 = ρ ∨
          y.1 ∈ incidenceYChildren T root β.1 β.2 :=
      (mem_componentBlockActiveSet_root
        (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
        (y := y.1) (αRoot := αRoot) (α := β) hβRoot).mp hmem
    rcases hmemRoot with hyρ | hyChild
    · left
      have hSource :
          componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot y = αRoot := by
        unfold componentYIncomingBlock
        simp [hyρ]
      rw [hβeq, hSource]
    · left
      have hyChildRoot :
          y.1 ∈ incidenceYChildren T root αRoot.1 αRoot.2 := by
        simpa [root, hβeq] using hyChild
      have hyρ : y.1 ≠ ρ := by
        intro hy
        exact root_not_mem_incidenceYChildren
          (A := A) (T := T) (hρ := hρ) (hα := αRoot.2)
          (by simpa [root, hy] using hyChildRoot)
      have hParent :
          IsRootParent T root
            ⟨Sum.inr αRoot.1, αRoot.2⟩ (componentYVertex y) := by
        rcases (mem_incidenceYChildren T root αRoot.1 αRoot.2 y.1).mp
            hyChildRoot with
          ⟨_hyC, hParent⟩
        simpa [root, componentYVertex] using hParent
      have hChoice :
          componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree y hyρ = αRoot :=
        componentYParentBlockChoice_eq_of_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hParent
      have hSource :
          componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot y = αRoot := by
        unfold componentYIncomingBlock
        simp [hyρ, hChoice]
      rw [hβeq, hSource]
  · by_cases hUnary :
      (incidenceYChildren T root β.1 β.2).card = 1
    · let D :=
        componentOrdinaryUnaryBlockDataChoice
          (A := A) hTle hTtree hβRoot (by simpa [root] using hUnary)
      have hmemPair :
          y.1 = D.parent.1 ∨ y.1 = D.child.1 := by
        simpa [root, D] using
          (mem_componentBlockActiveSet_unary
            (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
            (y := y.1) (αRoot := αRoot) (α := β)
            hβRoot (by simpa [root] using hUnary)).mp hmem
      rcases hmemPair with hParentVal | hChildVal
      · right
        have hParentEq : D.parent = y := Subtype.ext hParentVal.symm
        simpa [root, D, hParentEq] using D.ordinary_mem
      · left
        have hChildEq : D.child = y := Subtype.ext hChildVal.symm
        have hyChild : y ∈ componentBlockYChildren T root β := by
          simpa [root, D, hChildEq] using D.child_mem
        have hChildRaw :
            y.1 ∈ incidenceYChildren T root β.1 β.2 :=
          (mem_componentBlockYChildren T root β y).mp hyChild
        have hyρ : y.1 ≠ ρ := by
          intro hy
          exact root_not_mem_incidenceYChildren
            (A := A) (T := T) (hρ := hρ) (hα := β.2)
            (by simpa [root, hy] using hChildRaw)
        have hParent :
            IsRootParent T root
              ⟨Sum.inr β.1, β.2⟩ (componentYVertex y) := by
          simpa [root, D, hChildEq] using D.child_rel
        have hChoice :
            componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree y hyρ = β :=
          componentYParentBlockChoice_eq_of_parent
            (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hParent
        have hSource :
            componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
              hTle hTtree αRoot y = β := by
          unfold componentYIncomingBlock
          simp [hyρ, hChoice]
        exact hSource.symm
    · left
      have hChildRaw :
          y.1 ∈ incidenceYChildren T root β.1 β.2 := by
        exact
          (mem_componentBlockActiveSet_nonunary
            (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
            (y := y.1) (αRoot := αRoot) (α := β)
            hβRoot (by simpa [root] using hUnary)).mp hmem
      have hyρ : y.1 ≠ ρ := by
        intro hy
        exact root_not_mem_incidenceYChildren
          (A := A) (T := T) (hρ := hρ) (hα := β.2)
          (by simpa [root, hy] using hChildRaw)
      have hParent :
          IsRootParent T root
            ⟨Sum.inr β.1, β.2⟩ (componentYVertex y) := by
        rcases (mem_incidenceYChildren T root β.1 β.2 y.1).mp
            hChildRaw with
          ⟨_hyC, hParent⟩
        simpa [root, componentYVertex] using hParent
      have hChoice :
          componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree y hyρ = β :=
        componentYParentBlockChoice_eq_of_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree hyρ hParent
      have hSource :
          componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot y = β := by
        unfold componentYIncomingBlock
        simp [hyρ, hChoice]
      exact hSource.symm

theorem componentYIncomingBlock_not_mem_unaryChildrenExceptRoot
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C} :
    (componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot y).1 ∉
        componentYUnaryBlockChildrenExceptRoot
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  by_cases hyρ : y.1 = ρ
  · have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = αRoot := by
      unfold componentYIncomingBlock
      simp [hyρ]
    intro hmem
    have hroot :
        y = (⟨ρ, hρ⟩ : ComponentY A C) := Subtype.ext hyρ
    have hmemSource := hmem
    rw [hSource] at hmemSource
    have hmemRoot :
        αRoot.1 ∈
          componentYUnaryBlockChildrenExceptRoot
            T root ρ αRoot.1 (⟨ρ, hρ⟩ : ComponentY A C) := by
      simpa [root, hroot] using hmemSource
    exact componentYUnaryBlockChildrenExceptRoot_root_not_mem
      (A := A) T αRoot.1 hmemRoot
  · let src : ComponentBlock A C :=
      componentYParentBlockChoice (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree y hyρ
    have hSource :
        componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
          hTle hTtree αRoot y = src := by
      unfold componentYIncomingBlock
      simp [hyρ, src]
    intro hmem
    have hmemSrc :
        src.1 ∈ componentYUnaryBlockChildrenExceptRoot
          T root ρ αRoot.1 y := by
      simpa [root, hSource] using hmem
    have hUnaryMem :
        src.1 ∈ incidenceUnaryBlockChildren T root y.1 y.2 :=
      componentYUnaryBlockChildrenExceptRoot_subset
        T root ρ αRoot.1 y hmemSrc
    have hParentForward :
        IsRootParent T root ⟨Sum.inr src.1, src.2⟩
          (componentYVertex y) := by
      simpa [root, src] using
        componentYParentBlockChoice_parent
          (A := A) (ρ := ρ) (hρ := hρ) hTle hTtree y hyρ
    have hParentBackward :
        IsRootParent T root (componentYVertex y)
          ⟨Sum.inr src.1, src.2⟩ := by
      have h :=
        incidenceUnaryBlockChildren_parent (A := A) hUnaryMem
      simpa [root, src] using h
    have hdistForward := hParentForward.2
    have hdistBackward := hParentBackward.2
    omega

theorem componentYUnaryBlockChildrenExceptRoot_ne_rootBlock
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTtree : T.IsTree)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    {y : ComponentY A C} {α : Block}
    (hOrdinary :
      α ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    α ≠ αRoot.1 := by
  classical
  intro hEq
  let root : C := ⟨Sum.inl ρ, hρ⟩
  have hUnaryMem :
      α ∈ incidenceUnaryBlockChildren T root y.1 y.2 :=
    componentYUnaryBlockChildrenExceptRoot_subset
      T root ρ αRoot.1 y hOrdinary
  have hParentY :
      IsRootParent T root (componentYVertex y)
        ⟨Sum.inr α,
          incidenceUnaryBlockChildren_block_mem_component
            (A := A) hUnaryMem⟩ :=
    incidenceUnaryBlockChildren_parent (A := A) hUnaryMem
  have hParentYRoot :
      IsRootParent T root (componentYVertex y)
        ⟨Sum.inr αRoot.1, αRoot.2⟩ := by
    subst hEq
    simpa [root] using hParentY
  have hRootParent :
      IsRootParent T root (componentYVertex (⟨ρ, hρ⟩ : ComponentY A C))
        ⟨Sum.inr αRoot.1, αRoot.2⟩ := by
    simpa [root, componentYVertex] using isRootParent_root_of_adj hRootAlpha
  have hyRoot :
      y = (⟨ρ, hρ⟩ : ComponentY A C) :=
    componentBlockParentY_unique (A := A) hTtree hParentYRoot hRootParent
  have hyρ : y.1 = ρ := congrArg Subtype.val hyRoot
  have hExcept :=
    (mem_componentYUnaryBlockChildrenExceptRoot
      T root ρ αRoot.1 y α).mp hOrdinary
  exact hExcept.2 hyρ hEq

theorem componentYUnaryBlockChildrenExceptRoot_active_zmod_eq_neg_flow_label
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    {y : ComponentY A C} {α : Block}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (hOrdinary :
      α ∈ componentYUnaryBlockChildrenExceptRoot
        T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    let hα :
      (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp :=
        incidenceUnaryBlockChildren_block_mem_component
          (A := A)
          (componentYUnaryBlockChildrenExceptRoot_subset
            T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y hOrdinary)
    let β : ComponentBlock A C := ⟨α, hα⟩
    ((replicatedBlockColumnDegree
      ((componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
        β).toChoice)
      y.1 : Nat) : ZMod m) =
        -(flow y).flow.label ⟨α, hOrdinary⟩ := by
  classical
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  let hUnaryMem :
      α ∈ incidenceUnaryBlockChildren T root y.1 y.2 :=
    componentYUnaryBlockChildrenExceptRoot_subset
      T root ρ αRoot.1 y hOrdinary
  let hα :
      (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp :=
    incidenceUnaryBlockChildren_block_mem_component (A := A) hUnaryMem
  let β : ComponentBlock A C := ⟨α, hα⟩
  have hRoot :
      β.1 ≠ αRoot.1 :=
    componentYUnaryBlockChildrenExceptRoot_ne_rootBlock
      (A := A) hTtree hRootAlpha hOrdinary
  have hUnary :
      (incidenceYChildren T root β.1 β.2).card = 1 := by
    simpa [root, β, hα, hUnaryMem] using
      incidenceUnaryBlockChildren_child_card_eq_one
        (A := A) hUnaryMem
  simpa [flow, root, β, hα, hUnaryMem] using
    componentBlockActivePattern_unary_parent_zmod
      (A := A) hTle hTtree hmpos hA ha2
      PRoot PNonUnary flow hRoot hUnary hOrdinary

theorem componentVertexFlowDataFamily_final_residue_isUnit
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C} {y : ComponentY A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m) :
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    IsUnit
      ((flow y).incoming -
        ∑ α :
          {α : Block //
            α ∈ componentYUnaryBlockChildrenExceptRoot
              T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 y},
          (flow y).flow.label α) := by
  classical
  dsimp
  exact
    (componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
      y).flow.final_unit

theorem componentBlock_sum_if_val_mem_eq_subtype_sum
    {Y Block : Type} [Fintype Block] [DecidableEq Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {m : Nat}
    (U : Finset Block)
    (hU : forall α : Block, α ∈ U ->
      (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)
    (F : ComponentBlock A C -> ZMod m)
    (G : {α : Block // α ∈ U} -> ZMod m)
    (hFG : forall β : ComponentBlock A C,
      forall hβ : β.1 ∈ U, F β = G ⟨β.1, hβ⟩) :
    (∑ β : ComponentBlock A C,
      if β.1 ∈ U then F β else 0) =
        ∑ α : {α : Block // α ∈ U}, G α := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun β hβ => ⟨β.1, (Finset.mem_filter.mp hβ).2⟩)
    ?mem ?inj ?surj ?compat
  · intro β hβ
    simp
  · intro β _hβ γ _hγ hEq
    have hVal : β.1 = γ.1 :=
      congrArg (fun x : {α : Block // α ∈ U} => x.1) hEq
    exact Subtype.ext hVal
  · intro α _hα
    let β : ComponentBlock A C := ⟨α.1, hU α.1 α.2⟩
    refine ⟨β, ?_, ?_⟩
    · simp [β, α.2]
    · ext
      rfl
  · intro β hβ
    exact hFG β (Finset.mem_filter.mp hβ).2

theorem componentBlock_sum_dite_val_mem_eq_subtype_sum
    {Y Block : Type} [Fintype Block] [DecidableEq Block] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {m : Nat}
    (U : Finset Block)
    (hU : forall α : Block, α ∈ U ->
      (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp)
    (F : forall β : ComponentBlock A C, β.1 ∈ U -> ZMod m)
    (G : {α : Block // α ∈ U} -> ZMod m)
    (hFG : forall β : ComponentBlock A C,
      forall hβ : β.1 ∈ U, F β hβ = G ⟨β.1, hβ⟩) :
    (∑ β : ComponentBlock A C,
      if hβ : β.1 ∈ U then F β hβ else 0) =
        ∑ α : {α : Block // α ∈ U}, G α := by
  classical
  let F0 : ComponentBlock A C -> ZMod m := fun β =>
    if hβ : β.1 ∈ U then F β hβ else 0
  have hReindex :
      (∑ β : ComponentBlock A C,
        if β.1 ∈ U then F0 β else 0) =
          ∑ α : {α : Block // α ∈ U}, G α := by
    exact
      componentBlock_sum_if_val_mem_eq_subtype_sum
        (A := A) (C := C) (m := m) U hU F0 G
        (by
          intro β hβ
          simp [F0, hβ, hFG β hβ])
  have hLeft :
      (∑ β : ComponentBlock A C,
        if β.1 ∈ U then F0 β else 0) =
      (∑ β : ComponentBlock A C,
        if hβ : β.1 ∈ U then F β hβ else 0) := by
    apply Finset.sum_congr rfl
    intro β _hβ
    by_cases hmem : β.1 ∈ U
    · simp [F0, hmem]
    · simp [F0, hmem]
  exact hLeft.symm.trans hReindex

theorem componentBlockActiveContribution_eq_source_plus_unary
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Block]
    [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (y : ComponentY A C) (β : ComponentBlock A C) :
    let root : C := ⟨Sum.inl ρ, hρ⟩
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    let U := componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y
    let src :=
      componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot y
    let S :=
      componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot
    let P :=
      componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
    (if y.1 ∈ S β then
      ((replicatedBlockColumnDegree ((P β).toChoice) y.1 : Nat) : ZMod m)
    else 0) =
      (if β = src then (flow y).incoming else 0) +
        (if hβ : β.1 ∈ U then
          -((flow y).flow.label ⟨β.1, hβ⟩)
        else 0) := by
  classical
  dsimp
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  let U := componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y
  let src :=
    componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot y
  let S :=
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot
  let P :=
    componentBlockActivePattern
      (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
  by_cases hsrc : β = src
  · subst β
    have hmem :
        y.1 ∈ S src := by
      simpa [S, src, root] using
        componentYIncomingBlock_mem_activeSet
          (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
          (αRoot := αRoot) (y := y)
    have hnotU : src.1 ∉ U := by
      simpa [src, U, root] using
        componentYIncomingBlock_not_mem_unaryChildrenExceptRoot
          (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
          (αRoot := αRoot) (y := y)
    have hdeg :
        ((replicatedBlockColumnDegree ((P src).toChoice) y.1 : Nat) :
          ZMod m) = (flow y).incoming := by
      simpa [P, flow, src, root] using
        componentYIncomingBlock_active_zmod_eq_flow_incoming
          (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
          PRoot PNonUnary (y := y)
    rw [if_pos hmem, if_pos rfl]
    rw [dif_neg hnotU]
    simpa using hdeg
  · by_cases hU : β.1 ∈ U
    · have hRoot :
          β.1 ≠ αRoot.1 := by
        exact
          componentYUnaryBlockChildrenExceptRoot_ne_rootBlock
            (A := A) hTtree hRootAlpha hU
      have hUnaryMem :
          β.1 ∈ incidenceUnaryBlockChildren T root y.1 y.2 :=
        componentYUnaryBlockChildrenExceptRoot_subset
          T root ρ αRoot.1 y hU
      have hUnary :
          (incidenceYChildren T root β.1 β.2).card = 1 := by
        simpa [root] using
          incidenceUnaryBlockChildren_child_card_eq_one
            (A := A) hUnaryMem
      have hmem :
          y.1 ∈ S β := by
        simpa [S, root] using
          componentBlockActiveSet_mem_of_ordinary_parent
            (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
            (αRoot := αRoot) (α := β) (y := y)
            hRoot (by simpa [root] using hUnary) hU
      have hdeg :
          ((replicatedBlockColumnDegree ((P β).toChoice) y.1 : Nat) :
            ZMod m) =
              -((flow y).flow.label ⟨β.1, hU⟩) := by
        simpa [P, flow, U, root] using
          componentYUnaryBlockChildrenExceptRoot_active_zmod_eq_neg_flow_label
            (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
            hRootAlpha PRoot PNonUnary (y := y) (α := β.1) hU
      rw [if_pos hmem, if_neg hsrc]
      rw [dif_pos hU]
      simpa using hdeg
    · have hnotmem : y.1 ∉ S β := by
        intro hmem
        rcases componentBlockActiveSet_mem_source_or_unaryChild
            (A := A) hTle hTtree (ρ := ρ) (hρ := hρ)
            (αRoot := αRoot) (β := β) (y := y)
            (by simpa [S, root] using hmem) with hβsrc | hβU
        · exact hsrc (by simpa [src] using hβsrc)
        · exact hU (by simpa [U, root] using hβU)
      rw [if_neg hnotmem, if_neg hsrc]
      rw [dif_neg hU]
      simp

theorem componentBlockActiveContribution_sum_eq_final_residue
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmOdd : Odd m) (hm3 : 3 <= m) (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (y : ComponentY A C) :
    let root : C := ⟨Sum.inl ρ, hρ⟩
    let flow :=
      componentVertexFlowDataFamily
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
    let U := componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y
    let S :=
      componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
        hTle hTtree αRoot
    let P :=
      componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
    (∑ β : ComponentBlock A C,
      if y.1 ∈ S β then
        ((replicatedBlockColumnDegree ((P β).toChoice) y.1 : Nat) : ZMod m)
      else 0) =
        (flow y).incoming -
          ∑ α : {α : Block // α ∈ U}, (flow y).flow.label α := by
  classical
  dsimp
  let root : C := ⟨Sum.inl ρ, hρ⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  let U := componentYUnaryBlockChildrenExceptRoot T root ρ αRoot.1 y
  let src :=
    componentYIncomingBlock (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot y
  let S :=
    componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot
  let P :=
    componentBlockActivePattern
      (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow
  have hPoint :
      forall β : ComponentBlock A C,
        (if y.1 ∈ S β then
          ((replicatedBlockColumnDegree ((P β).toChoice) y.1 : Nat) :
            ZMod m)
        else 0) =
          (if β = src then (flow y).incoming else 0) +
            (if hβ : β.1 ∈ U then
              -((flow y).flow.label ⟨β.1, hβ⟩)
            else 0) := by
    intro β
    simpa [root, flow, U, src, S, P] using
      componentBlockActiveContribution_eq_source_plus_unary
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        hRootAlpha PRoot PNonUnary (y := y) (β := β)
  have hSourceSum :
      (∑ β : ComponentBlock A C,
        if β = src then (flow y).incoming else 0) =
          (flow y).incoming := by
    rw [Finset.sum_eq_single src]
    · simp
    · intro β _hβ hβsrc
      simp [hβsrc]
    · intro hsrc
      exact False.elim (hsrc (Finset.mem_univ src))
  have hUmem :
      forall α : Block, α ∈ U ->
        (Sum.inr α : IncidenceVertex Y Block) ∈ C.supp := by
    intro α hα
    exact
      incidenceUnaryBlockChildren_block_mem_component (A := A)
        (componentYUnaryBlockChildrenExceptRoot_subset
          T root ρ αRoot.1 y hα)
  have hUnarySum :
      (∑ β : ComponentBlock A C,
        if hβ : β.1 ∈ U then
          -((flow y).flow.label ⟨β.1, hβ⟩)
        else 0) =
          ∑ α : {α : Block // α ∈ U},
            -((flow y).flow.label α) := by
    exact
      componentBlock_sum_dite_val_mem_eq_subtype_sum
        (A := A) (C := C) (m := m) U hUmem
        (fun β hβ => -((flow y).flow.label ⟨β.1, hβ⟩))
        (fun α => -((flow y).flow.label α))
        (by
          intro β hβ
          rfl)
  calc
    (∑ β : ComponentBlock A C,
      if y.1 ∈ S β then
        ((replicatedBlockColumnDegree ((P β).toChoice) y.1 : Nat) : ZMod m)
      else 0)
        =
          ∑ β : ComponentBlock A C,
            ((if β = src then (flow y).incoming else 0) +
              (if hβ : β.1 ∈ U then
                -((flow y).flow.label ⟨β.1, hβ⟩)
              else 0)) := by
            apply Finset.sum_congr rfl
            intro β _hβ
            exact hPoint β
    _ =
          (∑ β : ComponentBlock A C,
            if β = src then (flow y).incoming else 0) +
          (∑ β : ComponentBlock A C,
            if hβ : β.1 ∈ U then
              -((flow y).flow.label ⟨β.1, hβ⟩)
            else 0) := by
            rw [Finset.sum_add_distrib]
    _ = (flow y).incoming +
          (∑ β : ComponentBlock A C,
            if hβ : β.1 ∈ U then
              -((flow y).flow.label ⟨β.1, hβ⟩)
            else 0) := by
            rw [hSourceSum]
    _ = (flow y).incoming +
          (∑ α : {α : Block // α ∈ U},
            -((flow y).flow.label α)) := by
            rw [hUnarySum]
    _ = (flow y).incoming -
          ∑ α : {α : Block // α ∈ U}, (flow y).flow.label α := by
            rw [Finset.sum_neg_distrib]
            rw [sub_eq_add_neg]

theorem componentBlockActivePatternFamily_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y) :
    Nonempty
      (forall α : ComponentBlock A C,
        ReplicatedBlockResiduePattern
          (A α.1)
          (componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot α)
          (a / 2) m) := by
  classical
  exact
    ⟨fun α =>
      componentBlockActivePattern
        (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow α⟩

/-- Skeleton of the remaining component assignment: the active sets and local
patterns can now be chosen for all component blocks.  The only missing field
of `RootedBranchComponentBlockResiduePatternUnitAssignmentGoal` is the final
proof that the resulting active contribution sum is a unit at every
component `Y`-vertex. -/
theorem componentBlockActiveAssignmentSkeleton_exists
    {Y Block : Type} [Fintype Block] [Fintype Y] [DecidableEq Y]
    {A : Block -> Finset Y}
    {C : IncidenceComponent A}
    {T : SimpleGraph C} (hTle : T ≤ C.toSimpleGraph) (hTtree : T.IsTree)
    {m a : Nat} (hmpos : 0 < m)
    (hA : forall α : Block, (A α).card = a) (ha2 : 2 <= a)
    {ρ : Y} {hρ : (Sum.inl ρ : IncidenceVertex Y Block) ∈ C.supp}
    {αRoot : ComponentBlock A C}
    (hRootAlpha :
      T.Adj ⟨Sum.inl ρ, hρ⟩ ⟨Sum.inr αRoot.1, αRoot.2⟩)
    (PRoot :
      ReplicatedBlockResiduePattern
        (A αRoot.1)
        (insert ρ
          (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ αRoot.1 αRoot.2))
        (a / 2) m)
    (PNonUnary :
      forall α : ComponentBlock A C,
        α.1 ≠ αRoot.1 ->
        (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2).card ≠ 1 ->
          ReplicatedBlockResiduePattern
            (A α.1)
            (incidenceYChildren T ⟨Sum.inl ρ, hρ⟩ α.1 α.2)
            (a / 2) m)
    (flow :
      forall y : ComponentY A C,
        ComponentVertexFlowData (m := m) (a := a)
          T ⟨Sum.inl ρ, hρ⟩ ρ αRoot y) :
    ∃ S : ComponentBlock A C -> Finset Y,
    ∃ _ : forall α : ComponentBlock A C,
        ReplicatedBlockResiduePattern (A α.1) (S α) (a / 2) m,
      (forall α : ComponentBlock A C, S α ⊆ A α.1) ∧
      S =
        fun α : ComponentBlock A C =>
          componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
            hTle hTtree αRoot α := by
  classical
  let S : ComponentBlock A C -> Finset Y :=
    fun α => componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α
  rcases componentBlockActivePatternFamily_exists
      (A := A) hTle hTtree hmpos hA ha2 PRoot PNonUnary flow with
    ⟨P⟩
  refine ⟨S, P, ?_, rfl⟩
  intro α
  exact componentBlockActiveSet_subset
    (A := A) hTle hTtree hRootAlpha α

theorem rootedBranchComponentBlockResiduePatternUnitAssignmentGoal_closed :
    RootedBranchComponentBlockResiduePatternUnitAssignmentGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
    C ρ hρ T hTle hTtree α0 hα0 hRootAlpha y0 hy0 hy0ρ hAlphaY
  letI := instY
  letI := instDec
  letI := instBlock
  classical
  have hmpos : 0 < m := by omega
  let αRoot : ComponentBlock A C := ⟨α0, hα0⟩
  rcases componentRootAndNonUnaryResiduePatterns_exists
      (A := A) hmOdd hm3 hTle hTtree hA
      (hRootAlpha := hRootAlpha) hy0ρ hAlphaY with
    ⟨PRoot, PNonUnary, _⟩
  let flow :=
    componentVertexFlowDataFamily
      (A := A) (ρ := ρ) (hρ := hρ) (αRoot := αRoot)
      hTle hTtree hmOdd hm3 hmpos hA ha2 PRoot PNonUnary
  let S : ComponentBlock A C -> Finset Y :=
    fun α => componentBlockActiveSet (A := A) (ρ := ρ) (hρ := hρ)
      hTle hTtree αRoot α
  let P : forall α : ComponentBlock A C,
      ReplicatedBlockResiduePattern (A α.1) (S α) (a / 2) m :=
    fun α =>
      componentBlockActivePattern
        (A := A) (ρ := ρ) (hρ := hρ) (αRoot := αRoot)
        hTle hTtree hmpos hA ha2 PRoot PNonUnary flow α
  refine ⟨S, P, ?_, ?_⟩
  · intro α
    simpa [S, αRoot] using
      componentBlockActiveSet_subset
        (A := A) hTle hTtree (αRoot := αRoot) hRootAlpha α
  · intro y hy
    let cy : ComponentY A C := ⟨y, hy⟩
    have hsum :
        (∑ α : ComponentBlock A C,
          if y ∈ S α then
            ((replicatedBlockColumnDegree ((P α).toChoice) y : Nat) :
              ZMod m)
          else 0) =
            (flow cy).incoming -
              ∑ α :
                {α : Block //
                  α ∈ componentYUnaryBlockChildrenExceptRoot
                    T ⟨Sum.inl ρ, hρ⟩ ρ αRoot.1 cy},
                (flow cy).flow.label α := by
      simpa [S, P, flow, cy, αRoot] using
        componentBlockActiveContribution_sum_eq_final_residue
          (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
          (αRoot := αRoot) hRootAlpha PRoot PNonUnary (y := cy)
    rw [hsum]
    simpa [flow, cy, αRoot] using
      componentVertexFlowDataFamily_final_residue_isUnit
        (A := A) hTle hTtree hmOdd hm3 hmpos hA ha2
        (αRoot := αRoot) (y := cy) PRoot PNonUnary

theorem replicatedGlobalSelectedDegree_eq_sum
    {Y Block : Type} [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y} {c m : Nat}
    (C : forall α : Block, ReplicatedBlockChoice (A α) c m) (y : Y) :
    Fintype.card
        {p : Sigma fun _ : Block => Fin m // y ∈ (C p.1).choose p.2} =
      ∑ α : Block, replicatedBlockColumnDegree (C α) y := by
  classical
  let e : {p : Sigma fun _ : Block => Fin m //
        y ∈ (C p.1).choose p.2} ≃
      Sigma fun α : Block => {z : Fin m // y ∈ (C α).choose z} :=
    { toFun := fun p => Sigma.mk p.1.1 (Subtype.mk p.1.2 p.2)
      invFun := fun p => Subtype.mk (Sigma.mk p.1 p.2.1) p.2.2
      left_inv := by
        rintro ⟨⟨α, z⟩, h⟩
        rfl
      right_inv := by
        rintro ⟨α, ⟨z, h⟩⟩
        rfl }
  calc
    Fintype.card
        {p : Sigma fun _ : Block => Fin m // y ∈ (C p.1).choose p.2}
        = Fintype.card
            (Sigma fun α : Block => {z : Fin m // y ∈ (C α).choose z}) :=
          Fintype.card_congr e
    _ = ∑ α : Block, replicatedBlockColumnDegree (C α) y := by
          rw [Fintype.card_sigma]
          rfl

/-- A replicated-block selection: every block has `m` rows, each row chooses
`c` vertices from that block's neighbour set, and every right vertex receives a
selected degree coprime to `m`. -/
structure ReplicatedSelection
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    (A : Block -> Finset Y) (c m : Nat) where
  choose : Block -> Fin m -> Finset Y
  choose_subset : forall α z, choose α z ⊆ A α
  choose_card : forall α z, (choose α z).card = c
  selectedDegree : Y -> Nat
  selectedDegree_eq : forall y : Y,
    selectedDegree y =
      Fintype.card
        {p : Sigma fun _ : Block => Fin m // y ∈ choose p.1 p.2}
  selectedDegree_coprime : forall y : Y, Nat.Coprime (selectedDegree y) m

theorem replicatedSelection_of_blockChoices
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y} {c m : Nat}
    (C : forall α : Block, ReplicatedBlockChoice (A α) c m)
    (hcop : forall y : Y,
      Nat.Coprime (∑ α : Block, replicatedBlockColumnDegree (C α) y) m) :
    Nonempty (ReplicatedSelection A c m) := by
  classical
  refine ⟨
    { choose := fun α z => (C α).choose z
      choose_subset := fun α z => (C α).choose_subset z
      choose_card := fun α z => (C α).choose_card z
      selectedDegree := fun y =>
        ∑ α : Block, replicatedBlockColumnDegree (C α) y
      selectedDegree_eq := ?_
      selectedDegree_coprime := hcop }⟩
  intro y
  exact (replicatedGlobalSelectedDegree_eq_sum C y).symm

/-- The `ZMod m` sum of the row indicators for a right vertex is exactly the
selected degree recorded in a replicated selection. -/
theorem replicatedSelection_zmod_sum_indicator_eq_selectedDegree
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y} {c m : Nat}
    (S : ReplicatedSelection A c m) (y : Y) :
    (∑ p : Sigma fun _ : Block => Fin m,
        if y ∈ S.choose p.1 p.2 then (1 : ZMod m) else 0) =
      (S.selectedDegree y : ZMod m) := by
  classical
  let P : (Sigma fun _ : Block => Fin m) -> Prop :=
    fun p => y ∈ S.choose p.1 p.2
  have hfilter :
      (Finset.univ.filter P).card = S.selectedDegree y := by
    rw [S.selectedDegree_eq y]
    rw [Fintype.card_subtype]
  calc
    (∑ p : Sigma fun _ : Block => Fin m,
        if y ∈ S.choose p.1 p.2 then (1 : ZMod m) else 0)
        =
          (Finset.univ.sum fun p : Sigma fun _ : Block => Fin m =>
            if P p then (1 : ZMod m) else 0) := by
          rfl
    _ = ((Finset.univ.filter P).sum fun _ => (1 : ZMod m)) := by
          rw [Finset.sum_filter]
    _ = ((Finset.univ.filter P).card : ZMod m) := by
          simp
    _ = (S.selectedDegree y : ZMod m) := by
          rw [hfilter]

/-- Consequently the replicated selection supplies a unit additive carry for
each right vertex. -/
theorem replicatedSelection_indicator_sum_isUnit
    {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block]
    {A : Block -> Finset Y} {c m : Nat}
    (S : ReplicatedSelection A c m) (y : Y) :
    IsUnit (∑ p : Sigma fun _ : Block => Fin m,
        if y ∈ S.choose p.1 p.2 then (1 : ZMod m) else 0) := by
  rw [replicatedSelection_zmod_sum_indicator_eq_selectedDegree S y]
  exact (ZMod.isUnit_iff_coprime (S.selectedDegree y) m).mpr
    (S.selectedDegree_coprime y)

/-- Transport the replicated-selection unit carry from `Block × Fin m` to the
actual vertex set using the `m`-fiber equivalence.  This is the arithmetic
input needed by the additive skew-product lift for each Hamilton colour. -/
theorem replicatedSelection_vertex_indicator_sum_isUnit
    {parts : List Nat} {m : Nat} [NeZero m]
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length)
    {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (color : Arc parts) :
    IsUnit (∑ x : Vertex parts m,
        if color ∈ S.choose (D.blockEquiv.symm x).1
            (D.blockEquiv.symm x).2
        then (1 : ZMod m) else 0) := by
  classical
  let g : Vertex parts m -> ZMod m := fun x =>
    if color ∈ S.choose (D.blockEquiv.symm x).1
        (D.blockEquiv.symm x).2
    then (1 : ZMod m) else 0
  have hsum :
      (∑ p : Sigma fun _ : D.Block => Fin m,
          if color ∈ S.choose p.1 p.2 then (1 : ZMod m) else 0) =
        ∑ x : Vertex parts m, g x := by
    simpa [g] using Equiv.sum_comp D.blockEquiv g
  rw [← hsum]
  exact replicatedSelection_indicator_sum_isUnit S color

/-- Hamiltonicity of each lifted colour in the abstract cyclic lift: the base
colour is a Hamilton cycle, and the replicated selection supplies unit total
carry in the new `ZMod m` sheet coordinate. -/
theorem replicatedSelection_liftedColor_singleCycle
    {parts : List Nat} {m : Nat} [NeZero m]
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length)
    {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (color : Arc parts) :
    IsSingleCycleMap
      (skewProductHolonomyMap
        (colorStep D.toDecomposition.colorArc color)
        (fun x : Vertex parts m =>
          Equiv.addRight
            (if color ∈ S.choose (D.blockEquiv.symm x).1
                (D.blockEquiv.symm x).2
             then (1 : ZMod m) else 0))) := by
  classical
  let carry : Vertex parts m -> ZMod m := fun x =>
    if color ∈ S.choose (D.blockEquiv.symm x).1
        (D.blockEquiv.symm x).2
    then (1 : ZMod m) else 0
  have hunit : IsUnit (∑ x : Vertex parts m, carry x) := by
    simpa [carry] using
      replicatedSelection_vertex_indicator_sum_isUnit D z0 dir S color
  simpa [carry] using
    single_cycle_skewProduct_additive_unit_sum
      (colorStep D.toDecomposition.colorArc color) carry (fun _ => 0)
      (D.toDecomposition.colorHamiltonian color) hunit

/-- Marked colours at an old vertex, read from the replicated selection via
the `m`-fiber coordinate of that vertex. -/
noncomputable def markedColorSet
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) : Finset (Arc parts) :=
  S.choose (D.blockEquiv.symm x).1 (D.blockEquiv.symm x).2

/-- Marked colours are a subset of the colours using the split direction at
the same old vertex. -/
theorem markedColorSet_subset_directionColorSet
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) :
    markedColorSet D z0 dir S x ⊆
      directionColorSet D.toDecomposition x dir := by
  classical
  intro color hcolor
  let p := D.blockEquiv.symm x
  have hsub := S.choose_subset p.1 p.2 hcolor
  have hx : D.blockEquiv p = x := by
    dsimp [p]
    exact D.blockEquiv.apply_symm_apply x
  have hrow :
      fiberDirectionColorSet D p.1 z0 dir =
        fiberDirectionColorSet D p.1 p.2 dir :=
    fiberDirectionColorSet_eq D p.1 z0 p.2 dir
  have hmem : color ∈ fiberDirectionColorSet D p.1 p.2 dir := by
    simpa [hrow] using hsub
  simpa [markedColorSet, p, fiberDirectionColorSet, hx] using hmem

theorem markedColorSet_card
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) :
    (markedColorSet D z0 dir S x).card = c := by
  exact S.choose_card (D.blockEquiv.symm x).1 (D.blockEquiv.symm x).2

/-- Unmarked colours using the split direction at an old vertex. -/
noncomputable def unmarkedColorSet
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) : Finset (Arc parts) :=
  directionColorSet D.toDecomposition x dir \ markedColorSet D z0 dir S x

theorem unmarkedColorSet_card
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) :
    (unmarkedColorSet D z0 dir S x).card = parts.get dir - c := by
  classical
  have hsub := markedColorSet_subset_directionColorSet D z0 dir S x
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  rw [directionColorSet_card, markedColorSet_card] at hsum
  rw [unmarkedColorSet]
  omega

theorem mem_unmarkedColorSet_iff
    {parts : List Nat} {m : Nat}
    (D : MFiberedDecomposition parts m) (z0 : Fin m)
    (dir : Fin parts.length) {c : Nat} [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir) c m)
    (x : Vertex parts m) (color : Arc parts) :
    color ∈ unmarkedColorSet D z0 dir S x <->
      color ∈ directionColorSet D.toDecomposition x dir ∧
        color ∉ markedColorSet D z0 dir S x := by
  simp [unmarkedColorSet]

theorem markedColorSet_card_contextSplit
    {m : Nat} (left : List Nat) (a : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left a right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block =>
        fiberDirectionColorSet D b z0 (contextSplitDir left a right))
      (a / 2) m)
    (x : Vertex (OldSplitParts left a right) m) :
    (markedColorSet D z0 (contextSplitDir left a right) S x).card =
      a / 2 := by
  exact markedColorSet_card D z0 (contextSplitDir left a right) S x

theorem unmarkedColorSet_card_contextSplit
    {m : Nat} (left : List Nat) (a : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left a right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block =>
        fiberDirectionColorSet D b z0 (contextSplitDir left a right))
      (a / 2) m)
    (x : Vertex (OldSplitParts left a right) m) :
    (unmarkedColorSet D z0 (contextSplitDir left a right) S x).card =
      (a + 1) / 2 := by
  have h := unmarkedColorSet_card D z0 (contextSplitDir left a right) S x
  rw [contextSplitDir_get] at h
  rw [h]
  omega

theorem markedColorSet_card_contextSplit_generic
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (x : Vertex (OldSplitParts left (b + c) right) m) :
    (markedColorSet D z0 (contextSplitDir left (b + c) right) S x).card =
      c := by
  exact markedColorSet_card D z0 (contextSplitDir left (b + c) right) S x

theorem unmarkedColorSet_card_contextSplit_generic
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (x : Vertex (OldSplitParts left (b + c) right) m) :
    (unmarkedColorSet D z0 (contextSplitDir left (b + c) right) S x).card =
      b := by
  have h := unmarkedColorSet_card D z0
    (contextSplitDir left (b + c) right) S x
  rw [contextSplitDir_get] at h
  rw [h]
  omega

/-- A finite set with known cardinality is equivalent to `Fin` of that
cardinality.  This packages the noncomputable copy-index choices used for the
split child directions. -/
noncomputable def finsetSubtypeEquivOfCard {α : Type*} [DecidableEq α]
    (S : Finset α) {n : Nat} (hcard : S.card = n) :
    Fin n ≃ {x : α // x ∈ S} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_fin]
  rw [Fintype.card_coe]
  exact hcard.symm

/-- Copy indices in the marked child direction are equivalent to marked old
colours at that vertex. -/
noncomputable def markedColorCopyEquiv
    {m : Nat} (left : List Nat) (a : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left a right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block =>
        fiberDirectionColorSet D b z0 (contextSplitDir left a right))
      (a / 2) m)
    (x : Vertex (OldSplitParts left a right) m) :
    Fin (a / 2) ≃
      {color : Arc (OldSplitParts left a right) //
        color ∈ markedColorSet D z0 (contextSplitDir left a right) S x} :=
  finsetSubtypeEquivOfCard
    (markedColorSet D z0 (contextSplitDir left a right) S x)
    (markedColorSet_card_contextSplit left a right D z0 S x)

/-- Copy indices in the unmarked child direction are equivalent to unmarked
old colours at that vertex. -/
noncomputable def unmarkedColorCopyEquiv
    {m : Nat} (left : List Nat) (a : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left a right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun b : D.Block =>
        fiberDirectionColorSet D b z0 (contextSplitDir left a right))
      (a / 2) m)
    (x : Vertex (OldSplitParts left a right) m) :
    Fin ((a + 1) / 2) ≃
      {color : Arc (OldSplitParts left a right) //
        color ∈ unmarkedColorSet D z0 (contextSplitDir left a right) S x} :=
  finsetSubtypeEquivOfCard
    (unmarkedColorSet D z0 (contextSplitDir left a right) S x)
    (unmarkedColorSet_card_contextSplit left a right D z0 S x)

/-- Generic marked-copy equivalence for a split class of size `b + c`, where
the replicated selection marks exactly `c` old colours. -/
noncomputable def markedColorCopyEquiv_contextSplit
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (x : Vertex (OldSplitParts left (b + c) right) m) :
    Fin c ≃
      {color : Arc (OldSplitParts left (b + c) right) //
        color ∈ markedColorSet D z0
          (contextSplitDir left (b + c) right) S x} :=
  finsetSubtypeEquivOfCard
    (markedColorSet D z0 (contextSplitDir left (b + c) right) S x)
    (markedColorSet_card_contextSplit_generic left b c right D z0 S x)

/-- Generic unmarked-copy equivalence for a split class of size `b + c`, where
the `c` marked old colours become the second child and the remaining `b` old
colours become the first child. -/
noncomputable def unmarkedColorCopyEquiv_contextSplit
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (x : Vertex (OldSplitParts left (b + c) right) m) :
    Fin b ≃
      {color : Arc (OldSplitParts left (b + c) right) //
        color ∈ unmarkedColorSet D z0
          (contextSplitDir left (b + c) right) S x} :=
  finsetSubtypeEquivOfCard
    (unmarkedColorSet D z0 (contextSplitDir left (b + c) right) S x)
    (unmarkedColorSet_card_contextSplit_generic left b c right D z0 S x)

/-- The lifted colour-to-arc map for one binary cyclic split, with colours kept
indexed by the old decomposition.  Non-split old directions are transported to
their corresponding new directions.  In the split direction, unmarked old
colours become first-child arcs and marked old colours become second-child
arcs. -/
noncomputable def splitLiftColorArc
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    Arc (OldSplitParts left (b + c) right) ->
      Vertex (NewSplitParts left b c right) m ->
        Arc (NewSplitParts left b c right) :=
  fun color y =>
    let p := contextSplitVertexEquiv left b c m right y
    let e := D.toDecomposition.colorArc color p.1
    if hlt : e.1.val < left.length then
      newArcOfOldBefore left b c right e hlt
    else if heq : e.1.val = left.length then
      if hmark : color ∈ markedColorSet D z0
          (contextSplitDir left (b + c) right) S p.1 then
        secondChildArc left b c right
          ((markedColorCopyEquiv_contextSplit
            left b c right D z0 S p.1).symm ⟨color, hmark⟩)
      else
        have hdir : e.1 = contextSplitDir left (b + c) right := by
          exact Fin.ext heq
        have hmemDir : color ∈ directionColorSet D.toDecomposition p.1
            (contextSplitDir left (b + c) right) := by
          rw [mem_directionColorSet]
          exact hdir
        have hunmark : color ∈ unmarkedColorSet D z0
            (contextSplitDir left (b + c) right) S p.1 := by
          rw [mem_unmarkedColorSet_iff]
          exact ⟨hmemDir, hmark⟩
        firstChildArc left b c right
          ((unmarkedColorCopyEquiv_contextSplit
            left b c right D z0 S p.1).symm ⟨color, hunmark⟩)
    else
      have hafter : left.length < e.1.val := by omega
      newArcOfOldAfter left b c right e hafter

/-- The additive sheet carry of an old colour in the binary split lift.  It is
`1` exactly at old vertices where the colour was marked for the second child,
and `0` otherwise. -/
noncomputable def splitLiftCarry
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (color : Arc (OldSplitParts left (b + c) right))
    (x : Vertex (OldSplitParts left (b + c) right) m) : ZMod m :=
  if color ∈ markedColorSet D z0 (contextSplitDir left (b + c) right) S x
  then 1 else 0

theorem splitLiftColorArc_step_conj
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (color : Arc (OldSplitParts left (b + c) right))
    (p : Vertex (OldSplitParts left (b + c) right) m × ZMod m) :
    contextSplitVertexEquiv left b c m right
      ((contextSplitVertexEquiv left b c m right).symm p +
        basis (NewSplitParts left b c right) m
          (splitLiftColorArc left b c right D z0 S color
            ((contextSplitVertexEquiv left b c m right).symm p)).1) =
      (p.1 + basis (OldSplitParts left (b + c) right) m
        (D.toDecomposition.colorArc color p.1).1,
       p.2 + splitLiftCarry left b c right D z0 S color p.1) := by
  classical
  let e := D.toDecomposition.colorArc color p.1
  by_cases hlt : e.1.val < left.length
  · have hnotMark : color ∉ markedColorSet D z0
        (contextSplitDir left (b + c) right) S p.1 := by
      intro hm
      have hdirMem := markedColorSet_subset_directionColorSet D z0
        (contextSplitDir left (b + c) right) S p.1 hm
      have hdir : e.1 = contextSplitDir left (b + c) right := by
        exact (mem_directionColorSet D.toDecomposition p.1
          (contextSplitDir left (b + c) right) color).mp hdirMem
      have : e.1.val = left.length := by
        rw [hdir]
        rfl
      omega
    subst e
    dsimp [splitLiftColorArc, splitLiftCarry]
    simp [hlt, hnotMark, newArcOfOldBefore,
      contextSplitVertexEquiv_add_oldBefore]
  · by_cases heq : e.1.val = left.length
    · have hdir : e.1 = contextSplitDir left (b + c) right := Fin.ext heq
      have hsplitEq :
          (contextSplitDir left (b + c) right).val = left.length := rfl
      by_cases hmark : color ∈ markedColorSet D z0
          (contextSplitDir left (b + c) right) S p.1
      · subst e
        dsimp [splitLiftColorArc, splitLiftCarry]
        simp [hsplitEq, hmark, hdir, secondChildArc,
          contextSplitVertexEquiv_add_secondChild]
      · subst e
        dsimp [splitLiftColorArc, splitLiftCarry]
        simp [hsplitEq, hmark, hdir, firstChildArc,
          contextSplitVertexEquiv_add_firstChild]
    · have hafter : left.length < e.1.val := by omega
      have hnotMark : color ∉ markedColorSet D z0
          (contextSplitDir left (b + c) right) S p.1 := by
        intro hm
        have hdirMem := markedColorSet_subset_directionColorSet D z0
          (contextSplitDir left (b + c) right) S p.1 hm
        have hdir : e.1 = contextSplitDir left (b + c) right := by
          exact (mem_directionColorSet D.toDecomposition p.1
            (contextSplitDir left (b + c) right) color).mp hdirMem
        have : e.1.val = left.length := by
          rw [hdir]
          rfl
        omega
      subst e
      dsimp [splitLiftColorArc, splitLiftCarry]
      simp [hlt, heq, hnotMark, newArcOfOldAfter,
        contextSplitVertexEquiv_add_oldAfter]

theorem splitLiftColorArc_surjective_before
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (y : Vertex (NewSplitParts left b c right) m)
    (e : Arc (NewSplitParts left b c right))
    (he : e.1.val < left.length) :
    ∃ color : Arc (OldSplitParts left (b + c) right),
      splitLiftColorArc left b c right D z0 S color y = e := by
  classical
  let x : Vertex (OldSplitParts left (b + c) right) m :=
    (contextSplitVertexEquiv left b c m right y).1
  let oldE := oldArcOfNewBefore left b c right e he
  have holdlt : oldE.1.val < left.length := by
    simpa [oldE, oldArcOfNewBefore, oldDirOfNewBefore] using he
  rcases D.toDecomposition.edgePartition x oldE with ⟨color, hcolor, _⟩
  refine ⟨color, ?_⟩
  dsimp [splitLiftColorArc]
  simp [x, oldE, hcolor, holdlt, newArcOfOldBefore_oldArcOfNewBefore]

theorem splitLiftColorArc_surjective_first
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (y : Vertex (NewSplitParts left b c right) m)
    (e : Arc (NewSplitParts left b c right))
    (hval : e.1.val = left.length) :
    ∃ color : Arc (OldSplitParts left (b + c) right),
      splitLiftColorArc left b c right D z0 S color y = e := by
  classical
  let x : Vertex (OldSplitParts left (b + c) right) m :=
    (contextSplitVertexEquiv left b c m right y).1
  have hdirNew : e.1 = contextSplitFirstDir left b c right := by
    exact Fin.ext hval
  let copy : Fin b := cast (by rw [hdirNew, contextSplitFirstDir_get]) e.2
  let U := unmarkedColorCopyEquiv_contextSplit left b c right D z0 S x
  let colorSub := U copy
  let color : Arc (OldSplitParts left (b + c) right) := colorSub.1
  have hunmark : color ∈ unmarkedColorSet D z0
      (contextSplitDir left (b + c) right) S x := colorSub.2
  have hmem := (mem_unmarkedColorSet_iff D z0
    (contextSplitDir left (b + c) right) S x color).mp hunmark
  have hOldDir : (D.toDecomposition.colorArc color x).1 =
      contextSplitDir left (b + c) right := by
    exact (mem_directionColorSet D.toDecomposition x
      (contextSplitDir left (b + c) right) color).mp hmem.1
  have hOldVal : (D.toDecomposition.colorArc color x).1.val =
      left.length := by
    rw [hOldDir]
    rfl
  have hcopy :
      (unmarkedColorCopyEquiv_contextSplit left b c right D z0 S x).symm
        ⟨color, hunmark⟩ = copy := by
    exact U.symm_apply_apply copy
  refine ⟨color, ?_⟩
  dsimp [splitLiftColorArc]
  simp [x, hOldVal, hmem.2, hcopy]
  exact firstChildArc_reconstruct left b c right e hdirNew

theorem splitLiftColorArc_surjective_second
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (y : Vertex (NewSplitParts left b c right) m)
    (e : Arc (NewSplitParts left b c right))
    (hval : e.1.val = left.length + 1) :
    ∃ color : Arc (OldSplitParts left (b + c) right),
      splitLiftColorArc left b c right D z0 S color y = e := by
  classical
  let x : Vertex (OldSplitParts left (b + c) right) m :=
    (contextSplitVertexEquiv left b c m right y).1
  have hdirNew : e.1 = contextSplitSecondDir left b c right := by
    exact Fin.ext hval
  let copy : Fin c := cast (by rw [hdirNew, contextSplitSecondDir_get]) e.2
  let U := markedColorCopyEquiv_contextSplit left b c right D z0 S x
  let colorSub := U copy
  let color : Arc (OldSplitParts left (b + c) right) := colorSub.1
  have hmark : color ∈ markedColorSet D z0
      (contextSplitDir left (b + c) right) S x := colorSub.2
  have hdirMem := markedColorSet_subset_directionColorSet D z0
    (contextSplitDir left (b + c) right) S x hmark
  have hOldDir : (D.toDecomposition.colorArc color x).1 =
      contextSplitDir left (b + c) right := by
    exact (mem_directionColorSet D.toDecomposition x
      (contextSplitDir left (b + c) right) color).mp hdirMem
  have hOldVal : (D.toDecomposition.colorArc color x).1.val =
      left.length := by
    rw [hOldDir]
    rfl
  have hcopy :
      (markedColorCopyEquiv_contextSplit left b c right D z0 S x).symm
        ⟨color, hmark⟩ = copy := by
    exact U.symm_apply_apply copy
  refine ⟨color, ?_⟩
  dsimp [splitLiftColorArc]
  simp [x, hOldVal, hmark, hcopy]
  exact secondChildArc_reconstruct left b c right e hdirNew

theorem splitLiftColorArc_surjective_after
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (y : Vertex (NewSplitParts left b c right) m)
    (e : Arc (NewSplitParts left b c right))
    (he : left.length + 1 < e.1.val) :
    ∃ color : Arc (OldSplitParts left (b + c) right),
      splitLiftColorArc left b c right D z0 S color y = e := by
  classical
  let x : Vertex (OldSplitParts left (b + c) right) m :=
    (contextSplitVertexEquiv left b c m right y).1
  let oldE := oldArcOfNewAfter left b c right e he
  have holdAfter : left.length < oldE.1.val := by
    simpa [oldE, oldArcOfNewAfter, oldDirOfNewAfter] using
      (Nat.lt_sub_of_add_lt he)
  have hnotLt : ¬ oldE.1.val < left.length := by omega
  have hnotEq : ¬ oldE.1.val = left.length := by omega
  rcases D.toDecomposition.edgePartition x oldE with ⟨color, hcolor, _⟩
  refine ⟨color, ?_⟩
  dsimp [splitLiftColorArc]
  simp [x, oldE, hcolor, hnotLt, hnotEq,
    newArcOfOldAfter_oldArcOfNewAfter]

theorem splitLiftColorArc_surjective_at_vertex
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (y : Vertex (NewSplitParts left b c right) m) :
    Function.Surjective (splitLiftColorArc left b c right D z0 S · y) := by
  intro e
  rcases lt_trichotomy e.1.val left.length with hlt | heq | hgt
  · exact splitLiftColorArc_surjective_before left b c right D z0 S y e hlt
  · exact splitLiftColorArc_surjective_first left b c right D z0 S y e heq
  · by_cases hsecond : e.1.val = left.length + 1
    · exact splitLiftColorArc_surjective_second
        left b c right D z0 S y e hsecond
    · exact splitLiftColorArc_surjective_after
        left b c right D z0 S y e (by omega)

/-- The number of arc-copy labels in a multitorus is the sum of the parallel
class sizes. -/
theorem arc_card_eq_sum (parts : List Nat) :
    Fintype.card (Arc parts) = parts.sum := by
  classical
  calc
    Fintype.card (Arc parts)
        = ∑ i : Fin parts.length, Fintype.card (Fin (parts.get i)) := by
          exact Fintype.card_sigma
    _ = ∑ i : Fin parts.length, parts.get i := by
          simp
    _ = (List.ofFn parts.get).sum := by
          rw [List.sum_ofFn]
    _ = parts.sum := by
          rw [List.ofFn_get]

theorem arc_card_eq_sum_context_old_new
    (left : List Nat) (b c : Nat) (right : List Nat) :
    Fintype.card (Arc (OldSplitParts left (b + c) right)) =
      Fintype.card (Arc (NewSplitParts left b c right)) := by
  rw [arc_card_eq_sum, arc_card_eq_sum]
  simp [OldSplitParts, NewSplitParts]
  omega

theorem splitLiftColorArc_edgePartition
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    IsColoredEdgePartition (splitLiftColorArc left b c right D z0 S) := by
  intro y e
  have hsurj :=
    splitLiftColorArc_surjective_at_vertex left b c right D z0 S y
  have hcard :
      Fintype.card (Arc (OldSplitParts left (b + c) right)) =
        Fintype.card (Arc (NewSplitParts left b c right)) :=
    arc_card_eq_sum_context_old_new left b c right
  have hbij :
      Function.Bijective (splitLiftColorArc left b c right D z0 S · y) :=
    (Fintype.bijective_iff_surjective_and_card
      (splitLiftColorArc left b c right D z0 S · y)).mpr
        ⟨hsurj, hcard⟩
  exact (Function.bijective_iff_existsUnique
    (splitLiftColorArc left b c right D z0 S · y)).mp hbij e

theorem splitLiftColorArc_colorHamiltonian
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    IsColoredHamiltonian (splitLiftColorArc left b c right D z0 S) := by
  intro color
  refine single_cycle_of_equiv_conj
    (contextSplitVertexEquiv left b c m right).symm
    (fun y : Vertex (NewSplitParts left b c right) m =>
      y + basis (NewSplitParts left b c right) m
        (splitLiftColorArc left b c right D z0 S color y).1)
    (skewProductHolonomyMap
      (colorStep D.toDecomposition.colorArc color)
      (fun x : Vertex (OldSplitParts left (b + c) right) m =>
        Equiv.addRight (splitLiftCarry left b c right D z0 S color x)))
    ?_ ?_
  · simpa [splitLiftCarry, markedColorSet] using
      replicatedSelection_liftedColor_singleCycle D z0
        (contextSplitDir left (b + c) right) S color
  · intro p
    simp [skewProductHolonomyMap]
    exact splitLiftColorArc_step_conj left b c right D z0 S color p

noncomputable def splitLiftColoredDecomposition
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    ColoredDecomposition (NewSplitParts left b c right) m
      (Arc (OldSplitParts left (b + c) right)) where
  colorArc := splitLiftColorArc left b c right D z0 S
  edgePartition := splitLiftColorArc_edgePartition left b c right D z0 S
  colorHamiltonian := splitLiftColorArc_colorHamiltonian left b c right D z0 S

/-- A noncanonical colour equivalence between old and new arc-copy labels in a
single split step.  The lifted cycles are naturally indexed by the old labels;
this equivalence transports the resulting coloured decomposition back to the
standard `Arc newParts` colour interface. -/
noncomputable def oldNewArcEquiv
    (left : List Nat) (b c : Nat) (right : List Nat) :
    Arc (OldSplitParts left (b + c) right) ≃
      Arc (NewSplitParts left b c right) :=
  Fintype.equivOfCardEq (arc_card_eq_sum_context_old_new left b c right)

noncomputable def splitLiftDecomposition
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    Decomposition (NewSplitParts left b c right) m :=
  decompositionOfColored (oldNewArcEquiv left b c right)
    (splitLiftColoredDecomposition left b c right D z0 S)

theorem hasDecomposition_of_splitLiftSelection
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    HasDecomposition (NewSplitParts left b c right) m :=
  ⟨splitLiftDecomposition left b c right D z0 S⟩

theorem splitLiftColorArc_fst_sheet_eq
    {m : Nat} (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (color : Arc (OldSplitParts left (b + c) right))
    (x : Vertex (OldSplitParts left (b + c) right) m)
    (z z' : ZMod m) :
    (splitLiftColorArc left b c right D z0 S color
      ((contextSplitVertexEquiv left b c m right).symm (x, z))).1 =
    (splitLiftColorArc left b c right D z0 S color
      ((contextSplitVertexEquiv left b c m right).symm (x, z'))).1 := by
  classical
  let e := D.toDecomposition.colorArc color x
  by_cases hlt : e.1.val < left.length
  · subst e
    dsimp [splitLiftColorArc]
    simp [hlt, newArcOfOldBefore]
  · by_cases heq : e.1.val = left.length
    · have hdir : e.1 = contextSplitDir left (b + c) right := Fin.ext heq
      have hsplitEq :
          (contextSplitDir left (b + c) right).val = left.length := rfl
      by_cases hmark : color ∈ markedColorSet D z0
          (contextSplitDir left (b + c) right) S x
      · subst e
        dsimp [splitLiftColorArc]
        simp [hsplitEq, hmark, hdir, secondChildArc]
      · subst e
        dsimp [splitLiftColorArc]
        simp [hsplitEq, hmark, hdir, firstChildArc]
    · subst e
      dsimp [splitLiftColorArc]
      simp [hlt, heq, newArcOfOldAfter]

noncomputable def splitLiftBlockEquiv
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat) :
    (Sigma fun _ : Vertex (OldSplitParts left (b + c) right) m => Fin m) ≃
      Vertex (NewSplitParts left b c right) m where
  toFun p := (contextSplitVertexEquiv left b c m right).symm
    (p.1, (ZMod.finEquiv m p.2 : ZMod m))
  invFun y :=
    let q := contextSplitVertexEquiv left b c m right y
    ⟨q.1, (ZMod.finEquiv m).symm q.2⟩
  left_inv := by
    intro p
    cases p with
    | mk x z =>
        simp
  right_inv := by
    intro y
    simp

theorem splitLiftDecomposition_sameDirectionColors
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m)
    (x : Vertex (OldSplitParts left (b + c) right) m)
    (z z' : Fin m)
    (dir : Fin (NewSplitParts left b c right).length)
    (color : Arc (NewSplitParts left b c right)) :
    ((splitLiftDecomposition left b c right D z0 S).colorArc color
        (splitLiftBlockEquiv left b c right ⟨x, z⟩)).1 = dir <->
      ((splitLiftDecomposition left b c right D z0 S).colorArc color
        (splitLiftBlockEquiv left b c right ⟨x, z'⟩)).1 = dir := by
  let oldColor := (oldNewArcEquiv left b c right).symm color
  have hs := splitLiftColorArc_fst_sheet_eq left b c right D z0 S oldColor x
    (ZMod.finEquiv m z : ZMod m) (ZMod.finEquiv m z' : ZMod m)
  dsimp [splitLiftDecomposition, decompositionOfColored, splitLiftBlockEquiv,
    splitLiftColoredDecomposition]
  simp [oldColor] at hs ⊢
  exact ⟨fun h => by rwa [← hs], fun h => by rwa [hs]⟩

noncomputable def splitLiftMFiberedDecomposition
    {m : Nat} [NeZero m]
    (left : List Nat) (b c : Nat) (right : List Nat)
    (D : MFiberedDecomposition (OldSplitParts left (b + c) right) m)
    (z0 : Fin m) [Fintype D.Block]
    (S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m) :
    MFiberedDecomposition (NewSplitParts left b c right) m where
  toDecomposition := splitLiftDecomposition left b c right D z0 S
  Block := Vertex (OldSplitParts left (b + c) right) m
  blockFintype := inferInstance
  blockEquiv := splitLiftBlockEquiv left b c right
  sameDirectionColors :=
    splitLiftDecomposition_sameDirectionColors left b c right D z0 S

/-- The remaining constructive core of the replicated balancing lemma, after
all local block reservoirs, unit arithmetic, and global counting have been
closed: produce one block choice for each replicated block so that the summed
right degrees are units modulo `m`. -/
def ReplicatedBlockChoiceUnitConstructionGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          ∃ C : forall α : Block, ReplicatedBlockChoice (A α) (a / 2) m,
            forall y : Y,
              IsUnit
                ((∑ α : Block,
                  replicatedBlockColumnDegree (C α) y : Nat) : ZMod m)

def ReplicatedBlockChoiceConstructionGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          ∃ C : forall α : Block, ReplicatedBlockChoice (A α) (a / 2) m,
            forall y : Y,
              Nat.Coprime
                (∑ α : Block, replicatedBlockColumnDegree (C α) y) m

theorem replicatedBlockChoiceUnitConstructionGoal_of_residuePatternUnitAssignment
    (hAssign : ReplicatedResiduePatternUnitAssignmentGoal) :
    ReplicatedBlockChoiceUnitConstructionGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
  letI := instY
  letI := instDec
  letI := instBlock
  rcases hAssign hmOdd hm3 ha2 A hA hNoIso with ⟨S, P, hUnit⟩
  refine ⟨fun α => (P α).toChoice, ?_⟩
  intro y
  rw [replicatedBlockResiduePattern_sum_zmod_eq_active_sum P y]
  exact hUnit y

theorem replicatedBlockChoiceConstructionGoal_of_unit
    (hUnit : ReplicatedBlockChoiceUnitConstructionGoal) :
    ReplicatedBlockChoiceConstructionGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
  letI := instY
  letI := instDec
  letI := instBlock
  rcases hUnit hmOdd hm3 ha2 A hA hNoIso with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro y
  exact
    (ZMod.isUnit_iff_coprime
      (∑ α : Block, replicatedBlockColumnDegree (C α) y) m).mp
      (hC y)

/-- Corrected replicated balancing target.

This is the hypergraph form of the proposed replacement lemma: each left
block consists of `m` identical rows with neighbour set `A α`; all neighbour
sets have size `a`; no right vertex is isolated. -/
def ReplicatedBalancingLemmaGoal : Prop :=
  forall {m a : Nat}, Odd m -> 3 <= m -> 2 <= a ->
    forall {Y Block : Type} [Fintype Y] [DecidableEq Y] [Fintype Block],
      forall A : Block -> Finset Y,
        (forall α : Block, (A α).card = a) ->
        (forall y : Y, exists α : Block, y ∈ A α) ->
          Nonempty (ReplicatedSelection A (a / 2) m)

theorem replicatedBalancingLemmaGoal_of_blockChoiceConstruction
    (hConstruct : ReplicatedBlockChoiceConstructionGoal) :
    ReplicatedBalancingLemmaGoal := by
  intro m a hmOdd hm3 ha2 Y Block instY instDec instBlock A hA hNoIso
  letI := instY
  letI := instDec
  letI := instBlock
  rcases hConstruct hmOdd hm3 ha2 A hA hNoIso with ⟨C, hcop⟩
  exact replicatedSelection_of_blockChoices C hcop

/-- Applying the corrected replicated balancing lemma to the incidence
hypergraph extracted from a fixed direction of an `m`-fibered decomposition.
This closes the cardinality and no-isolated hypotheses needed by balancing;
the subsequent cyclic-lift construction is a separate bookkeeping step. -/
theorem replicatedBalancing_for_fiberDirection
    (hBalancing : ReplicatedBalancingLemmaGoal)
    {parts : List Nat} {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    (D : MFiberedDecomposition parts m) (dir : Fin parts.length)
    (ha2 : 2 <= parts.get dir) (z0 : Fin m) :
    letI : Fintype D.Block := D.blockFintype
    Nonempty (ReplicatedSelection
      (fun b : D.Block => fiberDirectionColorSet D b z0 dir)
      ((parts.get dir) / 2) m) := by
  classical
  letI : Fintype D.Block := D.blockFintype
  exact hBalancing hmOdd hm3 ha2
    (fun b : D.Block => fiberDirectionColorSet D b z0 dir)
    (fun b => fiberDirectionColorSet_card D b z0 dir)
    (fun color =>
      fiberDirectionColorSet_no_isolated D (by omega) z0 dir color)

/-- The same balancing application specialized to the list-context direction
used by `MFiberedSplittingLemmaGoal`. -/
theorem replicatedBalancing_for_contextSplitDirection
    (hBalancing : ReplicatedBalancingLemmaGoal)
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    (left : List Nat) (a : Nat) (right : List Nat) (ha2 : 2 <= a)
    (D : MFiberedDecomposition (left ++ a :: right) m) :
    let z0 : Fin m := ⟨0, by omega⟩
    letI : Fintype D.Block := D.blockFintype
    Nonempty (ReplicatedSelection
      (fun b : D.Block =>
        fiberDirectionColorSet D b z0 (contextSplitDir left a right))
      (a / 2) m) := by
  classical
  let z0 : Fin m := ⟨0, by omega⟩
  letI : Fintype D.Block := D.blockFintype
  have hget :
      (left ++ a :: right).get (contextSplitDir left a right) = a :=
    contextSplitDir_get left a right
  have hpart :
      2 <= (left ++ a :: right).get (contextSplitDir left a right) := by
    rw [hget]
    exact ha2
  have hsel :=
    replicatedBalancing_for_fiberDirection hBalancing hmOdd hm3 D
      (contextSplitDir left a right) hpart z0
  rw [hget] at hsel
  simpa [z0] using hsel

/-- Replicated balancing plus the cyclic split lift gives the ordinary
Hamilton decomposition of the split multitorus.  This theorem deliberately
does not yet assert that the new decomposition is `m`-fibered; that final
invariant is the remaining bookkeeping needed for
`MFiberedSplittingLemmaGoal`. -/
theorem hasDecomposition_contextSplit_of_replicatedBalancing
    (hBalancing : ReplicatedBalancingLemmaGoal)
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    (left : List Nat) (a : Nat) (right : List Nat) (ha2 : 2 <= a)
    (hD : HasMFiberedDecomposition (OldSplitParts left a right) m) :
    HasDecomposition
      (NewSplitParts left ((a + 1) / 2) (a / 2) right) m := by
  classical
  letI : NeZero m := ⟨by omega⟩
  rcases hD with ⟨D0⟩
  let b : Nat := (a + 1) / 2
  let c : Nat := a / 2
  have hbc : b + c = a := by
    dsimp [b, c]
    omega
  have hcsel : (b + c) / 2 = c := by
    rw [hbc]
  let D : MFiberedDecomposition (OldSplitParts left (b + c) right) m := by
    simpa [b, c, hbc] using D0
  let z0 : Fin m := ⟨0, by omega⟩
  letI : Fintype D.Block := D.blockFintype
  have hselNonempty :=
    replicatedBalancing_for_contextSplitDirection hBalancing hmOdd hm3
      left (b + c) right (by omega) D
  dsimp only at hselNonempty
  rcases hselNonempty with ⟨S0⟩
  let S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m := by
    simpa [z0, hcsel] using S0
  have h := hasDecomposition_of_splitLiftSelection left b c right D z0 S
  simpa [b, c, NewSplitParts] using h

/-- Replicated balancing plus the cyclic split lift preserves the
`m`-fibered invariant. -/
theorem hasMFiberedDecomposition_contextSplit_of_replicatedBalancing
    (hBalancing : ReplicatedBalancingLemmaGoal)
    {m : Nat} (hmOdd : Odd m) (hm3 : 3 <= m)
    (left : List Nat) (a : Nat) (right : List Nat) (ha2 : 2 <= a)
    (hD : HasMFiberedDecomposition (OldSplitParts left a right) m) :
    HasMFiberedDecomposition
      (NewSplitParts left ((a + 1) / 2) (a / 2) right) m := by
  classical
  letI : NeZero m := ⟨by omega⟩
  rcases hD with ⟨D0⟩
  let b : Nat := (a + 1) / 2
  let c : Nat := a / 2
  have hbc : b + c = a := by
    dsimp [b, c]
    omega
  have hcsel : (b + c) / 2 = c := by
    rw [hbc]
  let D : MFiberedDecomposition (OldSplitParts left (b + c) right) m := by
    simpa [b, c, hbc] using D0
  let z0 : Fin m := ⟨0, by omega⟩
  letI : Fintype D.Block := D.blockFintype
  have hselNonempty :=
    replicatedBalancing_for_contextSplitDirection hBalancing hmOdd hm3
      left (b + c) right (by omega) D
  dsimp only at hselNonempty
  rcases hselNonempty with ⟨S0⟩
  let S : ReplicatedSelection
      (fun β : D.Block =>
        fiberDirectionColorSet D β z0 (contextSplitDir left (b + c) right))
      c m := by
    simpa [z0, hcsel] using S0
  refine ⟨?Dnew⟩
  exact (by
    simpa [b, c, NewSplitParts] using
      splitLiftMFiberedDecomposition left b c right D z0 S)

/-- Remaining bridge from the replicated balancing lemma to the actual
`m`-fibered lift construction.  It includes the cyclic lift bookkeeping and
the proof that the new decomposition remains `m`-fibered. -/
def MFiberedSplittingFromReplicatedBalancingGoal : Prop :=
  ReplicatedBalancingLemmaGoal -> MFiberedSplittingLemmaGoal

theorem mFiberedSplittingFromReplicatedBalancingGoal :
    MFiberedSplittingFromReplicatedBalancingGoal := by
  intro hBalancing m hmOdd hm3 left a right ha2 hD
  have hD' : HasMFiberedDecomposition (OldSplitParts left a right) m := by
    simpa [OldSplitParts, List.singleton_append] using hD
  have h :=
    hasMFiberedDecomposition_contextSplit_of_replicatedBalancing
      hBalancing hmOdd hm3 left a right ha2 hD'
  simpa [NewSplitParts, List.singleton_append] using h

/-! ## A concrete refutation of the proof-text balancing lemma -/

/-- Counterexample graph for the balancing lemma as stated in the prompt:
three left vertices, one right vertex, and two parallel incidences from each
left vertex to the only right vertex. -/
def counterBalancingGraph : IncidenceGraph (Fin 3) Unit where
  Inc := fun _ _ => Fin 2

/-- The left degree in the counterexample is `a = 2`. -/
def counterLeftDegree (_ : Fin 3) : Nat :=
  2

/-- The only right degree in the counterexample is `6`, positive and divisible
by `m = 3`. -/
def counterRightDegree (_ : Unit) : Nat :=
  6

/-- Since there is only one right vertex, selecting one incidence at each of the
three left vertices gives selected right degree `3`. -/
def counterSelectedDegree (_ : Unit) : Nat :=
  Fintype.card (Fin 3)

/-- The faithful conclusion demanded by the proof-text balancing lemma in this
counterexample.  It is impossible because the only selected right degree is
`3`, not a unit modulo `3`. -/
def CounterBalancedSelection : Prop :=
  exists choose :
      (x : Fin 3) -> Fin 1 -> LeftInc counterBalancingGraph x,
    (forall x : Fin 3, Function.Injective (choose x)) /\
      forall y : Unit, Nat.Coprime (counterSelectedDegree y) 3

/-- The numerical hypotheses of the proof-text balancing lemma hold for the
counterexample: `m = 3` is odd, every left degree is `2`, the only right degree
is positive and divisible by `3`, and `|X| = 3` is divisible by `3`. -/
theorem counterBalancing_hypotheses :
    Odd 3 /\ 2 <= 2 /\
      (forall x : Fin 3, counterLeftDegree x = 2) /\
      (forall y : Unit, 0 < counterRightDegree y /\
        3 ∣ counterRightDegree y) /\
      3 ∣ Fintype.card (Fin 3) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · intro x
    rfl
  constructor
  · intro y
    norm_num [counterRightDegree]
  · norm_num

/-- Therefore the balancing lemma in the prompt is false as stated. -/
theorem counterBalancing_no_unitSelection :
    Not CounterBalancedSelection := by
  rintro ⟨choose, hinj, hunit⟩
  have h := hunit ()
  norm_num [counterSelectedDegree, Nat.Coprime] at h

/-- Formal target connecting the balancing lemma to the multitorus lift. -/
def SplittingFromBalancingGoal : Prop :=
  BalancingLemmaGoal -> SplittingLemmaGoal

/-- List-context induction: if a property is preserved by replacing any part
`a >= 2` by `ceil(a/2), floor(a/2)`, then one part `a` may be replaced by
`a` many `1`s inside any fixed context. -/
theorem splitPartToOnesInContext
    (H : List Nat -> Prop)
    (hSplit :
      forall (left : List Nat) (a : Nat) (right : List Nat), 2 <= a ->
        H (left ++ [a] ++ right) ->
          H (left ++ [(a + 1) / 2, a / 2] ++ right)) :
    forall {a : Nat}, 1 <= a ->
      forall left right : List Nat,
        H (left ++ [a] ++ right) ->
          H (left ++ List.replicate a 1 ++ right) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro ha_pos left right hH
      by_cases ha_one : a = 1
      · subst a
        simpa using hH
      · have ha_two : 2 <= a := by omega
        let b : Nat := (a + 1) / 2
        let c : Nat := a / 2
        have hb_pos : 1 <= b := by
          dsimp [b]
          omega
        have hc_pos : 1 <= c := by
          dsimp [c]
          omega
        have hb_lt : b < a := by
          dsimp [b]
          omega
        have hc_lt : c < a := by
          dsimp [c]
          omega
        have hbc : b + c = a := by
          dsimp [b, c]
          omega
        have h_after_split :
            H (left ++ [b, c] ++ right) := by
          simpa [b, c] using hSplit left a right ha_two hH
        have h_b_context :
            H (left ++ [b] ++ ([c] ++ right)) := by
          simpa [List.append_assoc] using h_after_split
        have h_after_b :
            H (left ++ List.replicate b 1 ++ ([c] ++ right)) :=
          ih b hb_lt hb_pos left ([c] ++ right) h_b_context
        have h_c_context :
            H ((left ++ List.replicate b 1) ++ [c] ++ right) := by
          simpa [List.append_assoc] using h_after_b
        have h_after_c :
            H ((left ++ List.replicate b 1) ++
                List.replicate c 1 ++ right) :=
          ih c hc_lt hc_pos (left ++ List.replicate b 1) right h_c_context
        have hrep :
            List.replicate a 1 =
              List.replicate b 1 ++ List.replicate c 1 := by
          rw [← hbc]
          exact
            (List.replicate_append_replicate
              (n := b) (m := c) (a := 1)).symm
        simpa [List.append_assoc, hrep] using h_after_c

/-- Completion of the multitorus proof from the splitting lemma. -/
theorem allOnes_hasDecomposition_of_splitting
    (hSplit : SplittingLemmaGoal)
    {d m : Nat} (hd : 1 <= d) (hmOdd : Odd m) (hm3 : 3 <= m) :
    HasDecomposition (List.replicate d 1) m := by
  letI : NeZero m := ⟨by omega⟩
  have hBase : HasDecomposition ([] ++ [d] ++ []) m := by
    simpa using onePart_hasDecomposition d m
  have hContext :=
    splitPartToOnesInContext
      (H := fun parts => HasDecomposition parts m)
      (hSplit := fun left a right ha h =>
        hSplit hmOdd hm3 left a right ha h)
      hd [] [] hBase
  simpa using hContext

/-- Completion of the multitorus proof from the strengthened `m`-fibered
splitting lemma. -/
theorem allOnes_hasMFiberedDecomposition_of_mFibered_splitting
    (hSplit : MFiberedSplittingLemmaGoal)
    {d m : Nat} (hd : 1 <= d) (hmOdd : Odd m) (hm3 : 3 <= m) :
    HasMFiberedDecomposition (List.replicate d 1) m := by
  letI : NeZero m := ⟨by omega⟩
  have hBase : HasMFiberedDecomposition ([] ++ [d] ++ []) m := by
    simpa using onePart_hasMFiberedDecomposition d m
  have hContext :=
    splitPartToOnesInContext
      (H := fun parts => HasMFiberedDecomposition parts m)
      (hSplit := fun left a right ha h =>
        hSplit hmOdd hm3 left a right ha h)
      hd [] [] hBase
  simpa using hContext

/-- The strengthened `m`-fibered splitting route implies the ordinary all-ones
decomposition needed by the standard torus bridge. -/
theorem allOnes_hasDecomposition_of_mFibered_splitting
    (hSplit : MFiberedSplittingLemmaGoal)
    {d m : Nat} (hd : 1 <= d) (hmOdd : Odd m) (hm3 : 3 <= m) :
    HasDecomposition (List.replicate d 1) m :=
  hasDecomposition_of_mFibered
    (allOnes_hasMFiberedDecomposition_of_mFibered_splitting
      hSplit hd hmOdd hm3)

/-- Coordinate equivalence between the all-ones multitorus and the standard
directed torus. -/
noncomputable def replicateVertexEquiv (d m : Nat) :
    Vertex (List.replicate d 1) m ≃ TorusVertex d m where
  toFun x := fun i => x ⟨i.val, by
    rw [List.length_replicate]
    exact i.isLt⟩
  invFun y := fun j => y ⟨j.val, by
    simpa using j.isLt⟩
  left_inv := by
    intro x
    funext j
    simp
  right_inv := by
    intro y
    funext i
    simp

/-- Arc-copy equivalence between `T_m(1,...,1)` and the standard direction set.
-/
noncomputable def replicateArcEquiv (d : Nat) :
    Arc (List.replicate d 1) ≃ Fin d where
  toFun e := ⟨e.1.val, by
    simpa using e.1.isLt⟩
  invFun i := ⟨⟨i.val, by
    rw [List.length_replicate]
    exact i.isLt⟩, ⟨0, by simp⟩⟩
  left_inv := by
    intro e
    cases e with
    | mk i copy =>
      cases i with
      | mk n hn =>
        have hget : (List.replicate d 1).get ⟨n, hn⟩ = 1 := by
          simp
        have hcopy :
            copy =
              (⟨0, by simp⟩ :
                Fin ((List.replicate d 1).get ⟨n, hn⟩)) := by
          apply Fin.ext
          have hlt : copy.val < 1 := by
            simpa [hget] using copy.isLt
          omega
        subst hcopy
        rfl
  right_inv := by
    intro i
    rfl

/-- Convert an all-ones multitorus decomposition into the existing standard
colour-direction function. -/
noncomputable def standardColorDirOfAllOnes {d m : Nat}
    (D : Decomposition (List.replicate d 1) m) :
    TorusColor d -> TorusVertex d m -> TorusDirection d :=
  fun c x =>
    replicateArcEquiv d
      (D.colorArc ((replicateArcEquiv d).symm c)
        ((replicateVertexEquiv d m).symm x))

theorem standardColorDirOfAllOnes_edgePartition {d m : Nat}
    (D : Decomposition (List.replicate d 1) m) :
    IsCayleyEdgePartition (standardColorDirOfAllOnes D) := by
  intro x i
  let v : Vertex (List.replicate d 1) m :=
    (replicateVertexEquiv d m).symm x
  let e : Arc (List.replicate d 1) := (replicateArcEquiv d).symm i
  rcases D.edgePartition v e with ⟨c, hc, huniq⟩
  refine ⟨replicateArcEquiv d c, ?_, ?_⟩
  · simp [standardColorDirOfAllOnes, v, e, hc]
  · intro c' hc'
    have hpre : (replicateArcEquiv d).symm c' = c := by
      apply huniq
      apply (replicateArcEquiv d).injective
      simpa [standardColorDirOfAllOnes, v, e] using hc'
    calc
      c' = replicateArcEquiv d ((replicateArcEquiv d).symm c') := by
        simp
      _ = replicateArcEquiv d c := by rw [hpre]

theorem replicateVertexEquiv_symm_add_basis {d m : Nat}
    (x : TorusVertex d m) (e : Arc (List.replicate d 1)) :
    (replicateVertexEquiv d m).symm
      (x + torusBasis d m ((replicateArcEquiv d) e)) =
    (replicateVertexEquiv d m).symm x +
      basis (List.replicate d 1) m e.1 := by
  funext j
  by_cases h : j = e.1
  · subst j
    simp [replicateVertexEquiv, torusBasis, basis, replicateArcEquiv]
  · have hval : Not (j.val = e.1.val) := by
      intro hv
      exact h (Fin.ext hv)
    simp [replicateVertexEquiv, torusBasis, basis, replicateArcEquiv, h, hval]

theorem standardColorDirOfAllOnes_colorHamiltonian {d m : Nat}
    (D : Decomposition (List.replicate d 1) m) :
    IsCayleyColorHamiltonian (standardColorDirOfAllOnes D) := by
  intro c
  refine single_cycle_of_equiv_conj (replicateVertexEquiv d m)
    (cayleyColorStep (standardColorDirOfAllOnes D) c)
    (colorStep D.colorArc ((replicateArcEquiv d).symm c))
    (D.colorHamiltonian ((replicateArcEquiv d).symm c)) ?_
  intro x
  simp [cayleyColorStep, colorStep, standardColorDirOfAllOnes]
  rw [replicateVertexEquiv_symm_add_basis]
  simp

/-- The all-ones multitorus is the standard directed torus in the repository's
`CayleyDecomposition` interface. -/
noncomputable def standardDecompositionOfAllOnes {d m : Nat}
    (D : Decomposition (List.replicate d 1) m) :
    CayleyDecomposition d m where
  colorDir := standardColorDirOfAllOnes D
  edgePartition := standardColorDirOfAllOnes_edgePartition D
  colorHamiltonian := standardColorDirOfAllOnes_colorHamiltonian D

/-- Bridge target from the all-ones multitorus model to the repository's
standard Cayley-decomposition model.  This is bookkeeping: `T_m(1,...,1)` is
definitionally the directed torus `D_d(m)` up to the obvious coordinate/arc
copy equivalence. -/
def StandardBridgeGoal : Prop :=
  forall {d m : Nat},
    HasDecomposition (List.replicate d 1) m ->
      CayleyHamiltonDecomposition d m

/-- The standard bridge is closed: `T_m(1,...,1)` is the repository's
`D_d(m)`. -/
theorem standardBridgeGoal : StandardBridgeGoal := by
  intro d m h
  rcases h with ⟨D⟩
  exact ⟨standardDecompositionOfAllOnes D⟩

/-- Final odd-modulus directed-torus target. -/
def OddDirectedTorusGoal : Prop :=
  forall {d m : Nat}, 2 <= d -> Odd m -> 3 <= m ->
    CayleyHamiltonDecomposition d m

/-- The saved proof spine: balancing implies splitting; splitting plus the
all-ones bridge gives the directed Hamilton decomposition of every odd-modulus
directed torus. -/
theorem oddDirectedTorusGoal_of_balancing
    (hFromBalancing : SplittingFromBalancingGoal)
    (hBalancing : BalancingLemmaGoal)
    (hBridge : StandardBridgeGoal) :
    OddDirectedTorusGoal := by
  intro d m hd hmOdd hm3
  exact hBridge
    (allOnes_hasDecomposition_of_splitting
      (hFromBalancing hBalancing) (by omega) hmOdd hm3)

/-- Same final spine when the splitting lemma is supplied directly. -/
theorem oddDirectedTorusGoal_of_splitting
    (hSplit : SplittingLemmaGoal)
    (hBridge : StandardBridgeGoal) :
    OddDirectedTorusGoal := by
  intro d m hd hmOdd hm3
  exact hBridge
    (allOnes_hasDecomposition_of_splitting hSplit (by omega) hmOdd hm3)

/-- With the standard bridge closed, the only remaining mathematical input for
the multitorus proof spine is a corrected splitting lemma. -/
theorem oddDirectedTorusGoal_of_splitting_closedBridge
    (hSplit : SplittingLemmaGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_splitting hSplit standardBridgeGoal

/-- Final spine for the shortcut route: an `m`-fibered splitting lemma is
enough, because the one-part base decomposition is already `m`-fibered and the
standard all-ones bridge is closed. -/
theorem oddDirectedTorusGoal_of_mFibered_splitting_closedBridge
    (hSplit : MFiberedSplittingLemmaGoal) :
    OddDirectedTorusGoal := by
  intro d m hd hmOdd hm3
  exact standardBridgeGoal
    (allOnes_hasDecomposition_of_mFibered_splitting
      hSplit (by omega) hmOdd hm3)

/-- Final spine from the replicated balancing shortcut.  The remaining
mathematical input is precisely the bridge from replicated balancing to the
`m`-fibered cyclic splitting construction. -/
theorem oddDirectedTorusGoal_of_replicated_balancing
    (hFromReplicated : MFiberedSplittingFromReplicatedBalancingGoal)
    (hBalancing : ReplicatedBalancingLemmaGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_mFibered_splitting_closedBridge
    (hFromReplicated hBalancing)

/-- The replicated-balancing shortcut with the cyclic-lift bridge now closed:
the only remaining input is the replicated balancing lemma itself. -/
theorem oddDirectedTorusGoal_of_replicated_balancing_closedLift
    (hBalancing : ReplicatedBalancingLemmaGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_balancing
    mFiberedSplittingFromReplicatedBalancingGoal hBalancing

/-- Final spine if the remaining replicated block-choice construction is
supplied. -/
theorem oddDirectedTorusGoal_of_replicated_blockChoiceConstruction
    (hConstruct : ReplicatedBlockChoiceConstructionGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_balancing_closedLift
    (replicatedBalancingLemmaGoal_of_blockChoiceConstruction hConstruct)

theorem oddDirectedTorusGoal_of_replicated_blockChoiceUnitConstruction
    (hUnit : ReplicatedBlockChoiceUnitConstructionGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_blockChoiceConstruction
    (replicatedBlockChoiceConstructionGoal_of_unit hUnit)

/-- Final spine reduced to the pure finite hypergraph residue-assignment
problem. -/
theorem oddDirectedTorusGoal_of_replicated_residuePatternUnitAssignment
    (hAssign : ReplicatedResiduePatternUnitAssignmentGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_blockChoiceUnitConstruction
    (replicatedBlockChoiceUnitConstructionGoal_of_residuePatternUnitAssignment
      hAssign)

/-- Current shortest final spine: it remains only to prove the rooted-tree
top-down residue assignment. -/
theorem oddDirectedTorusGoal_of_replicated_rootedTreeResiduePatternUnitAssignment
    (hRooted : RootedTreeResiduePatternUnitAssignmentGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_residuePatternUnitAssignment
    (replicatedResiduePatternUnitAssignmentGoal_of_component
      (componentResiduePatternUnitAssignmentGoal_of_rootedTree hRooted))

/-- Branch-rooted final spine matching the shortcut proof's actual root
reservoir: each component is rooted at a block that has a non-root child in
the rooted spanning tree. -/
theorem oddDirectedTorusGoal_of_replicated_rootedBranchResiduePatternUnitAssignment
    (hRooted : RootedBranchResiduePatternUnitAssignmentGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_residuePatternUnitAssignment
    (replicatedResiduePatternUnitAssignmentGoal_of_component
      (componentResiduePatternUnitAssignmentGoal_of_rootedBranch hRooted))

/-- Sharpest current final spine: the remaining proof may work only on the
block vertices of the chosen connected component, with the outside-component
idle extension handled by
`rootedBranchResiduePatternUnitAssignmentGoal_of_componentBlock`. -/
theorem oddDirectedTorusGoal_of_replicated_rootedBranchComponentBlockResiduePatternUnitAssignment
    (hRooted : RootedBranchComponentBlockResiduePatternUnitAssignmentGoal) :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_rootedBranchResiduePatternUnitAssignment
    (rootedBranchResiduePatternUnitAssignmentGoal_of_componentBlock hRooted)

/-- Fully closed replicated-balancing shortcut proof. -/
theorem oddDirectedTorusGoal_replicated_shortcut_closed :
    OddDirectedTorusGoal :=
  oddDirectedTorusGoal_of_replicated_rootedBranchComponentBlockResiduePatternUnitAssignment
    rootedBranchComponentBlockResiduePatternUnitAssignmentGoal_closed

end OddMultitori
end Shared
