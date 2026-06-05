import EvenV11.FoldedSiteTrace

namespace EvenV11
namespace FiniteAudit

structure AuditEdge where
  tail : Nat
  head : Nat
  deriving DecidableEq, Repr

structure TreeStep where
  vertex : Nat
  parent : Nat
  deriving DecidableEq, Repr

structure TreeWitness where
  root : Nat
  steps : List TreeStep
  deriving DecidableEq, Repr

structure ForestClosingDatum where
  color : Nat
  forest : List AuditEdge
  isolated : Nat
  closing : AuditEdge
  sign : Int
  witness : TreeWitness
  deriving DecidableEq, Repr

structure SupportRowDatum where
  stage : Nat
  support : List AuditEdge
  active : List AuditEdge
  deriving DecidableEq, Repr

def edge (tail head : Nat) : AuditEdge :=
  { tail, head }

def natEqBool (a b : Nat) : Bool :=
  decide (a = b)

def natNeBool (a b : Nat) : Bool :=
  decide (a ≠ b)

def natLtBool (a b : Nat) : Bool :=
  decide (a < b)

def natLeBool (a b : Nat) : Bool :=
  decide (a ≤ b)

def intEqBool (a b : Int) : Bool :=
  decide (a = b)

def intNeBool (a b : Int) : Bool :=
  decide (a ≠ b)

def edgeInBounds (D : Nat) (e : AuditEdge) : Bool :=
  natLtBool e.tail D && natLtBool e.head D

def edgeTouches (v : Nat) (e : AuditEdge) : Bool :=
  natEqBool e.tail v || natEqBool e.head v

def EdgeUndirectedEquivalent (a b : AuditEdge) : Prop :=
  (a.tail = b.tail ∧ a.head = b.head) ∨
    (a.tail = b.head ∧ a.head = b.tail)

theorem EdgeUndirectedEquivalent.refl (e : AuditEdge) :
    EdgeUndirectedEquivalent e e :=
  Or.inl ⟨rfl, rfl⟩

theorem EdgeUndirectedEquivalent.symm {a b : AuditEdge}
    (h : EdgeUndirectedEquivalent a b) :
    EdgeUndirectedEquivalent b a := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

def edgeUndirectedEq (a b : AuditEdge) : Bool :=
  (natEqBool a.tail b.tail && natEqBool a.head b.head) ||
    (natEqBool a.tail b.head && natEqBool a.head b.tail)

def edgeMemberUndirected (e : AuditEdge) (edges : List AuditEdge) : Bool :=
  edges.any (fun f => edgeUndirectedEq e f)

def listNodupBool {α : Type*} [DecidableEq α] (xs : List α) : Bool :=
  decide xs.Nodup

def validNonisolatedVertex (D isolated v : Nat) : Bool :=
  natLtBool v D && natNeBool v isolated

def treeStepsBool
    (forest : List AuditEdge) (seen : List Nat) (steps : List TreeStep) :
    Bool :=
  match steps with
  | [] => true
  | step :: rest =>
      listNodupBool (step.vertex :: seen) &&
        seen.any (fun v => natEqBool v step.parent) &&
        edgeMemberUndirected (edge step.parent step.vertex) forest &&
        treeStepsBool forest (step.vertex :: seen) rest

def treeWitnessVertices (witness : TreeWitness) : List Nat :=
  witness.root :: witness.steps.map (fun step => step.vertex)

def treeWitnessBool
    (D isolated : Nat) (forest : List AuditEdge) (witness : TreeWitness) :
    Bool :=
  validNonisolatedVertex D isolated witness.root &&
    (witness.steps.length == D - 2) &&
    listNodupBool (treeWitnessVertices witness) &&
    (treeWitnessVertices witness).all
      (fun v => validNonisolatedVertex D isolated v) &&
    treeStepsBool forest [witness.root] witness.steps

def getD (xs : List Int) (i : Nat) : Int :=
  xs.getD i 0

def get2D (mat : List (List Int)) (i j : Nat) : Int :=
  getD (mat.getD i []) j

def edgeVectorCoeff (e : AuditEdge) (i : Nat) : Int :=
  (if e.head = i then (1 : Int) else 0) -
    if e.tail = i then (1 : Int) else 0

def reducedBasisVertices (D basisBase : Nat) : List Nat :=
  (List.range D).filter (fun i => natNeBool i basisBase)

def reducedBasisVertex (D basisBase row : Nat) : Nat :=
  (reducedBasisVertices D basisBase).getD row 0

theorem reducedBasisVertices_length_of_lt
    (D basisBase : Nat) (hbasis : basisBase < D) :
    (reducedBasisVertices D basisBase).length = D - 1 := by
  have hsplit :=
    List.length_eq_length_filter_add
      (l := List.range D) (f := fun x => natNeBool x basisBase)
  have hremoved :
      ((List.range D).filter
        (fun x => !natNeBool x basisBase)).length = 1 := by
    simp only [natNeBool, ne_eq, decide_not, Bool.not_not]
    rw [List.filter_eq basisBase]
    simp [List.count_range, hbasis]
  unfold reducedBasisVertices
  rw [hremoved] at hsplit
  simp at hsplit
  omega

theorem reducedBasisVertex_lt_of_row_lt
    (D basisBase row : Nat)
    (hrow : row < (reducedBasisVertices D basisBase).length) :
    reducedBasisVertex D basisBase row < D := by
  have hget :
      reducedBasisVertex D basisBase row =
        (reducedBasisVertices D basisBase)[row] := by
    unfold reducedBasisVertex
    exact List.getD_eq_getElem
      (reducedBasisVertices D basisBase) 0 hrow
  rw [hget]
  have hmem :
      (reducedBasisVertices D basisBase)[row] ∈
        reducedBasisVertices D basisBase := List.getElem_mem hrow
  exact List.mem_range.mp ((List.mem_filter.mp hmem).1)

theorem reducedBasisVertex_ne_basisBase_of_row_lt
    (D basisBase row : Nat)
    (hrow : row < (reducedBasisVertices D basisBase).length) :
    reducedBasisVertex D basisBase row ≠ basisBase := by
  have hget :
      reducedBasisVertex D basisBase row =
        (reducedBasisVertices D basisBase)[row] := by
    unfold reducedBasisVertex
    exact List.getD_eq_getElem
      (reducedBasisVertices D basisBase) 0 hrow
  rw [hget]
  have hmem :
      (reducedBasisVertices D basisBase)[row] ∈
        reducedBasisVertices D basisBase := List.getElem_mem hrow
  simpa [natNeBool] using ((List.mem_filter.mp hmem).2)

def vectorEdge (D : Nat) (e : AuditEdge) (basisBase : Nat) : List Int :=
  (reducedBasisVertices D basisBase).map (fun i => edgeVectorCoeff e i)

def columnsToRows (cols : List (List Int)) (height : Nat) :
    List (List Int) :=
  (List.range height).map (fun i =>
    (List.range cols.length).map (fun j => get2D cols j i))

theorem columnsToRows_length
    (cols : List (List Int)) (height : Nat) :
    (columnsToRows cols height).length = height := by
  simp [columnsToRows]

theorem list_getD_map_range_of_lt
    {α : Type*} (f : Nat → α) (n i : Nat) (d : α)
    (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem]
  · rw [List.getElem_map]
    simp
  · simpa using hi

theorem list_getD_map_range_of_length_le
    {α : Type*} (f : Nat → α) (n i : Nat) (d : α)
    (hi : n ≤ i) :
    ((List.range n).map f).getD i d = d := by
  rw [List.getD_eq_default]
  simpa using hi

theorem list_getD_map_of_lt
    {α β : Type*} (f : α → β) (xs : List α) (i : Nat)
    (dα : α) (dβ : β) (hi : i < xs.length) :
    (xs.map f).getD i dβ = f (xs.getD i dα) := by
  rw [List.getD_eq_getElem]
  · rw [List.getD_eq_getElem]
    rw [List.getElem_map]
  · simpa using hi

theorem columnsToRows_row_length_of_lt
    (cols : List (List Int)) (height row : Nat)
    (hrow : row < height) :
    ((columnsToRows cols height).getD row []).length = cols.length := by
  have hrowRead :
      (columnsToRows cols height).getD row [] =
        (List.range cols.length).map (fun j => get2D cols j row) := by
    simpa [columnsToRows] using
      (list_getD_map_range_of_lt
        (fun i => (List.range cols.length).map (fun j => get2D cols j i))
        height row [] hrow)
  rw [hrowRead]
  simp

theorem columnsToRows_get2D_of_lt
    (cols : List (List Int)) (height row col : Nat)
    (hrow : row < height) (hcol : col < cols.length) :
    get2D (columnsToRows cols height) row col = get2D cols col row := by
  have hrowRead :
      (columnsToRows cols height).getD row [] =
        (List.range cols.length).map (fun j => get2D cols j row) := by
    simpa [columnsToRows] using
      (list_getD_map_range_of_lt
        (fun i => (List.range cols.length).map (fun j => get2D cols j i))
        height row [] hrow)
  calc
    get2D (columnsToRows cols height) row col
        = getD ((columnsToRows cols height).getD row []) col := rfl
    _ = getD ((List.range cols.length).map
          (fun j => get2D cols j row)) col := by rw [hrowRead]
    _ = get2D cols col row := by
          unfold getD
          exact list_getD_map_range_of_lt
            (fun j => get2D cols j row) cols.length col 0 hcol

theorem columnsToRows_get2D_of_height_le
    (cols : List (List Int)) (height row col : Nat)
    (hrow : height ≤ row) :
    get2D (columnsToRows cols height) row col = 0 := by
  have hrowRead :
      (columnsToRows cols height).getD row [] = [] := by
    simpa [columnsToRows] using
      (list_getD_map_range_of_length_le
        (fun i => (List.range cols.length).map (fun j => get2D cols j i))
        height row [] hrow)
  calc
    get2D (columnsToRows cols height) row col
        = getD ((columnsToRows cols height).getD row []) col := rfl
    _ = getD [] col := by rw [hrowRead]
    _ = 0 := by simp [getD]

theorem columnsToRows_get2D_of_cols_length_le
    (cols : List (List Int)) (height row col : Nat)
    (hcol : cols.length ≤ col) :
    get2D (columnsToRows cols height) row col = 0 := by
  by_cases hrow : row < height
  · have hrowRead :
        (columnsToRows cols height).getD row [] =
          (List.range cols.length).map (fun j => get2D cols j row) := by
      simpa [columnsToRows] using
        (list_getD_map_range_of_lt
          (fun i => (List.range cols.length).map (fun j => get2D cols j i))
          height row [] hrow)
    calc
      get2D (columnsToRows cols height) row col
          = getD ((columnsToRows cols height).getD row []) col := rfl
      _ = getD ((List.range cols.length).map
            (fun j => get2D cols j row)) col := by rw [hrowRead]
      _ = 0 := by
            unfold getD
            exact list_getD_map_range_of_length_le
              (fun j => get2D cols j row) cols.length col 0 hcol
  · exact columnsToRows_get2D_of_height_le cols height row col
      (Nat.le_of_not_gt hrow)

def findPivot (n k : Nat) (mat : List (List Int)) : Option Nat :=
  (List.range n).find? (fun i =>
    natLeBool k i && intNeBool (get2D mat i k) 0)

def rowAt (mat : List (List Int)) (i : Nat) : List Int :=
  mat.getD i []

def swapRows (mat : List (List Int)) (i j : Nat) : List (List Int) :=
  (List.range mat.length).map (fun r =>
    if r = i then rowAt mat j else if r = j then rowAt mat i else rowAt mat r)

def bareissStep
    (n k : Nat) (pivot denom : Int) (mat : List (List Int)) :
    List (List Int) :=
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      if k < i ∧ k < j then
        (get2D mat i j * pivot - get2D mat i k * get2D mat k j) / denom
      else if k < i ∧ j = k then
        0
      else if i = k ∧ k < j then
        0
      else
        get2D mat i j))

def bareissLoop
    (fuel n k : Nat) (sign denom : Int) (mat : List (List Int)) : Int :=
  match fuel with
  | 0 => sign * get2D mat (n - 1) (n - 1)
  | fuel' + 1 =>
      match findPivot n k mat with
      | none => 0
      | some pivotRow =>
          let sign' := if pivotRow = k then sign else -sign
          let mat' := if pivotRow = k then mat else swapRows mat pivotRow k
          let pivot := get2D mat' k k
          let mat'' := bareissStep n k pivot denom mat'
          bareissLoop fuel' n (k + 1) sign' pivot mat''

def detInt (mat : List (List Int)) : Int :=
  match mat.length with
  | 0 => 1
  | n => bareissLoop (n - 1) n 0 1 1 mat

def primitiveDetBool (mat : List (List Int)) : Bool :=
  intEqBool (detInt mat) 1 || intEqBool (detInt mat) (-1)

theorem intEqBool_eq_true_iff {a b : Int} :
    intEqBool a b = true ↔ a = b := by
  simp [intEqBool]

theorem natEqBool_eq_true_iff {a b : Nat} :
    natEqBool a b = true ↔ a = b := by
  simp [natEqBool]

theorem natNeBool_eq_true_iff {a b : Nat} :
    natNeBool a b = true ↔ a ≠ b := by
  simp [natNeBool]

theorem natLtBool_eq_true_iff {a b : Nat} :
    natLtBool a b = true ↔ a < b := by
  simp [natLtBool]

theorem intNeBool_eq_true_iff {a b : Int} :
    intNeBool a b = true ↔ a ≠ b := by
  simp [intNeBool]

theorem edgeInBounds_eq_true_iff {D : Nat} {e : AuditEdge} :
    edgeInBounds D e = true ↔ e.tail < D ∧ e.head < D := by
  simp [edgeInBounds, natLtBool]

theorem edgeTouches_eq_false_iff {v : Nat} {e : AuditEdge} :
    edgeTouches v e = false ↔ e.tail ≠ v ∧ e.head ≠ v := by
  simp [edgeTouches, natEqBool]

theorem edgeUndirectedEq_eq_true_iff {a b : AuditEdge} :
    edgeUndirectedEq a b = true ↔ EdgeUndirectedEquivalent a b := by
  simp [EdgeUndirectedEquivalent, edgeUndirectedEq, natEqBool]

theorem edgeMemberUndirected_eq_true_iff
    {e : AuditEdge} {edges : List AuditEdge} :
    edgeMemberUndirected e edges = true ↔
      ∃ f ∈ edges, EdgeUndirectedEquivalent e f := by
  simp [edgeMemberUndirected, edgeUndirectedEq_eq_true_iff]

theorem edgeVectorCoeff_head_of_tail_ne
    {e : AuditEdge} {i : Nat}
    (hhead : e.head = i) (htail : e.tail ≠ i) :
    edgeVectorCoeff e i = 1 := by
  simp [edgeVectorCoeff, hhead, htail]

theorem edgeVectorCoeff_tail_of_head_ne
    {e : AuditEdge} {i : Nat}
    (hhead : e.head ≠ i) (htail : e.tail = i) :
    edgeVectorCoeff e i = -1 := by
  simp [edgeVectorCoeff, hhead, htail]

theorem edgeVectorCoeff_off
    {e : AuditEdge} {i : Nat}
    (hhead : e.head ≠ i) (htail : e.tail ≠ i) :
    edgeVectorCoeff e i = 0 := by
  simp [edgeVectorCoeff, hhead, htail]

theorem EdgeUndirectedEquivalent.edgeVectorCoeff_eq_or_neg
    {a b : AuditEdge} (h : EdgeUndirectedEquivalent a b) (i : Nat) :
    edgeVectorCoeff a i = edgeVectorCoeff b i ∨
      edgeVectorCoeff a i = -edgeVectorCoeff b i := by
  rcases h with h | h
  · left
    rcases h with ⟨htail, hhead⟩
    simp [edgeVectorCoeff, htail, hhead]
  · right
    rcases h with ⟨htail, hhead⟩
    simp [edgeVectorCoeff, htail, hhead]

theorem EdgeUndirectedEquivalent.vectorEdge_eq_or_neg
    {a b : AuditEdge} (h : EdgeUndirectedEquivalent a b)
    (D basisBase : Nat) :
    vectorEdge D a basisBase = vectorEdge D b basisBase ∨
      vectorEdge D a basisBase =
        (vectorEdge D b basisBase).map (fun z => -z) := by
  rcases h with h | h
  · left
    rcases h with ⟨htail, hhead⟩
    simp [vectorEdge, edgeVectorCoeff, htail, hhead]
  · right
    rcases h with ⟨htail, hhead⟩
    simp [vectorEdge, edgeVectorCoeff, htail, hhead]

theorem vectorEdge_getD_of_row_lt
    (D : Nat) (e : AuditEdge) (basisBase row : Nat)
    (hrow : row < (reducedBasisVertices D basisBase).length) :
    getD (vectorEdge D e basisBase) row =
      edgeVectorCoeff e (reducedBasisVertex D basisBase row) := by
  unfold getD vectorEdge reducedBasisVertex
  rw [List.getD_eq_getElem]
  · rw [List.getD_eq_getElem]
    rw [List.getElem_map]
  · simpa using hrow

theorem vectorEdge_getD_of_length_le
    (D : Nat) (e : AuditEdge) (basisBase row : Nat)
    (hrow : (reducedBasisVertices D basisBase).length ≤ row) :
    getD (vectorEdge D e basisBase) row = 0 := by
  unfold getD vectorEdge
  rw [List.getD_eq_default]
  simpa using hrow

theorem primitiveDetBool_eq_true_iff {mat : List (List Int)} :
    primitiveDetBool mat = true ↔
      detInt mat = 1 ∨ detInt mat = -1 := by
  simp [primitiveDetBool, intEqBool, Bool.or_eq_true]

theorem primitiveDetBool_detInt_eq_one_or_neg_one
    {mat : List (List Int)}
    (h : primitiveDetBool mat = true) :
    detInt mat = 1 ∨ detInt mat = -1 :=
  primitiveDetBool_eq_true_iff.mp h

theorem intCast_zmod_isUnit_of_eq_one_or_neg_one
    {m : Nat} [NeZero m] {z : Int}
    (h : z = 1 ∨ z = -1) :
    IsUnit (z : ZMod m) := by
  rcases h with h | h
  · rw [h]
    exact IsUnit.of_mul_eq_one (1 : ZMod m) (by simp)
  · rw [h]
    exact IsUnit.of_mul_eq_one (-1 : ZMod m) (by ring)

def closingMatrix (D : Nat) (datum : ForestClosingDatum) :
    List (List Int) :=
  let cols :=
    (datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated)
  columnsToRows cols (D - 1)

def listIntMatrix (mat : List (List Int)) (n : Nat) :
    Matrix (Fin n) (Fin n) Int :=
  fun i j => get2D mat i.val j.val

def closingMatrixFin (D : Nat) (datum : ForestClosingDatum) :
    Matrix (Fin (D - 1)) (Fin (D - 1)) Int :=
  listIntMatrix (closingMatrix D datum) (D - 1)

theorem listIntMatrix_apply
    (mat : List (List Int)) (n : Nat) (i j : Fin n) :
    listIntMatrix mat n i j = get2D mat i.val j.val :=
  rfl

theorem closingMatrixFin_apply
    (D : Nat) (datum : ForestClosingDatum)
    (i j : Fin (D - 1)) :
    closingMatrixFin D datum i j =
      get2D (closingMatrix D datum) i.val j.val :=
  rfl

theorem closingMatrix_length
    (D : Nat) (datum : ForestClosingDatum) :
    (closingMatrix D datum).length = D - 1 := by
  unfold closingMatrix
  exact columnsToRows_length
    ((datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated))
    (D - 1)

theorem closingMatrix_row_length_of_lt
    (D : Nat) (datum : ForestClosingDatum) (row : Nat)
    (hrow : row < D - 1) :
    ((closingMatrix D datum).getD row []).length =
      datum.forest.length + 1 := by
  unfold closingMatrix
  have h :=
    columnsToRows_row_length_of_lt
      ((datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated))
      (D - 1) row hrow
  simpa using h

theorem closingMatrix_row_length_eq_of_forest_length
    (D : Nat) (datum : ForestClosingDatum) (row : Nat)
    (hforest : datum.forest.length = D - 2)
    (hrow : row < D - 1) :
    ((closingMatrix D datum).getD row []).length = D - 1 := by
  rw [closingMatrix_row_length_of_lt D datum row hrow, hforest]
  omega

theorem closingMatrix_get2D_of_height_le
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hrow : D - 1 ≤ row) :
    get2D (closingMatrix D datum) row col = 0 := by
  unfold closingMatrix
  exact columnsToRows_get2D_of_height_le
    ((datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated))
    (D - 1) row col hrow

theorem closingMatrix_get2D_of_width_le
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hcol : datum.forest.length + 1 ≤ col) :
    get2D (closingMatrix D datum) row col = 0 := by
  unfold closingMatrix
  exact columnsToRows_get2D_of_cols_length_le
    ((datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated))
    (D - 1) row col (by simpa using hcol)

theorem closingMatrix_get2D_of_square_width_le
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hD : 2 ≤ D)
    (hforest : datum.forest.length = D - 2)
    (hcol : D - 1 ≤ col) :
    get2D (closingMatrix D datum) row col = 0 := by
  exact closingMatrix_get2D_of_width_le D datum row col (by
    rw [hforest]
    omega)

theorem closingMatrix_forest_column_getD_of_lt
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hrow : row < D - 1) (hcol : col < datum.forest.length) :
    get2D (closingMatrix D datum) row col =
      getD
        (vectorEdge D (datum.forest.getD col (edge 0 0)) datum.isolated)
        row := by
  unfold closingMatrix
  let cols :=
    (datum.forest ++ [datum.closing]).map
      (fun e => vectorEdge D e datum.isolated)
  have hcolAppend : col < (datum.forest ++ [datum.closing]).length := by
    simpa using Nat.lt_trans hcol (Nat.lt_succ_self datum.forest.length)
  have hcolAll : col < cols.length := by
    simpa [cols] using hcolAppend
  have hcolRead :
      cols.getD col [] =
        vectorEdge D (datum.forest.getD col (edge 0 0))
          datum.isolated := by
    have hmap :
        cols.getD col [] =
          vectorEdge D
            ((datum.forest ++ [datum.closing]).getD col (edge 0 0))
            datum.isolated := by
      simpa [cols] using
        (list_getD_map_of_lt
          (fun e => vectorEdge D e datum.isolated)
          (datum.forest ++ [datum.closing]) col (edge 0 0) []
          hcolAppend)
    have happend :
        (datum.forest ++ [datum.closing]).getD col (edge 0 0) =
          datum.forest.getD col (edge 0 0) :=
      List.getD_append datum.forest [datum.closing] (edge 0 0) col hcol
    rw [hmap, happend]
  calc
    get2D (columnsToRows cols (D - 1)) row col
        = get2D cols col row := by
          exact columnsToRows_get2D_of_lt cols (D - 1) row col hrow hcolAll
    _ = getD (cols.getD col []) row := rfl
    _ = getD
          (vectorEdge D (datum.forest.getD col (edge 0 0)) datum.isolated)
          row := by rw [hcolRead]

theorem closingMatrix_forest_column_coeff_of_lt
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length)
    (hcol : col < datum.forest.length) :
    get2D (closingMatrix D datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex D datum.isolated row) := by
  calc
    get2D (closingMatrix D datum) row col
        =
          getD
            (vectorEdge D (datum.forest.getD col (edge 0 0))
              datum.isolated) row :=
          closingMatrix_forest_column_getD_of_lt
            D datum row col hrowHeight hcol
    _ = edgeVectorCoeff (datum.forest.getD col (edge 0 0))
          (reducedBasisVertex D datum.isolated row) :=
          vectorEdge_getD_of_row_lt
            D (datum.forest.getD col (edge 0 0)) datum.isolated
            row hrowBasis

theorem closingMatrix_forest_column_coeff_of_lt_of_isolated_lt
    (D : Nat) (datum : ForestClosingDatum) (row col : Nat)
    (hisolated : datum.isolated < D)
    (hrowHeight : row < D - 1)
    (hcol : col < datum.forest.length) :
    get2D (closingMatrix D datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex D datum.isolated row) := by
  exact closingMatrix_forest_column_coeff_of_lt
    D datum row col hrowHeight
    (by
      simpa [reducedBasisVertices_length_of_lt D datum.isolated hisolated]
        using hrowHeight)
    hcol

theorem closingMatrix_closing_column_getD_of_row_lt
    (D : Nat) (datum : ForestClosingDatum) (row : Nat)
    (hrow : row < D - 1) :
    get2D (closingMatrix D datum) row datum.forest.length =
      getD (vectorEdge D datum.closing datum.isolated) row := by
  unfold closingMatrix
  have hcol :
      datum.forest.length <
        ((datum.forest ++ [datum.closing]).map
          (fun e => vectorEdge D e datum.isolated)).length := by
    simp
  calc
    get2D
        (columnsToRows
          ((datum.forest ++ [datum.closing]).map
            (fun e => vectorEdge D e datum.isolated)) (D - 1))
        row datum.forest.length
        =
          get2D
            ((datum.forest ++ [datum.closing]).map
              (fun e => vectorEdge D e datum.isolated))
            datum.forest.length row := by
          exact columnsToRows_get2D_of_lt
            ((datum.forest ++ [datum.closing]).map
              (fun e => vectorEdge D e datum.isolated))
            (D - 1) row datum.forest.length hrow hcol
    _ = getD (vectorEdge D datum.closing datum.isolated) row := by
          simp [get2D, getD]

theorem closingMatrix_closing_column_coeff_of_row_lt
    (D : Nat) (datum : ForestClosingDatum) (row : Nat)
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length) :
    get2D (closingMatrix D datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row) := by
  calc
    get2D (closingMatrix D datum) row datum.forest.length
        = getD (vectorEdge D datum.closing datum.isolated) row :=
          closingMatrix_closing_column_getD_of_row_lt
            D datum row hrowHeight
    _ = edgeVectorCoeff datum.closing
          (reducedBasisVertex D datum.isolated row) :=
          vectorEdge_getD_of_row_lt
            D datum.closing datum.isolated row hrowBasis

theorem closingMatrix_closing_column_coeff_of_row_lt_of_isolated_lt
    (D : Nat) (datum : ForestClosingDatum) (row : Nat)
    (hisolated : datum.isolated < D)
    (hrowHeight : row < D - 1) :
    get2D (closingMatrix D datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row) := by
  exact closingMatrix_closing_column_coeff_of_row_lt
    D datum row hrowHeight
    (by
      simpa [reducedBasisVertices_length_of_lt D datum.isolated hisolated]
        using hrowHeight)

def forestClosingDatumBool (D : Nat) (datum : ForestClosingDatum) :
    Bool :=
  natLtBool datum.color D &&
    (datum.forest.length == D - 2) &&
    datum.forest.all (edgeInBounds D) &&
    datum.forest.all (fun e => !edgeTouches datum.isolated e) &&
    treeWitnessBool D datum.isolated datum.forest datum.witness &&
    edgeInBounds D datum.closing &&
    natEqBool datum.closing.tail datum.isolated &&
    natNeBool datum.closing.head datum.isolated &&
    (intEqBool datum.sign 1 || intEqBool datum.sign (-1)) &&
    primitiveDetBool (closingMatrix D datum)

theorem forestClosingDatumBool_primitiveDet
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    primitiveDetBool (closingMatrix D datum) = true := by
  unfold forestClosingDatumBool at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem forestClosingDatumBool_detInt_eq_one_or_neg_one
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    detInt (closingMatrix D datum) = 1 ∨
      detInt (closingMatrix D datum) = -1 :=
  primitiveDetBool_detInt_eq_one_or_neg_one
    (forestClosingDatumBool_primitiveDet h)

theorem forestClosingDatumBool_detInt_zmod_unit
    {D m : Nat} [NeZero m] {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    IsUnit ((detInt (closingMatrix D datum) : Int) : ZMod m) :=
  intCast_zmod_isUnit_of_eq_one_or_neg_one
    (forestClosingDatumBool_detInt_eq_one_or_neg_one h)

structure ForestClosingDatumFacts (D : Nat)
    (datum : ForestClosingDatum) : Prop where
  color_lt : datum.color < D
  forest_length : datum.forest.length = D - 2
  forest_inBounds :
    ∀ e ∈ datum.forest, e.tail < D ∧ e.head < D
  forest_avoids_isolated :
    ∀ e ∈ datum.forest,
      e.tail ≠ datum.isolated ∧ e.head ≠ datum.isolated
  tree_witness :
    treeWitnessBool D datum.isolated datum.forest datum.witness = true
  closing_inBounds : datum.closing.tail < D ∧ datum.closing.head < D
  closing_tail_eq_isolated : datum.closing.tail = datum.isolated
  closing_head_ne_isolated : datum.closing.head ≠ datum.isolated
  sign_eq_one_or_neg_one : datum.sign = 1 ∨ datum.sign = -1
  primitive_det : primitiveDetBool (closingMatrix D datum) = true
  det_eq_one_or_neg_one :
    detInt (closingMatrix D datum) = 1 ∨
      detInt (closingMatrix D datum) = -1

theorem forestClosingDatumBool_facts
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    ForestClosingDatumFacts D datum := by
  have hs := by
    simpa [forestClosingDatumBool, natLtBool, natEqBool, natNeBool,
      intEqBool, edgeInBounds, edgeTouches] using h
  rcases hs with ⟨hs, hdet⟩
  rcases hs with ⟨hs, hsign⟩
  rcases hs with ⟨hs, hclosingHeadNe⟩
  rcases hs with ⟨hs, hclosingTail⟩
  rcases hs with ⟨hs, hclosingBounds⟩
  rcases hs with ⟨hs, htree⟩
  rcases hs with ⟨hs, hforestAvoid⟩
  rcases hs with ⟨hs, hforestBounds⟩
  rcases hs with ⟨hcolor, hforestLength⟩
  exact
    { color_lt := hcolor
      forest_length := hforestLength
      forest_inBounds := hforestBounds
      forest_avoids_isolated := hforestAvoid
      tree_witness := htree
      closing_inBounds := hclosingBounds
      closing_tail_eq_isolated := hclosingTail
      closing_head_ne_isolated := hclosingHeadNe
      sign_eq_one_or_neg_one := hsign
      primitive_det := hdet
      det_eq_one_or_neg_one :=
        primitiveDetBool_detInt_eq_one_or_neg_one hdet }

theorem forestClosingDatumBool_closing_tail_eq_isolated
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    datum.closing.tail = datum.isolated :=
  (forestClosingDatumBool_facts h).closing_tail_eq_isolated

theorem forestClosingDatumBool_closing_head_ne_isolated
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    datum.closing.head ≠ datum.isolated :=
  (forestClosingDatumBool_facts h).closing_head_ne_isolated

theorem forestClosingDatumBool_forest_avoids_isolated
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    ∀ e ∈ datum.forest,
      e.tail ≠ datum.isolated ∧ e.head ≠ datum.isolated :=
  (forestClosingDatumBool_facts h).forest_avoids_isolated

theorem forestClosingDatumBool_sign_eq_one_or_neg_one
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    datum.sign = 1 ∨ datum.sign = -1 :=
  (forestClosingDatumBool_facts h).sign_eq_one_or_neg_one

theorem ForestClosingDatumFacts.isolated_lt
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    datum.isolated < D := by
  rw [← F.closing_tail_eq_isolated]
  exact F.closing_inBounds.1

theorem ForestClosingDatumFacts.two_le
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    2 ≤ D := by
  have htail : datum.closing.tail < D := F.closing_inBounds.1
  have hhead : datum.closing.head < D := F.closing_inBounds.2
  have htailHead : datum.closing.tail ≠ datum.closing.head := by
    intro h
    exact F.closing_head_ne_isolated
      (h.symm.trans F.closing_tail_eq_isolated)
  omega

theorem forestClosingDatumBool_isolated_lt
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    datum.isolated < D :=
  (forestClosingDatumBool_facts h).isolated_lt

theorem forestClosingDatumBool_two_le
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    2 ≤ D :=
  (forestClosingDatumBool_facts h).two_le

theorem ForestClosingDatumFacts.closingMatrix_length
    {D : Nat} {datum : ForestClosingDatum}
    (_F : ForestClosingDatumFacts D datum) :
    (closingMatrix D datum).length = D - 1 :=
  FiniteAudit.closingMatrix_length D datum

theorem ForestClosingDatumFacts.closingMatrix_row_length
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrow : row < D - 1) :
    ((closingMatrix D datum).getD row []).length = D - 1 :=
  closingMatrix_row_length_eq_of_forest_length
    D datum row F.forest_length hrow

theorem ForestClosingDatumFacts.closingMatrix_height_zero
    {D : Nat} {datum : ForestClosingDatum}
    (_F : ForestClosingDatumFacts D datum) {row col : Nat}
    (hrow : D - 1 ≤ row) :
    get2D (closingMatrix D datum) row col = 0 :=
  closingMatrix_get2D_of_height_le D datum row col hrow

theorem ForestClosingDatumFacts.closingMatrix_width_zero
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row col : Nat}
    (hcol : D - 1 ≤ col) :
    get2D (closingMatrix D datum) row col = 0 :=
  closingMatrix_get2D_of_square_width_le
    D datum row col F.two_le F.forest_length hcol

theorem forestClosingDatumBool_closingMatrix_length
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    (closingMatrix D datum).length = D - 1 :=
  (forestClosingDatumBool_facts h).closingMatrix_length

theorem forestClosingDatumBool_closingMatrix_row_length
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrow : row < D - 1) :
    ((closingMatrix D datum).getD row []).length = D - 1 :=
  (forestClosingDatumBool_facts h).closingMatrix_row_length hrow

theorem forestClosingDatumBool_closingMatrix_height_zero
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row col : Nat}
    (hrow : D - 1 ≤ row) :
    get2D (closingMatrix D datum) row col = 0 :=
  (forestClosingDatumBool_facts h).closingMatrix_height_zero hrow

theorem forestClosingDatumBool_closingMatrix_width_zero
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row col : Nat}
    (hcol : D - 1 ≤ col) :
    get2D (closingMatrix D datum) row col = 0 :=
  (forestClosingDatumBool_facts h).closingMatrix_width_zero hcol

def ForestClosingDatumFacts.closingColumnFin
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) : Fin (D - 1) :=
  ⟨datum.forest.length, by
    have hD : 2 ≤ D := F.two_le
    rw [F.forest_length]
    omega⟩

theorem ForestClosingDatumFacts.closingColumnFin_val
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    F.closingColumnFin.val = datum.forest.length :=
  rfl

theorem ForestClosingDatumFacts.closingMatrixFin_forest_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum)
    (row col : Fin (D - 1))
    (hcol : col.val < datum.forest.length) :
    closingMatrixFin D datum row col =
      edgeVectorCoeff (datum.forest.getD col.val (edge 0 0))
        (reducedBasisVertex D datum.isolated row.val) := by
  rw [closingMatrixFin_apply]
  exact closingMatrix_forest_column_coeff_of_lt_of_isolated_lt
    D datum row.val col.val F.isolated_lt row.isLt hcol

theorem ForestClosingDatumFacts.closingMatrixFin_closing_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) (row : Fin (D - 1)) :
    closingMatrixFin D datum row F.closingColumnFin =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row.val) := by
  rw [closingMatrixFin_apply, F.closingColumnFin_val]
  exact closingMatrix_closing_column_coeff_of_row_lt_of_isolated_lt
    D datum row.val F.isolated_lt row.isLt

theorem forestClosingDatumBool_closingMatrixFin_forest_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true)
    (row col : Fin (D - 1))
    (hcol : col.val < datum.forest.length) :
    closingMatrixFin D datum row col =
      edgeVectorCoeff (datum.forest.getD col.val (edge 0 0))
        (reducedBasisVertex D datum.isolated row.val) :=
  (forestClosingDatumBool_facts h).closingMatrixFin_forest_column_coeff
    row col hcol

theorem forestClosingDatumBool_closingMatrixFin_closing_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true)
    (row : Fin (D - 1)) :
    closingMatrixFin D datum row
        (forestClosingDatumBool_facts h).closingColumnFin =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row.val) :=
  (forestClosingDatumBool_facts h).closingMatrixFin_closing_column_coeff row

theorem ForestClosingDatumFacts.detInt_zmod_unit
    {D m : Nat} [NeZero m] {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    IsUnit ((detInt (closingMatrix D datum) : Int) : ZMod m) :=
  intCast_zmod_isUnit_of_eq_one_or_neg_one F.det_eq_one_or_neg_one

theorem forestClosingDatumBool_facts_detInt_zmod_unit
    {D m : Nat} [NeZero m] {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    IsUnit ((detInt (closingMatrix D datum) : Int) : ZMod m) :=
  (forestClosingDatumBool_facts h).detInt_zmod_unit

structure ClosingMatrixPayload (D : Nat)
    (datum : ForestClosingDatum) : Prop where
  facts : ForestClosingDatumFacts D datum
  matrix_length : (closingMatrix D datum).length = D - 1
  row_length :
    ∀ row : Nat, row < D - 1 →
      ((closingMatrix D datum).getD row []).length = D - 1
  height_zero :
    ∀ row col : Nat, D - 1 ≤ row →
      get2D (closingMatrix D datum) row col = 0
  width_zero :
    ∀ row col : Nat, D - 1 ≤ col →
      get2D (closingMatrix D datum) row col = 0
  det_unit :
    ∀ {m : Nat}, [NeZero m] →
      IsUnit ((detInt (closingMatrix D datum) : Int) : ZMod m)
  closingColumn_val :
    facts.closingColumnFin.val = datum.forest.length
  forest_column_coeff :
    ∀ row col : Fin (D - 1),
      col.val < datum.forest.length →
        closingMatrixFin D datum row col =
          edgeVectorCoeff (datum.forest.getD col.val (edge 0 0))
            (reducedBasisVertex D datum.isolated row.val)
  closing_column_coeff :
    ∀ row : Fin (D - 1),
      closingMatrixFin D datum row facts.closingColumnFin =
        edgeVectorCoeff datum.closing
          (reducedBasisVertex D datum.isolated row.val)

theorem closingMatrixPayload_of_facts
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    ClosingMatrixPayload D datum where
  facts := F
  matrix_length := F.closingMatrix_length
  row_length := fun _row hrow => F.closingMatrix_row_length hrow
  height_zero := fun _row _col hrow => F.closingMatrix_height_zero hrow
  width_zero := fun _row _col hcol => F.closingMatrix_width_zero hcol
  det_unit := fun {_m} _inst => F.detInt_zmod_unit
  closingColumn_val := F.closingColumnFin_val
  forest_column_coeff := fun row col hcol =>
    F.closingMatrixFin_forest_column_coeff row col hcol
  closing_column_coeff := fun row =>
    F.closingMatrixFin_closing_column_coeff row

theorem closingMatrixPayload_of_bool
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    ClosingMatrixPayload D datum :=
  closingMatrixPayload_of_facts (forestClosingDatumBool_facts h)

theorem ForestClosingDatumFacts.closingMatrix_forest_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row col : Nat}
    (hrow : row < D - 1) (hcol : col < datum.forest.length) :
    get2D (closingMatrix D datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex D datum.isolated row) :=
  closingMatrix_forest_column_coeff_of_lt_of_isolated_lt
    D datum row col F.isolated_lt hrow hcol

theorem ForestClosingDatumFacts.closingMatrix_closing_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrow : row < D - 1) :
    get2D (closingMatrix D datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row) :=
  closingMatrix_closing_column_coeff_of_row_lt_of_isolated_lt
    D datum row F.isolated_lt hrow

theorem forestClosingDatumBool_closingMatrix_forest_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row col : Nat}
    (hrow : row < D - 1) (hcol : col < datum.forest.length) :
    get2D (closingMatrix D datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex D datum.isolated row) :=
  (forestClosingDatumBool_facts h).closingMatrix_forest_column_coeff
    hrow hcol

theorem forestClosingDatumBool_closingMatrix_closing_column_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrow : row < D - 1) :
    get2D (closingMatrix D datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex D datum.isolated row) :=
  (forestClosingDatumBool_facts h).closingMatrix_closing_column_coeff
    hrow

theorem ForestClosingDatumFacts.closing_head_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    edgeVectorCoeff datum.closing datum.closing.head = 1 := by
  have htail_ne_head : datum.closing.tail ≠ datum.closing.head := by
    intro h
    exact F.closing_head_ne_isolated
      (h.symm.trans F.closing_tail_eq_isolated)
  exact edgeVectorCoeff_head_of_tail_ne rfl htail_ne_head

theorem ForestClosingDatumFacts.closing_isolated_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    edgeVectorCoeff datum.closing datum.isolated = -1 :=
  edgeVectorCoeff_tail_of_head_ne
    F.closing_head_ne_isolated F.closing_tail_eq_isolated

theorem ForestClosingDatumFacts.closing_off_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {i : Nat}
    (hhead : i ≠ datum.closing.head) (hiso : i ≠ datum.isolated) :
    edgeVectorCoeff datum.closing i = 0 := by
  have hhead' : datum.closing.head ≠ i := fun h => hhead h.symm
  have htail' : datum.closing.tail ≠ i := by
    intro h
    exact hiso (h.symm.trans F.closing_tail_eq_isolated)
  exact edgeVectorCoeff_off hhead' htail'

theorem forestClosingDatumBool_closing_head_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    edgeVectorCoeff datum.closing datum.closing.head = 1 :=
  (forestClosingDatumBool_facts h).closing_head_coeff

theorem forestClosingDatumBool_closing_isolated_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    edgeVectorCoeff datum.closing datum.isolated = -1 :=
  (forestClosingDatumBool_facts h).closing_isolated_coeff

theorem forestClosingDatumBool_closing_off_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {i : Nat}
    (hhead : i ≠ datum.closing.head) (hiso : i ≠ datum.isolated) :
    edgeVectorCoeff datum.closing i = 0 :=
  (forestClosingDatumBool_facts h).closing_off_coeff hhead hiso

theorem ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff_of_row_lt
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrow : row < D - 1)
    (hvertex :
      reducedBasisVertex D datum.isolated row = datum.closing.head) :
    get2D (closingMatrix D datum) row datum.forest.length = 1 := by
  rw [F.closingMatrix_closing_column_coeff hrow, hvertex]
  exact F.closing_head_coeff

theorem ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff_of_row_lt
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrow : row < D - 1)
    (hhead :
      reducedBasisVertex D datum.isolated row ≠ datum.closing.head)
    (hiso :
      reducedBasisVertex D datum.isolated row ≠ datum.isolated) :
    get2D (closingMatrix D datum) row datum.forest.length = 0 := by
  rw [F.closingMatrix_closing_column_coeff hrow]
  exact F.closing_off_coeff hhead hiso

theorem forestClosingDatumBool_closingMatrix_closing_column_head_coeff_of_row_lt
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrow : row < D - 1)
    (hvertex :
      reducedBasisVertex D datum.isolated row = datum.closing.head) :
    get2D (closingMatrix D datum) row datum.forest.length = 1 :=
  (forestClosingDatumBool_facts h).closingMatrix_closing_column_head_coeff_of_row_lt
    hrow hvertex

theorem forestClosingDatumBool_closingMatrix_closing_column_off_coeff_of_row_lt
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrow : row < D - 1)
    (hhead :
      reducedBasisVertex D datum.isolated row ≠ datum.closing.head)
    (hiso :
      reducedBasisVertex D datum.isolated row ≠ datum.isolated) :
    get2D (closingMatrix D datum) row datum.forest.length = 0 :=
  (forestClosingDatumBool_facts h).closingMatrix_closing_column_off_coeff_of_row_lt
    hrow hhead hiso

theorem ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length)
    (hvertex :
      reducedBasisVertex D datum.isolated row = datum.closing.head) :
    get2D (closingMatrix D datum) row datum.forest.length = 1 := by
  rw [closingMatrix_closing_column_coeff_of_row_lt
    D datum row hrowHeight hrowBasis, hvertex]
  exact F.closing_head_coeff

theorem ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) {row : Nat}
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length)
    (hhead :
      reducedBasisVertex D datum.isolated row ≠ datum.closing.head)
    (hiso :
      reducedBasisVertex D datum.isolated row ≠ datum.isolated) :
    get2D (closingMatrix D datum) row datum.forest.length = 0 := by
  rw [closingMatrix_closing_column_coeff_of_row_lt
    D datum row hrowHeight hrowBasis]
  exact F.closing_off_coeff hhead hiso

theorem forestClosingDatumBool_closingMatrix_closing_column_head_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length)
    (hvertex :
      reducedBasisVertex D datum.isolated row = datum.closing.head) :
    get2D (closingMatrix D datum) row datum.forest.length = 1 :=
  (forestClosingDatumBool_facts h).closingMatrix_closing_column_head_coeff
    hrowHeight hrowBasis hvertex

theorem forestClosingDatumBool_closingMatrix_closing_column_off_coeff
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) {row : Nat}
    (hrowHeight : row < D - 1)
    (hrowBasis : row < (reducedBasisVertices D datum.isolated).length)
    (hhead :
      reducedBasisVertex D datum.isolated row ≠ datum.closing.head)
    (hiso :
      reducedBasisVertex D datum.isolated row ≠ datum.isolated) :
    get2D (closingMatrix D datum) row datum.forest.length = 0 :=
  (forestClosingDatumBool_facts h).closingMatrix_closing_column_off_coeff
    hrowHeight hrowBasis hhead hiso

theorem ForestClosingDatumFacts.closing_not_forest_undirected
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    ∀ e ∈ datum.forest,
      ¬ EdgeUndirectedEquivalent datum.closing e := by
  intro e he hEq
  have hAvoid := F.forest_avoids_isolated e he
  rcases hEq with hEq | hEq
  · exact hAvoid.1 (hEq.1.symm.trans F.closing_tail_eq_isolated)
  · exact hAvoid.2 (hEq.1.symm.trans F.closing_tail_eq_isolated)

theorem ForestClosingDatumFacts.closing_not_forest_member
    {D : Nat} {datum : ForestClosingDatum}
    (F : ForestClosingDatumFacts D datum) :
    edgeMemberUndirected datum.closing datum.forest = false := by
  cases hmem : edgeMemberUndirected datum.closing datum.forest
  · rfl
  · rcases edgeMemberUndirected_eq_true_iff.mp hmem with ⟨e, he, heq⟩
    exact False.elim ((F.closing_not_forest_undirected e he) heq)

theorem forestClosingDatumBool_closing_not_forest_member
    {D : Nat} {datum : ForestClosingDatum}
    (h : forestClosingDatumBool D datum = true) :
    edgeMemberUndirected datum.closing datum.forest = false :=
  (forestClosingDatumBool_facts h).closing_not_forest_member

def supportRowDatumBool (D : Nat) (row : SupportRowDatum) : Bool :=
  natLtBool row.stage D &&
    (row.support.length == D - row.stage - 1) &&
    row.support.all (edgeInBounds D) &&
    row.active.all (edgeInBounds D) &&
    row.active.all (fun e => edgeMemberUndirected e row.support)

structure SupportRowDatumFacts (D : Nat) (row : SupportRowDatum) :
    Prop where
  stage_lt : row.stage < D
  support_length : row.support.length = D - row.stage - 1
  support_inBounds :
    ∀ e ∈ row.support, e.tail < D ∧ e.head < D
  active_inBounds :
    ∀ e ∈ row.active, e.tail < D ∧ e.head < D
  active_member_undirected :
    ∀ e ∈ row.active, edgeMemberUndirected e row.support = true
  active_supported :
    ∀ e ∈ row.active, ∃ f ∈ row.support, EdgeUndirectedEquivalent e f

theorem supportRowDatumBool_facts
    {D : Nat} {row : SupportRowDatum}
    (h : supportRowDatumBool D row = true) :
    SupportRowDatumFacts D row := by
  have hs := by
    simpa [supportRowDatumBool, natLtBool, edgeInBounds] using h
  rcases hs with ⟨hs, hactiveMem⟩
  rcases hs with ⟨hs, hactiveBounds⟩
  rcases hs with ⟨hs, hsupportBounds⟩
  rcases hs with ⟨hstage, hsupportLength⟩
  exact
    { stage_lt := hstage
      support_length := hsupportLength
      support_inBounds := hsupportBounds
      active_inBounds := hactiveBounds
      active_member_undirected := hactiveMem
      active_supported := fun e he =>
        edgeMemberUndirected_eq_true_iff.mp (hactiveMem e he) }

theorem SupportRowDatumFacts.active_supported_inBounds
    {D : Nat} {row : SupportRowDatum}
    (F : SupportRowDatumFacts D row) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧ f.tail < D ∧ f.head < D := by
  intro e he
  rcases F.active_supported e he with ⟨f, hf, hEq⟩
  exact ⟨f, hf, hEq, F.support_inBounds f hf⟩

theorem supportRowDatumBool_active_supported_inBounds
    {D : Nat} {row : SupportRowDatum}
    (h : supportRowDatumBool D row = true) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧ f.tail < D ∧ f.head < D :=
  (supportRowDatumBool_facts h).active_supported_inBounds

theorem SupportRowDatumFacts.active_vectorEdge_eq_or_neg
    {D : Nat} {row : SupportRowDatum}
    (F : SupportRowDatumFacts D row) (basisBase : Nat) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧
          (vectorEdge D e basisBase = vectorEdge D f basisBase ∨
            vectorEdge D e basisBase =
              (vectorEdge D f basisBase).map (fun z => -z)) := by
  intro e he
  rcases F.active_supported e he with ⟨f, hf, hEq⟩
  exact
    ⟨f, hf, hEq,
      EdgeUndirectedEquivalent.vectorEdge_eq_or_neg hEq D basisBase⟩

theorem supportRowDatumBool_active_vectorEdge_eq_or_neg
    {D : Nat} {row : SupportRowDatum}
    (h : supportRowDatumBool D row = true) (basisBase : Nat) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧
          (vectorEdge D e basisBase = vectorEdge D f basisBase ∨
            vectorEdge D e basisBase =
              (vectorEdge D f basisBase).map (fun z => -z)) :=
  (supportRowDatumBool_facts h).active_vectorEdge_eq_or_neg basisBase

def modInt (x : Int) (m : Nat) : Int :=
  x % Int.ofNat m

def modEqBool (x : Int) (m r : Nat) : Bool :=
  intEqBool (modInt x m) (modInt (Int.ofNat r) m)

def modCoord (m : Nat) (point : List Int) : List Int :=
  point.map (fun x => modInt x m)

def d5ReservePlaneBool (point : List Int) : Bool :=
  (point.length == 4) &&
    modEqBool (getD point 2) 6 2 &&
    modEqBool (getD point 0 + getD point 1 + getD point 3) 6 5

def d7ReservePlaneBool (point : List Int) : Bool :=
  (point.length == 6) &&
    modEqBool (getD point 0) 8 1 &&
    modEqBool (getD point 3) 8 5 &&
    modEqBool (getD point 1 + getD point 5) 8 6 &&
    modEqBool (getD point 2 + getD point 4) 8 5

def reservePlaneAuditBool
    (modulus : Nat) (plane : List Int → Bool) (points : List (List Int)) :
    Bool :=
  listNodupBool (points.map (modCoord modulus)) &&
    points.all plane

def treeWitness (root : Nat) (steps : List (Nat × Nat)) :
    TreeWitness :=
  { root := root,
    steps := steps.map (fun step =>
      { vertex := step.fst, parent := step.snd }) }

def forestDatum
    (color : Nat) (forest : List AuditEdge) (isolated : Nat)
    (closing : AuditEdge) (sign : Int) (witness : TreeWitness) :
    ForestClosingDatum :=
  { color, forest, isolated, closing, sign, witness }

def supportDatum
    (stage : Nat) (support active : List AuditEdge) : SupportRowDatum :=
  { stage, support, active }

def d5ForestClosingData : List ForestClosingDatum :=
  [ forestDatum 0 [edge 0 2, edge 0 1, edge 2 4] 3
      (edge 3 0) 1 (treeWitness 0 [(2, 0), (1, 0), (4, 2)]),
    forestDatum 1 [edge 0 1, edge 2 3, edge 0 3] 4
      (edge 4 1) 1 (treeWitness 0 [(1, 0), (3, 0), (2, 3)]),
    forestDatum 2 [edge 1 2, edge 2 3, edge 2 4] 0
      (edge 0 2) 1 (treeWitness 1 [(2, 1), (3, 2), (4, 2)]),
    forestDatum 3 [edge 3 4, edge 1 4, edge 0 1] 2
      (edge 2 3) (-1) (treeWitness 3 [(4, 3), (1, 4), (0, 1)]),
    forestDatum 4 [edge 3 4, edge 0 4, edge 1 3] 2
      (edge 2 4) 1 (treeWitness 3 [(4, 3), (0, 4), (1, 3)]) ]

def d7ForestClosingData : List ForestClosingDatum :=
  [ forestDatum 0
      [edge 0 1, edge 1 3, edge 1 2, edge 3 4, edge 0 5] 6
      (edge 6 0) 1
      (treeWitness 0 [(1, 0), (3, 1), (2, 1), (4, 3), (5, 0)]),
    forestDatum 1
      [edge 1 2, edge 2 4, edge 0 3, edge 3 4, edge 4 6] 5
      (edge 5 1) (-1)
      (treeWitness 1 [(2, 1), (4, 2), (6, 4), (3, 4), (0, 3)]),
    forestDatum 2
      [edge 0 2, edge 1 3, edge 2 4, edge 1 5, edge 0 1] 6
      (edge 6 2) (-1)
      (treeWitness 0 [(2, 0), (1, 0), (3, 1), (5, 1), (4, 2)]),
    forestDatum 3
      [edge 3 4, edge 4 5, edge 5 6, edge 0 6, edge 1 5] 2
      (edge 2 3) 1
      (treeWitness 3 [(4, 3), (5, 4), (6, 5), (0, 6), (1, 5)]),
    forestDatum 4
      [edge 3 4, edge 2 5, edge 5 6, edge 0 6, edge 2 3] 1
      (edge 1 4) (-1)
      (treeWitness 3 [(4, 3), (2, 3), (5, 2), (6, 5), (0, 6)]),
    forestDatum 5
      [edge 5 6, edge 0 6, edge 0 3, edge 1 2, edge 2 3] 4
      (edge 4 5) 1
      (treeWitness 5 [(6, 5), (0, 6), (3, 0), (2, 3), (1, 2)]),
    forestDatum 6
      [edge 5 6, edge 0 6, edge 1 4, edge 2 5, edge 4 6] 3
      (edge 3 6) (-1)
      (treeWitness 5 [(6, 5), (0, 6), (4, 6), (1, 4), (2, 5)]) ]

def d5SupportRows : List SupportRowDatum :=
  [ supportDatum 1 [edge 0 1, edge 0 2, edge 0 3]
      [edge 0 1, edge 0 2],
    supportDatum 1 [edge 0 1, edge 0 3, edge 3 4]
      [edge 3 4],
    supportDatum 2 [edge 0 1, edge 0 4]
      [edge 0 1, edge 0 4],
    supportDatum 2 [edge 0 2, edge 2 3]
      [edge 2 3],
    supportDatum 3 [edge 2 4]
      [edge 2 4] ]

def d7SupportRows : List SupportRowDatum :=
  [ supportDatum 1
      [edge 0 1, edge 0 2, edge 0 3, edge 0 4, edge 0 5]
      [edge 0 2, edge 0 1],
    supportDatum 1
      [edge 0 1, edge 0 2, edge 0 3, edge 0 5, edge 3 4]
      [edge 3 4],
    supportDatum 1
      [edge 0 1, edge 0 2, edge 0 3, edge 0 5, edge 5 6]
      [edge 5 6],
    supportDatum 2
      [edge 0 1, edge 0 3, edge 2 4, edge 2 5]
      [edge 2 5, edge 2 4],
    supportDatum 2
      [edge 0 4, edge 0 5, edge 1 2, edge 1 3]
      [edge 1 3],
    supportDatum 2
      [edge 0 1, edge 0 2, edge 0 3, edge 0 6]
      [edge 0 6],
    supportDatum 3
      [edge 1 2, edge 1 4, edge 1 5]
      [edge 1 2, edge 1 4],
    supportDatum 3
      [edge 0 1, edge 0 3, edge 2 5]
      [edge 0 3],
    supportDatum 3
      [edge 0 2, edge 0 3, edge 5 6]
      [edge 5 6],
    supportDatum 4 [edge 1 2, edge 1 5]
      [edge 1 5, edge 1 2],
    supportDatum 4 [edge 0 5, edge 3 4]
      [edge 3 4],
    supportDatum 4 [edge 0 6, edge 2 3]
      [edge 0 6],
    supportDatum 5 [edge 4 6]
      [edge 4 6],
    supportDatum 5 [edge 2 3]
      [edge 2 3] ]

def d5ReservePoints : List (List Int) :=
  [ [1, 0, 2, 4], [0, 1, 2, 4], [-1, 2, 2, 4],
    [0, 0, 2, 5], [-1, 1, 2, 5], [-2, 2, 2, 5],
    [-3, 3, 2, 5], [-1, 0, 2, 6] ]

def d7ReservePoints : List (List Int) :=
  [ [1, 0, 3, 5, 2, 6], [1, -1, 3, 5, 2, 7],
    [1, -2, 3, 5, 2, 8], [1, 0, 2, 5, 3, 6],
    [1, -1, 2, 5, 3, 7], [1, -2, 2, 5, 3, 8],
    [1, -3, 2, 5, 3, 9], [1, -4, 2, 5, 3, 10],
    [1, -5, 2, 5, 3, 11], [1, 0, 1, 5, 4, 6] ]

def d5ForestClosingAuditBool : Bool :=
  (d5ForestClosingData.length == 5) &&
    d5ForestClosingData.all (forestClosingDatumBool 5)

def d7ForestClosingAuditBool : Bool :=
  (d7ForestClosingData.length == 7) &&
    d7ForestClosingData.all (forestClosingDatumBool 7)

def d5SupportAuditBool : Bool :=
  (d5SupportRows.length == 5) &&
    d5SupportRows.all (supportRowDatumBool 5)

def d7SupportAuditBool : Bool :=
  (d7SupportRows.length == 14) &&
    d7SupportRows.all (supportRowDatumBool 7)

def d5ReservePlaneAuditBool : Bool :=
  reservePlaneAuditBool 6 d5ReservePlaneBool d5ReservePoints

def d7ReservePlaneAuditBool : Bool :=
  reservePlaneAuditBool 8 d7ReservePlaneBool d7ReservePoints

theorem d5ForestClosingAudit :
    d5ForestClosingAuditBool = true := by
  decide

theorem d7ForestClosingAudit :
    d7ForestClosingAuditBool = true := by
  decide

theorem d5ForestClosingData_forall_datumBool
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    forestClosingDatumBool 5 datum = true := by
  have h := d5ForestClosingAudit
  unfold d5ForestClosingAuditBool at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 datum hmem

theorem d7ForestClosingData_forall_datumBool
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    forestClosingDatumBool 7 datum = true := by
  have h := d7ForestClosingAudit
  unfold d7ForestClosingAuditBool at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 datum hmem

theorem d5ForestClosingData_detInt_zmod_unit
    {m : Nat} [NeZero m] {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    IsUnit ((detInt (closingMatrix 5 datum) : Int) : ZMod m) :=
  forestClosingDatumBool_detInt_zmod_unit
    (d5ForestClosingData_forall_datumBool hmem)

theorem d7ForestClosingData_detInt_zmod_unit
    {m : Nat} [NeZero m] {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    IsUnit ((detInt (closingMatrix 7 datum) : Int) : ZMod m) :=
  forestClosingDatumBool_detInt_zmod_unit
    (d7ForestClosingData_forall_datumBool hmem)

theorem d5ForestClosingData_facts
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    ForestClosingDatumFacts 5 datum :=
  forestClosingDatumBool_facts
    (d5ForestClosingData_forall_datumBool hmem)

theorem d7ForestClosingData_facts
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    ForestClosingDatumFacts 7 datum :=
  forestClosingDatumBool_facts
    (d7ForestClosingData_forall_datumBool hmem)

theorem d5ForestClosingData_closingMatrixPayload
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    ClosingMatrixPayload 5 datum :=
  closingMatrixPayload_of_facts (d5ForestClosingData_facts hmem)

theorem d7ForestClosingData_closingMatrixPayload
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    ClosingMatrixPayload 7 datum :=
  closingMatrixPayload_of_facts (d7ForestClosingData_facts hmem)

theorem d5ForestClosingData_closingMatrix_length
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    (closingMatrix 5 datum).length = 4 := by
  simpa using (d5ForestClosingData_facts hmem).closingMatrix_length

theorem d7ForestClosingData_closingMatrix_length
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    (closingMatrix 7 datum).length = 6 := by
  simpa using (d7ForestClosingData_facts hmem).closingMatrix_length

theorem d5ForestClosingData_closingMatrix_row_length
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) {row : Nat}
    (hrow : row < 4) :
    ((closingMatrix 5 datum).getD row []).length = 4 := by
  simpa using
    (d5ForestClosingData_facts hmem).closingMatrix_row_length
      (by simpa using hrow)

theorem d7ForestClosingData_closingMatrix_row_length
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) {row : Nat}
    (hrow : row < 6) :
    ((closingMatrix 7 datum).getD row []).length = 6 := by
  simpa using
    (d7ForestClosingData_facts hmem).closingMatrix_row_length
      (by simpa using hrow)

theorem d5ForestClosingData_closingMatrix_forest_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) {row col : Nat}
    (hrow : row < 4) (hcol : col < datum.forest.length) :
    get2D (closingMatrix 5 datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex 5 datum.isolated row) := by
  simpa using
    (d5ForestClosingData_facts hmem).closingMatrix_forest_column_coeff
      (by simpa using hrow) hcol

theorem d7ForestClosingData_closingMatrix_forest_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) {row col : Nat}
    (hrow : row < 6) (hcol : col < datum.forest.length) :
    get2D (closingMatrix 7 datum) row col =
      edgeVectorCoeff (datum.forest.getD col (edge 0 0))
        (reducedBasisVertex 7 datum.isolated row) := by
  simpa using
    (d7ForestClosingData_facts hmem).closingMatrix_forest_column_coeff
      (by simpa using hrow) hcol

theorem d5ForestClosingData_closingMatrix_closing_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) {row : Nat}
    (hrow : row < 4) :
    get2D (closingMatrix 5 datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex 5 datum.isolated row) := by
  simpa using
    (d5ForestClosingData_facts hmem).closingMatrix_closing_column_coeff
      (by simpa using hrow)

theorem d7ForestClosingData_closingMatrix_closing_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) {row : Nat}
    (hrow : row < 6) :
    get2D (closingMatrix 7 datum) row datum.forest.length =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex 7 datum.isolated row) := by
  simpa using
    (d7ForestClosingData_facts hmem).closingMatrix_closing_column_coeff
      (by simpa using hrow)

theorem d5ForestClosingData_closingColumnFin_val
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData) :
    (d5ForestClosingData_facts hmem).closingColumnFin.val =
      datum.forest.length :=
  rfl

theorem d7ForestClosingData_closingColumnFin_val
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData) :
    (d7ForestClosingData_facts hmem).closingColumnFin.val =
      datum.forest.length :=
  rfl

theorem d5ForestClosingData_closingMatrixFin_forest_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData)
    (row col : Fin 4)
    (hcol : col.val < datum.forest.length) :
    closingMatrixFin 5 datum row col =
      edgeVectorCoeff (datum.forest.getD col.val (edge 0 0))
        (reducedBasisVertex 5 datum.isolated row.val) :=
  (d5ForestClosingData_facts hmem).closingMatrixFin_forest_column_coeff
    row col hcol

theorem d7ForestClosingData_closingMatrixFin_forest_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData)
    (row col : Fin 6)
    (hcol : col.val < datum.forest.length) :
    closingMatrixFin 7 datum row col =
      edgeVectorCoeff (datum.forest.getD col.val (edge 0 0))
        (reducedBasisVertex 7 datum.isolated row.val) :=
  (d7ForestClosingData_facts hmem).closingMatrixFin_forest_column_coeff
    row col hcol

theorem d5ForestClosingData_closingMatrixFin_closing_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d5ForestClosingData)
    (row : Fin 4) :
    closingMatrixFin 5 datum row
        (d5ForestClosingData_facts hmem).closingColumnFin =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex 5 datum.isolated row.val) :=
  (d5ForestClosingData_facts hmem).closingMatrixFin_closing_column_coeff
    row

theorem d7ForestClosingData_closingMatrixFin_closing_column_coeff
    {datum : ForestClosingDatum}
    (hmem : datum ∈ d7ForestClosingData)
    (row : Fin 6) :
    closingMatrixFin 7 datum row
        (d7ForestClosingData_facts hmem).closingColumnFin =
      edgeVectorCoeff datum.closing
        (reducedBasisVertex 7 datum.isolated row.val) :=
  (d7ForestClosingData_facts hmem).closingMatrixFin_closing_column_coeff
    row

theorem d5SupportAudit :
    d5SupportAuditBool = true := by
  decide

theorem d7SupportAudit :
    d7SupportAuditBool = true := by
  decide

theorem d5SupportRows_forall_rowBool
    {row : SupportRowDatum}
    (hmem : row ∈ d5SupportRows) :
    supportRowDatumBool 5 row = true := by
  have h := d5SupportAudit
  unfold d5SupportAuditBool at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 row hmem

theorem d7SupportRows_forall_rowBool
    {row : SupportRowDatum}
    (hmem : row ∈ d7SupportRows) :
    supportRowDatumBool 7 row = true := by
  have h := d7SupportAudit
  unfold d7SupportAuditBool at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 row hmem

theorem d5SupportRows_facts
    {row : SupportRowDatum}
    (hmem : row ∈ d5SupportRows) :
    SupportRowDatumFacts 5 row :=
  supportRowDatumBool_facts
    (d5SupportRows_forall_rowBool hmem)

theorem d7SupportRows_facts
    {row : SupportRowDatum}
    (hmem : row ∈ d7SupportRows) :
    SupportRowDatumFacts 7 row :=
  supportRowDatumBool_facts
    (d7SupportRows_forall_rowBool hmem)

theorem d5SupportRows_active_supported_inBounds
    {row : SupportRowDatum}
    (hmem : row ∈ d5SupportRows) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧ f.tail < 5 ∧ f.head < 5 :=
  (d5SupportRows_facts hmem).active_supported_inBounds

theorem d7SupportRows_active_supported_inBounds
    {row : SupportRowDatum}
    (hmem : row ∈ d7SupportRows) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧ f.tail < 7 ∧ f.head < 7 :=
  (d7SupportRows_facts hmem).active_supported_inBounds

theorem d5SupportRows_active_vectorEdge_eq_or_neg
    {row : SupportRowDatum}
    (hmem : row ∈ d5SupportRows) (basisBase : Nat) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧
          (vectorEdge 5 e basisBase = vectorEdge 5 f basisBase ∨
            vectorEdge 5 e basisBase =
              (vectorEdge 5 f basisBase).map (fun z => -z)) :=
  (d5SupportRows_facts hmem).active_vectorEdge_eq_or_neg basisBase

theorem d7SupportRows_active_vectorEdge_eq_or_neg
    {row : SupportRowDatum}
    (hmem : row ∈ d7SupportRows) (basisBase : Nat) :
    ∀ e ∈ row.active,
      ∃ f ∈ row.support,
        EdgeUndirectedEquivalent e f ∧
          (vectorEdge 7 e basisBase = vectorEdge 7 f basisBase ∨
            vectorEdge 7 e basisBase =
              (vectorEdge 7 f basisBase).map (fun z => -z)) :=
  (d7SupportRows_facts hmem).active_vectorEdge_eq_or_neg basisBase

theorem d5ReservePlaneAudit :
    d5ReservePlaneAuditBool = true := by
  decide

theorem d7ReservePlaneAudit :
    d7ReservePlaneAuditBool = true := by
  decide

theorem foldedTerminalWordAudit :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  ⟨foldedSites4_singleCycle, foldedSites6_singleCycle⟩

theorem v28FiniteAuditSummary :
    d5ForestClosingAuditBool = true ∧
    d7ForestClosingAuditBool = true ∧
    d5SupportAuditBool = true ∧
    d7SupportAuditBool = true ∧
    d5ReservePlaneAuditBool = true ∧
    d7ReservePlaneAuditBool = true ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  ⟨d5ForestClosingAudit, d7ForestClosingAudit, d5SupportAudit,
    d7SupportAudit, d5ReservePlaneAudit, d7ReservePlaneAudit,
    foldedTerminalWordAudit.1, foldedTerminalWordAudit.2⟩

end FiniteAudit

export FiniteAudit
  (d5ForestClosingAudit d7ForestClosingAudit
   d5SupportAudit d7SupportAudit
   d5ReservePlaneAudit d7ReservePlaneAudit
   intEqBool_eq_true_iff primitiveDetBool_eq_true_iff
   natEqBool_eq_true_iff natNeBool_eq_true_iff
   natLtBool_eq_true_iff intNeBool_eq_true_iff
   edgeInBounds_eq_true_iff edgeTouches_eq_false_iff
   EdgeUndirectedEquivalent EdgeUndirectedEquivalent.refl
   EdgeUndirectedEquivalent.symm edgeUndirectedEq_eq_true_iff
   edgeMemberUndirected_eq_true_iff
   edgeVectorCoeff edgeVectorCoeff_head_of_tail_ne
   edgeVectorCoeff_tail_of_head_ne edgeVectorCoeff_off
   reducedBasisVertices reducedBasisVertex
   reducedBasisVertices_length_of_lt
   reducedBasisVertex_lt_of_row_lt
   reducedBasisVertex_ne_basisBase_of_row_lt
   EdgeUndirectedEquivalent.edgeVectorCoeff_eq_or_neg
   EdgeUndirectedEquivalent.vectorEdge_eq_or_neg
   vectorEdge_getD_of_row_lt vectorEdge_getD_of_length_le
   columnsToRows_length list_getD_map_range_of_lt
   list_getD_map_range_of_length_le list_getD_map_of_lt
     columnsToRows_row_length_of_lt columnsToRows_get2D_of_lt
     columnsToRows_get2D_of_height_le
     columnsToRows_get2D_of_cols_length_le
     listIntMatrix closingMatrixFin
     listIntMatrix_apply closingMatrixFin_apply
     closingMatrix_length
     closingMatrix_row_length_of_lt
     closingMatrix_row_length_eq_of_forest_length
     closingMatrix_get2D_of_height_le
     closingMatrix_get2D_of_width_le
     closingMatrix_get2D_of_square_width_le
     closingMatrix_forest_column_getD_of_lt
     closingMatrix_forest_column_coeff_of_lt
     closingMatrix_forest_column_coeff_of_lt_of_isolated_lt
   closingMatrix_closing_column_getD_of_row_lt
   closingMatrix_closing_column_coeff_of_row_lt
   closingMatrix_closing_column_coeff_of_row_lt_of_isolated_lt
   primitiveDetBool_detInt_eq_one_or_neg_one
   intCast_zmod_isUnit_of_eq_one_or_neg_one
   forestClosingDatumBool_primitiveDet
   forestClosingDatumBool_detInt_eq_one_or_neg_one
   forestClosingDatumBool_detInt_zmod_unit
   ForestClosingDatumFacts forestClosingDatumBool_facts
   forestClosingDatumBool_closing_tail_eq_isolated
   forestClosingDatumBool_closing_head_ne_isolated
     forestClosingDatumBool_forest_avoids_isolated
     forestClosingDatumBool_sign_eq_one_or_neg_one
     ForestClosingDatumFacts.isolated_lt
     forestClosingDatumBool_isolated_lt
     ForestClosingDatumFacts.two_le
     forestClosingDatumBool_two_le
     ForestClosingDatumFacts.closingMatrix_length
     ForestClosingDatumFacts.closingMatrix_row_length
     ForestClosingDatumFacts.closingMatrix_height_zero
     ForestClosingDatumFacts.closingMatrix_width_zero
     forestClosingDatumBool_closingMatrix_length
     forestClosingDatumBool_closingMatrix_row_length
     forestClosingDatumBool_closingMatrix_height_zero
     forestClosingDatumBool_closingMatrix_width_zero
     ForestClosingDatumFacts.closingColumnFin
     ForestClosingDatumFacts.closingColumnFin_val
     ForestClosingDatumFacts.closingMatrixFin_forest_column_coeff
     ForestClosingDatumFacts.closingMatrixFin_closing_column_coeff
     forestClosingDatumBool_closingMatrixFin_forest_column_coeff
     forestClosingDatumBool_closingMatrixFin_closing_column_coeff
     ForestClosingDatumFacts.detInt_zmod_unit
     forestClosingDatumBool_facts_detInt_zmod_unit
     ClosingMatrixPayload
     closingMatrixPayload_of_facts
     closingMatrixPayload_of_bool
     ForestClosingDatumFacts.closingMatrix_forest_column_coeff
     ForestClosingDatumFacts.closingMatrix_closing_column_coeff
     forestClosingDatumBool_closingMatrix_forest_column_coeff
     forestClosingDatumBool_closingMatrix_closing_column_coeff
     ForestClosingDatumFacts.closing_head_coeff
     ForestClosingDatumFacts.closing_isolated_coeff
     ForestClosingDatumFacts.closing_off_coeff
     forestClosingDatumBool_closing_head_coeff
     forestClosingDatumBool_closing_isolated_coeff
     forestClosingDatumBool_closing_off_coeff
     ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff_of_row_lt
     ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff_of_row_lt
     forestClosingDatumBool_closingMatrix_closing_column_head_coeff_of_row_lt
     forestClosingDatumBool_closingMatrix_closing_column_off_coeff_of_row_lt
     ForestClosingDatumFacts.closingMatrix_closing_column_head_coeff
     ForestClosingDatumFacts.closingMatrix_closing_column_off_coeff
   forestClosingDatumBool_closingMatrix_closing_column_head_coeff
   forestClosingDatumBool_closingMatrix_closing_column_off_coeff
   ForestClosingDatumFacts.closing_not_forest_undirected
   ForestClosingDatumFacts.closing_not_forest_member
   forestClosingDatumBool_closing_not_forest_member
   SupportRowDatumFacts supportRowDatumBool_facts
   SupportRowDatumFacts.active_supported_inBounds
   supportRowDatumBool_active_supported_inBounds
   SupportRowDatumFacts.active_vectorEdge_eq_or_neg
   supportRowDatumBool_active_vectorEdge_eq_or_neg
   d5ForestClosingData_forall_datumBool
   d7ForestClosingData_forall_datumBool
     d5ForestClosingData_detInt_zmod_unit
     d7ForestClosingData_detInt_zmod_unit
     d5ForestClosingData_facts d7ForestClosingData_facts
     d5ForestClosingData_closingMatrixPayload
     d7ForestClosingData_closingMatrixPayload
     d5ForestClosingData_closingMatrix_length
     d7ForestClosingData_closingMatrix_length
     d5ForestClosingData_closingMatrix_row_length
     d7ForestClosingData_closingMatrix_row_length
     d5ForestClosingData_closingMatrix_forest_column_coeff
     d7ForestClosingData_closingMatrix_forest_column_coeff
     d5ForestClosingData_closingMatrix_closing_column_coeff
     d7ForestClosingData_closingMatrix_closing_column_coeff
     d5ForestClosingData_closingColumnFin_val
     d7ForestClosingData_closingColumnFin_val
     d5ForestClosingData_closingMatrixFin_forest_column_coeff
     d7ForestClosingData_closingMatrixFin_forest_column_coeff
     d5ForestClosingData_closingMatrixFin_closing_column_coeff
     d7ForestClosingData_closingMatrixFin_closing_column_coeff
   d5SupportRows_forall_rowBool d7SupportRows_forall_rowBool
   d5SupportRows_facts d7SupportRows_facts
   d5SupportRows_active_supported_inBounds
   d7SupportRows_active_supported_inBounds
   d5SupportRows_active_vectorEdge_eq_or_neg
   d7SupportRows_active_vectorEdge_eq_or_neg
   foldedTerminalWordAudit v28FiniteAuditSummary)

end EvenV11
