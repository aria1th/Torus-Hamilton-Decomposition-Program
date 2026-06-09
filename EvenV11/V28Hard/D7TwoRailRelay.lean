import EvenV11.RootFlatCycleData
import EvenV11.FiniteAudit
import EvenV11.FiniteAuditBridge

/-!
# Hard slots H3/H4: D7 two-rail relay blueprint

This file encodes the paper's `D₇` relay tables as ordinary Lean data and then
states the proof interface that should replace the generated finite blobs.

The point is not to finish RF1/RF2/RF3 here.  The point is to make the difficult
paper proof editable in small Lean-native pieces:

* `stageRows` is the shifted two-rail support table from the manuscript;
* `colorClosureData` is the coforest/closing-edge audit used in the finite
  checker;
* `terminalAlignment` is the final low-modulus alignment with the terminal
  `A₂` block;
* `TwoRailRelayRealization m` is exactly the object that produces
  `RootFlatCycle.RootFlatCycleData 6 m`.

Once the realization is filled, `cycleData_of_realization` replaces both
finite-backed checkpoints without changing the main induction spine.
-/

namespace EvenV11
namespace V28Hard
namespace D7TwoRailRelay

open Shared
open StandardRootFlatLift

abbrev Label := Fin 7
abbrev Edge := Label × Label
abbrev Dir := TorusDirection 7
abbrev Color := TorusColor 7

def L0 : Label := 0
def L1 : Label := 1
def L2 : Label := 2
def L3 : Label := 3
def L4 : Label := 4
def L5 : Label := 5
def L6 : Label := 6

def E (a b : Label) : Edge := (a, b)

def edge01 : Edge := E L0 L1
def edge02 : Edge := E L0 L2
def edge03 : Edge := E L0 L3
def edge04 : Edge := E L0 L4
def edge05 : Edge := E L0 L5
def edge06 : Edge := E L0 L6
def edge12 : Edge := E L1 L2
def edge13 : Edge := E L1 L3
def edge14 : Edge := E L1 L4
def edge15 : Edge := E L1 L5
def edge16 : Edge := E L1 L6
def edge23 : Edge := E L2 L3
def edge24 : Edge := E L2 L4
def edge25 : Edge := E L2 L5
/-- Oriented as `(6,2)` in the audit table. -/
def edge62 : Edge := E L6 L2
def edge34 : Edge := E L3 L4
def edge35 : Edge := E L3 L5
def edge36 : Edge := E L3 L6
def edge45 : Edge := E L4 L5
def edge46 : Edge := E L4 L6
def edge56 : Edge := E L5 L6

/-- One visible two-rail row in the D7 relay table.  `stage` is the manuscript
stage number after the displayed shift has been applied.  `support` is the
row/coforest support; `active` is the list of support edges actually spliced at
that row. -/
structure RelayRow where
  stage : Nat
  support : List Edge
  active : List Edge
  deriving DecidableEq, Repr

/-- Shifted D7 two-rail row table, transcribed from the paper/finite audit. -/
def stageRows : List RelayRow :=
  [ { stage := 1,
      support := [edge01, edge02, edge03, edge04, edge05],
      active := [edge02, edge01] },
    { stage := 1,
      support := [edge01, edge02, edge03, edge05, edge34],
      active := [edge34] },
    { stage := 1,
      support := [edge01, edge02, edge03, edge05, edge56],
      active := [edge56] },
    { stage := 2,
      support := [edge01, edge03, edge24, edge25],
      active := [edge25, edge24] },
    { stage := 2,
      support := [edge04, edge05, edge12, edge13],
      active := [edge13] },
    { stage := 2,
      support := [edge01, edge02, edge03, edge06],
      active := [edge06] },
    { stage := 3,
      support := [edge12, edge14, edge15],
      active := [edge12, edge14] },
    { stage := 3,
      support := [edge01, edge03, edge25],
      active := [edge03] },
    { stage := 3,
      support := [edge02, edge03, edge56],
      active := [edge56] },
    { stage := 4,
      support := [edge12, edge15],
      active := [edge15, edge12] },
    { stage := 4,
      support := [edge05, edge34],
      active := [edge34] },
    { stage := 4,
      support := [edge06, edge23],
      active := [edge06] },
    { stage := 5,
      support := [edge46],
      active := [edge46] },
    { stage := 5,
      support := [edge23],
      active := [edge23] } ]

/-- The five relay stages as displayed in the manuscript before row expansion. -/
structure StageSkeleton where
  stage : Nat
  shift : Label
  triple : Label × Label × Label
  pair₁ : Edge
  pair₂ : Edge
  shiftedTriple : Label × Label × Label
  shiftedPair₁ : Edge
  shiftedPair₂ : Edge
  deriving DecidableEq, Repr

def stageSkeletons : List StageSkeleton :=
  [ { stage := 1, shift := L0,
      triple := (L0, L1, L2), pair₁ := edge34, pair₂ := edge56,
      shiftedTriple := (L0, L1, L2), shiftedPair₁ := edge34,
      shiftedPair₂ := edge56 },
    { stage := 2, shift := L1,
      triple := (L1, L3, L4), pair₁ := edge02, pair₂ := edge56,
      shiftedTriple := (L2, L4, L5), shiftedPair₁ := edge13,
      shiftedPair₂ := edge06 },
    { stage := 3, shift := L2,
      triple := (L0, L6, L2), pair₁ := edge15, pair₂ := edge34,
      shiftedTriple := (L2, L1, L4), shiftedPair₁ := edge03,
      shiftedPair₂ := edge56 },
    { stage := 4, shift := L3,
      triple := (L2, L5, L6), pair₁ := edge01, pair₂ := edge34,
      shiftedTriple := (L5, L1, L2), shiftedPair₁ := edge34,
      shiftedPair₂ := edge06 },
    { stage := 5, shift := L5,
      triple := (L0, L2, L3), pair₁ := edge16, pair₂ := edge45,
      shiftedTriple := (L5, L0, L1), shiftedPair₁ := edge46,
      shiftedPair₂ := edge23 } ]

/-- One color's closure row from the finite audit: a coforest, an isolated root,
a closing edge, and the sign/orientation used for determinant bookkeeping. -/
structure ColorClosureDatum where
  color : Label
  coforest : List Edge
  isolated : Label
  closing : Edge
  sign : Int
  deriving DecidableEq, Repr

def colorClosureData : List ColorClosureDatum :=
  [ { color := L0,
      coforest := [edge01, edge13, edge12, edge34, edge05],
      isolated := L6, closing := edge06, sign := 1 },
    { color := L1,
      coforest := [edge12, edge24, edge03, edge34, edge46],
      isolated := L5, closing := edge15, sign := -1 },
    { color := L2,
      coforest := [edge02, edge13, edge24, edge15, edge01],
      isolated := L6, closing := edge62, sign := -1 },
    { color := L3,
      coforest := [edge34, edge45, edge56, edge06, edge15],
      isolated := L2, closing := edge23, sign := 1 },
    { color := L4,
      coforest := [edge34, edge25, edge56, edge06, edge23],
      isolated := L1, closing := edge14, sign := -1 },
    { color := L5,
      coforest := [edge56, edge06, edge03, edge12, edge23],
      isolated := L4, closing := edge45, sign := 1 },
    { color := L6,
      coforest := [edge56, edge06, edge14, edge25, edge46],
      isolated := L3, closing := edge36, sign := -1 } ]

/-- Final terminal alignment used when the relay is glued to the low-dimensional
terminal block. -/
structure TerminalAlignment where
  terminalTriple : Label × Label × Label
  shiftedRoots : Label × Label × Label
  basisEdge₁ : Edge
  basisEdge₂ : Edge
  row₁ : Int × Int
  row₂ : Int × Int
  row₃ : Int × Int
  permutation : Label × Label × Label
  signs : Int × Int × Int
  deriving DecidableEq, Repr

def terminalAlignment : TerminalAlignment :=
  { terminalTriple := (L0, L2, L3)
    shiftedRoots := (L5, L0, L1)
    basisEdge₁ := edge05
    basisEdge₂ := edge01
    row₁ := (-1, 0)
    row₂ := (1, 1)
    row₃ := (0, -1)
    permutation := (L0, L1, L2)
    signs := (1, 1, -1) }

/-- Fast sanity check: the expanded relay table has 14 displayed rows. -/
theorem stageRows_length : stageRows.length = 14 := by
  decide

/-- Fast sanity check: the five coarse relay stages are present. -/
theorem stageSkeletons_length : stageSkeletons.length = 5 := by
  decide

/-- Apply the stage shift to an edge, renormalising to the ascending
orientation used by the skeleton tables. -/
def shiftEdge (s : Label) (e : Edge) : Edge :=
  let a := e.1 + s
  let b := e.2 + s
  if a ≤ b then (a, b) else (b, a)

/-- Transcription guard: the shifted columns of `stageSkeletons` are exactly
the base columns moved by the stage shift, so a copy error in either column is
caught by `decide` instead of surviving as silent data drift. -/
theorem stageSkeletons_shift_consistent :
    ∀ sk ∈ stageSkeletons,
      sk.shiftedTriple =
        (sk.triple.1 + sk.shift, sk.triple.2.1 + sk.shift,
          sk.triple.2.2 + sk.shift) ∧
      sk.shiftedPair₁ = shiftEdge sk.shift sk.pair₁ ∧
      sk.shiftedPair₂ = shiftEdge sk.shift sk.pair₂ := by
  decide

/-- Fast sanity check: one closure datum per color. -/
theorem colorClosureData_length : colorClosureData.length = 7 := by
  decide

/-! ## Bridge to the JSON / Python finite audit -/

/-- Forget the `Fin 7` endpoints to the natural-number edge format used by the
JSON/Python audit. -/
def edgeToAudit (e : Edge) : FiniteAudit.AuditEdge :=
  FiniteAudit.edge e.1.val e.2.val

/-- The relay support row, in the exact audit schema of
`FiniteAudit.d7SupportRows`. -/
def relayRowToSupportDatum (row : RelayRow) : FiniteAudit.SupportRowDatum :=
  FiniteAudit.supportDatum row.stage
    (row.support.map edgeToAudit)
    (row.active.map edgeToAudit)

/-- Closing-edge orientation as stored in the determinant audit.  Most closing
edges use the displayed orientation.  Colors `0` and `1` are reversed in the
finite-audit table because the sign is attached to that oriented closing
column. -/
def closingEdgeToAudit (datum : ColorClosureDatum) : FiniteAudit.AuditEdge :=
  match datum.color.val with
  | 0 => FiniteAudit.edge 6 0
  | 1 => FiniteAudit.edge 5 1
  | _ => edgeToAudit datum.closing

/-- The spanning-tree witnesses attached to the seven D7 closing rows in the
finite audit JSON. -/
def closureWitness : Nat → FiniteAudit.TreeWitness
  | 0 => FiniteAudit.treeWitness 0 [(1, 0), (3, 1), (2, 1), (4, 3), (5, 0)]
  | 1 => FiniteAudit.treeWitness 1 [(2, 1), (4, 2), (6, 4), (3, 4), (0, 3)]
  | 2 => FiniteAudit.treeWitness 0 [(2, 0), (1, 0), (3, 1), (5, 1), (4, 2)]
  | 3 => FiniteAudit.treeWitness 3 [(4, 3), (5, 4), (6, 5), (0, 6), (1, 5)]
  | 4 => FiniteAudit.treeWitness 3 [(4, 3), (2, 3), (5, 2), (6, 5), (0, 6)]
  | 5 => FiniteAudit.treeWitness 5 [(6, 5), (0, 6), (3, 0), (2, 3), (1, 2)]
  | 6 => FiniteAudit.treeWitness 5 [(6, 5), (0, 6), (4, 6), (1, 4), (2, 5)]
  | _ => FiniteAudit.treeWitness 0 []

/-- The relay closing row, in the exact audit schema of
`FiniteAudit.d7ForestClosingData`. -/
def closureDatumToForestClosingDatum
    (datum : ColorClosureDatum) : FiniteAudit.ForestClosingDatum :=
  FiniteAudit.forestDatum datum.color.val
    (datum.coforest.map edgeToAudit)
    datum.isolated.val
    (closingEdgeToAudit datum)
    datum.sign
    (closureWitness datum.color.val)

/-- The Lean relay rows are definitionally the D7 support rows from the finite
JSON audit. -/
theorem stageRows_match_finiteAudit_d7SupportRows :
    stageRows.map relayRowToSupportDatum = FiniteAudit.d7SupportRows := by
  decide

/-- The Lean closure rows are definitionally the D7 forest-closing rows from the
finite JSON audit, including the primitive determinant witnesses. -/
theorem colorClosureData_match_finiteAudit_d7ForestClosingData :
    colorClosureData.map closureDatumToForestClosingDatum =
      FiniteAudit.d7ForestClosingData := by
  decide

def stageRowsActiveLengthBool : Bool :=
  stageRows.all (fun row => decide (row.active.length ≤ row.support.length))

theorem stageRowsActiveLengthBool_true :
    stageRowsActiveLengthBool = true := by
  decide

theorem stageRows_active_length_le_support_length
    (row : RelayRow) (hmem : row ∈ stageRows) :
    row.active.length ≤ row.support.length := by
  have h := stageRowsActiveLengthBool_true
  unfold stageRowsActiveLengthBool at h
  have hrow := List.all_eq_true.mp h row hmem
  exact of_decide_eq_true hrow

def colorClosureDataCoforestLengthBool : Bool :=
  colorClosureData.all (fun datum => decide (datum.coforest.length = 5))

theorem colorClosureDataCoforestLengthBool_true :
    colorClosureDataCoforestLengthBool = true := by
  decide

theorem colorClosureData_coforest_length
    (datum : ColorClosureDatum) (hmem : datum ∈ colorClosureData) :
    datum.coforest.length = 5 := by
  have h := colorClosureDataCoforestLengthBool_true
  unfold colorClosureDataCoforestLengthBool at h
  have hdatum := List.all_eq_true.mp h datum hmem
  exact of_decide_eq_true hdatum

def colorClosureDataPrimitiveSignBool : Bool :=
  colorClosureData.all (fun datum => decide (datum.sign = 1 ∨ datum.sign = -1))

theorem colorClosureDataPrimitiveSignBool_true :
    colorClosureDataPrimitiveSignBool = true := by
  decide

theorem colorClosureData_primitive_sign
    (datum : ColorClosureDatum) (hmem : datum ∈ colorClosureData) :
    datum.sign = 1 ∨ datum.sign = -1 := by
  have h := colorClosureDataPrimitiveSignBool_true
  unfold colorClosureDataPrimitiveSignBool at h
  have hdatum := List.all_eq_true.mp h datum hmem
  exact of_decide_eq_true hdatum

/-- Finite arithmetic audit needed by the two D7 relays.  These are the exact
paper-table facts checked by the companion Python script: the displayed rows,
coforest closures, primitive closing columns, support containment, reserve
separation, and the terminal alignment used by the low-base glue.  Unlike the
previous placeholder version, every non-RF field below is an actual proposition
proved from the imported JSON/audit data. -/
structure RelayFiniteAuditEvidence where
  rows_length : stageRows.length = 14
  skeletons_length : stageSkeletons.length = 5
  closures_length : colorClosureData.length = 7
  terminal_triple : terminalAlignment.terminalTriple = (L0, L2, L3)
  active_edges_supported : ∀ row ∈ stageRows, row.active.length ≤ row.support.length
  coforest_supports_rooted : ∀ datum ∈ colorClosureData, datum.coforest.length = 5
  closing_columns_primitive : ∀ datum ∈ colorClosureData, datum.sign = 1 ∨ datum.sign = -1
  stageRows_match_supportJson :
    stageRows.map relayRowToSupportDatum = FiniteAudit.d7SupportRows
  colorClosures_match_forestJson :
    colorClosureData.map closureDatumToForestClosingDatum =
      FiniteAudit.d7ForestClosingData
  d7ForestClosingAudit : FiniteAudit.d7ForestClosingAuditBool = true
  d7SupportAudit : FiniteAudit.d7SupportAuditBool = true
  d7ReservePlaneAudit : FiniteAudit.d7ReservePlaneAuditBool = true
  d7HighEvenAnchorAudit : FiniteAuditBridge.d7HighEvenAnchorAuditBool = true
  forestClosingPayload :
    ∀ datum ∈ FiniteAudit.d7ForestClosingData,
      FiniteAudit.ClosingMatrixPayload 7 datum
  supportRows_active_supported_inBounds :
    ∀ row ∈ FiniteAudit.d7SupportRows,
      ∀ e ∈ row.active,
        ∃ f ∈ row.support,
          FiniteAudit.EdgeUndirectedEquivalent e f ∧ f.tail < 7 ∧ f.head < 7
  folded_word_m4_matches_terminal_block :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4))
  folded_word_m6_matches_terminal_block :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6))

/-- Closed D7 finite-audit package obtained from the JSON values already ported
into `FiniteAudit.lean`.  This does not prove RF1/RF2/RF3 for the D7 relay, but
it closes the table/JSON side of H3/H4 without a placeholder proposition. -/
def relayFiniteAuditEvidence : RelayFiniteAuditEvidence where
  rows_length := stageRows_length
  skeletons_length := stageSkeletons_length
  closures_length := colorClosureData_length
  terminal_triple := by decide
  active_edges_supported := stageRows_active_length_le_support_length
  coforest_supports_rooted := colorClosureData_coforest_length
  closing_columns_primitive := colorClosureData_primitive_sign
  stageRows_match_supportJson := stageRows_match_finiteAudit_d7SupportRows
  colorClosures_match_forestJson := colorClosureData_match_finiteAudit_d7ForestClosingData
  d7ForestClosingAudit := FiniteAudit.d7ForestClosingAudit
  d7SupportAudit := FiniteAudit.d7SupportAudit
  d7ReservePlaneAudit := FiniteAudit.d7ReservePlaneAudit
  d7HighEvenAnchorAudit := FiniteAuditBridge.d7HighEvenAnchorAudit
  forestClosingPayload := fun _datum hmem =>
    FiniteAudit.d7ForestClosingData_closingMatrixPayload hmem
  supportRows_active_supported_inBounds := fun _row hmem =>
    FiniteAudit.d7SupportRows_active_supported_inBounds hmem
  folded_word_m4_matches_terminal_block := FiniteAudit.foldedTerminalWordAudit.1
  folded_word_m6_matches_terminal_block := FiniteAudit.foldedTerminalWordAudit.2

/-- The actual paper proof should construct this object for `m = 4` and `m = 6`.
All fields below are mathematical RF1/RF2/RF3 obligations.  The JSON/audit
provenance is carried separately by `RelayFiniteAuditEvidence`. -/
structure TwoRailRelayRealization (m : Nat) [NeZero m] where
  dir : ZMod m → RootState 6 m → Color → Dir
  /-- RF1: each visible row is a Latin row.  Expected proof: every row is a
  product of disjoint edge swaps composed with a fixed 7-row permutation. -/
  rowLatin : (RootFlatCycle.schedule dir).rowLatin
  /-- RF2: every layer/color map is bijective.  Expected proof: each relay stage
  is a triangular/shear map in the six root coordinates, with unit determinant. -/
  layerBijective : (RootFlatCycle.schedule dir).layerBijective
  /-- RF3: first return is one Hamiltonian cycle on the root section.  Expected
  proof: splice the two rails using `stageRows`, then close with
  `colorClosureData`. -/
  returnsSingleCycle : (RootFlatCycle.schedule dir).returnsSingleCycle

/-- Convert a paper D7 two-rail realization into the generic low-base handoff. -/
def cycleData_of_realization {m : Nat} [NeZero m]
    (R : TwoRailRelayRealization m) :
    RootFlatCycle.RootFlatCycleData 6 m where
  dir := R.dir
  rowLatin := R.rowLatin
  layerBijective := R.layerBijective
  returnsSingleCycle := R.returnsSingleCycle


/-- Constructive low-base package for the two D7 relays.  The two fields are
ordinary RF1/RF2/RF3 realizations over the standard root-flat lift, one at
`m = 4` and one at `m = 6`. -/
structure TwoRailRelaySolutions where
  finiteAudit : RelayFiniteAuditEvidence
  d7m4 : TwoRailRelayRealization 4
  d7m6 : TwoRailRelayRealization 6

/-- H3 cycle-data handoff produced from a supplied two-rail realization. -/
theorem d7m4CycleData_of_realization
    (R : TwoRailRelayRealization 4) :
    Nonempty (RootFlatCycle.RootFlatCycleData 6 4) :=
  ⟨cycleData_of_realization R⟩

/-- H4 cycle-data handoff produced from a supplied two-rail realization. -/
theorem d7m6CycleData_of_realization
    (R : TwoRailRelayRealization 6) :
    Nonempty (RootFlatCycle.RootFlatCycleData 6 6) :=
  ⟨cycleData_of_realization R⟩

/-- H3 cycle-data handoff produced from the supplied D7 package. -/
theorem d7m4CycleData_of_solutions
    (solutions : TwoRailRelaySolutions) :
    Nonempty (RootFlatCycle.RootFlatCycleData 6 4) :=
  d7m4CycleData_of_realization solutions.d7m4

/-- H4 cycle-data handoff produced from the supplied D7 package. -/
theorem d7m6CycleData_of_solutions
    (solutions : TwoRailRelaySolutions) :
    Nonempty (RootFlatCycle.RootFlatCycleData 6 6) :=
  d7m6CycleData_of_realization solutions.d7m6

/-- D7(4) replacement target for H3. -/
theorem finalLowD7M4RootFlatCertificateFamily_of_twoRail
    (R : TwoRailRelayRealization 4) :
    FinalLowD7M4RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M4RootFlatCertificateFamily_of_cycleData
    (cycleData_of_realization R)

/-- D7(6) replacement target for H4. -/
theorem finalLowD7M6RootFlatCertificateFamily_of_twoRail
    (R : TwoRailRelayRealization 6) :
    FinalLowD7M6RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M6RootFlatCertificateFamily_of_cycleData
    (cycleData_of_realization R)

/-- Final paper-faithful constructor for a D7 relay.  The finite JSON side is
closed by `relayFiniteAuditEvidence`; the only remaining local input here is the
actual RF1/RF2/RF3 proof of the displayed direction table. -/
def realization_of_relayProofs {m : Nat} [NeZero m]
    (dir : ZMod m → RootState 6 m → Color → Dir)
    (hRow : (RootFlatCycle.schedule dir).rowLatin)
    (hLayer : (RootFlatCycle.schedule dir).layerBijective)
    (hReturn : (RootFlatCycle.schedule dir).returnsSingleCycle) :
    TwoRailRelayRealization m where
  dir := dir
  rowLatin := hRow
  layerBijective := hLayer
  returnsSingleCycle := hReturn

end D7TwoRailRelay
end V28Hard
end EvenV11
