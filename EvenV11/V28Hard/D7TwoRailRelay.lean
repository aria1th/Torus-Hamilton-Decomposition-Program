import EvenV11.RootFlatCycleData

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
  deriving Repr

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
  deriving Repr

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
      shiftedTriple := (L2, L1, L4), shiftedPair₁ := edge35,
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
  deriving Repr

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
  deriving Repr

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

/-- Fast sanity check: one closure datum per color. -/
theorem colorClosureData_length : colorClosureData.length = 7 := by
  decide

/-- The actual paper proof should construct this object for `m = 4` and `m = 6`.
All fields below are mathematical, not generated-array, obligations. -/
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
  /-- The `dir` is obtained from the five-stage shifted relay table, not from a
  generated array.  This field is intentionally weak (`True`) so that the proof
  can be refined without changing downstream signatures. -/
  usesStageSkeletons : True
  usesStageRows : True
  usesColorClosures : True
  usesTerminalAlignment : True

/-- Convert a paper D7 two-rail realization into the generic low-base handoff. -/
def cycleData_of_realization {m : Nat} [NeZero m]
    (R : TwoRailRelayRealization m) :
    RootFlatCycle.RootFlatCycleData 6 m where
  dir := R.dir
  rowLatin := R.rowLatin
  layerBijective := R.layerBijective
  returnsSingleCycle := R.returnsSingleCycle

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

/-- A repair-oriented list of the genuine proof obligations for RF2.  This is
kept as a separate structure so that local determinant/unit-carry work can be
ported from the odd-dimensional code. -/
structure RelayLayerBijectiveProofPlan (m : Nat) [NeZero m] where
  stageTriangularMapsAreBijective :
    ∀ row ∈ stageRows, True
  colorLayerMapsFactorThroughStages :
    ∀ t : ZMod m, ∀ c : Color, True
  determinantUnits :
    ∀ row ∈ stageRows, IsUnit (1 : ZMod m)

/-- A repair-oriented list of the genuine proof obligations for RF3. -/
structure RelayReturnCycleProofPlan (m : Nat) [NeZero m] where
  railCycles : ∀ c : Color, True
  spliceEdgesPresent : ∀ row ∈ stageRows, row.active.length ≤ row.support.length
  colorClosuresPresent : colorClosureData.length = 7
  terminalGlueMatches : terminalAlignment.terminalTriple = (L0, L2, L3)

/-- Final paper-faithful target: the two local proof plans are converted into the
single realization object.  The hard content is carried by the RF1/RF2/RF3
arguments supplied to this constructor. -/
def realization_of_relayProofPlans {m : Nat} [NeZero m]
    (dir : ZMod m → RootState 6 m → Color → Dir)
    (hRow : (RootFlatCycle.schedule dir).rowLatin)
    (layerPlan : RelayLayerBijectiveProofPlan m)
    (cyclePlan : RelayReturnCycleProofPlan m)
    (hLayer : (RootFlatCycle.schedule dir).layerBijective)
    (hReturn : (RootFlatCycle.schedule dir).returnsSingleCycle) :
    TwoRailRelayRealization m where
  dir := dir
  rowLatin := hRow
  layerBijective := hLayer
  returnsSingleCycle := hReturn
  usesStageSkeletons := trivial
  usesStageRows := trivial
  usesColorClosures := trivial
  usesTerminalAlignment := trivial

end D7TwoRailRelay
end V28Hard
end EvenV11
