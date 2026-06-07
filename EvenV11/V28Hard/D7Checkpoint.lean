import EvenV11.V28PaperInterface
import EvenV11.V28Hard.D7FiniteToCycleData

/-!
# D7 finite-backed checkpoint, explicitly quarantined

This module is intentionally **not** the paper-faithful D7 route.  It records the
practical checkpoint where the generated finite audits for `D₇(4)` and `D₇(6)`
are transported into the structural `RootFlatCycleData` interface.  The only
purpose is to test the rest of the theorem spine while the handwritten two-rail
RF1/RF2/RF3 proof is being developed.

The default/paper spine should import handwritten D7 data instead of this file.
-/

namespace EvenV11
namespace V28Hard
namespace D7Checkpoint

open V28PaperInterface

/-- Checkpoint D7(4) target: structural interface, finite-backed source. -/
abbrev D7M4CheckpointCycleData := RootFlatCycle.RootFlatCycleData 6 4

/-- Checkpoint D7(6) target: structural interface, finite-backed source. -/
abbrev D7M6CheckpointCycleData := RootFlatCycle.RootFlatCycleData 6 6

/-- Explicit tag to make finite-backed D7 uses searchable in theorem names and
source review.  The fields are structural `RootFlatCycleData`, but their source
is the generated finite audit. -/
structure FiniteBackedD7Checkpoint where
  d7m4 : Nonempty D7M4CheckpointCycleData
  d7m6 : Nonempty D7M6CheckpointCycleData
  checkpointOnly : True

/-- The generated finite audits, quarantined behind a checkpoint name. -/
def generatedFiniteBackedCheckpoint : FiniteBackedD7Checkpoint where
  d7m4 := D7FiniteToCycleData.M4.nonempty_cycleData
  d7m6 := D7FiniteToCycleData.M6.nonempty_cycleData
  checkpointOnly := trivial

/-- D7(4) checklist input obtained from a quarantined checkpoint. -/
def d7m4Input_of_checkpoint
    (ck : FiniteBackedD7Checkpoint) : D7M4TwoRailInput where
  data := ck.d7m4

/-- D7(6) checklist input obtained from a quarantined checkpoint. -/
def d7m6Input_of_checkpoint
    (ck : FiniteBackedD7Checkpoint) : D7M6TwoRailInput where
  data := ck.d7m6

/-- The generated finite-backed D7(4) input.  Any theorem using this should have
`checkpoint` or `finiteBackedD7` in its name. -/
def generatedD7M4CheckpointInput : D7M4TwoRailInput :=
  d7m4Input_of_checkpoint generatedFiniteBackedCheckpoint

/-- The generated finite-backed D7(6) input.  Any theorem using this should have
`checkpoint` or `finiteBackedD7` in its name. -/
def generatedD7M6CheckpointInput : D7M6TwoRailInput :=
  d7m6Input_of_checkpoint generatedFiniteBackedCheckpoint

/-- Convenience pair for checkpoint theorem assembly. -/
def generatedD7CheckpointInputs : D7M4TwoRailInput × D7M6TwoRailInput :=
  (generatedD7M4CheckpointInput, generatedD7M6CheckpointInput)

end D7Checkpoint
end V28Hard
end EvenV11
