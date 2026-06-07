import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.LowD5M4RibbonInterface
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions

/-!
# v28 hard-slot experimental code

This umbrella deliberately is **not** imported by `EvenV11.lean`.  The files
below are aggressive paper-faithful implementations/blueprints for the remaining
hard obligations.  They are written to be copied into the proof spine slot by
slot after local Lean repair.

The old generated/blob-backed and legacy H2 table modules are kept as source
checkpoints under `EvenV11/V28Hard/`, but they are not imported here while their
dependencies live under `archive/EvenV11/`.  The live H2 interface is
`EvenV11.LowD5M4RibbonInterface`.
-/
