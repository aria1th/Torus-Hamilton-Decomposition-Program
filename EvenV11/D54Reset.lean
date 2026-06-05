import EvenV11.TerminalA2LowMod

namespace EvenV11
namespace D54Reset

def terminalResetOrbit4 : Fin 16 → TerminalQ 4 := fun i =>
  match i.val with
  | 0 => TerminalA2LowMod.q4 0 0
  | 1 => TerminalA2LowMod.q4 2 1
  | 2 => TerminalA2LowMod.q4 0 1
  | 3 => TerminalA2LowMod.q4 1 0
  | 4 => TerminalA2LowMod.q4 3 0
  | 5 => TerminalA2LowMod.q4 0 3
  | 6 => TerminalA2LowMod.q4 2 3
  | 7 => TerminalA2LowMod.q4 1 2
  | 8 => TerminalA2LowMod.q4 2 0
  | 9 => TerminalA2LowMod.q4 3 2
  | 10 => TerminalA2LowMod.q4 1 3
  | 11 => TerminalA2LowMod.q4 3 3
  | 12 => TerminalA2LowMod.q4 2 2
  | 13 => TerminalA2LowMod.q4 0 2
  | 14 => TerminalA2LowMod.q4 3 1
  | _ => TerminalA2LowMod.q4 1 1

theorem terminalResetOrbit4_bijective :
    Function.Bijective terminalResetOrbit4 := by
  decide

noncomputable def terminalResetOrbit4Equiv :
    Fin 16 ≃ TerminalQ 4 :=
  Equiv.ofBijective terminalResetOrbit4 terminalResetOrbit4_bijective

theorem terminalResetTrace4_stepOrbit_raw :
    ∀ i : Fin 16,
      terminalResetOrbit4 (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4 i) := by
  decide

theorem terminalResetTrace4_stepOrbit :
    ∀ i : Fin 16,
      terminalResetOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4Equiv i) := by
  simpa [terminalResetOrbit4Equiv] using
    terminalResetTrace4_stepOrbit_raw

noncomputable def terminalResetTrace4Certificate :
    IndexedWordOrbitCertificate TerminalSymbol (TerminalQ 4) 16 where
  symbolStep := terminalSymbolStep 4
  word := terminalResetTrace4
  orbit := terminalResetOrbit4Equiv
  stepOrbit := terminalResetTrace4_stepOrbit

theorem terminalResetTrace4_singleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) := by
  simpa [terminalResetTrace4Certificate] using
    indexedWordOrbitCertificate_singleCycle terminalResetTrace4Certificate

end D54Reset

export D54Reset
  (terminalResetOrbit4 terminalResetOrbit4_bijective
   terminalResetOrbit4Equiv terminalResetTrace4_stepOrbit
   terminalResetTrace4Certificate terminalResetTrace4_singleCycle)

end EvenV11
