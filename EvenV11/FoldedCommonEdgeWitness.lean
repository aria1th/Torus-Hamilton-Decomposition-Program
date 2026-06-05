import EvenV11.FoldedReserveSeparation

namespace EvenV11
namespace FoldedCommonEdgeWitness

structure CommonEdgeColors where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

structure SingletonCommonEdgeWitness (m : Nat) where
  colors : CommonEdgeColors
  selector : CodedCoord m
  commonImage : CodedCoord m
  protectedSet : List (CodedCoord m)
  protectedSize : Nat
  terminalTrace : List TerminalSymbol
  deriving DecidableEq, Repr

def singletonCommonEdgeWitness4 : SingletonCommonEdgeWitness 4 where
  colors := { first := 0, second := 1 }
  selector := { coord := foldedCoord 0 1 0 1 0 0, code := 68 }
  commonImage := { coord := foldedCoord 0 2 0 1 1 1, code := 1352 }
  protectedSet := protected4
  protectedSize := 4
  terminalTrace := terminalTrace4

def singletonCommonEdgeWitness6 : SingletonCommonEdgeWitness 6 where
  colors := { first := 2, second := 5 }
  selector := { coord := foldedCoord 0 5 2 1 2 0, code := 2910 }
  commonImage := { coord := foldedCoord 0 0 3 2 2 1, code := 10908 }
  protectedSet := protected6
  protectedSize := 4
  terminalTrace := terminalTrace6

theorem singletonCommonEdgeWitness4_colors :
    singletonCommonEdgeWitness4.colors = { first := 0, second := 1 } :=
  rfl

theorem singletonCommonEdgeWitness6_colors :
    singletonCommonEdgeWitness6.colors = { first := 2, second := 5 } :=
  rfl

theorem singletonCommonEdgeWitness4_selectorCode :
    singletonCommonEdgeWitness4.selector.code = 68 :=
  rfl

theorem singletonCommonEdgeWitness6_selectorCode :
    singletonCommonEdgeWitness6.selector.code = 2910 :=
  rfl

theorem singletonCommonEdgeWitness4_commonImageCode :
    singletonCommonEdgeWitness4.commonImage.code = 1352 :=
  rfl

theorem singletonCommonEdgeWitness6_commonImageCode :
    singletonCommonEdgeWitness6.commonImage.code = 10908 :=
  rfl

theorem singletonCommonEdgeWitness4_selectorCodeMatches :
    codedCoordMatches singletonCommonEdgeWitness4.selector = true :=
  rfl

theorem singletonCommonEdgeWitness6_selectorCodeMatches :
    codedCoordMatches singletonCommonEdgeWitness6.selector = true :=
  rfl

theorem singletonCommonEdgeWitness4_commonImageCodeMatches :
    codedCoordMatches singletonCommonEdgeWitness4.commonImage = true :=
  rfl

theorem singletonCommonEdgeWitness6_commonImageCodeMatches :
    codedCoordMatches singletonCommonEdgeWitness6.commonImage = true :=
  rfl

theorem singletonCommonEdgeWitness4_protected :
    singletonCommonEdgeWitness4.protectedSet = protected4 :=
  rfl

theorem singletonCommonEdgeWitness6_protected :
    singletonCommonEdgeWitness6.protectedSet = protected6 :=
  rfl

theorem singletonCommonEdgeWitness4_protectedSize :
    singletonCommonEdgeWitness4.protectedSet.length = singletonCommonEdgeWitness4.protectedSize :=
  rfl

theorem singletonCommonEdgeWitness6_protectedSize :
    singletonCommonEdgeWitness6.protectedSet.length = singletonCommonEdgeWitness6.protectedSize :=
  rfl

theorem singletonCommonEdgeWitness4_protected_nodup :
    (codedCoords singletonCommonEdgeWitness4.protectedSet).Nodup := by
  rw [singletonCommonEdgeWitness4_protected]
  exact protected4_nodup

theorem singletonCommonEdgeWitness6_protected_nodup :
    (codedCoords singletonCommonEdgeWitness6.protectedSet).Nodup := by
  rw [singletonCommonEdgeWitness6_protected]
  exact protected6_nodup

theorem singletonCommonEdgeWitness4_selector_mem_protected :
    singletonCommonEdgeWitness4.selector ∈ singletonCommonEdgeWitness4.protectedSet := by
  decide

theorem singletonCommonEdgeWitness6_selector_mem_protected :
    singletonCommonEdgeWitness6.selector ∈ singletonCommonEdgeWitness6.protectedSet := by
  decide

theorem singletonCommonEdgeWitness4_commonImage_mem_protected :
    singletonCommonEdgeWitness4.commonImage ∈ singletonCommonEdgeWitness4.protectedSet := by
  decide

theorem singletonCommonEdgeWitness6_commonImage_mem_protected :
    singletonCommonEdgeWitness6.commonImage ∈ singletonCommonEdgeWitness6.protectedSet := by
  decide

theorem singletonCommonEdgeWitness4_selector_ne_commonImage :
    singletonCommonEdgeWitness4.selector ≠
      singletonCommonEdgeWitness4.commonImage := by
  decide

theorem singletonCommonEdgeWitness6_selector_ne_commonImage :
    singletonCommonEdgeWitness6.selector ≠
      singletonCommonEdgeWitness6.commonImage := by
  decide

theorem singletonCommonEdgeWitness4_terminalTrace :
    singletonCommonEdgeWitness4.terminalTrace = terminalTrace4 :=
  rfl

theorem singletonCommonEdgeWitness6_terminalTrace :
    singletonCommonEdgeWitness6.terminalTrace = terminalTrace6 :=
  rfl

theorem singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites :
    singletonCommonEdgeWitness4.terminalTrace =
      chronologicalTrace 4 foldedSites4 := by
  rw [singletonCommonEdgeWitness4_terminalTrace,
    foldedSites4_chronologicalTrace]

theorem singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites :
    singletonCommonEdgeWitness6.terminalTrace =
      chronologicalTrace 6 foldedSites6 := by
  rw [singletonCommonEdgeWitness6_terminalTrace,
    foldedSites6_chronologicalTrace]

theorem singletonCommonEdgeWitness4_terminalTrace_by_slots :
    singletonCommonEdgeWitness4.terminalTrace =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1] := by
  rw [singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites]
  exact foldedSites4_chronologicalTrace_by_slots

theorem singletonCommonEdgeWitness6_terminalTrace_by_slots :
    singletonCommonEdgeWitness6.terminalTrace =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
        TerminalSymbol.F1, TerminalSymbol.F1] := by
  rw [singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites]
  exact foldedSites6_chronologicalTrace_by_slots

theorem singletonCommonEdgeWitness4_traceSingleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) := by
  rw [singletonCommonEdgeWitness4_terminalTrace]
  exact terminalTrace4_singleCycle

theorem singletonCommonEdgeWitness6_traceSingleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) := by
  rw [singletonCommonEdgeWitness6_terminalTrace]
  exact terminalTrace6_singleCycle

theorem singletonCommonEdgeWitness4_traceSingleCycle_fromFoldedSites :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) := by
  rw [singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites]
  exact foldedSites4_singleCycle

theorem singletonCommonEdgeWitness6_traceSingleCycle_fromFoldedSites :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) := by
  rw [singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites]
  exact foldedSites6_singleCycle

theorem singletonCommonEdgeWitness4_traceSingleCycle_fromSlots :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) := by
  rw [singletonCommonEdgeWitness4_terminalTrace_by_slots]
  change Shared.IsSingleCycleMap
    (wordEval (terminalSymbolStep 4) terminalTrace4)
  exact terminalTrace4_singleCycle

theorem singletonCommonEdgeWitness6_traceSingleCycle_fromSlots :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) := by
  rw [singletonCommonEdgeWitness6_terminalTrace_by_slots]
  change Shared.IsSingleCycleMap
    (wordEval (terminalSymbolStep 6) terminalTrace6)
  exact terminalTrace6_singleCycle

theorem singletonCommonEdgeWitness4_protectedSeparatedFromSites :
    qzSeparatedFromSites (codedCoords singletonCommonEdgeWitness4.protectedSet) foldedSites4 := by
  rw [singletonCommonEdgeWitness4_protected]
  exact protected4_qzSeparatedFromSites

theorem singletonCommonEdgeWitness6_protectedSeparatedFromSites :
    qzSeparatedFromSites (codedCoords singletonCommonEdgeWitness6.protectedSet) foldedSites6 := by
  rw [singletonCommonEdgeWitness6_protected]
  exact protected6_qzSeparatedFromSites

end FoldedCommonEdgeWitness

export FoldedCommonEdgeWitness
  (CommonEdgeColors SingletonCommonEdgeWitness
   singletonCommonEdgeWitness4 singletonCommonEdgeWitness6
   singletonCommonEdgeWitness4_colors singletonCommonEdgeWitness6_colors
   singletonCommonEdgeWitness4_selectorCode singletonCommonEdgeWitness6_selectorCode
   singletonCommonEdgeWitness4_commonImageCode singletonCommonEdgeWitness6_commonImageCode
   singletonCommonEdgeWitness4_selectorCodeMatches singletonCommonEdgeWitness6_selectorCodeMatches
   singletonCommonEdgeWitness4_commonImageCodeMatches
   singletonCommonEdgeWitness6_commonImageCodeMatches
   singletonCommonEdgeWitness4_protected singletonCommonEdgeWitness6_protected
   singletonCommonEdgeWitness4_protectedSize singletonCommonEdgeWitness6_protectedSize
   singletonCommonEdgeWitness4_protected_nodup
   singletonCommonEdgeWitness6_protected_nodup
   singletonCommonEdgeWitness4_selector_mem_protected
   singletonCommonEdgeWitness6_selector_mem_protected
   singletonCommonEdgeWitness4_commonImage_mem_protected
   singletonCommonEdgeWitness6_commonImage_mem_protected
   singletonCommonEdgeWitness4_selector_ne_commonImage
   singletonCommonEdgeWitness6_selector_ne_commonImage
   singletonCommonEdgeWitness4_terminalTrace singletonCommonEdgeWitness6_terminalTrace
   singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites
   singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites
   singletonCommonEdgeWitness4_terminalTrace_by_slots
   singletonCommonEdgeWitness6_terminalTrace_by_slots
   singletonCommonEdgeWitness4_traceSingleCycle singletonCommonEdgeWitness6_traceSingleCycle
   singletonCommonEdgeWitness4_traceSingleCycle_fromFoldedSites
   singletonCommonEdgeWitness6_traceSingleCycle_fromFoldedSites
   singletonCommonEdgeWitness4_traceSingleCycle_fromSlots
   singletonCommonEdgeWitness6_traceSingleCycle_fromSlots
   singletonCommonEdgeWitness4_protectedSeparatedFromSites
   singletonCommonEdgeWitness6_protectedSeparatedFromSites)

end EvenV11
