import EvenV11.PhaseSupport
import EvenV11.WordSkew

namespace EvenV11
namespace PhaseWordSupport

theorem phaseReserveProtectedSupportedWordEvalsCommute
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseLine (h := h) (M := M) (2 : ZMod h)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (PhaseProtectedStrips h M) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedWordEvalsCommute (@phaseProjection h M)
    leftStep rightStep hleft hright
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)
    leftWord rightWord

theorem phaseReserveProtectedSupportedWordEvalsCommute_symmSupports
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (PhaseProtectedStrips h M) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseLine (h := h) (M := M) (2 : ZMod h)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedWordEvalsCommute_symmSupports
    (@phaseProjection h M) leftStep rightStep hleft hright
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)
    leftWord rightWord

theorem phaseReserveProtectedSupportedWordEvalIteratesCommute
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseLine (h := h) (M := M) (2 : ZMod h)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (PhaseProtectedStrips h M) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedWordEvalIteratesCommute (@phaseProjection h M)
    leftStep rightStep hleft hright
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)
    leftWord rightWord n k

theorem phaseReserveProtectedSupportedWordEvalIteratesCommute_symmSupports
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (PhaseProtectedStrips h M) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseLine (h := h) (M := M) (2 : ZMod h)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedWordEvalIteratesCommute_symmSupports
    (@phaseProjection h M) leftStep rightStep hleft hright
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)
    leftWord rightWord n k

theorem phaseReserveLineSlot_fixedByProtectedSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (i : Fin (2 * a + 3)) :
    wordEval step word (phaseReserveLineSlot h a m ha hm i).1 =
      (phaseReserveLineSlot h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i)

theorem phaseReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) (i : Fin (2 * a + 3)) :
    ((wordEval step word)^[n]) (phaseReserveLineSlot h a m ha hm i).1 =
      (phaseReserveLineSlot h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i)

theorem phaseReserveLineSlotList_fixedByProtectedSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    wordEval step word x.1 = x.1 :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseReserveLineSlotList_not_mem_protectedStrips h a m hh ha hm hx)

theorem phaseReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    ((wordEval step word)^[n]) x.1 = x.1 :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseReserveLineSlotList_not_mem_protectedStrips h a m hh ha hm hx)

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    wordEval step word x = x :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseReserveLineSlotPointList_not_mem_protectedStrips
      h a m hh ha hm hx)

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseReserveLineSlotPointList_not_mem_protectedStrips
      h a m hh ha hm hx)

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointSet h a m ha hm) :
    wordEval step word x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointSet h a m ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) :
    MapsInto (phaseReserveLineSlotPointSet h a m ha hm)
      (wordEval step word) := by
  intro x hx
  rw [phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word hx]
  exact hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (phaseReserveLineSlotPointSet h a m ha hm)
      ((wordEval step word)^[n]) := by
  intro x hx
  rw [phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx]
  exact hx

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedSupportedWordEvalsCommute hh leftStep rightStep
    (fun i => supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) (hleft i))
    hright leftWord rightWord

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute_symmSupports
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedSupportedWordEvalsCommute_symmSupports
    hh leftStep rightStep hleft
    (fun j => supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) (hright j))
    leftWord rightWord

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedSupportedWordEvalIteratesCommute hh leftStep rightStep
    (fun i => supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) (hleft i))
    hright leftWord rightWord n k

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute_symmSupports
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedSupportedWordEvalIteratesCommute_symmSupports
    hh leftStep rightStep hleft
    (fun j => supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) (hright j))
    leftWord rightWord n k

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    wordEval step word x = x :=
  supportedOn_wordEval_apply_of_mem_disjoint step hstep
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) word hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEval
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (step j))
    (word : List ι) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) (wordEval step word) :=
  mapsInto_wordEval_of_supportedOn_disjoint step hstep
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) word

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_wordEval_iterate_apply_of_mem_disjoint step hstep
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) word n hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseReserveLineSlotPointSet h a m ha hm) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (PhaseProtectedStrips h (m ^ a))
      ((wordEval step word)^[n]) :=
  mapsInto_wordEval_iterate_of_supportedOn_disjoint step hstep
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) word n

end PhaseWordSupport

export PhaseWordSupport
  (phaseReserveProtectedSupportedWordEvalsCommute
   phaseReserveProtectedSupportedWordEvalsCommute_symmSupports
   phaseReserveProtectedSupportedWordEvalIteratesCommute
   phaseReserveProtectedSupportedWordEvalIteratesCommute_symmSupports
   phaseReserveLineSlot_fixedByProtectedSupportedWordEval
   phaseReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
   phaseReserveLineSlotList_fixedByProtectedSupportedWordEval
   phaseReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
   phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEval
   phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
   phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
   phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
   phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
   phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
   phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute
   phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute_symmSupports
   phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute
   phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute_symmSupports
   phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEval
   phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEval
   phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
   phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate)

end EvenV11
