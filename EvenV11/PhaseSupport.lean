import EvenV11.PhaseDoubling
import EvenV11.SupportSeparation

namespace EvenV11
namespace PhaseSupport

theorem phaseReserveProtectedSupportedMapsCommute
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseLine (h := h) (M := M) (2 : ZMod h)) f)
    (hg : SupportedOn (PhaseProtectedStrips h M) g) :
    Function.Commute f g :=
  projectionSeparatedSupportedMapsCommute (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)

theorem phaseReserveProtectedSupportedMapsCommute_symmSupports
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseProtectedStrips h M) f)
    (hg : SupportedOn (PhaseLine (h := h) (M := M) (2 : ZMod h)) g) :
    Function.Commute f g :=
  projectionSeparatedSupportedMapsCommute_symmSupports
    (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)

theorem phaseReserveProtectedSupportedIteratesCommute
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseLine (h := h) (M := M) (2 : ZMod h)) f)
    (hg : SupportedOn (PhaseProtectedStrips h M) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  projectionSeparatedSupportedIteratesCommute (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh) n k

theorem phaseReserveProtectedSupportedIteratesCommute_symmSupports
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseProtectedStrips h M) f)
    (hg : SupportedOn (PhaseLine (h := h) (M := M) (2 : ZMod h)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  projectionSeparatedSupportedIteratesCommute_symmSupports
    (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh) n k

theorem phaseReserveLineSlot_fixedByProtectedSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (i : Fin (2 * a + 3)) :
    f (phaseReserveLineSlot h a m ha hm i).1 =
      (phaseReserveLineSlot h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem hf
    (phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i)

theorem phaseReserveLineSlot_fixedByProtectedSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) (i : Fin (2 * a + 3)) :
    (f^[n]) (phaseReserveLineSlot h a m ha hm i).1 =
      (phaseReserveLineSlot h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i)

theorem phaseReserveLineSlotList_fixedByProtectedSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    f x.1 = x.1 :=
  supportedOn_apply_of_not_mem hf
    (phaseReserveLineSlotList_not_mem_protectedStrips h a m hh ha hm hx)

theorem phaseReserveLineSlotList_fixedByProtectedSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    (f^[n]) x.1 = x.1 :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseReserveLineSlotList_not_mem_protectedStrips h a m hh ha hm hx)

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    f x = x :=
  supportedOn_apply_of_not_mem hf
    (phaseReserveLineSlotPointList_not_mem_protectedStrips
      h a m hh ha hm hx)

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    (f^[n]) x = x :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseReserveLineSlotPointList_not_mem_protectedStrips
      h a m hh ha hm hx)

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointSet h a m ha hm) :
    f x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedMap
    h a m hh ha hm hf hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointSet h a m ha hm) :
    (f^[n]) x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f) :
    MapsInto (phaseReserveLineSlotPointSet h a m ha hm) f := by
  intro x hx
  rw [phaseReserveLineSlotPointSet_fixedByProtectedSupportedMap
    h a m hh ha hm hf hx]
  exact hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f) (n : Nat) :
    MapsInto (phaseReserveLineSlotPointSet h a m ha hm) (f^[n]) := by
  intro x hx
  rw [phaseReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n hx]
  exact hx

theorem phaseReserveLineSlotPointSetProtectedSupportedMapsCommute
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f)
    (hg : SupportedOn (PhaseProtectedStrips h (m ^ a)) g) :
    Function.Commute f g :=
  phaseReserveProtectedSupportedMapsCommute (M := m ^ a) hh
    (supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) hf)
    hg

theorem phaseReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (hg : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) g) :
    Function.Commute f g :=
  phaseReserveProtectedSupportedMapsCommute_symmSupports (M := m ^ a) hh
    hf
    (supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) hg)

theorem phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f)
    (hg : SupportedOn (PhaseProtectedStrips h (m ^ a)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedSupportedIteratesCommute (M := m ^ a) hh
    (supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) hf)
    hg n k

theorem phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (hg : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedSupportedIteratesCommute_symmSupports (M := m ^ a) hh
    hf
    (supportedOn_mono
      (phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm) hg)
    n k

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    f x = x :=
  supportedOn_apply_of_mem_disjoint hf
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedMap
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) f :=
  mapsInto_of_supportedOn_disjoint hf
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm)

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    (f^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint hf
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) n hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedIterate
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseReserveLineSlotPointSet h a m ha hm) f)
    (n : Nat) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) (f^[n]) :=
  mapsInto_iterate_of_supportedOn_disjoint hf
    (phaseReserveLineSlotPointSet_disjointFromProtectedStrips
      h a m hh ha hm) n

end PhaseSupport

export PhaseSupport
  (phaseReserveProtectedSupportedMapsCommute
   phaseReserveProtectedSupportedMapsCommute_symmSupports
   phaseReserveProtectedSupportedIteratesCommute
   phaseReserveProtectedSupportedIteratesCommute_symmSupports
   phaseReserveLineSlot_fixedByProtectedSupportedMap
   phaseReserveLineSlot_fixedByProtectedSupportedIterate
   phaseReserveLineSlotList_fixedByProtectedSupportedMap
   phaseReserveLineSlotList_fixedByProtectedSupportedIterate
   phaseReserveLineSlotPointList_fixedByProtectedSupportedMap
   phaseReserveLineSlotPointList_fixedByProtectedSupportedIterate
   phaseReserveLineSlotPointSet_fixedByProtectedSupportedMap
   phaseReserveLineSlotPointSet_fixedByProtectedSupportedIterate
   phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
   phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
   phaseReserveLineSlotPointSetProtectedSupportedMapsCommute
   phaseReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
   phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute
   phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
   phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedMap
   phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedMap
   phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedIterate
   phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedIterate)

end EvenV11
