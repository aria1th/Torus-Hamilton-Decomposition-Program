import EvenV11.D3EvenM4
import EvenV11.FiniteArrayCert
import EvenV11.RootFlatCycleData

set_option linter.style.nativeDecide false

/-!
# Direct `D₃(4)` root-flat cycle data

This is a small finite root-flat witness for `D₃(4)`, obtained by reading the
closed full-torus `D3EvenM4.colorDir` table in the standard root-flat chart.  It
is deliberately separate from the paper terminal `A₂` realization interface:
the first returns here prove direct existence of root-flat cycle data at
`m = 4`; they are not asserted to be the manuscript terminal carriers `F_i`.
-/

namespace EvenV11
namespace V28Hard
namespace D3M4DirectRootFlat

open Shared

abbrev Color := TorusColor 3
abbrev Direction := TorusDirection 3
abbrev RootState := StandardRootFlatLift.RootState 2 4

def zmodToFin (m : Nat) [NeZero m] (t : ZMod m) : Fin m :=
  ⟨t.val, ZMod.val_lt t⟩

theorem zmodToFin_val_cast (m : Nat) [NeZero m] (t : ZMod m) :
    ((zmodToFin m t).val : ZMod m) = t := by
  exact ZMod.natCast_zmod_val t

def rootIndex (w : RootState) : Fin 16 :=
  ⟨4 * (w 0).val + (w 1).val, by
    have h0 := (w 0).val_lt
    have h1 := (w 1).val_lt
    omega⟩

def rootOfIndex (i : Fin 16) : RootState :=
  fun j =>
    if j = (0 : Fin 2) then
      (((i.val / 4) % 4 : Nat) : ZMod 4)
    else
      ((i.val % 4 : Nat) : ZMod 4)

def rootIndexEquiv : RootState ≃ Fin 16 where
  toFun := rootIndex
  invFun := rootOfIndex
  left_inv := by
    intro w
    funext j
    native_decide +revert
  right_inv := by
    intro i
    apply Fin.ext
    native_decide +revert

def dirIndex (t : Fin 4) (w : RootState) (c : Color) : Nat :=
  (t.val * 16 + (rootIndex w).val) * 3 + c.val

/-- Direction table indexed by `(layer, rootIndex, color)`. -/
def dirTable : Array Nat :=
#[
  2, 1, 0, 2, 1, 0, 2, 0, 1, 2, 0, 1,
  2, 1, 0, 2, 0, 1, 2, 0, 1, 2, 1, 0,
  2, 0, 1, 2, 0, 1, 2, 1, 0, 2, 1, 0,
  2, 0, 1, 2, 1, 0, 2, 1, 0, 2, 0, 1,
  0, 1, 2, 2, 0, 1, 2, 1, 0, 2, 1, 0,
  1, 2, 0, 0, 1, 2, 2, 1, 0, 2, 0, 1,
  0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0, 2,
  0, 1, 2, 2, 1, 0, 2, 0, 1, 2, 1, 0,
  1, 2, 0, 0, 2, 1, 1, 2, 0, 1, 0, 2,
  2, 1, 0, 1, 0, 2, 1, 2, 0, 0, 1, 2,
  0, 2, 1, 2, 1, 0, 2, 1, 0, 1, 0, 2,
  1, 2, 0, 1, 2, 0, 0, 2, 1, 2, 0, 1,
  0, 2, 1, 1, 2, 0, 0, 1, 2, 2, 0, 1,
  1, 2, 0, 0, 2, 1, 0, 2, 1, 2, 0, 1,
  2, 1, 0, 0, 1, 2, 1, 0, 2, 0, 1, 2,
  0, 2, 1, 0, 2, 1, 2, 0, 1, 1, 2, 0
]

def dir (t : ZMod 4) (w : RootState) (c : Color) : Direction :=
  ⟨dirTable.getD (dirIndex (zmodToFin 4 t) w c) 0 % 3,
    Nat.mod_lt _ (by decide)⟩

def schedule :
    RootFlatSchedule Color Direction RootState 4 :=
  RootFlatCycle.schedule dir

theorem schedule_rowLatin : schedule.rowLatin := by
  intro t w
  native_decide +revert

theorem schedule_layerBijective : schedule.layerBijective := by
  intro t c
  native_decide +revert

def returnNext0 : Array Nat :=
  #[5, 9, 3, 4, 10, 13, 7, 15, 1, 11, 8, 0, 2, 14, 6, 12]

def returnRank0 : Array Nat :=
  #[0, 13, 8, 9, 10, 1, 4, 5, 12, 14, 11, 15, 7, 2, 3, 6]

def returnInvRank0 : Array Nat :=
  #[0, 5, 13, 14, 6, 7, 15, 12, 2, 3, 4, 10, 8, 1, 9, 11]

def returnCert0 : FiniteArrayCert.RankArrayCert 16 where
  next := returnNext0
  rank := returnRank0
  invRank := returnInvRank0

theorem returnCert0_ok : returnCert0.ok = true := by
  native_decide

def returnNext1 : Array Nat :=
  #[10, 11, 4, 15, 6, 14, 8, 5, 13, 2, 7, 9, 1, 3, 12, 0]

def returnRank1 : Array Nat :=
  #[0, 6, 9, 14, 10, 3, 11, 2, 12, 8, 1, 7, 5, 13, 4, 15]

def returnInvRank1 : Array Nat :=
  #[0, 10, 7, 5, 14, 12, 1, 11, 9, 2, 4, 6, 8, 13, 3, 15]

def returnCert1 : FiniteArrayCert.RankArrayCert 16 where
  next := returnNext1
  rank := returnRank1
  invRank := returnInvRank1

theorem returnCert1_ok : returnCert1.ok = true := by
  native_decide

def returnNext2 : Array Nat :=
  #[9, 6, 4, 8, 14, 15, 12, 11, 5, 3, 13, 0, 2, 7, 10, 1]

def returnRank2 : Array Nat :=
  #[0, 6, 9, 2, 10, 4, 7, 14, 3, 1, 12, 15, 8, 13, 11, 5]

def returnInvRank2 : Array Nat :=
  #[0, 9, 3, 8, 5, 15, 1, 6, 12, 2, 4, 14, 10, 13, 7, 11]

def returnCert2 : FiniteArrayCert.RankArrayCert 16 where
  next := returnNext2
  rank := returnRank2
  invRank := returnInvRank2

theorem returnCert2_ok : returnCert2.ok = true := by
  native_decide

def returnIndexMap (c : Color) : Fin 16 → Fin 16 :=
  fun i => rootIndexEquiv (schedule.returnMap c (rootIndexEquiv.symm i))

theorem returnIndexMap_eq_next0 :
    returnIndexMap (0 : Color) =
      returnCert0.nextFunOfOk returnCert0_ok := by
  funext i
  native_decide +revert

theorem returnIndexMap_eq_next1 :
    returnIndexMap (1 : Color) =
      returnCert1.nextFunOfOk returnCert1_ok := by
  funext i
  native_decide +revert

theorem returnIndexMap_eq_next2 :
    returnIndexMap (2 : Color) =
      returnCert2.nextFunOfOk returnCert2_ok := by
  funext i
  native_decide +revert

theorem schedule_returnsSingleCycle : schedule.returnsSingleCycle := by
  intro c
  fin_cases c
  · exact single_cycle_of_equiv_conj rootIndexEquiv.symm
      (schedule.returnMap (0 : Color))
      (returnCert0.nextFunOfOk returnCert0_ok)
      (FiniteArrayCert.RankArrayCert.singleCycle_of_ok
        returnCert0 returnCert0_ok)
      (by
        intro i
        change rootIndexEquiv
            (schedule.returnMap (0 : Color) (rootIndexEquiv.symm i)) =
          returnCert0.nextFunOfOk returnCert0_ok i
        simpa [returnIndexMap] using congrFun returnIndexMap_eq_next0 i)
  · exact single_cycle_of_equiv_conj rootIndexEquiv.symm
      (schedule.returnMap (1 : Color))
      (returnCert1.nextFunOfOk returnCert1_ok)
      (FiniteArrayCert.RankArrayCert.singleCycle_of_ok
        returnCert1 returnCert1_ok)
      (by
        intro i
        change rootIndexEquiv
            (schedule.returnMap (1 : Color) (rootIndexEquiv.symm i)) =
          returnCert1.nextFunOfOk returnCert1_ok i
        simpa [returnIndexMap] using congrFun returnIndexMap_eq_next1 i)
  · exact single_cycle_of_equiv_conj rootIndexEquiv.symm
      (schedule.returnMap (2 : Color))
      (returnCert2.nextFunOfOk returnCert2_ok)
      (FiniteArrayCert.RankArrayCert.singleCycle_of_ok
        returnCert2 returnCert2_ok)
      (by
        intro i
        change rootIndexEquiv
            (schedule.returnMap (2 : Color) (rootIndexEquiv.symm i)) =
          returnCert2.nextFunOfOk returnCert2_ok i
        simpa [returnIndexMap] using congrFun returnIndexMap_eq_next2 i)

/-- Closed direct root-flat cycle data for `D₃(4)`. -/
def cycleData : RootFlatCycle.RootFlatCycleData 2 4 where
  dir := dir
  rowLatin := schedule_rowLatin
  layerBijective := schedule_layerBijective
  returnsSingleCycle := schedule_returnsSingleCycle

theorem nonemptyCycleData :
    Nonempty (RootFlatCycle.RootFlatCycleData 2 4) :=
  ⟨cycleData⟩

end D3M4DirectRootFlat
end V28Hard
end EvenV11
