import D7Odd.Handoff.CanonicalFamily
import D7Odd.Handoff.PrimeCanonicalData
import D7Odd.Handoff.PrimeRoot

namespace D7Odd
namespace Handoff
namespace PrimeRoot
namespace PrimeDimension

theorem prefixLabelToDirection_seven_eq_fixed (r : Fin 7) :
    seven.prefixLabelToDirection r =
      Handoff.prefixLabelToDirection r := by
  apply Fin.ext
  simp [prefixLabelToDirection, Handoff.prefixLabelToDirection, seven]

theorem prefixLabelStep_seven_eq_fixed {m : Nat}
    (r : Fin 7) (z : seven.Prefix m) :
    seven.prefixLabelStep r z =
      Handoff.prefixLabelStep r z := by
  rfl

theorem prefixLabelUnstep_seven_eq_fixed {m : Nat}
    (r : Fin 7) (z : seven.Prefix m) :
    seven.prefixLabelUnstep r z =
      Handoff.prefixLabelUnstep r z := by
  rfl

theorem canonicalPrefixLabelOfRho_seven_eq_fixed
    (rho : seven.Rho) (sym : Fin 7) :
    seven.canonicalPrefixLabelOfRho rho sym =
      Handoff.canonicalPrefixLabelOfRho rho sym := by
  simp [canonicalPrefixLabelOfRho, Handoff.canonicalPrefixLabelOfRho,
    zero, one, seven]

theorem canonicalDirOfRho_seven_eq_fixed
    (rho : seven.Rho) (sym : Fin 7) :
    seven.canonicalDirOfRho rho sym =
      Handoff.canonicalDirOfRho rho sym := by
  rw [canonicalDirOfRho, Handoff.canonicalDirOfRho,
    canonicalPrefixLabelOfRho_seven_eq_fixed,
    prefixLabelToDirection_seven_eq_fixed]

theorem rowSum_seven_eq_fixed (A : seven.CountMatrix) (i : Fin 7) :
    seven.rowSum A i = Handoff.rowSum A i := by
  rfl

theorem colSum_seven_eq_fixed (A : seven.CountMatrix) (j : Fin 7) :
    seven.colSum A j = Handoff.colSum A j := by
  rfl

theorem CountMatrixValid_seven_eq_fixed (m : Nat) (A : seven.CountMatrix) :
    seven.CountMatrixValid m A ↔ Handoff.CountMatrixValid m A := by
  rfl

theorem canonicalRowPrimitive_seven_eq_fixed
    (m : Nat) (row : Fin 7 → Nat) :
    seven.canonicalRowPrimitive m row ↔
      Handoff.canonicalRowPrimitive m row := by
  rfl

theorem CountMatrixPrimitive_seven_eq_fixed
    (m : Nat) (A : seven.CountMatrix) :
    seven.CountMatrixPrimitive m A ↔
      Handoff.CountMatrixPrimitive m A := by
  rfl

theorem CountMatrixCertified_seven_eq_fixed
    (m : Nat) (A : seven.CountMatrix) :
    seven.CountMatrixCertified m A ↔
      Handoff.CountMatrixCertified m A := by
  rfl

theorem scheduleCount_seven_eq_fixed
    (L : List Handoff.SymbolPerm7) (c sym : Fin 7) :
    seven.scheduleCount L c sym =
      Handoff.scheduleCount L c sym := by
  rfl

theorem scheduleListLatin_seven_eq_fixed
    (L : List Handoff.SymbolPerm7) :
    seven.scheduleListLatin L ↔
      Handoff.scheduleListLatin L := by
  rfl

theorem canonicalWord_seven_eq_fixed
    (L : List Handoff.SymbolPerm7) (c : Fin 7) :
    seven.canonicalWord L c =
      Handoff.canonicalWord L c := by
  rfl

theorem canonicalWordCount_seven_eq_fixed
    (W : List (Fin 7)) (sym : Fin 7) :
    seven.canonicalWordCount W sym =
      Handoff.canonicalWordCount W sym := by
  rfl

theorem CanonicalWordCertified_seven_eq_fixed
    (m : Nat) (W : List (Fin 7)) :
    seven.CanonicalWordCertified m W ↔
      Handoff.CanonicalWordCertified m W := by
  rfl

def countMatrixScheduleSevenOfFixed {m : Nat}
    (P : Handoff.CountMatrixSchedule m) :
    seven.CountMatrixSchedule m where
  matrix := P.matrix
  schedule := P.schedule
  certified := (CountMatrixCertified_seven_eq_fixed m P.matrix).2 P.certified
  latin := (scheduleListLatin_seven_eq_fixed P.schedule).2 P.latin
  length_eq := P.length_eq
  count_eq := by
    intro c sym
    simpa [scheduleCount_seven_eq_fixed] using P.count_eq c sym

def countMatrixScheduleFixedOfSeven {m : Nat}
    (P : seven.CountMatrixSchedule m) :
    Handoff.CountMatrixSchedule m where
  matrix := P.matrix
  schedule := P.schedule
  certified := (CountMatrixCertified_seven_eq_fixed m P.matrix).1 P.certified
  latin := (scheduleListLatin_seven_eq_fixed P.schedule).1 P.latin
  length_eq := P.length_eq
  count_eq := by
    intro c sym
    simpa [scheduleCount_seven_eq_fixed] using P.count_eq c sym

def canonicalSchedule7_prime_certified :
    seven.CountMatrixSchedule 7 :=
  countMatrixScheduleSevenOfFixed Handoff.canonicalSchedule7_certified

end PrimeDimension
end PrimeRoot
end Handoff
end D7Odd
