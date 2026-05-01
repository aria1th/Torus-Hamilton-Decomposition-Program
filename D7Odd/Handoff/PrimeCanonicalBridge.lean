import D7Odd.Handoff.CanonicalFamily
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

end PrimeDimension
end PrimeRoot
end Handoff
end D7Odd
