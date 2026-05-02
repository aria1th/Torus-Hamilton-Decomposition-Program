import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

/-!
Lean-facing Target-B' scalar interface.

The zero-set-only/congruence-family fiber compiler is expected to reduce the
`A3` monodromy to a triangular clock/carry map.  This file proves the reusable
criterion needed by that reduction: if the clock translation and the carry
return scalar are both units, and one full clock round has the recorded carry
return, then the triangular map is one `m^2` cycle.
-/

def a3ClockPair {m : Nat} (w : ARoot3 m) : ZMod m × ZMod m :=
  (w.1 0 + w.1 1, w.1 0)

def a3OfClockPair {m : Nat} (p : ZMod m × ZMod m) : ARoot3 m :=
  vec3OfPrefix p.2 (p.1 - p.2)

theorem a3ClockPair_a3OfClockPair {m : Nat} (p : ZMod m × ZMod m) :
    a3ClockPair (a3OfClockPair p) = p := by
  rcases p with ⟨s, x⟩
  simp [a3ClockPair, a3OfClockPair, vec3OfPrefix]

set_option linter.flexible false in
theorem a3OfClockPair_a3ClockPair {m : Nat} (w : ARoot3 m) :
    a3OfClockPair (a3ClockPair w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [a3ClockPair, a3OfClockPair, vec3OfPrefix]
  · rw [root3_sink_eq]
    ring

def a3ClockEquiv (m : Nat) : ARoot3 m ≃ ZMod m × ZMod m where
  toFun := a3ClockPair
  invFun := a3OfClockPair
  left_inv := a3OfClockPair_a3ClockPair
  right_inv := a3ClockPair_a3OfClockPair

def triangularPairMap {m : Nat} (A : ZMod m) (phi : ZMod m → ZMod m) :
    ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p => (p.1 + A, p.2 + phi p.1)

def a3TriangularMap {m : Nat} (A : ZMod m) (phi : ZMod m → ZMod m) :
    ARoot3 m → ARoot3 m :=
  fun w => a3OfClockPair (triangularPairMap A phi (a3ClockPair w))

theorem zmod_add_right_bijective {m : Nat} (a : ZMod m) :
    Function.Bijective fun x : ZMod m => x + a := by
  constructor
  · intro x y hxy
    exact add_right_cancel hxy
  · intro y
    refine ⟨y - a, ?_⟩
    simp

theorem zmod_add_single_cycle_of_isUnit
    {m : Nat} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    IsSingleCycleMap (fun x : ZMod m => x + a) := by
  rcases ha with ⟨u, rfl⟩
  let rank : ZMod m → ZMod m := Units.mulLeft u⁻¹
  have hrank : Function.Bijective rank := by
    exact Equiv.bijective (Units.mulLeft u⁻¹)
  have hstep : ∀ x, rank (x + (u : ZMod m)) = rank x + 1 := by
    intro x
    dsimp [rank]
    rw [mul_add]
    rw [show (↑u⁻¹ : ZMod m) * (u : ZMod m) = 1 by simp]
  exact single_cycle_of_zmod_rank
    (fun x : ZMod m => x + (u : ZMod m)) rank hrank hstep

theorem triangularPairMap_bijective {m : Nat}
    (A : ZMod m) (phi : ZMod m → ZMod m) :
    Function.Bijective (triangularPairMap A phi) := by
  constructor
  · intro p q hpq
    rcases p with ⟨sp, xp⟩
    rcases q with ⟨sq, xq⟩
    have hs : sp + A = sq + A := by
      simpa [triangularPairMap] using congrArg Prod.fst hpq
    have hspq : sp = sq := add_right_cancel hs
    subst sq
    have hx : xp + phi sp = xq + phi sp := by
      simpa [triangularPairMap] using congrArg Prod.snd hpq
    have hxpq : xp = xq := add_right_cancel hx
    subst xq
    rfl
  · intro q
    rcases q with ⟨s, x⟩
    refine ⟨(s - A, x - phi (s - A)), ?_⟩
    simp [triangularPairMap]

structure A3TriangularScalarCertificate (m : Nat) [NeZero m] where
  A : ZMod m
  E : ZMod m
  phi : ZMod m → ZMod m
  A_unit : IsUnit A
  E_unit : IsUnit E
  roundAtZero :
    ∀ x : ZMod m, (triangularPairMap A phi)^[m] (0, x) = (0, x + E)

namespace A3TriangularScalarCertificate

theorem pair_single_cycle {m : Nat} [NeZero m]
    (cert : A3TriangularScalarCertificate m) :
    IsSingleCycleMap (triangularPairMap cert.A cert.phi) := by
  refine single_cycle_of_fiber_return
    (f := triangularPairMap cert.A cert.phi)
    (g := fun s : ZMod m => s + cert.A)
    (proj := Prod.fst)
    (fiberBase := fun x : ZMod m => (0, x))
    (fiberNext := fun x : ZMod m => x + cert.E)
    (returnTime := m)
    (b₀ := 0)
    ?hf ?hcomm ?hfiber_surj ?hreturn ?hbase ?hfiber
  · exact triangularPairMap_bijective cert.A cert.phi
  · intro p
    rfl
  · intro p hp
    rcases p with ⟨s, x⟩
    have hs : s = 0 := by
      simpa using hp
    subst s
    exact ⟨x, rfl⟩
  · intro x
    exact cert.roundAtZero x
  · exact zmod_add_single_cycle_of_isUnit cert.A_unit
  · exact zmod_add_single_cycle_of_isUnit cert.E_unit

theorem a3_single_cycle {m : Nat} [NeZero m]
    (cert : A3TriangularScalarCertificate m) :
    IsSingleCycleMap (a3TriangularMap cert.A cert.phi) := by
  have hpair := cert.pair_single_cycle
  have hshared : Shared.IsSingleCycleMap (triangularPairMap cert.A cert.phi) := by
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using hpair
  have haroot_shared :
      Shared.IsSingleCycleMap (a3TriangularMap cert.A cert.phi) := by
    refine Shared.single_cycle_of_equiv_conj
      (e := (a3ClockEquiv m).symm)
      (f := a3TriangularMap cert.A cert.phi)
      (g := triangularPairMap cert.A cert.phi)
      hshared ?_
    intro p
    simp [a3TriangularMap, a3ClockEquiv, a3ClockPair_a3OfClockPair]
  simpa [Shared.IsSingleCycleMap, IsSingleCycleMap] using haroot_shared

end A3TriangularScalarCertificate

end Additive4Plus2
end Handoff
end D7Odd
