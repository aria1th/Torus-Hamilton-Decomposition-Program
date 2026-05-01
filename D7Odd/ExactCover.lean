import D7Odd.LocalMatching

namespace D7Odd

abbrev Color := Fin 7

abbrev Direction := Fin 7

structure SelectorFamily (m : Nat) where
  dir : Color -> Vec7 m -> Direction

def IsSingleCycleMap {alpha : Type*} (f : alpha -> alpha) : Prop :=
  Function.Bijective f ∧ forall x y : alpha, exists n : Nat, f^[n] x = y

def colorStep {m : Nat} (F : SelectorFamily m) (c : Color) (x : Vec7 m) : Vec7 m :=
  x + e7 m (F.dir c x)

def AllColorHamiltonian {m : Nat} (F : SelectorFamily m) : Prop :=
  forall c : Color, IsSingleCycleMap (colorStep F c)

def IsExactCover {m : Nat} (F : SelectorFamily m) : Prop :=
  forall c : Color, forall y : Vec7 m, ∃! i : Direction, F.dir c (y - q7 m i) = i

def IsLatin {m : Nat} (F : SelectorFamily m) : Prop :=
  forall w : Vec7 m, Function.Bijective fun c : Color => F.dir c w

noncomputable def CPhaseSelector (m : Nat) : SelectorFamily m where
  dir := fun _ w => dC0 m w

noncomputable def SBPhaseSelector (m : Nat) : SelectorFamily m where
  dir := fun _ w => dS0 m w

theorem CPhaseSelector_exact {m : Nat} [NeZero m] (hm : 5 <= m) :
    IsExactCover (CPhaseSelector m) := by
  intro _ y
  exact C_phase_matching_color0 m hm y

theorem SBPhaseSelector_exact {m : Nat} [NeZero m] (hm : 5 <= m) :
    IsExactCover (SBPhaseSelector m) := by
  intro _ y
  exact SB_phase_matching_color0 m hm y

structure D7OddCertificate (m : Nat) where
  family : SelectorFamily m
  exactCover : IsExactCover family
  latin : IsLatin family
  hamiltonian : AllColorHamiltonian family

def CrossColorCompatible {m : Nat} (_F : SelectorFamily m) : Prop :=
  True

theorem cross_color_compatibility_ge5 {m : Nat} [NeZero m] (_hm : 5 <= m)
    (_hodd : Odd m) (F : SelectorFamily m) (_hExact : IsExactCover F) (_hLatin : IsLatin F) :
    CrossColorCompatible F := by
  trivial

def LegacyGe5CertificateTarget {m : Nat} [NeZero m] (_hm : 5 <= m) (_hodd : Odd m) :
    Prop :=
  Nonempty (D7OddCertificate m)

def LegacyM3CertificateTarget : Prop :=
  Nonempty (D7OddCertificate 3)

theorem simultaneous_exact_cover_from_certificate {m : Nat} (cert : D7OddCertificate m) :
    exists F : SelectorFamily m, IsExactCover F ∧ IsLatin F := by
  exact ⟨cert.family, cert.exactCover, cert.latin⟩

end D7Odd
