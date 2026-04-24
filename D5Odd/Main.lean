import D5Odd.ReturnCycle

namespace D5Odd

def HamiltonDecompositionD5 (m : Nat) : Prop :=
  exists F : LayerSchedule m, IsLayerExactCover F ∧ IsScheduleLatin F ∧ AllColorHamiltonian F

structure D5OddCertificate (m : Nat) where
  schedule : LayerSchedule m
  exactCover : IsLayerExactCover schedule
  latin : IsScheduleLatin schedule
  hamiltonian : AllColorHamiltonian schedule

def D5Ge5CertificateTarget (m : Nat) : Prop :=
  IsLayerExactCover (ge5Schedule m) ∧ AllColorHamiltonian (ge5Schedule m)

def D5M3CertificateTarget : Prop :=
  IsLayerExactCover m3Schedule ∧ AllColorHamiltonian m3Schedule

theorem D5_odd_from_certificate (cert : D5OddCertificate m) :
    HamiltonDecompositionD5 m := by
  exact ⟨cert.schedule, cert.exactCover, cert.latin, cert.hamiltonian⟩

theorem D5_odd_ge5_from_target {m : Nat} (_hm : 5 <= m) (_hodd : Odd m)
    (h : D5Ge5CertificateTarget m) :
    HamiltonDecompositionD5 m := by
  exact ⟨ge5Schedule m, h.1, ge5Schedule_latin m, h.2⟩

theorem D5_odd_ge5_from_hamiltonian {m : Nat} [NeZero m] (hm : 5 <= m) (_hodd : Odd m)
    (h : AllColorHamiltonian (ge5Schedule m)) :
    HamiltonDecompositionD5 m := by
  exact ⟨ge5Schedule m, ge5Schedule_exact hm, ge5Schedule_latin m, h⟩

theorem D5_odd_m3_from_target (h : D5M3CertificateTarget) :
    HamiltonDecompositionD5 3 := by
  exact ⟨m3Schedule, h.1, m3Schedule_latin, h.2⟩

theorem D5_odd_m3_from_hamiltonian (h : AllColorHamiltonian m3Schedule) :
    HamiltonDecompositionD5 3 := by
  exact ⟨m3Schedule, m3Schedule_exact, m3Schedule_latin, h⟩

theorem D5M3CertificateTarget_iff :
    D5M3CertificateTarget ↔ AllColorHamiltonian m3Schedule := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨m3Schedule_exact, h⟩

theorem D5M3CertificateTarget_unconditional : D5M3CertificateTarget := by
  exact D5M3CertificateTarget_iff.2 m3Schedule_allColorHamiltonian

theorem D5Ge5CertificateTarget_iff {m : Nat} [NeZero m] (hm : 5 <= m) :
    D5Ge5CertificateTarget m ↔ AllColorHamiltonian (ge5Schedule m) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨ge5Schedule_exact hm, h⟩

theorem D5Ge5CertificateTarget_unconditional {m h : Nat} [NeZero m]
    (hm : m = 2 * h + 1) (hh2 : 2 <= h) :
    D5Ge5CertificateTarget m := by
  have hm5 : 5 <= m := by omega
  exact (D5Ge5CertificateTarget_iff (m := m) hm5).2
    (ge5Schedule_allColorHamiltonian hm hh2)

theorem D5_odd_unconditional_from_targets {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m)
    (hge5 : 5 <= m -> D5Ge5CertificateTarget m)
    (hm3Target : m = 3 -> D5M3CertificateTarget) :
    HamiltonDecompositionD5 m := by
  by_cases hm5 : 5 <= m
  · exact D5_odd_ge5_from_target (m := m) hm5 hodd (hge5 hm5)
  · have hmle4 : m <= 4 := by omega
    interval_cases m
    · exact D5_odd_m3_from_target (hm3Target rfl)
    · norm_num at hodd

theorem D5_odd_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    HamiltonDecompositionD5 m := by
  apply D5_odd_unconditional_from_targets hodd hm3
  · intro hm5
    rcases hodd with ⟨h, rfl⟩
    exact D5Ge5CertificateTarget_unconditional rfl (by omega)
  · intro _hm
    exact D5M3CertificateTarget_unconditional

end D5Odd
