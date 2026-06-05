import EvenV11.FinalTargetPredicateBridge

namespace EvenV11
namespace FinalTargetRootFlatCertificateBridge

def finalRootFlatModelColorDir {d m : Nat} {RootState : Type}
    (schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m)
    (torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m) :
    Shared.TorusColor d → Shared.TorusVertex d m →
      Shared.TorusDirection d :=
  fun c x => schedule.dir (torusEquiv.symm x).1 (torusEquiv.symm x).2 c

structure FinalRootFlatTorusModel
    (d m : Nat) [NeZero m] (RootState : Type)
    (schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m)
    (torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m) :
    Prop where
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle
  stepConjugacy :
    ∀ c : Shared.TorusColor d, ∀ tw : ZMod m × RootState,
      Shared.cayleyColorStep
        (finalRootFlatModelColorDir schedule torusEquiv)
        c (torusEquiv tw) =
      torusEquiv (schedule.fullStep c tw)

theorem finalRootFlatTorusModel_of_fields
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (hRow : schedule.rowLatin)
    (hLayer : schedule.layerBijective)
    (hReturn : schedule.returnsSingleCycle)
    (hStep :
      ∀ c : Shared.TorusColor d, ∀ tw : ZMod m × RootState,
        Shared.cayleyColorStep
          (finalRootFlatModelColorDir schedule torusEquiv)
          c (torusEquiv tw) =
        torusEquiv (schedule.fullStep c tw)) :
    FinalRootFlatTorusModel d m RootState schedule torusEquiv where
  rowLatin := hRow
  layerBijective := hLayer
  returnsSingleCycle := hReturn
  stepConjugacy := hStep

def FinalRootFlatTorusCertificate (d m : Nat) : Prop :=
  ∃ h : NeZero m, ∃ RootState : Type,
    ∃ schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m,
    ∃ torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m,
      @FinalRootFlatTorusModel d m h RootState schedule torusEquiv

theorem finalRootFlatTorusCertificate_of_model
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    FinalRootFlatTorusCertificate d m :=
  ⟨inferInstance, RootState, schedule, torusEquiv, model⟩

theorem finalRootFlatTorusCertificate_of_fields
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (hRow : schedule.rowLatin)
    (hLayer : schedule.layerBijective)
    (hReturn : schedule.returnsSingleCycle)
    (hStep :
      ∀ c : Shared.TorusColor d, ∀ tw : ZMod m × RootState,
        Shared.cayleyColorStep
          (finalRootFlatModelColorDir schedule torusEquiv)
          c (torusEquiv tw) =
        torusEquiv (schedule.fullStep c tw)) :
    FinalRootFlatTorusCertificate d m :=
  finalRootFlatTorusCertificate_of_model
    (finalRootFlatTorusModel_of_fields hRow hLayer hReturn hStep)

theorem finalRootFlatTorusModelEdgePartition
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.IsCayleyEdgePartition
      (finalRootFlatModelColorDir schedule torusEquiv) := by
  intro x i
  let tw : ZMod m × RootState := torusEquiv.symm x
  have hrow :
      Function.Bijective
        (fun c : Shared.TorusColor d => schedule.dir tw.1 tw.2 c) :=
    model.rowLatin tw.1 tw.2
  rcases hrow.2 i with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · simpa [finalRootFlatModelColorDir, tw] using hc
  · intro c' hc'
    apply hrow.1
    have hc'' : schedule.dir tw.1 tw.2 c' = i := by
      simpa [finalRootFlatModelColorDir, tw] using hc'
    exact hc''.trans hc.symm

theorem finalRootFlatTorusModelColorHamiltonian
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.IsCayleyColorHamiltonian
      (finalRootFlatModelColorDir schedule torusEquiv) := by
  intro c
  have hRoot : Shared.IsSingleCycleMap (schedule.fullStep c) :=
    Shared.RootFlatSchedule.fullStep_singleCycle_of_return
      schedule model.layerBijective (model.returnsSingleCycle c)
  refine Shared.single_cycle_of_equiv_conj torusEquiv
    (Shared.cayleyColorStep
      (finalRootFlatModelColorDir schedule torusEquiv) c)
    (schedule.fullStep c) hRoot ?_
  intro tw
  calc
    torusEquiv.symm
        (Shared.cayleyColorStep
          (finalRootFlatModelColorDir schedule torusEquiv)
          c (torusEquiv tw)) =
        torusEquiv.symm (torusEquiv (schedule.fullStep c tw)) := by
          rw [model.stepConjugacy c tw]
    _ = schedule.fullStep c tw := by simp

theorem finalRootFlatTorusModelCayley
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.CayleyHamiltonDecomposition d m :=
  ⟨{
    colorDir := finalRootFlatModelColorDir schedule torusEquiv
    edgePartition := finalRootFlatTorusModelEdgePartition model
    colorHamiltonian := finalRootFlatTorusModelColorHamiltonian model
  }⟩

theorem finalRootFlatOrdinaryTarget_of_model
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    FinalOrdinaryTarget d m :=
  (Shared.torusHamiltonDecomposition_iff_cayley).mpr
    (finalRootFlatTorusModelCayley model)

theorem finalRootFlatMarkedTarget_of_model
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    FinalMarkedTarget d m :=
  finalRootFlatOrdinaryTarget_of_model model

theorem finalRootFlatCayley_of_certificate
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases certificate with
    ⟨h, RootState, schedule, torusEquiv, model⟩
  exact @finalRootFlatTorusModelCayley
    d m h RootState schedule torusEquiv model

theorem finalRootFlatOrdinaryTarget_of_certificate
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    FinalOrdinaryTarget d m :=
  (Shared.torusHamiltonDecomposition_iff_cayley).mpr
    (finalRootFlatCayley_of_certificate certificate)

theorem finalRootFlatMarkedTarget_of_certificate
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    FinalMarkedTarget d m :=
  finalRootFlatOrdinaryTarget_of_certificate certificate

end FinalTargetRootFlatCertificateBridge

export FinalTargetRootFlatCertificateBridge
  (finalRootFlatModelColorDir
   FinalRootFlatTorusModel
   finalRootFlatTorusModel_of_fields
   FinalRootFlatTorusCertificate
   finalRootFlatTorusCertificate_of_model
   finalRootFlatTorusCertificate_of_fields
   finalRootFlatTorusModelEdgePartition
   finalRootFlatTorusModelColorHamiltonian
   finalRootFlatTorusModelCayley
   finalRootFlatOrdinaryTarget_of_model
   finalRootFlatMarkedTarget_of_model
   finalRootFlatCayley_of_certificate
   finalRootFlatOrdinaryTarget_of_certificate
   finalRootFlatMarkedTarget_of_certificate)

end EvenV11
