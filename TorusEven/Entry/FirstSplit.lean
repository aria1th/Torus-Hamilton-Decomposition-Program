-- STATUS: main-path
import TorusEven.Collar.Closure
import TorusEven.Entry.SingleVoltage

namespace TorusEven.Collar

open Surgery

variable {C I Y : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable [Fintype Y] {m : ℕ} [NeZero m]
variable {F : MultitorusFactorization C I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
variable {active : Finset C} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
variable {i : I} (hc : CircuitConsistent F frame) (S : BlockSelection F frame i ∅)
variable (hi : 2 ≤ F.width i)

theorem BlockSelection.enters_collar (hm : Even m) (hA : F.ActiveSeparated active)
    (hp : ∀ j, 2 ≤ F.width j → Incidence.EvenComponents (F.blockSupport frame j))
    (hs : ∀ c ∈ active, GapSupport (F.step c) U (splitVoltage S.sources c)) :
    RelativeCollarState (S.factorization hc hi) (splitChart i) active (splitMarks U i) := by
  let K := S.sources
  let G := S.factorization hc hi
  have hsem (c : C) : Function.Semiconj (splitChart i) (lift (F.step c) (splitVoltage K c))
      (G.step c) := F.split_semiconj i K (F.width i / 2) (by omega) (by omega)
        (S.subset hc) (S.card hc) c
  have hor (c : C) (p q : (I → ZMod m) × ZMod m) :
      splitChart i q ∈ orbitSet (G.step c) (splitChart i p) ↔ q.1 ∈ orbitSet (F.step c) p.1 :=
    split_orbit_iff F i K (F.width i / 2) (by omega) (by omega)
      (S.subset hc) (S.card hc) (S.unit hc) c p q
  refine ⟨S.consistent hc hi, ?_, fun _ hu => hu.2, ?_, S.parity hc hi hm hp⟩
  · exact F.split_activeSeparated i K (F.width i / 2) (by omega) (by omega)
      (S.subset hc) (S.card hc) active hA
  · intro c ha u hu
    obtain ⟨⟨x, t⟩, rfl⟩ := (splitChart i).surjective u
    obtain ⟨hx, rfl⟩ := (mem_splitMarks U i x t).mp hu
    obtain ⟨a, ha, hau, hg⟩ := relative_renewal (F.step c) U (splitVoltage K c)
      (S.unit hc c) (hs c ha) hx
    refine ⟨splitChart i (a, 0), (mem_splitMarks U i a 0).mpr ⟨ha, rfl⟩,
      (hor c (x, 0) (a, 0)).mpr hau, ?_⟩
    intro z hz ht
    obtain ⟨p, rfl⟩ := (splitChart i).surjective z
    have ht' : p.2 ≠ 0 := by simpa only [Equiv.symm_apply_apply] using ht
    exact openGap_map (lift (F.step c) (splitVoltage K c)) (zeroSection U) (G.step c)
      (splitMarks U i) (splitChart i) (hsem c) (fun q => (mem_splitMarks U i q.1 q.2).symm)
      ⟨ha, rfl⟩ (hg p.1 ((hor c (x, 0) p).mp hz) p.2 ht')

end TorusEven.Collar

namespace TorusEven.Collar

theorem hamilton_decomposition_of_entry_palette
    {C : Type} [Fintype C] [DecidableEq C] {m : ℕ} [NeZero m]
    {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]
    {F : MultitorusFactorization C I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
    {active : Finset C} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
    (hc : CircuitConsistent F frame) (hm : 4 ≤ m) (heven : Even m)
    (hA : F.ActiveSeparated active)
    (hp : ∀ j, 2 ≤ F.width j → Incidence.EvenComponents (F.blockSupport frame j))
    {i : I} (S : BlockSelection F frame i ∅) (hi : 2 ≤ F.width i)
    (hs : ∀ c ∈ active, GapSupport (F.step c) U (splitVoltage S.sources c))
    (R : Recolouring F active U) (hH : ∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) :
    Nonempty (Shared.CayleyDecomposition (Fintype.card C) m) :=
  (BlockSelection.enters_collar hc S hi heven hA hp hs).hamilton_decomposition_palette hm heven
    (R.split hc S hi hs) (R.split_hamilton hc S hi hs hH)

theorem hamilton_decomposition_of_entry {d m : ℕ} [NeZero m]
    {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]
    {F : MultitorusFactorization (Fin d) I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
    {active : Finset (Fin d)} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
    (hc : CircuitConsistent F frame) (hm : 4 ≤ m) (heven : Even m)
    (hA : F.ActiveSeparated active)
    (hp : ∀ j, 2 ≤ F.width j → Incidence.EvenComponents (F.blockSupport frame j))
    {i : I} (S : BlockSelection F frame i ∅) (hi : 2 ≤ F.width i)
    (hs : ∀ c ∈ active, GapSupport (F.step c) U (splitVoltage S.sources c))
    (R : Recolouring F active U) (hH : ∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) :
    Nonempty (Shared.CayleyDecomposition d m) :=
  (BlockSelection.enters_collar hc S hi heven hA hp hs).hamilton_decomposition hm heven
    (R.split hc S hi hs) (R.split_hamilton hc S hi hs hH)

end TorusEven.Collar
