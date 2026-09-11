-- STATUS: main-path
import TorusEven.Collar.Recolouring

namespace TorusEven.Collar

inductive SplitResolution {d m : ℕ} [NeZero m] :
    {I : Type} → [Fintype I] → [DecidableEq I] →
      MultitorusFactorization (Fin d) I m → ℕ → Prop where
  | terminal {I : Type} [Fintype I] [DecidableEq I]
      (F : MultitorusFactorization (Fin d) I m) (hw : ∀ i, F.width i = 1) :
      SplitResolution F 0
  | split {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]
      {F : MultitorusFactorization (Fin d) I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
      {active : Finset (Fin d)} {i : I} (hc : CircuitConsistent F frame)
      (S : BlockSelection F frame i active) (hi : 2 ≤ F.width i) {n : ℕ}
      (tail : SplitResolution (S.factorization hc hi) n) : SplitResolution F (n + 1)

theorem RelativeCollarState.exists_split
    {C I Y : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I] [Fintype Y]
    {m : ℕ} [NeZero m] {F : MultitorusFactorization C I m}
    {frame : Y × ZMod m ≃ (I → ZMod m)} {active : Finset C}
    {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
    (h : RelativeCollarState F frame active U) (hm : 4 ≤ m) (heven : Even m)
    (i : I) (hi : 2 ≤ F.width i) :
    ∃ S : BlockSelection F frame i active,
      RelativeCollarState (S.factorization h.consistent hi) (splitChart i) active (splitMarks U i) ∧
      ∀ (R : Recolouring F active U) c,
        Surgery.circuitCount ((R.lift h S hi).factorization.step c) =
          Surgery.circuitCount (R.factorization.step c) := by
  obtain ⟨S⟩ := h.selection hm i hi
  exact ⟨S, h.split S hi heven, fun R c => R.lift_circuitCount h S hi c⟩

private theorem close_of_excess {d m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m) (n : ℕ) :
    ∀ {I Y : Type} [Fintype I] [DecidableEq I] [Finite Y]
      (F : MultitorusFactorization (Fin d) I m) (frame : Y × ZMod m ≃ (I → ZMod m))
      (active : Finset (Fin d)) (U : Set (I → ZMod m)) [DecidablePred (· ∈ U)]
      (_h : RelativeCollarState F frame active U), F.excess = n →
      SplitResolution F n ∧ ∀ R : Recolouring F active U,
        (∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) →
          Nonempty (Shared.CayleyDecomposition d m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I Y _ _ _ F frame active U _ h hn
    letI : Fintype Y := Fintype.ofFinite Y
    by_cases hzero : n = 0
    · have hw := F.excess_zero_iff.mp (hn.trans hzero)
      refine ⟨hzero.symm ▸ SplitResolution.terminal F hw, ?_⟩
      exact fun R hH => ⟨R.factorization.toCayleyOfUnitWidths hw hH⟩
    · have hnext : ∃ i, 2 ≤ F.width i := by
        by_contra! hnone
        have hw (i : I) : F.width i = 1 := by have := F.width_pos i; have := hnone i; omega
        have hz := F.excess_zero_iff.mpr hw
        omega
      obtain ⟨i, hi⟩ := hnext
      obtain ⟨S⟩ := h.selection hm i hi
      have hex : (S.factorization h.consistent hi).excess + 1 = n := by
        rw [← hn]
        exact F.split_excess i S.sources (F.width i / 2) (by omega) (by omega)
          (S.subset h.consistent) (S.card h.consistent)
      obtain ⟨hrun, hclose⟩ := ih (S.factorization h.consistent hi).excess (by omega)
        (S.factorization h.consistent hi) (splitChart i) active (splitMarks U i)
        (h.split S hi heven) rfl
      refine ⟨hex ▸ SplitResolution.split h.consistent S hi hrun, ?_⟩
      exact fun R hH => hclose (R.lift h S hi) (R.lift_hamilton h S hi hH)

theorem RelativeCollarState.resolution {d m : ℕ} [NeZero m]
    {I Y : Type} [Fintype I] [DecidableEq I] [Finite Y]
    {F : MultitorusFactorization (Fin d) I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
    {active : Finset (Fin d)} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
    (h : RelativeCollarState F frame active U) (hm : 4 ≤ m) (heven : Even m) :
    SplitResolution F F.excess :=
  (close_of_excess hm heven F.excess F frame active U h rfl).1

theorem RelativeCollarState.hamilton_decomposition {d m : ℕ} [NeZero m]
    {I Y : Type} [Fintype I] [DecidableEq I] [Finite Y]
    {F : MultitorusFactorization (Fin d) I m} {frame : Y × ZMod m ≃ (I → ZMod m)}
    {active : Finset (Fin d)} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]
    (h : RelativeCollarState F frame active U) (hm : 4 ≤ m) (heven : Even m)
    (R : Recolouring F active U) (hH : ∀ c, Shared.IsSingleCycleMap (R.factorization.step c)) :
    Nonempty (Shared.CayleyDecomposition d m) :=
  (close_of_excess hm heven F.excess F frame active U h rfl).2 R hH

end TorusEven.Collar
