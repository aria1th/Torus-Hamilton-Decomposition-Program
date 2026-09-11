-- STATUS: main-path
import TorusEven.Collar.SourceSelection
import TorusEven.Collar.IncidenceTransport

namespace TorusEven.Collar

open Surgery

variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable {m : ℕ} [NeZero m] (F : MultitorusFactorization C I m) (i : I)
variable (K : (I → ZMod m) → Finset C) (b : ℕ) (hb : 0 < b) (hbi : b < F.width i)
variable (hK : ∀ x, K x ⊆ F.users x i) (hcard : ∀ x, (K x).card = b)
variable (hunit : ∀ c, UnitCarry (F.step c) (splitVoltage K c))

noncomputable def splitCircuitEquiv (c : C) :
    Circuit ((F.split i K b hb hbi hK hcard).step c) ≃ Circuit (F.step c) :=
  (circuitEquiv (lift (F.step c) (splitVoltage K c))
    ((F.split i K b hb hbi hK hcard).step c) (splitChart i)
    (F.split_semiconj i K b hb hbi hK hcard c)).symm.trans
      (liftCircuitEquiv (F.step c) (splitVoltage K c) (hunit c))

@[simp] theorem splitCircuitEquiv_apply (c : C) (x : I → ZMod m) (t : ZMod m) :
    splitCircuitEquiv F i K b hb hbi hK hcard hunit c
      (circuitOf ((F.split i K b hb hbi hK hcard).step c) (splitChart i (x, t))) =
        circuitOf (F.step c) x := by
  let e := circuitEquiv (lift (F.step c) (splitVoltage K c))
    ((F.split i K b hb hbi hK hcard).step c) (splitChart i)
    (F.split_semiconj i K b hb hbi hK hcard c)
  have he : e (circuitOf (lift (F.step c) (splitVoltage K c)) (x, t)) =
      circuitOf ((F.split i K b hb hbi hK hcard).step c) (splitChart i (x, t)) := rfl
  have hi := congrArg (liftCircuitEquiv (F.step c) (splitVoltage K c) (hunit c))
    (e.symm_apply_apply (circuitOf (lift (F.step c) (splitVoltage K c)) (x, t)))
  simpa only [he, liftCircuitEquiv_apply] using hi

noncomputable def splitLabelEquiv : (F.split i K b hb hbi hK hcard).CircuitLabel ≃ F.CircuitLabel :=
  Equiv.sigmaCongrRight (splitCircuitEquiv F i K b hb hbi hK hcard hunit)

@[simp] theorem splitLabelEquiv_labelAt (c : C) (x : I → ZMod m) (t : ZMod m) :
    splitLabelEquiv F i K b hb hbi hK hcard hunit
      ((F.split i K b hb hbi hK hcard).labelAt (splitChart i (x, t)) c) = F.labelAt x c := by
  exact congrArg (Sigma.mk c) (splitCircuitEquiv_apply F i K b hb hbi hK hcard hunit c x t)

include hunit in
theorem split_circuitConsistent :
    CircuitConsistent (F.split i K b hb hbi hK hcard) (splitChart i) :=
  ⟨F.split_fibre_direction i K b hb hbi hK hcard,
    fun c => F.split_fibre_circuit i K b hb hbi hK hcard c (hunit c)⟩

include hunit in
theorem split_orbit_iff (c : C) (p q : (I → ZMod m) × ZMod m) :
    splitChart i q ∈ orbitSet ((F.split i K b hb hbi hK hcard).step c) (splitChart i p) ↔
      q.1 ∈ orbitSet (F.step c) p.1 :=
  (orbit_equiv_iff _ _ (splitChart i) (F.split_semiconj i K b hb hbi hK hcard c) p q).trans
    (lift_orbit_iff (F.step c) (splitVoltage K c) (hunit c) p q)

theorem split_blockSupport_mem (j : Option I) (x : I → ZMod m) (q : F.CircuitLabel) :
    (splitLabelEquiv F i K b hb hbi hK hcard hunit).symm q ∈
        (F.split i K b hb hbi hK hcard).blockSupport (splitChart i) j x ↔
      splitDirection F K q.1 x = j ∧ F.labelAt x q.1 = q := by
  let G := F.split i K b hb hbi hK hcard
  let e := splitLabelEquiv F i K b hb hbi hK hcard hunit
  have hcolor : (e.symm q).1 = q.1 := rfl
  rw [MultitorusFactorization.blockSupport, G.mem_supportAt]
  have hlabel : circuitOf (G.step (e.symm q).1) (splitChart i (x, 0)) = (e.symm q).2 ↔
      F.labelAt x q.1 = q := by
    have hL : G.labelAt (splitChart i (x, 0)) (e.symm q).1 = e.symm q ↔
        F.labelAt x q.1 = q := by
      rw [← e.apply_eq_iff_eq, e.apply_symm_apply]
      rw [splitLabelEquiv_labelAt, hcolor]
    rw [← hL]
    cases he : e.symm q with | mk c s =>
      change circuitOf (G.step c) (splitChart i (x, 0)) = s ↔
        (Sigma.mk c (circuitOf (G.step c) (splitChart i (x, 0))) : G.CircuitLabel) = Sigma.mk c s
      simp
  rw [hlabel]
  change (splitDirection F K (e.symm q).1 ((splitChart i).symm (splitChart i (x, 0))).1 = j ∧ _) ↔ _
  simp only [Equiv.symm_apply_apply, hcolor]

end TorusEven.Collar
