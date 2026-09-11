-- STATUS: main-path
import TorusEven.Collar.Multitorus
import TorusEven.Collar.Circuits

namespace TorusEven.Collar

open Surgery

variable {C I : Type*} [Fintype C] [Fintype I] [DecidableEq I] {m : ℕ} [NeZero m]

abbrev MultitorusFactorization.CircuitLabel (F : MultitorusFactorization C I m) :=
  Σ c, Circuit (F.step c)

def MultitorusFactorization.labelAt (F : MultitorusFactorization C I m) (x : I → ZMod m) :
    C ↪ F.CircuitLabel where
  toFun c := ⟨c, circuitOf (F.step c) x⟩
  inj' _ _ h := congrArg Sigma.fst h

def MultitorusFactorization.supportAt (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) : Finset F.CircuitLabel := (F.users x i).map (F.labelAt x)

@[simp] theorem MultitorusFactorization.mem_supportAt (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) (q : F.CircuitLabel) :
    q ∈ F.supportAt i x ↔ F.direction q.1 x = i ∧ circuitOf (F.step q.1) x = q.2 := by
  constructor
  · intro h
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp h
    exact ⟨(F.mem_users x i c).mp hc, rfl⟩
  · rintro ⟨hd, hq⟩
    refine Finset.mem_map.mpr ⟨q.1, (F.mem_users _ _ _).mpr hd, ?_⟩
    cases q
    exact congrArg (Sigma.mk _) hq

@[simp] theorem MultitorusFactorization.card_supportAt (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) : (F.supportAt i x).card = F.width i := by
  rw [supportAt, Finset.card_map, F.card_users]

theorem MultitorusFactorization.supportAt_fst_injOn (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) : Set.InjOn Sigma.fst (F.supportAt i x : Set F.CircuitLabel) := by
  intro q hq q' hq' h
  have hq := (F.mem_supportAt i x q).mp hq
  have hq' := (F.mem_supportAt i x q').mp hq'
  rcases q with ⟨c, q⟩
  rcases q' with ⟨c', q'⟩
  change c = c' at h
  subst c'
  exact congrArg (Sigma.mk c) (hq.2.symm.trans hq'.2)

theorem MultitorusFactorization.labelAt_fst_of_mem (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) {q : F.CircuitLabel} (h : q ∈ F.supportAt i x) :
    F.labelAt x q.1 = q := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp h
  rfl

theorem MultitorusFactorization.mem_supportAt_label (F : MultitorusFactorization C I m)
    (i : I) (x : I → ZMod m) (q : F.CircuitLabel) :
    q ∈ F.supportAt i x ↔ F.direction q.1 x = i ∧ F.labelAt x q.1 = q := by
  constructor
  · intro h
    exact ⟨((F.mem_supportAt i x q).mp h).1, F.labelAt_fst_of_mem i x h⟩
  · rintro ⟨hd, hq⟩
    exact Finset.mem_map.mpr ⟨q.1, (F.mem_users _ _ _).mpr hd, hq⟩

variable {Y : Type*}

structure CircuitConsistent (F : MultitorusFactorization C I m)
    (frame : Y × ZMod m ≃ (I → ZMod m)) : Prop where
  direction : ∀ c y s t, F.direction c (frame (y, s)) = F.direction c (frame (y, t))
  circuit : ∀ c y s t, circuitOf (F.step c) (frame (y, s)) = circuitOf (F.step c) (frame (y, t))

def MultitorusFactorization.blockSupport (F : MultitorusFactorization C I m)
    (frame : Y × ZMod m ≃ (I → ZMod m)) (i : I) (y : Y) : Finset F.CircuitLabel :=
  F.supportAt i (frame (y, 0))

theorem CircuitConsistent.supportAt (F : MultitorusFactorization C I m)
    (frame : Y × ZMod m ≃ (I → ZMod m)) (h : CircuitConsistent F frame)
    (i : I) (y : Y) (t : ZMod m) :
    F.supportAt i (frame (y, t)) = F.blockSupport frame i y := by
  ext q
  simp only [MultitorusFactorization.blockSupport, F.mem_supportAt,
    h.direction q.1 y t 0, h.circuit q.1 y t 0]

noncomputable instance MultitorusFactorization.circuitLabelFintype
    (F : MultitorusFactorization C I m) :
    Fintype F.CircuitLabel := Fintype.ofFinite _

noncomputable def MultitorusFactorization.activeColumns (F : MultitorusFactorization C I m)
    (active : Finset C) : Finset F.CircuitLabel := by
  classical
  exact Finset.univ.filter (fun q => q.1 ∈ active)

@[simp] theorem MultitorusFactorization.mem_activeColumns (F : MultitorusFactorization C I m)
    (active : Finset C) (q : F.CircuitLabel) : q ∈ F.activeColumns active ↔ q.1 ∈ active := by
  classical
  simp [activeColumns]

theorem MultitorusFactorization.activeColumns_card_le_one (F : MultitorusFactorization C I m)
    [DecidableEq F.CircuitLabel]
    (active : Finset C) (h : F.ActiveSeparated active) (i : I) (x : I → ZMod m) :
    (F.supportAt i x ∩ F.activeColumns active).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro q hq q' hq'
  have hqA := (Finset.mem_inter.mp hq).1
  have hqA' := (Finset.mem_inter.mp hq').1
  apply F.supportAt_fst_injOn i x hqA hqA'
  exact h x ((F.mem_activeColumns active q).mp (Finset.mem_inter.mp hq).2)
    ((F.mem_activeColumns active q').mp (Finset.mem_inter.mp hq').2)
    (((F.mem_supportAt i x q).mp hqA).1.trans ((F.mem_supportAt i x q').mp hqA').1.symm)

end TorusEven.Collar
