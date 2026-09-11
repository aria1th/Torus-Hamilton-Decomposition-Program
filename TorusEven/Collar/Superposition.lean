-- STATUS: main-path
import TorusEven.Collar.CircuitBlocks
import TorusEven.Collar.Recolouring

namespace TorusEven.Collar

variable {C D I : Type*} [Fintype C] [Fintype D] [DecidableEq I] {m : ℕ}

def MultitorusFactorization.superpose
    (F : MultitorusFactorization C I m) (G : MultitorusFactorization D I m) :
    MultitorusFactorization (C ⊕ D) I m where
  width i := F.width i + G.width i
  width_pos i := Nat.add_pos_left (F.width_pos i) _
  direction := Sum.elim F.direction G.direction
  step := Sum.elim F.step G.step
  step_eq c x j := by
    cases c with
    | inl c => exact F.step_eq c x j
    | inr c => exact G.step_eq c x j
  quota x i := by
    have h := congrArg₂ (· + ·) (F.quota x i) (G.quota x i)
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr] using h

variable [Fintype I] [NeZero m]
variable (F : MultitorusFactorization C I m) (G : MultitorusFactorization D I m)

def MultitorusFactorization.superposeLabels :
    (F.superpose G).CircuitLabel ≃ F.CircuitLabel ⊕ G.CircuitLabel where
  toFun q := match q with
    | ⟨.inl c, q⟩ => .inl ⟨c, q⟩
    | ⟨.inr c, q⟩ => .inr ⟨c, q⟩
  invFun q := match q with
    | .inl ⟨c, q⟩ => ⟨.inl c, q⟩
    | .inr ⟨c, q⟩ => ⟨.inr c, q⟩
  left_inv q := by rcases q with ⟨c, q⟩; cases c <;> rfl
  right_inv q := by rcases q with ⟨c, q⟩ | ⟨c, q⟩ <;> rfl

theorem MultitorusFactorization.mem_superpose_support_left
    (i : I) (v : I → ZMod m) (q : F.CircuitLabel) :
    (F.superposeLabels G).symm (.inl q) ∈ (F.superpose G).supportAt i v ↔
      q ∈ F.supportAt i v := by
  rcases q with ⟨c, q⟩
  simp only [MultitorusFactorization.mem_supportAt]
  rfl

theorem MultitorusFactorization.mem_superpose_support_right
    (i : I) (v : I → ZMod m) (q : G.CircuitLabel) :
    (F.superposeLabels G).symm (.inr q) ∈ (F.superpose G).supportAt i v ↔
      q ∈ G.supportAt i v := by
  rcases q with ⟨c, q⟩
  simp only [MultitorusFactorization.mem_supportAt]
  rfl

theorem CircuitConsistent.superpose {Y : Type*} (frame : Y × ZMod m ≃ (I → ZMod m))
    (hf : CircuitConsistent F frame) (hg : CircuitConsistent G frame) :
    CircuitConsistent (F.superpose G) frame where
  direction c y s t := by
    cases c with
    | inl c => exact hf.direction c y s t
    | inr c => exact hg.direction c y s t
  circuit c y s t := by
    cases c with
    | inl c => exact hf.circuit c y s t
    | inr c => exact hg.circuit c y s t

variable [DecidableEq C] [DecidableEq D]
variable {active : Finset C} {U : Set (I → ZMod m)} [DecidablePred (· ∈ U)]

def Recolouring.superpose (R : Recolouring F active U) :
    Recolouring (F.superpose G) (active.map Function.Embedding.inl) U where
  boundary := Sum.elim R.boundary (fun _ => Equiv.refl U)
  routing u := Equiv.sumCongr (R.routing u) (Equiv.refl D)
  routing_inactive u c hc := by
    cases c with
    | inl c =>
      have hn : c ∉ active := by simpa using hc
      simp [R.routing_inactive u c hn]
    | inr c => rfl
  head c u := by
    cases c with
    | inl c => exact R.head c u
    | inr c => rfl

omit [Fintype I] [NeZero m] [DecidableEq C] [DecidableEq D] in
theorem Recolouring.superpose_step_left (R : Recolouring F active U) (c : C) :
    (R.superpose F G).factorization.step (.inl c) = R.factorization.step c := rfl

omit [Fintype I] [NeZero m] [DecidableEq C] [DecidableEq D] in
theorem Recolouring.superpose_step_right (R : Recolouring F active U) (c : D) :
    (R.superpose F G).factorization.step (.inr c) = G.step c := Surgery.patch_refl _ _

end TorusEven.Collar
