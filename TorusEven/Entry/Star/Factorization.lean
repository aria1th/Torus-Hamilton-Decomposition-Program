-- STATUS: main-path
import TorusEven.Entry.Star.Cycle
import TorusEven.Entry.Replacement
import TorusEven.Entry.Anchors

namespace TorusEven.Entry.Star

open Collar

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

def conjugate (e : Equiv.Perm (Plane m)) : Equiv.Perm (Plane m) :=
  turn.symm.toEquiv.trans (e.trans turn.toEquiv)

omit [NeZero m] in
theorem conjugate_apply {e : Equiv.Perm (Plane m)} {c : Fin 3}
    (he : ∀ p, e p = surgeryMap c p) (p : Plane m) :
    conjugate e p = surgeryMap (rotate c) p := by
  obtain ⟨p, rfl⟩ := turn.surjective p
  simp only [conjugate, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, AddEquiv.symm_apply_apply, he]
  exact (surgeryMap_rotate c p).symm

noncomputable def surgeryPerm (c : Fin 3) : Equiv.Perm (Plane m) :=
  ![zeroPerm hm, conjugate (zeroPerm hm), conjugate (conjugate (zeroPerm hm))] c

theorem surgeryPerm_apply (c : Fin 3) (p : Plane m) : surgeryPerm hm c p = surgeryMap c p := by
  fin_cases c
  · exact zeroPerm_apply hm p
  · exact conjugate_apply (zeroPerm_apply hm) p
  · exact conjugate_apply (conjugate_apply (zeroPerm_apply hm)) p

noncomputable def layer (c : Fin 3) (h : ZMod m) : Equiv.Perm (Plane m) :=
  if h = 1 then (surgeryPerm hm c).trans (Equiv.addRight (generator c))
  else Equiv.addRight (generator (constantRow h c))

theorem layer_apply (c : Fin 3) (h : ZMod m) (p : Plane m) :
    layer hm c h p = p + generator ((if h = 1 then starRow p.1 p.2 else constantRow h) c) := by
  by_cases hh : h = 1
  · simp only [layer, if_pos hh, Equiv.trans_apply, surgeryPerm_apply]
    change surgeryMap c p + generator c = p + generator (starRow p.1 p.2 c)
    simp [surgeryMap]
  · simp [layer, hh]

noncomputable def heightStep (c : Fin 3) : Equiv.Perm (ZMod m × Plane m) where
  toFun p := (p.1 + 1, layer hm c p.1 p.2)
  invFun p := (p.1 - 1, (layer hm c (p.1 - 1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def chart : (ZMod m × Plane m) ≃ Point m where
  toFun p := ![p.1 - p.2.1 - (p.2.2 + 3), p.2.1, p.2.2 + 3]
  invFun v := (height v, (v 1, v 2 - 3))
  left_inv p := by
    rcases p with ⟨h, a, b⟩
    dsimp [height]
    congr 2
    all_goals ring
  right_inv v := by
    funext j
    fin_cases j <;> simp [height]; ring

omit [NeZero m] in
@[simp] theorem height_chart (p : ZMod m × Plane m) : height (chart p) = p.1 := by
  simp [height, chart]
  ring

noncomputable def step (c : Fin 3) : Equiv.Perm (Point m) :=
  chart.symm.trans ((heightStep hm c).trans chart)

omit [NeZero m] in
@[simp] theorem step_chart (c : Fin 3) (p : ZMod m × Plane m) :
    step hm c (chart p) = chart (heightStep hm c p) := by simp [step]

theorem step_eq (c : Fin 3) (v : Point m) (j : Fin 3) :
    step hm ((Equiv.swap 1 2) c) v j = v j + if j = terminalRow v c then 1 else 0 := by
  obtain ⟨⟨h, a, b⟩, rfl⟩ := chart.surjective v
  rw [step_chart]
  change chart (h + 1, layer hm ((Equiv.swap 1 2) c) h (a, b)) j = _
  rw [layer_apply]
  simp only [terminalRow, Equiv.trans_apply, height_chart]
  have hshift : chart (h, (a, b)) 2 - 3 = b := by simp [chart]
  rw [hshift]
  change chart (h + 1, (a, b) + generator
    ((if h = 1 then starRow a b else constantRow h) ((Equiv.swap 1 2) c))) j =
    chart (h, (a, b)) j + if j =
      (if h = 1 then starRow a b else constantRow h) ((Equiv.swap 1 2) c) then 1 else 0
  generalize (if h = 1 then starRow a b else constantRow h) ((Equiv.swap 1 2) c) = k
  fin_cases j <;> fin_cases k <;> simp [chart, generator] <;> ring

noncomputable def factorization : MultitorusFactorization (Fin 3) (Fin 3) m where
  width _ := 1
  width_pos _ := by decide
  direction c v := terminalRow v c
  step c := step hm ((Equiv.swap 1 2) c)
  step_eq := step_eq hm
  quota v i := by
    apply Finset.card_eq_one.mpr
    refine ⟨(terminalRow v).symm i, ?_⟩
    ext c
    simp [Equiv.apply_eq_iff_eq_symm_apply]

noncomputable def replacement : Recolouring (NearCore.factorization (m := m))
    Finset.univ (replacementSupport m) :=
  Recolouring.ofReplacement NearCore.factorization (factorization hm) Finset.univ
    (replacementSupport m)
    (fun v => (terminalRow v).trans (nearRow (height v) (v 2)).symm)
    (fun _ _ h => False.elim (h (Finset.mem_univ _)))
    (fun c v => (nearRow (height v) (v 2)).apply_symm_apply (terminalRow v c) |>.symm)
    (fun c v hv => by
      have hr : terminalRow v = nearRow (height v) (v 2) := not_not.mp hv
      funext j
      rw [(factorization hm).step_eq, NearCore.factorization.step_eq]
      change v j + (if j = terminalRow v c then 1 else 0) =
        v j + if j = nearRow (height v) (v 2) c then 1 else 0
      rw [hr])

theorem replacement_step (c : Fin 3) :
    (replacement hm).factorization.step c = (factorization hm).step c :=
  Recolouring.ofReplacement_step _ _ _ _ _ _ _ _ c

end TorusEven.Entry.Star
