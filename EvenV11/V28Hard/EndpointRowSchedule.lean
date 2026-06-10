import EvenV11.RootFlatCycleData
import EvenV11.V28Hard.EndpointChart

/-!
# Hard slot H6 (E5): child row schedule skeleton

A *row schedule* is a standard-lift root-flat schedule whose layer rows are
permutations of the direction set `Fin (n+1)`:

  `dir t w := rowAt t w : Equiv.Perm (Fin (n+1))`.

For such schedules the certificate obligations degrade gracefully:

* **RF1 (`rowLatin`) is automatic** — every row is a permutation
  (`rowSchedule_rowLatin`);
* **RF2 (`layerBijective`) reduces to translation invariance.**  The layer
  map of color `c` is `w ↦ rootStep (rowAt t w c) w`, and `rootStep i` is
  translation by the indicator vector `stepVec i` (`rootStep_eq_add`).  So:
  - a layer with a *constant* row is a fixed translation, hence bijective
    (`layerMap_bijective_of_constant`);
  - a layer that substitutes `σ` for `ρ` on a cylinder `U` is bijective as
    soon as `U` is invariant under translation by the difference vector
    `stepVec (σ c) - stepVec (ρ c)` (`layerMap_bijective_of_cylinder`, the
    paper's RF2 ribbon identity);
  - when `σ = ρ.trans (Equiv.swap α β)`, only the two colors `ρ.symm α`
    and `ρ.symm β` move, and their difference vectors are
    `±(stepVec β - stepVec α)`; since invariance under `+d` is equivalent to
    invariance under `-d` (`mem_iff_add_neg_mem`), the SINGLE hypothesis
    `∀ w, w ∈ U ↔ w + (stepVec β - stepVec α) ∈ U` settles ALL colors
    (`layerMap_bijective_of_swap_cylinder`).

The chart rows of `EvenV11.V28Hard.EndpointChart` instantiate these criteria
at `n = 2*b`: completion layers `C_h` are constant rows, and exchange/reset
layers `X_i`, `R` are swap-on-cylinder rows.  A per-layer plan
(`LayerDesc` + `rowSchedule_layerBijective_of_plan`) bundles a full RF2
certificate from one descriptor per layer.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace EndpointRowSchedule

open Shared StandardRootFlatLift

/-! ## Step vectors: `rootStep` as a translation -/

/-- Indicator step vector of direction `i`: the root-state displacement
performed by `rootStep i` (zero for the carry direction `Fin.last n`). -/
def stepVec {n m : Nat} (i : Fin (n + 1)) : RootState n m :=
  fun j => if i = j.castSucc then 1 else 0

/-- `rootStep i` is translation by the step vector of `i`. -/
theorem rootStep_eq_add {n m : Nat} (i : Fin (n + 1)) (w : RootState n m) :
    rootStep i w = w + stepVec i := by
  funext j
  by_cases h : i = j.castSucc <;> simp [rootStep, stepVec, h]

/-! ## Cylinder substitutions in an additive group -/

/-- A set invariant under translation by `d` is invariant under `-d`. -/
theorem mem_iff_add_neg_mem {G : Type*} [AddCommGroup G] {U : Set G}
    {d : G} (hinv : ∀ w, w ∈ U ↔ w + d ∈ U) (w : G) :
    w ∈ U ↔ w + -d ∈ U := by
  have h := hinv (w + -d)
  have he : w + -d + d = w := by abel
  rw [he] at h
  exact h.symm

/-- Cylinder substitution: translate by `d` on `U`, fix everything off `U`. -/
def cylinderShift {G : Type*} [Add G] (U : Set G)
    [DecidablePred (· ∈ U)] (d : G) (w : G) : G :=
  if w ∈ U then w + d else w

/-- On the cylinder, `cylinderShift` translates by `d`. -/
theorem cylinderShift_apply_of_mem {G : Type*} [Add G] {U : Set G}
    [DecidablePred (· ∈ U)] {d w : G} (hw : w ∈ U) :
    cylinderShift U d w = w + d := if_pos hw

/-- Off the cylinder, `cylinderShift` is the identity. -/
theorem cylinderShift_apply_of_not_mem {G : Type*} [Add G] {U : Set G}
    [DecidablePred (· ∈ U)] {d w : G} (hw : w ∉ U) :
    cylinderShift U d w = w := if_neg hw

/-- The cylinder substitution is a bijection whenever the cylinder is
invariant under translation by `d`. -/
theorem cylinderShift_bijective {G : Type*} [AddCommGroup G] (U : Set G)
    [DecidablePred (· ∈ U)] (d : G)
    (hinv : ∀ w, w ∈ U ↔ w + d ∈ U) :
    Function.Bijective (cylinderShift U d) := by
  constructor
  · intro x y hxy
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
    · rw [cylinderShift_apply_of_mem hx,
        cylinderShift_apply_of_mem hy] at hxy
      exact add_right_cancel hxy
    · rw [cylinderShift_apply_of_mem hx,
        cylinderShift_apply_of_not_mem hy] at hxy
      exact absurd (hxy ▸ (hinv x).mp hx) hy
    · rw [cylinderShift_apply_of_not_mem hx,
        cylinderShift_apply_of_mem hy] at hxy
      exact absurd (hxy.symm ▸ (hinv y).mp hy) hx
    · rwa [cylinderShift_apply_of_not_mem hx,
        cylinderShift_apply_of_not_mem hy] at hxy
  · intro y
    by_cases hy : y ∈ U
    · have hyd : y - d ∈ U := by
        have h := hinv (y - d)
        have he : y - d + d = y := by abel
        rw [he] at h
        exact h.mpr hy
      exact ⟨y - d, by rw [cylinderShift_apply_of_mem hyd]; abel⟩
    · exact ⟨y, cylinderShift_apply_of_not_mem hy⟩

/-! ## Part A: permutation-row schedules and free RF1 -/

/-- A standard-lift schedule whose every layer row is a permutation of the
direction set. -/
def rowSchedule {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1))) :
    RootFlatSchedule (TorusColor (n + 1)) (TorusDirection (n + 1))
      (RootState n m) m :=
  RootFlatCycle.schedule (fun t w c => rowAt t w c)

@[simp] theorem rowSchedule_dir_apply {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (w : RootState n m) (c : TorusColor (n + 1)) :
    (rowSchedule rowAt).dir t w c = rowAt t w c := rfl

/-- The layer map of a row schedule is the state-dependent translation by
the step vector of the read direction. -/
theorem rowSchedule_layerMap_apply {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1)) (w : RootState n m) :
    (rowSchedule rowAt).layerMap t c w = w + stepVec (rowAt t w c) := by
  rw [← rootStep_eq_add]
  rfl

/-- **RF1 is free** for a row schedule: every row is a permutation. -/
theorem rowSchedule_rowLatin {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1))) :
    (rowSchedule rowAt).rowLatin := by
  intro t w
  exact (rowAt t w).bijective

/-! ## Part B: RF2 criteria -/

/-- **RF2, constant case**: a layer whose row is constantly a fixed
permutation `ρ` is the translation by `stepVec (ρ c)`, hence bijective. -/
theorem layerMap_bijective_of_constant {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hconst : ∀ w, rowAt t w = ρ) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  have hlayer : (rowSchedule rowAt).layerMap t c =
      fun w : RootState n m => w + stepVec (ρ c) := by
    funext w
    rw [rowSchedule_layerMap_apply, hconst w]
  rw [hlayer]
  exact (Equiv.addRight (stepVec (ρ c))).bijective

/-- **RF2, cylinder-substitution case** (the paper's RF2 ribbon identity):
if a layer row equals `ρ` off a cylinder `U` and `σ` on `U`, and `U` is
invariant under translation by the difference vector
`stepVec (σ c) - stepVec (ρ c)`, then the layer map of color `c` is
bijective.  It factors as translation by `stepVec (ρ c)` after the cylinder
substitution by the difference vector. -/
theorem layerMap_bijective_of_cylinder {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ σ : Equiv.Perm (Fin (n + 1))) (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = σ)
    (hinv : ∀ w, w ∈ U ↔
      (w + (stepVec (σ c) - stepVec (ρ c))) ∈ U) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  classical
  have key : (rowSchedule rowAt).layerMap t c =
      (fun w : RootState n m => w + stepVec (ρ c)) ∘
        cylinderShift U (stepVec (σ c) - stepVec (ρ c)) := by
    funext w
    simp only [Function.comp_apply]
    by_cases hw : w ∈ U
    · rw [cylinderShift_apply_of_mem hw, rowSchedule_layerMap_apply,
        hon w hw]
      abel
    · rw [cylinderShift_apply_of_not_mem hw,
        rowSchedule_layerMap_apply, hoff w hw]
  rw [key]
  exact (Equiv.addRight (stepVec (ρ c))).bijective.comp
    (cylinderShift_bijective U _ hinv)

/-- Convenience corollary of the cylinder criterion for colors not moved by
the substitution (`σ c = ρ c`): the invariance hypothesis is trivial. -/
theorem layerMap_bijective_of_cylinder_unmoved {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ σ : Equiv.Perm (Fin (n + 1))) (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = σ)
    (hc : σ c = ρ c) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  refine layerMap_bijective_of_cylinder rowAt t c ρ σ U hoff hon ?_
  intro w
  rw [hc]
  simp

/-! ## Part C: swap-on-cylinder rows and per-layer plans -/

/-- **RF2, swap-on-cylinder case**: if the substituted row is
`σ = ρ.trans (Equiv.swap α β)`, the only moved colors are `ρ.symm α` and
`ρ.symm β` with difference vectors `±(stepVec β - stepVec α)`, so the single
invariance hypothesis `∀ w, w ∈ U ↔ w + (stepVec β - stepVec α) ∈ U`
suffices for ALL colors at once. -/
theorem layerMap_bijective_of_swap_cylinder {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (ρ σ : Equiv.Perm (Fin (n + 1))) (α β : Fin (n + 1))
    (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = σ)
    (hswap : σ = ρ.trans (Equiv.swap α β))
    (hinv : ∀ w, w ∈ U ↔ (w + (stepVec β - stepVec α)) ∈ U) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c) := by
  intro c
  refine layerMap_bijective_of_cylinder rowAt t c ρ σ U hoff hon ?_
  have hσc : σ c = Equiv.swap α β (ρ c) := by
    rw [hswap, Equiv.trans_apply]
  by_cases hα : ρ c = α
  · have hb : σ c = β := by rw [hσc, hα, Equiv.swap_apply_left]
    rw [hb, hα]
    exact hinv
  · by_cases hβ : ρ c = β
    · have ha : σ c = α := by rw [hσc, hβ, Equiv.swap_apply_right]
      rw [ha, hβ]
      intro w
      have h := mem_iff_add_neg_mem hinv w
      rwa [neg_sub] at h
    · have hfix : σ c = ρ c := by
        rw [hσc, Equiv.swap_apply_of_ne_of_ne hα hβ]
      rw [hfix]
      intro w
      simp

/-- Per-layer RF2 descriptor for a permutation-row schedule: at each layer
the row is either a fixed permutation (`const ρ`) or a base permutation `ρ`
with the transposition `α ↔ β` substituted on a cylinder `U`
(`swapCylinder ρ α β U`). -/
inductive LayerDesc (n m : Nat) where
  /-- The row at this layer is constantly `ρ`. -/
  | const (ρ : Equiv.Perm (Fin (n + 1)))
  /-- The row is `ρ` off `U` and `ρ.trans (Equiv.swap α β)` on `U`. -/
  | swapCylinder (ρ : Equiv.Perm (Fin (n + 1))) (α β : Fin (n + 1))
      (U : Set (RootState n m))

/-- The RF2 obligations tying a layer descriptor to the actual row family
at layer `t`: a constant descriptor must match everywhere; a swap-cylinder
descriptor must match `ρ` off `U` and the swapped row on `U`, with `U`
invariant under translation by `stepVec β - stepVec α`. -/
def LayerDesc.Matches {n m : Nat}
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) : LayerDesc n m → Prop
  | const ρ => ∀ w, rowAt t w = ρ
  | swapCylinder ρ α β U =>
      (∀ w ∉ U, rowAt t w = ρ) ∧
        (∀ w ∈ U, rowAt t w = ρ.trans (Equiv.swap α β)) ∧
        ∀ w, w ∈ U ↔ (w + (stepVec β - stepVec α)) ∈ U

/-- **Bundled RF2**: if every layer has a matching descriptor — constant or
swap-on-cylinder with its invariance hypothesis — the whole row schedule is
`layerBijective`. -/
theorem rowSchedule_layerBijective_of_plan {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (plan : ZMod m → LayerDesc n m)
    (hplan : ∀ t, (plan t).Matches rowAt t) :
    (rowSchedule rowAt).layerBijective := by
  intro t c
  have h := hplan t
  cases hp : plan t with
  | const ρ =>
      rw [hp] at h
      exact layerMap_bijective_of_constant rowAt t c ρ h
  | swapCylinder ρ α β U =>
      rw [hp] at h
      exact layerMap_bijective_of_swap_cylinder rowAt t ρ
        (ρ.trans (Equiv.swap α β)) α β U h.1 h.2.1 rfl h.2.2 c

/-! ## Chart-row instantiations (`n = 2*b`, dimension `2*b+1`)

The endpoint chart rows of `EvenV11.V28Hard.EndpointChart` are exactly the
two descriptor shapes: completion rows `C_h` (and the neutral row `N = C_0`)
are constant rows, while the exchanges `X_i` and the reset `R` are
transpositions substituted on a cylinder. -/

/-- Chart completion layer: a layer whose row is constantly `C_h` (this also
covers the neutral row `N = C_0`) is RF2-bijective. -/
theorem layerMap_bijective_of_completionRow {b m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (c : TorusColor (2 * b + 1)) (h : ZMod (2 * b + 1))
    (hconst : ∀ w, rowAt t w = EndpointChart.completionRow b h) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  layerMap_bijective_of_constant rowAt t c
    (EndpointChart.completionRow b h) hconst

/-- Chart exchange layer: a layer that substitutes `ρ.trans (X_i)` for `ρ`
on a cylinder `U` invariant under translation by
`stepVec p_{i+1}⁺ - stepVec τ_i` is RF2-bijective in every color. -/
theorem layerMap_bijective_of_exchangeRow {b m : Nat} [NeZero m]
    (hb : 4 ≤ b)
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (i : Fin 3) (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U,
      rowAt t w = ρ.trans (EndpointChart.exchangeRow hb i))
    (hinv : ∀ w, w ∈ U ↔
      (w + (stepVec (EndpointChart.exchangePlusIdx hb i)
        - stepVec (EndpointChart.exchangeTauIdx hb i))) ∈ U) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  layerMap_bijective_of_swap_cylinder rowAt t ρ
    (ρ.trans (EndpointChart.exchangeRow hb i))
    (EndpointChart.exchangeTauIdx hb i)
    (EndpointChart.exchangePlusIdx hb i) U hoff hon rfl hinv

/-- Chart reset layer: a layer that substitutes `ρ.trans R` for `ρ` on a
cylinder `U` invariant under translation by `stepVec p₂⁻ - stepVec p₁⁻` is
RF2-bijective in every color. -/
theorem layerMap_bijective_of_resetRow {b m : Nat} [NeZero m]
    (hb : 4 ≤ b)
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = ρ.trans (EndpointChart.resetRow hb))
    (hinv : ∀ w, w ∈ U ↔
      (w + (stepVec (EndpointChart.resetSecondIdx hb)
        - stepVec (EndpointChart.resetFirstIdx hb))) ∈ U) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  layerMap_bijective_of_swap_cylinder rowAt t ρ
    (ρ.trans (EndpointChart.resetRow hb))
    (EndpointChart.resetFirstIdx hb)
    (EndpointChart.resetSecondIdx hb) U hoff hon rfl hinv

/-- Layer descriptor of a chart completion layer `C_h` (covers `N = C_0`). -/
def completionDesc (b m : Nat) (h : ZMod (2 * b + 1)) :
    LayerDesc (2 * b) m :=
  .const (EndpointChart.completionRow b h)

/-- Layer descriptor of a chart exchange layer `X_i` substituted on the
cylinder `U` over the base row `ρ`. -/
def exchangeDesc {b m : Nat} (hb : 4 ≤ b) (i : Fin 3)
    (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m)) : LayerDesc (2 * b) m :=
  .swapCylinder ρ (EndpointChart.exchangeTauIdx hb i)
    (EndpointChart.exchangePlusIdx hb i) U

/-- Layer descriptor of a chart reset layer `R` substituted on the cylinder
`U` over the base row `ρ`. -/
def resetDesc {b m : Nat} (hb : 4 ≤ b)
    (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m)) : LayerDesc (2 * b) m :=
  .swapCylinder ρ (EndpointChart.resetFirstIdx hb)
    (EndpointChart.resetSecondIdx hb) U

/-- A constantly-`C_h` layer matches its completion descriptor. -/
theorem completionDesc_matches {b m : Nat}
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (h : ZMod (2 * b + 1))
    (hconst : ∀ w, rowAt t w = EndpointChart.completionRow b h) :
    (completionDesc b m h).Matches rowAt t :=
  hconst

/-- A `ρ`-with-`X_i`-on-`U` layer matches its exchange descriptor. -/
theorem exchangeDesc_matches {b m : Nat} (hb : 4 ≤ b)
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (i : Fin 3) (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U,
      rowAt t w = ρ.trans (EndpointChart.exchangeRow hb i))
    (hinv : ∀ w, w ∈ U ↔
      (w + (stepVec (EndpointChart.exchangePlusIdx hb i)
        - stepVec (EndpointChart.exchangeTauIdx hb i))) ∈ U) :
    (exchangeDesc hb i ρ U).Matches rowAt t :=
  ⟨hoff, hon, hinv⟩

/-- A `ρ`-with-`R`-on-`U` layer matches its reset descriptor. -/
theorem resetDesc_matches {b m : Nat} (hb : 4 ≤ b)
    (rowAt : ZMod m → RootState (2 * b) m →
      Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (ρ : Equiv.Perm (Fin (2 * b + 1)))
    (U : Set (RootState (2 * b) m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = ρ.trans (EndpointChart.resetRow hb))
    (hinv : ∀ w, w ∈ U ↔
      (w + (stepVec (EndpointChart.resetSecondIdx hb)
        - stepVec (EndpointChart.resetFirstIdx hb))) ∈ U) :
    (resetDesc hb ρ U).Matches rowAt t :=
  ⟨hoff, hon, hinv⟩

end EndpointRowSchedule
end V28Hard
end EvenV11
