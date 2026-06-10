import EvenV11.V28Hard.EndpointRowSchedule

/-!
# Hard slot H6 (E6d): the localized-`C_h` row obstruction (paper erratum W2)

Machine-checked negative theorems pinning the author-confirmed paper erratum
**W2** (`docs/QUESTION_W2_COMPLETION_FIBER_20260610.md`, status note of
2026-06-10; `docs/E6_DESIGN_20260610.md` §4.2): in
`even_modulus_directed_tori.tex` v28, `subtex/endpoint_successor.tex`, the
construction `def:lifted-completion-fiber` (:265–281) +
`lem:completion-fiber-bijectivity` (:283–298) + the `C_h` row of
`lem:endpoint-local-row-realization` (:300–335) substitutes the FULL cyclic
completion row `C_h` on a proper nonempty fiber `U` over a constant base
row.  This necessarily breaks per-color layer bijectivity (RF2): the lifted
fiber pins old-section/terminal coordinates whose reads `C_h` also shifts,
so some color's difference vector moves a pinned coordinate and the exact
two-valued criterion (★) `U + (e_{σ(c)} − e_{ρ(c)}) = U` fails.  The
image-disjointness argument printed in `lem:completion-fiber-bijectivity`
separates *sites*, not the colliding (in-fiber, out-of-fiber) source pairs
along the pinned directions.  The author has confirmed the erratum; the
formalization therefore routes completion carries through two-color swaps
(`EndpointRowSchedule.layerMap_bijective_of_swap_cylinder` over the
`w 0`-free cylinder family, design Q3 route) and never through localized
`C_h` rows — constant `C_h` layers (`EndpointRowSchedule.completionDesc`)
remain RF2-legal.

Contents:

* **Part A — necessity** (`cylinder_invariance_of_layerMap_bijective`): the
  exact converse of E5's sufficiency `layerMap_bijective_of_cylinder`.  For
  a two-valued row (`ρ` off `U`, `σ` on `U`), bijectivity of the color-`c`
  layer map FORCES `U` to be invariant under translation by
  `stepVec (σ c) - stepVec (ρ c)`: injectivity kills the cross collision
  pair `(w, w + d)`, giving `U + d ⊆ U`, and finiteness upgrades the
  inclusion to equality.  `layerMap_bijective_iff_cylinder_invariance`
  records (★) as an exact equivalence.
* **Part B — the pinned-coordinate obstruction**
  (`cylinder_fixing_moved_coordinate_not_invariant`,
  `layerMap_not_bijective_of_pinned_coordinate`,
  `completionRow_substitution_not_bijective`): a nonempty cylinder pinning
  a coordinate moved by some color's difference vector is never invariant,
  so that color's layer map is never bijective — parametrically in
  `(b, m, h)`, for any base row and any pinned site (the W2 content: the
  obstruction is site-independent).
* **Part C — the `b = 4, m = 4` anchor** (`b4_collision`,
  `b4_completion_fiber_substitution_not_bijective`): the smallest endpoint
  instance.  `b4FiberU` is the lifted-fiber-shaped cylinder pinning the
  terminal block `q = (w 1, w 2)` and the parent block `y = (w 3, w 5, w 7)`
  to the zero site (a representative `c_ν`; Part B shows the pinned values
  are immaterial) while freeing the minus lanes `w 4, w 6` and the
  `τ₀`-slack `w 0`.  Substituting `C₁` over the neutral base row `N` on
  this fiber, color `t₀` reads `τ₁` (pinned) on the fiber and `τ₀` (free)
  off it; the EXPLICIT collision pair `b4Witness = 0`,
  `b4Witness' = b4Witness + (e_{τ₁} − e_{τ₀})` has equal layer-map images,
  refuting injectivity — single-point `decide`s only.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace EndpointChRowObstruction

open Shared StandardRootFlatLift EndpointRowSchedule

/-! ## Part A — the two-valued necessity direction -/

/-- **Necessity of the (★) invariance** (converse of E5's
`layerMap_bijective_of_cylinder`): if a layer row equals `ρ` off `U` and `σ`
on `U`, and the color-`c` layer map is bijective, then `U` must be invariant
under translation by the difference vector `stepVec (σ c) - stepVec (ρ c)`.
Injectivity forces `U + d ⊆ U` (else `(w, w + d)` is a collision pair with
common image `w + stepVec (σ c)`), and finiteness of the root-state space
upgrades the inclusion to the full invariance. -/
theorem cylinder_invariance_of_layerMap_bijective {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ σ : Equiv.Perm (Fin (n + 1))) (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ) (hon : ∀ w ∈ U, rowAt t w = σ)
    (hbij : Function.Bijective ((rowSchedule rowAt).layerMap t c)) :
    ∀ w, w ∈ U ↔ (w + (stepVec (σ c) - stepVec (ρ c))) ∈ U := by
  classical
  have hmaps : ∀ w ∈ U, w + (stepVec (σ c) - stepVec (ρ c)) ∈ U := by
    intro w hw
    by_contra hwd
    have h1 : (rowSchedule rowAt).layerMap t c w = w + stepVec (σ c) := by
      rw [rowSchedule_layerMap_apply, hon w hw]
    have h2 : (rowSchedule rowAt).layerMap t c
        (w + (stepVec (σ c) - stepVec (ρ c))) = w + stepVec (σ c) := by
      rw [rowSchedule_layerMap_apply, hoff _ hwd]
      abel
    have hcol : w + (stepVec (σ c) - stepVec (ρ c)) = w :=
      hbij.injective (h2.trans h1.symm)
    rw [hcol] at hwd
    exact hwd hw
  have hfin : U.Finite := Set.toFinite U
  have hbijOn :
      Set.BijOn (fun w => w + (stepVec (σ c) - stepVec (ρ c))) U U :=
    (hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp
      fun x _ y _ hxy => add_right_cancel hxy
  intro w
  refine ⟨hmaps w, fun hwd => ?_⟩
  obtain ⟨u, hu, hue⟩ := hbijOn.surjOn hwd
  have huw : u = w := add_right_cancel hue
  exact huw ▸ hu

/-- **The exact two-valued RF2 criterion (★)**: for a two-valued row (`ρ`
off `U`, `σ` on `U`), bijectivity of the color-`c` layer map is EQUIVALENT
to invariance of `U` under the difference-vector translation.  Sufficiency
is E5's `layerMap_bijective_of_cylinder`; necessity is the theorem above.
This is the criterion against which `lem:completion-fiber-bijectivity`
fails (W2). -/
theorem layerMap_bijective_iff_cylinder_invariance {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ σ : Equiv.Perm (Fin (n + 1))) (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ) (hon : ∀ w ∈ U, rowAt t w = σ) :
    Function.Bijective ((rowSchedule rowAt).layerMap t c) ↔
      ∀ w, w ∈ U ↔ (w + (stepVec (σ c) - stepVec (ρ c))) ∈ U :=
  ⟨cylinder_invariance_of_layerMap_bijective rowAt t c ρ σ U hoff hon,
    layerMap_bijective_of_cylinder rowAt t c ρ σ U hoff hon⟩

/-! ## Part B — the pinned-coordinate obstruction (parametric W2) -/

/-- A nonempty set pinning coordinate `j` to the value `a` is not invariant
under translation by any vector `d` that moves coordinate `j`. -/
theorem cylinder_fixing_moved_coordinate_not_invariant {n m : Nat}
    {U : Set (RootState n m)} {j : Fin n} {a : ZMod m}
    (hpin : ∀ w ∈ U, w j = a) (hne : U.Nonempty)
    {d : RootState n m} (hd : d j ≠ 0) :
    ¬ ∀ w, w ∈ U ↔ (w + d) ∈ U := by
  intro hinv
  obtain ⟨w₀, hw₀⟩ := hne
  have h1 : w₀ j + d j = a := hpin _ ((hinv w₀).mp hw₀)
  rw [hpin w₀ hw₀] at h1
  exact hd (add_left_cancel (h1.trans (add_zero a).symm))

/-- The difference vector `stepVec β - stepVec α` moves coordinate `j`
whenever `β` steps `j` and `α` does not (and `1 < m`). -/
theorem stepVec_sub_apply_ne_zero {n m : Nat} (hm : 1 < m)
    {β α : Fin (n + 1)} {j : Fin n}
    (hβ : β = j.castSucc) (hα : α ≠ j.castSucc) :
    (stepVec β - stepVec α : RootState n m) j ≠ 0 := by
  haveI : Fact (1 < m) := ⟨hm⟩
  simp [Pi.sub_apply, stepVec, hβ, hα]

/-- **Parametric W2 obstruction**: a two-valued row over a nonempty cylinder
pinning a coordinate moved by color `c`'s difference vector fails RF2 in
color `c` — by necessity (Part A) plus the pinned-coordinate
non-invariance. -/
theorem layerMap_not_bijective_of_pinned_coordinate {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n + 1)))
    (t : ZMod m) (c : TorusColor (n + 1))
    (ρ σ : Equiv.Perm (Fin (n + 1))) (U : Set (RootState n m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ) (hon : ∀ w ∈ U, rowAt t w = σ)
    {j : Fin n} {a : ZMod m}
    (hpin : ∀ w ∈ U, w j = a) (hne : U.Nonempty)
    (hd : (stepVec (σ c) - stepVec (ρ c) : RootState n m) j ≠ 0) :
    ¬ Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  fun hbij =>
    cylinder_fixing_moved_coordinate_not_invariant hpin hne hd
      (cylinder_invariance_of_layerMap_bijective rowAt t c ρ σ U hoff hon
        hbij)

/-- **W2 for the chart completion rows, parametrically**: substituting the
full cyclic completion row `C_h` over ANY constant base row `ρ` on a
nonempty cylinder that pins a coordinate `j` shifted-into by some color
(`C_h (ρ c) = j.castSucc` while `ρ c ≠ j.castSucc`) makes that color's
layer map non-bijective.  In particular no pinned-value choice for the
lifted completion fiber can rescue `lem:completion-fiber-bijectivity`. -/
theorem completionRow_substitution_not_bijective {b m : Nat} [NeZero m]
    (hm : 1 < m)
    (rowAt : ZMod m → RootState (2 * b) m → Equiv.Perm (Fin (2 * b + 1)))
    (t : ZMod m) (c : TorusColor (2 * b + 1)) (h : ZMod (2 * b + 1))
    (ρ : Equiv.Perm (Fin (2 * b + 1))) (U : Set (RootState (2 * b) m))
    (hoff : ∀ w ∉ U, rowAt t w = ρ)
    (hon : ∀ w ∈ U, rowAt t w = ρ.trans (EndpointChart.completionRow b h))
    {j : Fin (2 * b)} {a : ZMod m}
    (hpin : ∀ w ∈ U, w j = a) (hne : U.Nonempty)
    (hread : EndpointChart.completionRow b h (ρ c) = j.castSucc)
    (hbase : ρ c ≠ j.castSucc) :
    ¬ Function.Bijective ((rowSchedule rowAt).layerMap t c) :=
  layerMap_not_bijective_of_pinned_coordinate rowAt t c ρ
    (ρ.trans (EndpointChart.completionRow b h)) U hoff hon hpin hne
    (stepVec_sub_apply_ne_zero hm
      (by rw [Equiv.trans_apply]; exact hread) hbase)

/-! ## Part C — the `b = 4, m = 4` anchor (concrete erratum witness)

Coordinates of `w : RootState 8 4` in the Lean chart (E1):
`w 0 = τ₀`-slack, `w 1 = τ₁ (q₁)`, `w 2 = τ₂ (q₂)`, `w 3 = p₁⁺ (y₀)`,
`w 4 = p₁⁻ (z₀)`, `w 5 = p₂⁺ (y₁)`, `w 6 = p₂⁻ (z₁)`, `w 7 = p₃⁺ (y₂)`;
direction `8 = Fin.last = p₃⁻` is the zero step. -/

/-- The `b = 4` lifted-completion-fiber-shaped cylinder: pin the terminal
block `q = (w 1, w 2)` and the parent block `y = (w 3, w 5, w 7)` to the
zero site (a representative `c_ν`; the obstruction is pinned-value
independent by `completionRow_substitution_not_bijective`), free the minus
lanes `w 4, w 6` and the `τ₀`-slack `w 0` (design §1.2 fiber shape). -/
def b4FiberU : Set (RootState 8 4) :=
  {w | w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 5 = 0 ∧ w 7 = 0}

instance : DecidablePred (· ∈ b4FiberU) := fun w =>
  inferInstanceAs
    (Decidable (w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 5 = 0 ∧ w 7 = 0))

/-- The W2 row family at `b = 4, m = 4`: the full cyclic completion row
`C₁` substituted on the lifted fiber over the neutral base row `N` (shift
`h = 1`, the paper's first completion row), at every layer. -/
def b4Row (_t : ZMod 4) (w : RootState 8 4) : Equiv.Perm (Fin 9) :=
  if w ∈ b4FiberU then EndpointChart.completionRow 4 1
  else EndpointChart.neutralRow 4

/-- Off the fiber, the row is the neutral base row `N`. -/
theorem b4Row_of_not_mem (t : ZMod 4) {w : RootState 8 4}
    (hw : w ∉ b4FiberU) : b4Row t w = EndpointChart.neutralRow 4 :=
  if_neg hw

/-- On the fiber, the row is the full cyclic completion row `C₁`. -/
theorem b4Row_of_mem (t : ZMod 4) {w : RootState 8 4}
    (hw : w ∈ b4FiberU) : b4Row t w = EndpointChart.completionRow 4 1 :=
  if_pos hw

/-- First collision witness: the zero state (a point of the fiber). -/
def b4Witness : RootState 8 4 := fun _ => 0

/-- Second collision witness: the fiber point translated by the difference
vector `e_{τ₁} − e_{τ₀}` of the violating color `t₀` (so `w 0 = -1 = 3`,
`w 1 = 1`); it lies OFF the fiber because the pinned terminal coordinate
`τ₁` moved. -/
def b4Witness' : RootState 8 4 :=
  fun i => if i = 0 then 3 else if i = 1 then 1 else 0

/-- `b4Witness` lies on the fiber. -/
theorem b4Witness_mem : b4Witness ∈ b4FiberU := by decide

/-- `b4Witness'` lies off the fiber (its pinned coordinate `τ₁` is `1`). -/
theorem b4Witness'_not_mem : b4Witness' ∉ b4FiberU := by decide

/-- The fiber is a PROPER subset: `b4Witness'` is outside. -/
theorem b4FiberU_ne_univ : b4FiberU ≠ Set.univ := fun hU =>
  b4Witness'_not_mem (hU.symm ▸ Set.mem_univ b4Witness')

/-- The two witnesses differ exactly by the difference vector
`stepVec τ₁ - stepVec τ₀` of color `t₀` (on-fiber read `C₁ 0 = τ₁`,
off-fiber read `N 0 = τ₀`). -/
theorem b4Witness'_eq_add_diff :
    b4Witness' = b4Witness + (stepVec 1 - stepVec 0) := by decide

/-- **The explicit W2 collision at `b = 4, m = 4`** (concrete erratum
anchor for `lem:completion-fiber-bijectivity`): at layer `0`, color `t₀`'s
layer map sends the in-fiber witness (read `τ₁`, image `0 + e_{τ₁}`) and
the off-fiber witness (read `τ₀`, image `(e_{τ₁} − e_{τ₀}) + e_{τ₀}`) to
the SAME state, yet the witnesses differ. -/
theorem b4_collision :
    (rowSchedule b4Row).layerMap 0 0 b4Witness =
        (rowSchedule b4Row).layerMap 0 0 b4Witness' ∧
      b4Witness ≠ b4Witness' := by decide

/-- Color `t₀`'s layer map of the substituted `C₁` layer is not bijective. -/
theorem b4_layerMap_color_t0_not_bijective :
    ¬ Function.Bijective ((rowSchedule b4Row).layerMap 0 0) := fun hbij =>
  b4_collision.2 (hbij.injective b4_collision.1)

/-- The same conclusion through the parametric route (Part B, no point
computation): color `t₀`'s difference vector moves the pinned terminal
coordinate `τ₁`, so necessity of (★) refutes bijectivity. -/
theorem b4_layerMap_color_t0_not_bijective' :
    ¬ Function.Bijective ((rowSchedule b4Row).layerMap 0 0) :=
  completionRow_substitution_not_bijective (b := 4) (m := 4)
    (by omega) b4Row 0 0 1 (EndpointChart.neutralRow 4) b4FiberU
    (fun _ hw => b4Row_of_not_mem 0 hw)
    (fun _ hw => by rw [b4Row_of_mem 0 hw]; exact Equiv.ext fun _ => rfl)
    (j := (1 : Fin 8)) (a := (0 : ZMod 4)) (fun _ hw => hw.1)
    ⟨b4Witness, b4Witness_mem⟩ (by decide) (by decide)

/-- **W2 at `b = 4, m = 4`** (smallest endpoint instance): substituting the
full cyclic completion row `C₁` on the lifted-fiber-shaped proper nonempty
cylinder `b4FiberU` over the neutral base row fails layer bijectivity for
at least one color (namely `t₀`).  Concrete erratum anchor for
`lem:completion-fiber-bijectivity`; the author-confirmed reading is that
the printed image-disjointness argument does not survive the exact
two-valued criterion (★). -/
theorem b4_completion_fiber_substitution_not_bijective :
    ¬ ∀ c : TorusColor 9,
      Function.Bijective ((rowSchedule b4Row).layerMap 0 c) := fun hall =>
  b4_layerMap_color_t0_not_bijective (hall 0)

/-- A fortiori, the substituted schedule fails the full RF2 predicate. -/
theorem b4_not_layerBijective :
    ¬ (rowSchedule b4Row).layerBijective := fun hbij =>
  b4_layerMap_color_t0_not_bijective (hbij 0 0)

end EndpointChRowObstruction
end V28Hard
end EvenV11
