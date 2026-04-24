import D5Odd.Main

namespace D5Odd

abbrev Vertex5 (m : Nat) := Vec5 m

def finMAddNat {m : Nat} [NeZero m] (i : Fin m) (k : Nat) : Fin m :=
  ⟨(i.val + k) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

def layerOf {m : Nat} [NeZero m] (x : Vertex5 m) : Fin m :=
  ⟨(sum5 m x).val, ZMod.val_lt (sum5 m x)⟩

theorem sum5_sub (m : Nat) (x y : Vec5 m) :
    sum5 m (x - y) = sum5 m x - sum5 m y := by
  simp [sum5, Pi.sub_apply, Finset.sum_sub_distrib]

def rootAtLayer {m : Nat} [NeZero m] (x : Vertex5 m) : ARoot5 m :=
  ⟨x - (((layerOf x).val : Nat) : ZMod m) • e5 m 4, by
    unfold Root5
    calc
      sum5 m (x - (((layerOf x).val : Nat) : ZMod m) • e5 m 4)
          = sum5 m x -
              sum5 m ((((layerOf x).val : Nat) : ZMod m) • e5 m 4) := by
            rw [sum5_sub]
      _ = sum5 m x - (((layerOf x).val : Nat) : ZMod m) * sum5 m (e5 m 4) := by
            rw [sum5_smul]
      _ = sum5 m x - (((layerOf x).val : Nat) : ZMod m) := by
            rw [sum5_e5]
            ring
      _ = 0 := by
            have hval :
                (((sum5 m x).val : Nat) : ZMod m) = sum5 m x :=
              ZMod.natCast_zmod_val (sum5 m x)
            simp [layerOf, hval]⟩

def torusOfLayerRoot {m : Nat} (t : Fin m) (w : ARoot5 m) : Vertex5 m :=
  w.1 + (((t.val : Nat) : ZMod m) • e5 m 4)

theorem layerOf_torusOfLayerRoot {m : Nat} [NeZero m] (t : Fin m) (w : ARoot5 m) :
    layerOf (torusOfLayerRoot t w) = t := by
  apply Fin.ext
  have hsum :
      sum5 m (torusOfLayerRoot t w) = (((t.val : Nat) : ZMod m)) := by
    unfold torusOfLayerRoot
    calc
      sum5 m (w.1 + (((t.val : Nat) : ZMod m) • e5 m 4))
          = sum5 m w.1 + sum5 m ((((t.val : Nat) : ZMod m) • e5 m 4)) := by
            rw [sum5_add]
      _ = 0 + (((t.val : Nat) : ZMod m) * sum5 m (e5 m 4)) := by
            rw [w.2, sum5_smul]
      _ = (((t.val : Nat) : ZMod m)) := by
            rw [sum5_e5]
            ring
  change (sum5 m (torusOfLayerRoot t w)).val = t.val
  rw [hsum]
  exact ZMod.val_natCast_of_lt t.isLt

theorem rootAtLayer_torusOfLayerRoot {m : Nat} [NeZero m] (t : Fin m) (w : ARoot5 m) :
    rootAtLayer (torusOfLayerRoot t w) = w := by
  apply Subtype.ext
  ext i
  change
    (torusOfLayerRoot t w -
        (((layerOf (torusOfLayerRoot t w)).val : Nat) : ZMod m) • e5 m 4) i = w.1 i
  rw [layerOf_torusOfLayerRoot t w]
  by_cases hi : i = 4
  · subst hi
    simp [torusOfLayerRoot, e5]
  · simp [torusOfLayerRoot, e5, hi]

theorem torusOfLayerRoot_layerOf_rootAtLayer {m : Nat} [NeZero m] (x : Vertex5 m) :
    torusOfLayerRoot (layerOf x) (rootAtLayer x) = x := by
  ext i
  change
    ((x - (((layerOf x).val : Nat) : ZMod m) • e5 m 4) +
        (((layerOf x).val : Nat) : ZMod m) • e5 m 4) i = x i
  simp

def layerRootEquiv {m : Nat} [NeZero m] : (Fin m × ARoot5 m) ≃ Vertex5 m where
  toFun tw := torusOfLayerRoot tw.1 tw.2
  invFun x := (layerOf x, rootAtLayer x)
  left_inv := by
    rintro ⟨t, w⟩
    simp [layerOf_torusOfLayerRoot, rootAtLayer_torusOfLayerRoot]
  right_inv := torusOfLayerRoot_layerOf_rootAtLayer

def torusColorStep {m : Nat} [NeZero m] (F : LayerSchedule m) (c : Color)
    (x : Vertex5 m) : Vertex5 m :=
  x + e5 m (F.dir (layerOf x) c (rootAtLayer x).1)

def layerRootStep {m : Nat} [NeZero m] (F : LayerSchedule m) (c : Color)
    (tw : Fin m × ARoot5 m) : Fin m × ARoot5 m :=
  (finMAddNat tw.1 1, layerMap F tw.1 c tw.2)

theorem finMAddNat_one_eq_finRotate {m : Nat} [NeZero m] (t : Fin m) :
    finMAddNat t 1 = finRotate m t := by
  apply Fin.ext
  have hrot := finRotate_iterate_val (n := m) (i := t) (k := 1)
  simpa [finMAddNat] using hrot.symm

theorem finMAddNat_one_bijective {m : Nat} [NeZero m] :
    Function.Bijective fun t : Fin m => finMAddNat t 1 := by
  simpa [finMAddNat_one_eq_finRotate] using (finRotate m).bijective

theorem layerRootStep_bijective_of_exactCover {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hF : IsLayerExactCover F) (c : Color) :
    Function.Bijective (layerRootStep F c) := by
  constructor
  · intro x y hxy
    rcases x with ⟨tx, wx⟩
    rcases y with ⟨ty, wy⟩
    have ht : tx = ty :=
      finMAddNat_one_bijective.1 (congrArg Prod.fst hxy)
    subst ty
    have hw :
        layerMap F tx c wx = layerMap F tx c wy := by
      simpa [layerRootStep] using congrArg Prod.snd hxy
    exact Prod.ext rfl ((layerMap_bijective_of_exactCover hF tx c).1 hw)
  · intro y
    rcases y with ⟨ty, wy⟩
    rcases finMAddNat_one_bijective.2 ty with ⟨tx, htx⟩
    rcases (layerMap_bijective_of_exactCover hF tx c).2 wy with ⟨wx, hwx⟩
    refine ⟨(tx, wx), ?_⟩
    ext <;> simp [layerRootStep, htx, hwx]

theorem single_cycle_of_layer_zero_return_cover {m : Nat} [NeZero m]
    {beta : Type*} (S : Fin m × beta -> Fin m × beta) (R : beta -> beta)
    (hS : Function.Bijective S)
    (hreturn : forall w : beta, S^[m] ((0 : Fin m), w) = ((0 : Fin m), R w))
    (hR : IsSingleCycleMap R)
    (hcover : forall x : Fin m × beta, exists w : beta,
      S^[x.1.val] ((0 : Fin m), w) = x) :
    IsSingleCycleMap S := by
  have hreturn_iter :
      forall n : Nat, forall w : beta,
        S^[n * m] ((0 : Fin m), w) = ((0 : Fin m), R^[n] w) := by
    intro n
    induction n with
    | zero =>
        intro w
        simp
    | succ n ih =>
        intro w
        calc
          S^[(n + 1) * m] ((0 : Fin m), w)
              = S^[n * m + m] ((0 : Fin m), w) := by
                  congr 1
                  ring
          _ = S^[n * m] (S^[m] ((0 : Fin m), w)) := by
                  rw [Function.iterate_add_apply]
          _ = S^[n * m] ((0 : Fin m), R w) := by
                  rw [hreturn]
          _ = ((0 : Fin m), R^[n] (R w)) := ih (R w)
          _ = ((0 : Fin m), R^[n + 1] w) := by
                  rw [Function.iterate_succ_apply]
  refine ⟨hS, ?_⟩
  intro x y
  rcases hcover x with ⟨a, hx⟩
  rcases hcover y with ⟨b, hy⟩
  let r := x.1.val
  let s := y.1.val
  by_cases hrs : r <= s
  · rcases hR.2 a b with ⟨q, hq⟩
    refine ⟨q * m + (s - r), ?_⟩
    rw [← hx, ← hy]
    calc
      S^[q * m + (s - r)] (S^[r] ((0 : Fin m), a))
          = S^[q * m + s] ((0 : Fin m), a) := by
              rw [← Function.iterate_add_apply]
              congr 1
              omega
      _ = S^[s + q * m] ((0 : Fin m), a) := by
              congr 1
              omega
      _ = S^[s] (S^[q * m] ((0 : Fin m), a)) := by
              rw [Function.iterate_add_apply]
      _ = S^[s] ((0 : Fin m), R^[q] a) := by
              rw [hreturn_iter]
      _ = S^[s] ((0 : Fin m), b) := by
              rw [hq]
  · have hsr : s < r := by omega
    have hrlt : r < m := by simp [r]
    have hslt : s < m := by simp [s]
    rcases hR.2 (R a) b with ⟨q, hq⟩
    have hq' : R^[q + 1] a = b := by
      rw [Function.iterate_succ_apply]
      exact hq
    refine ⟨q * m + (m + s - r), ?_⟩
    rw [← hx, ← hy]
    calc
      S^[q * m + (m + s - r)] (S^[r] ((0 : Fin m), a))
          = S^[(q + 1) * m + s] ((0 : Fin m), a) := by
              rw [← Function.iterate_add_apply]
              congr 1
              calc
                q * m + (m + s - r) + r = q * m + (m + s) := by
                  rw [Nat.add_assoc]
                  rw [Nat.sub_add_cancel]
                  omega
                _ = (q + 1) * m + s := by
                  ring
      _ = S^[s + (q + 1) * m] ((0 : Fin m), a) := by
              congr 1
              omega
      _ = S^[s] (S^[(q + 1) * m] ((0 : Fin m), a)) := by
              rw [Function.iterate_add_apply]
      _ = S^[s] ((0 : Fin m), R^[q + 1] a) := by
              rw [hreturn_iter]
      _ = S^[s] ((0 : Fin m), b) := by
              rw [hq']

theorem finMAddNat_zero_zero {m : Nat} [NeZero m] :
    finMAddNat (0 : Fin m) 0 = 0 := by
  apply Fin.ext
  simp [finMAddNat]

theorem finMAddNat_zero_add_one {m : Nat} [NeZero m] (n : Nat) :
    finMAddNat (finMAddNat (0 : Fin m) n) 1 = finMAddNat (0 : Fin m) (n + 1) := by
  apply Fin.ext
  simp [finMAddNat, Nat.mod_add_mod]

theorem finMAddNat_zero_card {m : Nat} [NeZero m] :
    finMAddNat (0 : Fin m) m = 0 := by
  apply Fin.ext
  simp [finMAddNat]

theorem finMAddNat_zero_val {m : Nat} [NeZero m] (t : Fin m) :
    finMAddNat (0 : Fin m) t.val = t := by
  apply Fin.ext
  simp [finMAddNat, Nat.mod_eq_of_lt t.isLt]

theorem map_finMAddNat_zero_range {m : Nat} [NeZero m] :
    (List.range m).map (fun k => finMAddNat (0 : Fin m) k) = List.finRange m := by
  apply List.ext_getElem
  · simp
  · intro n _ h2
    have hn : n < m := by simpa using h2
    apply Fin.ext
    simp [finMAddNat, Nat.mod_eq_of_lt hn]

theorem layerRootStep_iterate_zero_range {m : Nat} [NeZero m]
    (F : LayerSchedule m) (c : Color) (n : Nat) (w : ARoot5 m) :
    (layerRootStep F c)^[n] ((0 : Fin m), w) =
      (finMAddNat (0 : Fin m) n,
        (List.range n).foldl
          (fun x k => layerMap F (finMAddNat (0 : Fin m) k) c x) w) := by
  induction n with
  | zero =>
      simp [finMAddNat_zero_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      ext
      · exact congrArg Fin.val (finMAddNat_zero_add_one n)
      · simp [layerRootStep, List.range_succ, List.foldl_append]

theorem layerRootStep_m_return {m : Nat} [NeZero m]
    (F : LayerSchedule m) (c : Color) (w : ARoot5 m) :
    (layerRootStep F c)^[m] ((0 : Fin m), w) = ((0 : Fin m), colorReturn F c w) := by
  rw [layerRootStep_iterate_zero_range]
  apply Prod.ext
  · exact finMAddNat_zero_card
  · unfold colorReturn
    rw [← map_finMAddNat_zero_range (m := m)]
    rw [List.foldl_map]

theorem prefixFold_surjective_of_exactCover {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hF : IsLayerExactCover F) (c : Color) (n : Nat) :
    Function.Surjective fun w : ARoot5 m =>
      (List.range n).foldl
        (fun x k => layerMap F (finMAddNat (0 : Fin m) k) c x) w := by
  induction n with
  | zero =>
      intro y
      exact ⟨y, rfl⟩
  | succ n ih =>
      intro y
      rcases (layerMap_bijective_of_exactCover hF (finMAddNat (0 : Fin m) n) c).2 y with
        ⟨z, hz⟩
      rcases ih z with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      simp [List.range_succ, List.foldl_append, hw, hz]

theorem layerRootStep_cover_of_exactCover {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hF : IsLayerExactCover F) (c : Color) :
    forall x : Fin m × ARoot5 m, exists w : ARoot5 m,
      (layerRootStep F c)^[x.1.val] ((0 : Fin m), w) = x := by
  intro x
  rcases x with ⟨t, y⟩
  rcases prefixFold_surjective_of_exactCover hF c t.val y with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  rw [layerRootStep_iterate_zero_range]
  apply Prod.ext
  · exact finMAddNat_zero_val t
  · exact hw

theorem zmod_finMAddNat_one {m : Nat} [NeZero m] (t : Fin m) :
    (((finMAddNat t 1).val : Nat) : ZMod m) =
      (((t.val : Nat) : ZMod m) + 1) := by
  simp [finMAddNat, Nat.cast_add]

theorem torusColorStep_torusOfLayerRoot {m : Nat} [NeZero m]
    (F : LayerSchedule m) (c : Color) (t : Fin m) (w : ARoot5 m) :
    torusColorStep F c (torusOfLayerRoot t w) =
      torusOfLayerRoot (finMAddNat t 1) (layerMap F t c w) := by
  ext i
  have hlayer := layerOf_torusOfLayerRoot t w
  have hroot := rootAtLayer_torusOfLayerRoot t w
  have hrootVal : (rootAtLayer (torusOfLayerRoot t w)).1 = w.1 :=
    congrArg Subtype.val hroot
  have hlayer' :
      layerOf (w.1 + (((t.val : Nat) : ZMod m) • e5 m 4)) = t := by
    simpa [torusOfLayerRoot] using hlayer
  have hrootVal' :
      (rootAtLayer (w.1 + (((t.val : Nat) : ZMod m) • e5 m 4))).1 = w.1 := by
    simpa [torusOfLayerRoot] using hrootVal
  have hsucc := zmod_finMAddNat_one t
  simp [torusColorStep, torusOfLayerRoot, layerMap, hlayer', hrootVal', q5, hsucc]
  by_cases hi : i = 4
  · subst hi
    simp [e5]
    ring
  · simp [e5, hi]

theorem torusColorStep_layerRootEquiv {m : Nat} [NeZero m]
    (F : LayerSchedule m) (c : Color) (tw : Fin m × ARoot5 m) :
    torusColorStep F c (layerRootEquiv tw) =
      layerRootEquiv (layerRootStep F c tw) := by
  rcases tw with ⟨t, w⟩
  exact torusColorStep_torusOfLayerRoot F c t w

theorem torusColorStep_outgoing_latin {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hLatin : IsScheduleLatin F) (x : Vertex5 m) :
    Function.Bijective fun c : Color =>
      F.dir (layerOf x) c (rootAtLayer x).1 := by
  exact hLatin (layerOf x) (rootAtLayer x).1

def TorusHamiltonDecompositionD5 (m : Nat) [NeZero m] : Prop :=
  exists F : LayerSchedule m,
    IsLayerExactCover F ∧ IsScheduleLatin F ∧
      forall c : Color, IsSingleCycleMap (torusColorStep F c)

theorem layerRootStep_single_cycle_of_schedule {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hF : IsLayerExactCover F)
    (hHam : AllColorHamiltonian F) (c : Color) :
    IsSingleCycleMap (layerRootStep F c) := by
  exact single_cycle_of_layer_zero_return_cover
    (S := layerRootStep F c) (R := colorReturn F c)
    (layerRootStep_bijective_of_exactCover hF c)
    (layerRootStep_m_return F c)
    (hHam c)
    (layerRootStep_cover_of_exactCover hF c)

theorem torusColorStep_single_cycle_of_schedule {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hF : IsLayerExactCover F)
    (hHam : AllColorHamiltonian F) (c : Color) :
    IsSingleCycleMap (torusColorStep F c) := by
  exact single_cycle_of_bijective_semiconj
    (f := layerRootStep F c)
    (g := torusColorStep F c)
    (phi := layerRootEquiv)
    (layerRootEquiv.bijective)
    (fun tw => (torusColorStep_layerRootEquiv F c tw).symm)
    (layerRootStep_single_cycle_of_schedule hF hHam c)

theorem torusHamiltonDecomposition_of_model {m : Nat} [NeZero m]
    (h : HamiltonDecompositionD5 m) :
    TorusHamiltonDecompositionD5 m := by
  rcases h with ⟨F, hExact, hLatin, hHam⟩
  exact ⟨F, hExact, hLatin, fun c => torusColorStep_single_cycle_of_schedule hExact hHam c⟩

theorem D5_odd_torus_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    TorusHamiltonDecompositionD5 m := by
  exact torusHamiltonDecomposition_of_model (D5_odd_unconditional hodd hm3)

end D5Odd
