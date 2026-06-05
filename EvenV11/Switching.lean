import EvenV11.Basic

namespace EvenV11
namespace Switching

def IsSingletonCommon {α : Type*} (A B : Set α) (x : α) : Prop :=
  x ∈ A ∧ x ∈ B ∧ ∀ y : α, y ∈ A → y ∈ B → y = x

theorem singletonCommon_unique
    {α : Type*} {A B : Set α} {x y : α}
    (hx : IsSingletonCommon A B x)
    (hy : IsSingletonCommon A B y) :
    x = y :=
  hy.2.2 x hx.1 hx.2.1

theorem singletonCommon_iff_inter_eq_singleton
    {α : Type*} {A B : Set α} {x : α} :
    IsSingletonCommon A B x ↔ A ∩ B = {x} := by
  constructor
  · intro h
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (h.2.2 y hy.1 hy.2)
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨h.1, h.2.1⟩
  · intro h
    have hxAB : x ∈ A ∩ B := by
      rw [h]
      exact Set.mem_singleton x
    refine ⟨hxAB.1, hxAB.2, ?_⟩
    intro y hyA hyB
    have hy : y ∈ ({x} : Set α) := by
      rw [← h]
      exact ⟨hyA, hyB⟩
    exact Set.mem_singleton_iff.mp hy

def singletonSwitchLeft {α : Type*} [DecidableEq α]
    (G H : α → α) (c : α) : α → α :=
  fun x => if x = c then H x else G x

def singletonSwitchRight {α : Type*} [DecidableEq α]
    (G H : α → α) (c : α) : α → α :=
  fun x => if x = c then G x else H x

theorem singletonSwitchLeft_eq_of_common_image
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchLeft G H c = G := by
  funext x
  by_cases hx : x = c
  · subst x
    simp [singletonSwitchLeft, hcommon.symm]
  · simp [singletonSwitchLeft, hx]

theorem singletonSwitchRight_eq_of_common_image
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchRight G H c = H := by
  funext x
  by_cases hx : x = c
  · subst x
    simp [singletonSwitchRight, hcommon]
  · simp [singletonSwitchRight, hx]

theorem singletonCommonEdgeSwitch_identity
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchLeft G H c = G ∧ singletonSwitchRight G H c = H :=
  ⟨singletonSwitchLeft_eq_of_common_image hcommon,
   singletonSwitchRight_eq_of_common_image hcommon⟩

theorem singletonCommonEdgeSwitch_preserves_singleCycle
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c)
    (hG : Shared.IsSingleCycleMap G) (hH : Shared.IsSingleCycleMap H) :
    Shared.IsSingleCycleMap (singletonSwitchLeft G H c) ∧
      Shared.IsSingleCycleMap (singletonSwitchRight G H c) := by
  constructor
  · rw [singletonSwitchLeft_eq_of_common_image hcommon]
    exact hG
  · rw [singletonSwitchRight_eq_of_common_image hcommon]
    exact hH

def comparisonMap {α : Type*} (T R : α ≃ α) : α ≃ α :=
  R.trans T.symm

theorem comparisonMap_apply {α : Type*} (T R : α ≃ α) (x : α) :
    comparisonMap T R x = T.symm (R x) :=
  rfl

theorem comparisonMap_symm {α : Type*} (T R : α ≃ α) :
    (comparisonMap T R).symm = comparisonMap R T := by
  ext x
  rfl

def ComparisonSetInvariant {α : Type*} (T R : α ≃ α) (U : Set α) :
    Prop :=
  ∀ x : α, x ∈ U ↔ T.symm (R x) ∈ U

theorem comparisonSetInvariant_iff_comparisonMap
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      ∀ x : α, x ∈ U ↔ comparisonMap T R x ∈ U := by
  rfl

theorem comparisonMap_fixed_iff_common_image
    {α : Type*} (T R : α ≃ α) (c : α) :
    comparisonMap T R c = c ↔ T c = R c := by
  constructor
  · intro h
    have hRT : R c = T c := by
      simpa [comparisonMap] using congrArg T h
    exact hRT.symm
  · intro hcommon
    simp [comparisonMap, ← hcommon]

theorem comparisonMap_fixed_of_common_image
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    comparisonMap T R c = c :=
  (comparisonMap_fixed_iff_common_image T R c).mpr hcommon

theorem common_image_of_comparisonMap_fixed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hfixed : comparisonMap T R c = c) :
    T c = R c :=
  (comparisonMap_fixed_iff_common_image T R c).mp hfixed

theorem comparisonMap_inverse_fixed_of_common_image
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    comparisonMap R T c = c :=
  comparisonMap_fixed_of_common_image hcommon.symm

theorem comparisonMap_iterate_fixed_of_common_image
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) (n : Nat) :
    ((comparisonMap T R : α → α)^[n]) c = c := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact comparisonMap_fixed_of_common_image hcommon

theorem comparisonMap_inverse_iterate_fixed_of_common_image
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) (n : Nat) :
    ((comparisonMap R T : α → α)^[n]) c = c :=
  comparisonMap_iterate_fixed_of_common_image hcommon.symm n

theorem comparisonSetInvariant_singleton_iff_comparisonMap_fixed
    {α : Type*} (T R : α ≃ α) (c : α) :
    ComparisonSetInvariant T R ({c} : Set α) ↔
      comparisonMap T R c = c := by
  constructor
  · intro hU
    have hc : c ∈ ({c} : Set α) := Set.mem_singleton c
    have h := (hU c).mp hc
    exact Set.mem_singleton_iff.mp h
  · intro hfix x
    constructor
    · intro hx
      have hx_eq : x = c := Set.mem_singleton_iff.mp hx
      subst x
      exact Set.mem_singleton_iff.mpr hfix
    · intro hx
      have hxImage : comparisonMap T R x = c :=
        Set.mem_singleton_iff.mp hx
      have hsame : comparisonMap T R x = comparisonMap T R c := by
        rw [hxImage, hfix]
      exact Set.mem_singleton_iff.mpr ((comparisonMap T R).injective hsame)

theorem comparisonSetInvariant_singleton_iff_common_image
    {α : Type*} (T R : α ≃ α) (c : α) :
    ComparisonSetInvariant T R ({c} : Set α) ↔ T c = R c :=
  (comparisonSetInvariant_singleton_iff_comparisonMap_fixed T R c).trans
    (comparisonMap_fixed_iff_common_image T R c)

def partialExchangeLeft {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)] : α → α :=
  fun x => if x ∈ U then R x else T x

def partialExchangeRight {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)] : α → α :=
  fun x => if x ∈ U then T x else R x

theorem comparisonSetInvariant_symm {α : Type*} {T R : α ≃ α}
    {U : Set α} (hU : ComparisonSetInvariant T R U) :
    ComparisonSetInvariant R T U := by
  intro x
  have h := hU (R.symm (T x))
  simpa using h.symm

theorem comparisonSetInvariant_preimage_eq
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    comparisonMap T R ⁻¹' U = U := by
  ext x
  exact (hU x).symm

theorem comparisonSetInvariant_iff_preimage_eq
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      comparisonMap T R ⁻¹' U = U := by
  constructor
  · intro hU
    exact comparisonSetInvariant_preimage_eq hU
  · intro hU x
    constructor
    · intro hx
      have hxPre : x ∈ comparisonMap T R ⁻¹' U := by
        rw [hU]
        exact hx
      simpa [comparisonMap] using hxPre
    · intro hx
      have hxPre : x ∈ comparisonMap T R ⁻¹' U := by
        simpa [comparisonMap] using hx
      rw [hU] at hxPre
      exact hxPre

theorem comparisonSetInvariant_image_eq
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    comparisonMap T R '' U = U := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hxU, hxy⟩
    rw [← hxy]
    exact (hU x).mp hxU
  · intro hyU
    refine ⟨comparisonMap R T y, ?_, ?_⟩
    · exact (comparisonSetInvariant_symm hU y).mp hyU
    · simp [comparisonMap]

theorem comparisonSetInvariant_iff_image_eq
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      comparisonMap T R '' U = U := by
  constructor
  · intro hU
    exact comparisonSetInvariant_image_eq hU
  · intro hU x
    constructor
    · intro hx
      have hxImageSet : comparisonMap T R x ∈ comparisonMap T R '' U :=
        ⟨x, hx, rfl⟩
      rw [hU] at hxImageSet
      simpa [comparisonMap] using hxImageSet
    · intro hx
      have hxTarget : comparisonMap T R x ∈ U := by
        simpa [comparisonMap] using hx
      have hxImageSet : comparisonMap T R x ∈ comparisonMap T R '' U := by
        rw [hU]
        exact hxTarget
      rcases hxImageSet with ⟨y, hyU, hy⟩
      have hyx : y = x := (comparisonMap T R).injective hy
      simpa [hyx] using hyU

theorem comparisonSetInvariant_iterate
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : α) :
    x ∈ U ↔ ((comparisonMap T R : α → α)^[n]) x ∈ U := by
  revert x
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      exact (ih x).trans (by
        have h := hU (((comparisonMap T R : α → α)^[n]) x)
        simpa [Function.iterate_succ_apply'] using h)

theorem comparisonSetInvariant_forward_iterate_mem
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : x ∈ U) :
    ((comparisonMap T R : α → α)^[n]) x ∈ U :=
  (comparisonSetInvariant_iterate hU n x).mp hx

theorem comparisonSetInvariant_backward_iterate_mem
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : ((comparisonMap T R : α → α)^[n]) x ∈ U) :
    x ∈ U :=
  (comparisonSetInvariant_iterate hU n x).mpr hx

theorem comparisonSetInvariant_iterate_preimage_eq
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) :
    ((comparisonMap T R : α → α)^[n]) ⁻¹' U = U := by
  ext x
  exact (comparisonSetInvariant_iterate hU n x).symm

theorem comparisonSetInvariant_inverse_iterate
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : α) :
    x ∈ U ↔ ((comparisonMap R T : α → α)^[n]) x ∈ U :=
  comparisonSetInvariant_iterate (comparisonSetInvariant_symm hU) n x

theorem comparisonSetInvariant_forward_inverse_iterate_mem
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : x ∈ U) :
    ((comparisonMap R T : α → α)^[n]) x ∈ U :=
  (comparisonSetInvariant_inverse_iterate hU n x).mp hx

theorem comparisonSetInvariant_backward_inverse_iterate_mem
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : ((comparisonMap R T : α → α)^[n]) x ∈ U) :
    x ∈ U :=
  (comparisonSetInvariant_inverse_iterate hU n x).mpr hx

theorem comparisonSetInvariant_inverse_iterate_preimage_eq
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) :
    ((comparisonMap R T : α → α)^[n]) ⁻¹' U = U := by
  ext x
  exact (comparisonSetInvariant_inverse_iterate hU n x).symm

def comparisonMapSubtype
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) : U ≃ U where
  toFun x := ⟨comparisonMap T R x, (hU x).mp x.property⟩
  invFun x := ⟨comparisonMap R T x,
    (comparisonSetInvariant_symm hU x).mp x.property⟩
  left_inv x := by
    ext
    simp [comparisonMap]
  right_inv x := by
    ext
    simp [comparisonMap]

theorem comparisonMapSubtype_apply
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    comparisonMapSubtype T R U hU x =
      ⟨comparisonMap T R x, (hU x).mp x.property⟩ :=
  rfl

theorem comparisonMapSubtype_coe_apply
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    ((comparisonMapSubtype T R U hU x : U) : α) = comparisonMap T R x :=
  rfl

theorem comparisonMapSubtype_symm_coe_apply
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    (((comparisonMapSubtype T R U hU).symm x : U) : α) =
      comparisonMap R T x :=
  rfl

theorem comparisonMapSubtype_iterate_coe
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : U) :
    (((comparisonMapSubtype T R U hU : U → U)^[n]) x : α) =
      ((comparisonMap T R : α → α)^[n]) x := by
  revert x
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        (((comparisonMapSubtype T R U hU : U → U)^[n.succ]) x : α)
            = (comparisonMapSubtype T R U hU
                (((comparisonMapSubtype T R U hU : U → U)^[n]) x) : U) := by
                rw [Function.iterate_succ_apply']
        _ = comparisonMap T R
              ((((comparisonMapSubtype T R U hU : U → U)^[n]) x : U) : α) := rfl
        _ = comparisonMap T R (((comparisonMap T R : α → α)^[n]) x) := by
              rw [ih x]
        _ = ((comparisonMap T R : α → α)^[n.succ]) x := by
              rw [Function.iterate_succ_apply']

theorem comparisonMapSubtype_symm_iterate_coe
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : U) :
    ((((comparisonMapSubtype T R U hU).symm : U → U)^[n]) x : α) =
      ((comparisonMap R T : α → α)^[n]) x := by
  revert x
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        ((((comparisonMapSubtype T R U hU).symm : U → U)^[n.succ]) x : α)
            = ((comparisonMapSubtype T R U hU).symm
                ((((comparisonMapSubtype T R U hU).symm : U → U)^[n]) x) : U) := by
                rw [Function.iterate_succ_apply']
        _ = comparisonMap R T
              (((((comparisonMapSubtype T R U hU).symm : U → U)^[n]) x : U) : α) := rfl
        _ = comparisonMap R T (((comparisonMap R T : α → α)^[n]) x) := by
              rw [ih x]
        _ = ((comparisonMap R T : α → α)^[n.succ]) x := by
              rw [Function.iterate_succ_apply']

theorem comparisonSetInvariant_empty {α : Type*} (T R : α ≃ α) :
    ComparisonSetInvariant T R (∅ : Set α) := by
  intro x
  simp

theorem comparisonSetInvariant_univ {α : Type*} (T R : α ≃ α) :
    ComparisonSetInvariant T R (Set.univ : Set α) := by
  intro x
  simp

theorem comparisonSetInvariant_union
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U ∪ V) := by
  intro x
  constructor
  · intro hx
    rcases hx with hxU | hxV
    · exact Or.inl ((hU x).mp hxU)
    · exact Or.inr ((hV x).mp hxV)
  · intro hx
    rcases hx with hxU | hxV
    · exact Or.inl ((hU x).mpr hxU)
    · exact Or.inr ((hV x).mpr hxV)

theorem comparisonSetInvariant_inter
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U ∩ V) := by
  intro x
  constructor
  · intro hx
    exact ⟨(hU x).mp hx.1, (hV x).mp hx.2⟩
  · intro hx
    exact ⟨(hU x).mpr hx.1, (hV x).mpr hx.2⟩

theorem comparisonSetInvariant_iUnion
    {ι α : Type*} {T R : α ≃ α} {S : ι → Set α}
    (hS : ∀ i : ι, ComparisonSetInvariant T R (S i)) :
    ComparisonSetInvariant T R (⋃ i : ι, S i) := by
  intro x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, (hS i x).mp hxi⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, (hS i x).mpr hxi⟩

theorem comparisonSetInvariant_iInter
    {ι α : Type*} {T R : α ≃ α} {S : ι → Set α}
    (hS : ∀ i : ι, ComparisonSetInvariant T R (S i)) :
    ComparisonSetInvariant T R (⋂ i : ι, S i) := by
  intro x
  constructor
  · intro hx
    exact Set.mem_iInter.mpr fun i =>
      (hS i x).mp (Set.mem_iInter.mp hx i)
  · intro hx
    exact Set.mem_iInter.mpr fun i =>
      (hS i x).mpr (Set.mem_iInter.mp hx i)

theorem comparisonSetInvariant_compl
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    ComparisonSetInvariant T R Uᶜ := by
  intro x
  constructor
  · intro hx hxImage
    exact hx ((hU x).mpr hxImage)
  · intro hx hxU
    exact hx ((hU x).mp hxU)

theorem comparisonSetInvariant_diff
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U \ V) :=
  comparisonSetInvariant_inter hU (comparisonSetInvariant_compl hV)

theorem comparisonSetInvariant_singleton_of_common_image
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    ComparisonSetInvariant T R ({c} : Set α) :=
  (comparisonSetInvariant_singleton_iff_common_image T R c).mpr hcommon

theorem partialExchangeLeft_bijective
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeLeft T R U) := by
  constructor
  · intro x y hxy
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · have hR : R x = R y := by
          simpa [partialExchangeLeft, hx, hy] using hxy
        exact R.injective hR
      · exfalso
        have hRT : R x = T y := by
          simpa [partialExchangeLeft, hx, hy] using hxy
        have hxImage : T.symm (R x) ∈ U := (hU x).mp hx
        have hpre : T.symm (R x) = y := by
          rw [hRT]
          simp
        exact hy (by simpa [hpre] using hxImage)
    · by_cases hy : y ∈ U
      · exfalso
        have hTR : T x = R y := by
          simpa [partialExchangeLeft, hx, hy] using hxy
        have hyImage : T.symm (R y) ∈ U := (hU y).mp hy
        have hpre : T.symm (R y) = x := by
          rw [← hTR]
          simp
        exact hx (by simpa [hpre] using hyImage)
      · have hT : T x = T y := by
          simpa [partialExchangeLeft, hx, hy] using hxy
        exact T.injective hT
  · intro y
    by_cases hy : T.symm y ∈ U
    · refine ⟨R.symm y, ?_⟩
      have hx : R.symm y ∈ U := by
        have hy' : T.symm (R (R.symm y)) ∈ U := by
          simpa using hy
        have h := (hU (R.symm y)).mpr hy'
        simpa using h
      simp [partialExchangeLeft, hx]
    · refine ⟨T.symm y, ?_⟩
      simp [partialExchangeLeft, hy]

theorem partialExchangeRight_bijective
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeRight T R U) := by
  simpa [partialExchangeRight, partialExchangeLeft] using
    partialExchangeLeft_bijective R T U
      (comparisonSetInvariant_symm hU)

theorem partialExchangePair_bijective
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeLeft T R U) ∧
      Function.Bijective (partialExchangeRight T R U) :=
  ⟨partialExchangeLeft_bijective T R U hU,
   partialExchangeRight_bijective T R U hU⟩

theorem partialExchangePair_bijective_singleton_of_common_image
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    Function.Bijective (partialExchangeLeft T R ({c} : Set α)) ∧
      Function.Bijective (partialExchangeRight T R ({c} : Set α)) :=
  partialExchangePair_bijective T R ({c} : Set α)
    (comparisonSetInvariant_singleton_of_common_image hcommon)

theorem rootFlatLayerBijective_of_partialExchangeLeft_eq
    {Color Direction RootState : Type*} {m : Nat}
    (S : Shared.RootFlatSchedule Color Direction RootState m)
    (T R : ZMod m → Color → RootState ≃ RootState)
    (U : ZMod m → Color → Set RootState)
    [∀ t c x, Decidable (x ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        S.layerMap t c w =
          partialExchangeLeft (T t c) (R t c) (U t c) w) :
    S.layerBijective :=
  Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq
    (fun t c => partialExchangeLeft (T t c) (R t c) (U t c))
    (fun t c => partialExchangeLeft_bijective (T t c) (R t c) (U t c) (hU t c))
    hLayer

theorem rootFlatLayerBijective_of_partialExchangeRight_eq
    {Color Direction RootState : Type*} {m : Nat}
    (S : Shared.RootFlatSchedule Color Direction RootState m)
    (T R : ZMod m → Color → RootState ≃ RootState)
    (U : ZMod m → Color → Set RootState)
    [∀ t c x, Decidable (x ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        S.layerMap t c w =
          partialExchangeRight (T t c) (R t c) (U t c) w) :
    S.layerBijective :=
  Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq
    (fun t c => partialExchangeRight (T t c) (R t c) (U t c))
    (fun t c => partialExchangeRight_bijective (T t c) (R t c) (U t c) (hU t c))
    hLayer

theorem rootFlatLayerBijective_of_partialExchangeChoice_eq
    {Color Direction RootState : Type*} {m : Nat}
    (S : Shared.RootFlatSchedule Color Direction RootState m)
    (T R : ZMod m → Color → RootState ≃ RootState)
    (U : ZMod m → Color → Set RootState)
    (chooseLeft : ZMod m → Color → Bool)
    [∀ t c x, Decidable (x ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        S.layerMap t c w =
          (if chooseLeft t c then
            partialExchangeLeft (T t c) (R t c) (U t c)
          else
            partialExchangeRight (T t c) (R t c) (U t c)) w) :
    S.layerBijective :=
  Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq
    (fun t c =>
      if chooseLeft t c then
        partialExchangeLeft (T t c) (R t c) (U t c)
      else
        partialExchangeRight (T t c) (R t c) (U t c))
    (fun t c => by
      by_cases hchoose : chooseLeft t c
      · simp [hchoose, partialExchangeLeft_bijective (T t c) (R t c) (U t c) (hU t c)]
      · simp [hchoose, partialExchangeRight_bijective (T t c) (R t c) (U t c) (hU t c)])
    hLayer

theorem partialExchangeLeft_singleton_eq_singletonSwitchLeft
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α) :
    partialExchangeLeft T R ({c} : Set α) = singletonSwitchLeft T R c := by
  funext x
  by_cases hx : x = c
  · subst x
    simp [partialExchangeLeft, singletonSwitchLeft]
  · have hxSet : x ∉ ({c} : Set α) := by
      simpa [Set.mem_singleton_iff] using hx
    simp [partialExchangeLeft, singletonSwitchLeft, hx, hxSet]

theorem partialExchangeRight_singleton_eq_singletonSwitchRight
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α) :
    partialExchangeRight T R ({c} : Set α) = singletonSwitchRight T R c := by
  funext x
  by_cases hx : x = c
  · subst x
    simp [partialExchangeRight, singletonSwitchRight]
  · have hxSet : x ∉ ({c} : Set α) := by
      simpa [Set.mem_singleton_iff] using hx
    simp [partialExchangeRight, singletonSwitchRight, hx, hxSet]

theorem partialExchangePair_identity_singleton_of_common_image
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeLeft T R ({c} : Set α) = T ∧
      partialExchangeRight T R ({c} : Set α) = R := by
  constructor
  · rw [partialExchangeLeft_singleton_eq_singletonSwitchLeft]
    exact (singletonCommonEdgeSwitch_identity hcommon).1
  · rw [partialExchangeRight_singleton_eq_singletonSwitchRight]
    exact (singletonCommonEdgeSwitch_identity hcommon).2

noncomputable def partialExchangeLeftEquiv
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) : α ≃ α :=
  Equiv.ofBijective (partialExchangeLeft T R U)
    (partialExchangeLeft_bijective T R U hU)

noncomputable def partialExchangeRightEquiv
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) : α ≃ α :=
  Equiv.ofBijective (partialExchangeRight T R U)
    (partialExchangeRight_bijective T R U hU)

theorem partialExchangeLeftEquiv_apply
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) (x : α) :
    partialExchangeLeftEquiv T R U hU x = partialExchangeLeft T R U x :=
  rfl

theorem partialExchangeRightEquiv_apply
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) (x : α) :
    partialExchangeRightEquiv T R U hU x = partialExchangeRight T R U x :=
  rfl

theorem partialExchangeLeftEquiv_singleton_of_common_image
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeLeftEquiv T R ({c} : Set α)
        (comparisonSetInvariant_singleton_of_common_image hcommon) = T := by
  ext x
  rw [partialExchangeLeftEquiv_apply]
  exact congrFun
    (partialExchangePair_identity_singleton_of_common_image T R c hcommon).1 x

theorem partialExchangeRightEquiv_singleton_of_common_image
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeRightEquiv T R ({c} : Set α)
        (comparisonSetInvariant_singleton_of_common_image hcommon) = R := by
  ext x
  rw [partialExchangeRightEquiv_apply]
  exact congrFun
    (partialExchangePair_identity_singleton_of_common_image T R c hcommon).2 x

def FixesOutside {α : Type*} (S : Set α) (f : α → α) : Prop :=
  ∀ x : α, x ∉ S → f x = x

def MapsInto {α : Type*} (S : Set α) (f : α → α) : Prop :=
  ∀ x : α, x ∈ S → f x ∈ S

def SupportedOn {α : Type*} (S : Set α) (f : α → α) : Prop :=
  FixesOutside S f ∧ MapsInto S f

theorem supportedOn_fixesOutside {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) :
    FixesOutside S f :=
  h.1

theorem supportedOn_mapsInto {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) :
    MapsInto S f :=
  h.2

theorem supportedOn_apply_of_not_mem {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) {x : α} (hx : x ∉ S) :
    f x = x :=
  supportedOn_fixesOutside h x hx

theorem supportedOn_mem_of_mem {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) {x : α} (hx : x ∈ S) :
    f x ∈ S :=
  supportedOn_mapsInto h x hx

theorem fixesOutside_mono {α : Type*} {S T : Set α} {f : α → α}
    (hST : S ⊆ T) (hf : FixesOutside S f) :
    FixesOutside T f := by
  intro x hxT
  exact hf x (fun hxS => hxT (hST hxS))

theorem supportedOn_mono {α : Type*} {S T : Set α} {f : α → α}
    (hST : S ⊆ T) (hf : SupportedOn S f) :
    SupportedOn T f := by
  constructor
  · exact fixesOutside_mono hST (supportedOn_fixesOutside hf)
  · intro x hxT
    by_cases hxS : x ∈ S
    · exact hST (supportedOn_mem_of_mem hf hxS)
    · rw [supportedOn_apply_of_not_mem hf hxS]
      exact hxT

theorem fixesOutside_union_left {α : Type*} {S T : Set α} {f : α → α}
    (hf : FixesOutside S f) :
    FixesOutside (S ∪ T) f :=
  fixesOutside_mono (by
    intro x hxS
    exact Or.inl hxS) hf

theorem fixesOutside_union_right {α : Type*} {S T : Set α} {f : α → α}
    (hf : FixesOutside T f) :
    FixesOutside (S ∪ T) f :=
  fixesOutside_mono (by
    intro x hxT
    exact Or.inr hxT) hf

theorem supportedOn_union_left {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) :
    SupportedOn (S ∪ T) f :=
  supportedOn_mono (by
    intro x hxS
    exact Or.inl hxS) hf

theorem supportedOn_union_right {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn T f) :
    SupportedOn (S ∪ T) f :=
  supportedOn_mono (by
    intro x hxT
    exact Or.inr hxT) hf

theorem fixesOutside_comp {α : Type*} {S : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside S g) :
    FixesOutside S (fun x => f (g x)) := by
  intro x hx
  change f (g x) = x
  rw [hg x hx]
  exact hf x hx

theorem mapsInto_comp {α : Type*} {S : Set α} {f g : α → α}
    (hf : MapsInto S f) (hg : MapsInto S g) :
    MapsInto S (fun x => f (g x)) := by
  intro x hx
  exact hf (g x) (hg x hx)

theorem supportedOn_comp {α : Type*} {S : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn S g) :
    SupportedOn S (fun x => f (g x)) := by
  constructor
  · exact fixesOutside_comp (supportedOn_fixesOutside hf)
      (supportedOn_fixesOutside hg)
  · exact mapsInto_comp (supportedOn_mapsInto hf) (supportedOn_mapsInto hg)

theorem fixesOutside_comp_union {α : Type*} {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) :
    FixesOutside (S ∪ T) (fun x => f (g x)) := by
  intro x hx
  change f (g x) = x
  have hxS : x ∉ S := by
    intro hxS
    exact hx (Or.inl hxS)
  have hxT : x ∉ T := by
    intro hxT
    exact hx (Or.inr hxT)
  rw [hg x hxT]
  exact hf x hxS

theorem supportedOn_comp_union {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) :
    SupportedOn (S ∪ T) (fun x => f (g x)) := by
  constructor
  · exact fixesOutside_comp_union
      (supportedOn_fixesOutside hf) (supportedOn_fixesOutside hg)
  · intro x hx
    change f (g x) ∈ S ∪ T
    have hgUnion : g x ∈ S ∪ T := by
      rcases hx with hxS | hxT
      · by_cases hxT : x ∈ T
        · exact Or.inr (supportedOn_mem_of_mem hg hxT)
        · rw [supportedOn_apply_of_not_mem hg hxT]
          exact Or.inl hxS
      · exact Or.inr (supportedOn_mem_of_mem hg hxT)
    by_cases hgxS : g x ∈ S
    · exact Or.inl (supportedOn_mem_of_mem hf hgxS)
    · rw [supportedOn_apply_of_not_mem hf hgxS]
      exact hgUnion

theorem fixesOutside_comp_union_reverse {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) :
    FixesOutside (S ∪ T) (fun x => g (f x)) :=
  fixesOutside_mono (by
    intro x hx
    rcases hx with hxT | hxS
    · exact Or.inr hxT
    · exact Or.inl hxS) (fixesOutside_comp_union hg hf)

theorem supportedOn_comp_union_reverse {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) :
    SupportedOn (S ∪ T) (fun x => g (f x)) :=
  supportedOn_mono (by
    intro x hx
    rcases hx with hxT | hxS
    · exact Or.inr hxT
    · exact Or.inl hxS) (supportedOn_comp_union hg hf)

def SetsDisjoint {α : Type*} (S T : Set α) : Prop :=
  ∀ x : α, x ∈ S → x ∈ T → False

theorem setsDisjoint_symm {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) :
    SetsDisjoint T S := by
  intro x hxT hxS
  exact h x hxS hxT

theorem not_mem_right_of_mem_left {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) {x : α} (hxS : x ∈ S) :
    x ∉ T := by
  intro hxT
  exact h x hxS hxT

theorem not_mem_left_of_mem_right {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) {x : α} (hxT : x ∈ T) :
    x ∉ S :=
  not_mem_right_of_mem_left (setsDisjoint_symm h) hxT

theorem supportedOn_apply_of_mem_disjoint {α : Type*}
    {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T)
    {x : α} (hxT : x ∈ T) :
    f x = x :=
  supportedOn_apply_of_not_mem hf
    (not_mem_left_of_mem_right hdisj hxT)

theorem mapsInto_of_supportedOn_disjoint {α : Type*}
    {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T) :
    MapsInto T f := by
  intro x hxT
  rw [supportedOn_apply_of_mem_disjoint hf hdisj hxT]
  exact hxT

theorem fixesOutside_id {α : Type*} (S : Set α) :
    FixesOutside S (fun x : α => x) := by
  intro x _hx
  rfl

theorem mapsInto_id {α : Type*} (S : Set α) :
    MapsInto S (fun x : α => x) := by
  intro x hx
  exact hx

theorem supportedOn_id {α : Type*} (S : Set α) :
    SupportedOn S (fun x : α => x) := by
  constructor
  · exact fixesOutside_id S
  · exact mapsInto_id S

theorem fixesOutside_iterate {α : Type*} {S : Set α} {f : α → α}
    (hf : FixesOutside S f) (n : Nat) :
    FixesOutside S (f^[n]) := by
  induction n with
  | zero =>
      simpa using fixesOutside_id S
  | succ n ih =>
      simpa [Function.iterate_succ] using fixesOutside_comp ih hf

theorem mapsInto_iterate {α : Type*} {S : Set α} {f : α → α}
    (hf : MapsInto S f) (n : Nat) :
    MapsInto S (f^[n]) := by
  induction n with
  | zero =>
      simpa using mapsInto_id S
  | succ n ih =>
      simpa [Function.iterate_succ] using mapsInto_comp ih hf

theorem supportedOn_iterate {α : Type*} {S : Set α} {f : α → α}
    (hf : SupportedOn S f) (n : Nat) :
    SupportedOn S (f^[n]) := by
  constructor
  · exact fixesOutside_iterate (supportedOn_fixesOutside hf) n
  · exact mapsInto_iterate (supportedOn_mapsInto hf) n

theorem supportedOn_iterate_apply_of_mem_disjoint {α : Type*}
    {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T)
    (n : Nat) {x : α} (hxT : x ∈ T) :
    (f^[n]) x = x :=
  supportedOn_apply_of_mem_disjoint (supportedOn_iterate hf n) hdisj hxT

theorem mapsInto_iterate_of_supportedOn_disjoint {α : Type*}
    {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T) (n : Nat) :
    MapsInto T (f^[n]) := by
  intro x hxT
  rw [supportedOn_iterate_apply_of_mem_disjoint hf hdisj n hxT]
  exact hxT

theorem fixesOutside_iterates_comp_union {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) (n k : Nat) :
    FixesOutside (S ∪ T) (fun x => (f^[n]) ((g^[k]) x)) :=
  fixesOutside_comp_union
    (fixesOutside_iterate hf n) (fixesOutside_iterate hg k)

theorem supportedOn_iterates_comp_union {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) (n k : Nat) :
    SupportedOn (S ∪ T) (fun x => (f^[n]) ((g^[k]) x)) :=
  supportedOn_comp_union
    (supportedOn_iterate hf n) (supportedOn_iterate hg k)

theorem fixesOutside_iterates_comp_union_reverse {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) (n k : Nat) :
    FixesOutside (S ∪ T) (fun x => (g^[k]) ((f^[n]) x)) :=
  fixesOutside_comp_union_reverse
    (fixesOutside_iterate hf n) (fixesOutside_iterate hg k)

theorem supportedOn_iterates_comp_union_reverse {α : Type*}
    {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) (n k : Nat) :
    SupportedOn (S ∪ T) (fun x => (g^[k]) ((f^[n]) x)) :=
  supportedOn_comp_union_reverse
    (supportedOn_iterate hf n) (supportedOn_iterate hg k)

theorem commuteOfDisjointSupportedOn
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hdisj : SetsDisjoint S T) :
    Function.Commute f g := by
  intro x
  by_cases hxS : x ∈ S
  · have hxNotT : x ∉ T :=
      not_mem_right_of_mem_left hdisj hxS
    have gx : g x = x := hg.1 x hxNotT
    have hfxS : f x ∈ S := hf.2 x hxS
    have hfxNotT : f x ∉ T :=
      not_mem_right_of_mem_left hdisj hfxS
    have gfx : g (f x) = f x := hg.1 (f x) hfxNotT
    rw [gx, gfx]
  · by_cases hxT : x ∈ T
    · have fx : f x = x := hf.1 x hxS
      have hgxT : g x ∈ T := hg.2 x hxT
      have hgxNotS : g x ∉ S :=
        not_mem_left_of_mem_right hdisj hgxT
      have fgx : f (g x) = g x := hf.1 (g x) hgxNotS
      rw [fx, fgx]
    · have fx : f x = x := hf.1 x hxS
      have gx : g x = x := hg.1 x hxT
      calc
        f (g x) = f x := by rw [gx]
        _ = x := fx
        _ = g x := gx.symm
        _ = g (f x) := by rw [fx]

theorem commuteOfDisjointSupportedOn_symmSupports
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hdisj : SetsDisjoint S T) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg (setsDisjoint_symm hdisj)

theorem commuteOfDisjointSupportedOn_iterates
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hdisj : SetsDisjoint S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn
    (supportedOn_iterate hf n) (supportedOn_iterate hg k) hdisj

theorem commuteOfDisjointSupportedOn_iterates_symmSupports
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hdisj : SetsDisjoint S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjoint_symm hdisj) n k

end Switching

export Switching
  (IsSingletonCommon singletonCommon_unique
   singletonCommon_iff_inter_eq_singleton
   singletonSwitchLeft singletonSwitchRight
   singletonSwitchLeft_eq_of_common_image
   singletonSwitchRight_eq_of_common_image
   singletonCommonEdgeSwitch_identity
   singletonCommonEdgeSwitch_preserves_singleCycle
   comparisonMap comparisonMap_apply comparisonMap_symm
   ComparisonSetInvariant comparisonSetInvariant_iff_comparisonMap
   comparisonMap_fixed_iff_common_image
   comparisonMap_fixed_of_common_image
   common_image_of_comparisonMap_fixed
   comparisonMap_inverse_fixed_of_common_image
   comparisonMap_iterate_fixed_of_common_image
   comparisonMap_inverse_iterate_fixed_of_common_image
   comparisonSetInvariant_singleton_iff_comparisonMap_fixed
   comparisonSetInvariant_singleton_iff_common_image
   partialExchangeLeft partialExchangeRight
   comparisonSetInvariant_symm
   comparisonSetInvariant_preimage_eq
   comparisonSetInvariant_iff_preimage_eq
   comparisonSetInvariant_image_eq
   comparisonSetInvariant_iff_image_eq
   comparisonSetInvariant_iterate
   comparisonSetInvariant_forward_iterate_mem
   comparisonSetInvariant_backward_iterate_mem
   comparisonSetInvariant_iterate_preimage_eq
   comparisonSetInvariant_inverse_iterate
   comparisonSetInvariant_forward_inverse_iterate_mem
   comparisonSetInvariant_backward_inverse_iterate_mem
   comparisonSetInvariant_inverse_iterate_preimage_eq
   comparisonMapSubtype comparisonMapSubtype_apply
   comparisonMapSubtype_coe_apply
   comparisonMapSubtype_symm_coe_apply
   comparisonMapSubtype_iterate_coe
   comparisonMapSubtype_symm_iterate_coe
   comparisonSetInvariant_empty comparisonSetInvariant_univ
   comparisonSetInvariant_union comparisonSetInvariant_inter
   comparisonSetInvariant_iUnion comparisonSetInvariant_iInter
   comparisonSetInvariant_compl comparisonSetInvariant_diff
   comparisonSetInvariant_singleton_of_common_image
   partialExchangeLeft_bijective partialExchangeRight_bijective
   partialExchangePair_bijective
   partialExchangePair_bijective_singleton_of_common_image
   rootFlatLayerBijective_of_partialExchangeLeft_eq
   rootFlatLayerBijective_of_partialExchangeRight_eq
   rootFlatLayerBijective_of_partialExchangeChoice_eq
   partialExchangeLeft_singleton_eq_singletonSwitchLeft
   partialExchangeRight_singleton_eq_singletonSwitchRight
   partialExchangePair_identity_singleton_of_common_image
   partialExchangeLeftEquiv partialExchangeRightEquiv
   partialExchangeLeftEquiv_apply partialExchangeRightEquiv_apply
   partialExchangeLeftEquiv_singleton_of_common_image
   partialExchangeRightEquiv_singleton_of_common_image
   FixesOutside MapsInto SupportedOn supportedOn_fixesOutside
   supportedOn_mapsInto supportedOn_apply_of_not_mem
   supportedOn_mem_of_mem fixesOutside_mono supportedOn_mono
   fixesOutside_union_left fixesOutside_union_right
   supportedOn_union_left supportedOn_union_right
   fixesOutside_comp mapsInto_comp supportedOn_comp
   fixesOutside_comp_union supportedOn_comp_union
   fixesOutside_comp_union_reverse supportedOn_comp_union_reverse
   SetsDisjoint
   setsDisjoint_symm not_mem_right_of_mem_left not_mem_left_of_mem_right
   supportedOn_apply_of_mem_disjoint
   mapsInto_of_supportedOn_disjoint
   fixesOutside_id mapsInto_id supportedOn_id
   fixesOutside_iterate mapsInto_iterate supportedOn_iterate
   supportedOn_iterate_apply_of_mem_disjoint
   mapsInto_iterate_of_supportedOn_disjoint
   fixesOutside_iterates_comp_union supportedOn_iterates_comp_union
   fixesOutside_iterates_comp_union_reverse
   supportedOn_iterates_comp_union_reverse
   commuteOfDisjointSupportedOn
   commuteOfDisjointSupportedOn_symmSupports
   commuteOfDisjointSupportedOn_iterates
   commuteOfDisjointSupportedOn_iterates_symmSupports)

end EvenV11
