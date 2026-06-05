import EvenV11.Switching

namespace EvenV11
namespace AffineSeparation

def ProjectionFiber {α β : Type*} (π : α → β) (value : β) : Set α :=
  {x | π x = value}

def ProjectionAvoids {α β : Type*} (π : α → β)
    (S : Set α) (value : β) : Prop :=
  ∀ x : α, x ∈ S → π x ≠ value

def ProjectionConstantOn {α β : Type*} (π : α → β)
    (S : Set α) (value : β) : Prop :=
  ∀ x : α, x ∈ S → π x = value

def ProjectionImagesDisjoint {α β : Type*} (π : α → β)
    (S T : Set α) : Prop :=
  ∀ x y : α, x ∈ S → y ∈ T → π x ≠ π y

def ProductCylinder {α β : Type*} (S : Set α) (T : Set β) :
    Set (α × β) :=
  {x | x.1 ∈ S ∧ x.2 ∈ T}

theorem projectionFiber_mem {α β : Type*}
    (π : α → β) (value : β) (x : α) :
    x ∈ ProjectionFiber π value ↔ π x = value :=
  Iff.rfl

theorem productCylinder_mem {α β : Type*}
    (S : Set α) (T : Set β) (x : α × β) :
    x ∈ ProductCylinder S T ↔ x.1 ∈ S ∧ x.2 ∈ T :=
  Iff.rfl

theorem projectionFiberConstantOn {α β : Type*}
    (π : α → β) (value : β) :
    ProjectionConstantOn π (ProjectionFiber π value) value := by
  intro x hx
  exact hx

theorem projectionAvoids_mono
    {α β : Type*} (π : α → β) {S T : Set α} (value : β)
    (hST : S ⊆ T) (hAvoid : ProjectionAvoids π T value) :
    ProjectionAvoids π S value := by
  intro x hxS
  exact hAvoid x (hST hxS)

theorem projectionConstantOn_mono
    {α β : Type*} (π : α → β) {S T : Set α} (value : β)
    (hST : S ⊆ T) (hConst : ProjectionConstantOn π T value) :
    ProjectionConstantOn π S value := by
  intro x hxS
  exact hConst x (hST hxS)

theorem projectionImagesDisjoint_mono
    {α β : Type*} (π : α → β) {S S' T T' : Set α}
    (hSS' : S ⊆ S') (hTT' : T ⊆ T')
    (hSep : ProjectionImagesDisjoint π S' T') :
    ProjectionImagesDisjoint π S T := by
  intro x y hxS hyT
  exact hSep x y (hSS' hxS) (hTT' hyT)

theorem projectionAvoidsOfConstantProjectionNe
    {α β : Type*} (π : α → β) (S : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a) (hne : a ≠ b) :
    ProjectionAvoids π S b := by
  intro x hxS
  rw [hS x hxS]
  exact hne

theorem projectionFiberDisjointOfAvoids
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    (hAvoid : ProjectionAvoids π S value) :
    SetsDisjoint (ProjectionFiber π value) S := by
  intro x hxFiber hxS
  exact hAvoid x hxS hxFiber

theorem projectionAvoidsOfFiberDisjoint
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    (hDisjoint : SetsDisjoint (ProjectionFiber π value) S) :
    ProjectionAvoids π S value := by
  intro x hxS hxValue
  exact hDisjoint x hxValue hxS

theorem projectionAvoids_iff_fiberDisjoint
    {α β : Type*} (π : α → β) (value : β) (S : Set α) :
    ProjectionAvoids π S value ↔
      SetsDisjoint (ProjectionFiber π value) S :=
  ⟨projectionFiberDisjointOfAvoids π value S,
    projectionAvoidsOfFiberDisjoint π value S⟩

theorem projectionAvoids_iff_disjointFiber
    {α β : Type*} (π : α → β) (value : β) (S : Set α) :
    ProjectionAvoids π S value ↔
      SetsDisjoint S (ProjectionFiber π value) :=
  ⟨fun hAvoid =>
      setsDisjoint_symm (projectionFiberDisjointOfAvoids π value S hAvoid),
    fun hDisjoint =>
      projectionAvoidsOfFiberDisjoint π value S
        (setsDisjoint_symm hDisjoint)⟩

theorem setsDisjointOfProjectionImagesDisjoint
    {α β : Type*} (π : α → β) (S T : Set α)
    (hSep : ProjectionImagesDisjoint π S T) :
    SetsDisjoint S T := by
  intro x hxS hxT
  exact hSep x x hxS hxT rfl

theorem projectionImagesDisjoint_symm
    {α β : Type*} (π : α → β) {S T : Set α}
    (hSep : ProjectionImagesDisjoint π S T) :
    ProjectionImagesDisjoint π T S := by
  intro x y hxT hyS hxy
  exact hSep y x hyS hxT hxy.symm

theorem projectionImagesDisjointOfConstantProjectionNe
    {α β : Type*} (π : α → β) (S T : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    ProjectionImagesDisjoint π S T := by
  intro x y hxS hyT hxy
  apply hne
  calc
    a = π x := (hS x hxS).symm
    _ = π y := hxy
    _ = b := hT y hyT

theorem projectionImagesDisjointOfConstantProjectionAvoids
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    ProjectionImagesDisjoint π S T := by
  intro x y hxS hyT hxy
  exact hT y hyT (hxy.symm.trans (hS x hxS))

theorem setsDisjointOfConstantProjectionAvoids
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    SetsDisjoint S T :=
  setsDisjointOfProjectionImagesDisjoint π S T
    (projectionImagesDisjointOfConstantProjectionAvoids π S T value hS hT)

theorem projectionImagesDisjointOfAvoidsConstantProjection
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    ProjectionImagesDisjoint π S T :=
  projectionImagesDisjoint_symm π
    (projectionImagesDisjointOfConstantProjectionAvoids π T S value hT hS)

theorem setsDisjointOfAvoidsConstantProjection
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    SetsDisjoint S T :=
  setsDisjointOfProjectionImagesDisjoint π S T
    (projectionImagesDisjointOfAvoidsConstantProjection π S T value hS hT)

theorem setsDisjointOfConstantProjectionNe
    {α β : Type*} (π : α → β) (S T : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    SetsDisjoint S T :=
  setsDisjointOfProjectionImagesDisjoint π S T
    (projectionImagesDisjointOfConstantProjectionNe π S T a b hS hT hne)

theorem projectionFiberDisjointOfConstantProjectionNe
    {α β : Type*} (π : α → β) (S : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a) (hne : a ≠ b) :
    SetsDisjoint (ProjectionFiber π b) S :=
  projectionFiberDisjointOfAvoids π b S
    (projectionAvoidsOfConstantProjectionNe π S a b hS hne)

theorem productCylinderDisjointOfLeftDisjoint
    {α β : Type*} (S S' : Set α) (T T' : Set β)
    (hS : SetsDisjoint S S') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') := by
  intro x hxLeft hxRight
  exact hS x.1 hxLeft.1 hxRight.1

theorem productCylinderDisjointOfRightDisjoint
    {α β : Type*} (S S' : Set α) (T T' : Set β)
    (hT : SetsDisjoint T T') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') := by
  intro x hxLeft hxRight
  exact hT x.2 hxLeft.2 hxRight.2

theorem productCylinderDisjointOfLeftProjectionImagesDisjoint
    {α β γ : Type*} (π : α → γ)
    (S S' : Set α) (T T' : Set β)
    (hSep : ProjectionImagesDisjoint π S S') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfLeftDisjoint S S' T T'
    (setsDisjointOfProjectionImagesDisjoint π S S' hSep)

theorem productCylinderDisjointOfRightProjectionImagesDisjoint
    {α β γ : Type*} (π : β → γ)
    (S S' : Set α) (T T' : Set β)
    (hSep : ProjectionImagesDisjoint π T T') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfRightDisjoint S S' T T'
    (setsDisjointOfProjectionImagesDisjoint π T T' hSep)

theorem singletonSetsDisjoint_iff_ne
    {α : Type*} {x y : α} :
    SetsDisjoint ({x} : Set α) ({y} : Set α) ↔ x ≠ y := by
  constructor
  · intro hdisj hxy
    exact hdisj x (Set.mem_singleton x) (by
      rw [hxy]
      exact Set.mem_singleton y)
  · intro hne z hzX hzY
    exact hne
      ((Set.mem_singleton_iff.mp hzX).symm.trans
        (Set.mem_singleton_iff.mp hzY))

theorem singletonSetsDisjoint_of_ne
    {α : Type*} {x y : α} (hxy : x ≠ y) :
    SetsDisjoint ({x} : Set α) ({y} : Set α) :=
  singletonSetsDisjoint_iff_ne.mpr hxy

theorem singletonIndexedSetsDisjoint_of_injective
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) :
    SetsDisjoint ({p i} : Set α) ({p j} : Set α) :=
  singletonSetsDisjoint_of_ne (fun hpij => hij (hp hpij))

theorem productCylinder_singleton_singleton_mem
    {α β : Type*} (a : α) (b : β) (x : α × β) :
    x ∈ ProductCylinder ({a} : Set α) ({b} : Set β) ↔ x = (a, b) := by
  constructor
  · intro hx
    exact Prod.ext
      (Set.mem_singleton_iff.mp hx.1)
      (Set.mem_singleton_iff.mp hx.2)
  · intro hx
    rw [hx]
    exact ⟨Set.mem_singleton a, Set.mem_singleton b⟩

theorem productCylinderSingletonSingleton_eq_singleton
    {α β : Type*} (a : α) (b : β) :
    ProductCylinder ({a} : Set α) ({b} : Set β) =
      ({(a, b)} : Set (α × β)) := by
  ext x
  rw [productCylinder_singleton_singleton_mem a b x]
  rfl

theorem productCylinderSingletonLeftDisjoint_of_ne
    {α β : Type*} {a a' : α} (haa' : a ≠ a')
    (T T' : Set β) :
    SetsDisjoint (ProductCylinder ({a} : Set α) T)
      (ProductCylinder ({a'} : Set α) T') :=
  productCylinderDisjointOfLeftDisjoint ({a} : Set α) ({a'} : Set α)
    T T' (singletonSetsDisjoint_of_ne haa')

theorem productCylinderSingletonRightDisjoint_of_ne
    {α β : Type*} (S S' : Set α) {b b' : β} (hbb' : b ≠ b') :
    SetsDisjoint (ProductCylinder S ({b} : Set β))
      (ProductCylinder S' ({b'} : Set β)) :=
  productCylinderDisjointOfRightDisjoint S S' ({b} : Set β) ({b'} : Set β)
    (singletonSetsDisjoint_of_ne hbb')

theorem productCylinderSingletonsDisjoint_of_pair_ne
    {α β : Type*} {a a' : α} {b b' : β}
    (hpair : (a, b) ≠ (a', b')) :
    SetsDisjoint (ProductCylinder ({a} : Set α) ({b} : Set β))
      (ProductCylinder ({a'} : Set α) ({b'} : Set β)) := by
  intro x hxLeft hxRight
  exact hpair (Prod.ext
    ((Set.mem_singleton_iff.mp hxLeft.1).symm.trans
      (Set.mem_singleton_iff.mp hxRight.1))
    ((Set.mem_singleton_iff.mp hxLeft.2).symm.trans
      (Set.mem_singleton_iff.mp hxRight.2)))

theorem productCylinderIndexedSingletonsDisjoint_of_injective_pair
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) :
    SetsDisjoint (ProductCylinder ({p i} : Set α) ({q i} : Set β))
      (ProductCylinder ({p j} : Set α) ({q j} : Set β)) :=
  productCylinderSingletonsDisjoint_of_pair_ne
    (fun hpqij => hij (hpq hpqij))

end AffineSeparation

export AffineSeparation
  (ProjectionFiber ProjectionAvoids ProjectionConstantOn
   ProjectionImagesDisjoint ProductCylinder
   projectionFiber_mem productCylinder_mem
   projectionFiberConstantOn
   projectionAvoids_mono projectionConstantOn_mono
   projectionImagesDisjoint_mono
   projectionAvoidsOfConstantProjectionNe
   projectionFiberDisjointOfAvoids
   projectionAvoidsOfFiberDisjoint
   projectionAvoids_iff_fiberDisjoint
   projectionAvoids_iff_disjointFiber
   setsDisjointOfProjectionImagesDisjoint
   projectionImagesDisjoint_symm
   projectionImagesDisjointOfConstantProjectionNe
   projectionImagesDisjointOfConstantProjectionAvoids
   setsDisjointOfConstantProjectionAvoids
   projectionImagesDisjointOfAvoidsConstantProjection
   setsDisjointOfAvoidsConstantProjection
   setsDisjointOfConstantProjectionNe
   projectionFiberDisjointOfConstantProjectionNe
   productCylinderDisjointOfLeftDisjoint
   productCylinderDisjointOfRightDisjoint
   productCylinderDisjointOfLeftProjectionImagesDisjoint
   productCylinderDisjointOfRightProjectionImagesDisjoint
   singletonSetsDisjoint_iff_ne
   singletonSetsDisjoint_of_ne
   singletonIndexedSetsDisjoint_of_injective
   productCylinder_singleton_singleton_mem
   productCylinderSingletonSingleton_eq_singleton
   productCylinderSingletonLeftDisjoint_of_ne
   productCylinderSingletonRightDisjoint_of_ne
   productCylinderSingletonsDisjoint_of_pair_ne
   productCylinderIndexedSingletonsDisjoint_of_injective_pair)

end EvenV11
