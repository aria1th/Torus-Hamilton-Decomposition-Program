import EvenV11.AffineSeparation

namespace EvenV11
namespace SupportSeparation

theorem projectionSeparatedSupportedMapsCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hSep : ProjectionImagesDisjoint π S T) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjointOfProjectionImagesDisjoint π S T hSep)

theorem projectionSeparatedSupportedMapsCommute_symmSupports
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hSep : ProjectionImagesDisjoint π S T) :
    Function.Commute f g :=
  projectionSeparatedSupportedMapsCommute π hf hg
    (projectionImagesDisjoint_symm π hSep)

theorem projectionSeparatedSupportedIteratesCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hSep : ProjectionImagesDisjoint π S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjointOfProjectionImagesDisjoint π S T hSep) n k

theorem projectionSeparatedSupportedIteratesCommute_symmSupports
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hSep : ProjectionImagesDisjoint π S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  projectionSeparatedSupportedIteratesCommute π hf hg
    (projectionImagesDisjoint_symm π hSep) n k

theorem productCylinderLeftDisjointSupportedMapsCommute
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hS : SetsDisjoint S S') :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (productCylinderDisjointOfLeftDisjoint S S' T T' hS)

theorem productCylinderRightDisjointSupportedMapsCommute
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hT : SetsDisjoint T T') :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (productCylinderDisjointOfRightDisjoint S S' T T' hT)

theorem productCylinderLeftProjectionSeparatedSupportedMapsCommute
    {α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π S S') :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (productCylinderDisjointOfLeftProjectionImagesDisjoint π S S' T T' hSep)

theorem productCylinderRightProjectionSeparatedSupportedMapsCommute
    {α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π T T') :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (productCylinderDisjointOfRightProjectionImagesDisjoint π S S' T T' hSep)

theorem productCylinderLeftDisjointSupportedIteratesCommute
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hS : SetsDisjoint S S') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (productCylinderDisjointOfLeftDisjoint S S' T T' hS) n k

theorem productCylinderRightDisjointSupportedIteratesCommute
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hT : SetsDisjoint T T') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (productCylinderDisjointOfRightDisjoint S S' T T' hT) n k

theorem productCylinderLeftProjectionSeparatedSupportedIteratesCommute
    {α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π S S') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (productCylinderDisjointOfLeftProjectionImagesDisjoint π S S' T T' hSep)
    n k

theorem productCylinderRightProjectionSeparatedSupportedIteratesCommute
    {α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π T T') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (productCylinderDisjointOfRightProjectionImagesDisjoint π S S' T T' hSep)
    n k

theorem indexedSingletonSupportedMapsCommute_of_injective
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p i} : Set α) f)
    (hg : SupportedOn ({p j} : Set α) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (singletonIndexedSetsDisjoint_of_injective hp hij)

theorem indexedSingletonSupportedMapsCommute_symmSupports_of_injective
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p j} : Set α) f)
    (hg : SupportedOn ({p i} : Set α) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjoint_symm (singletonIndexedSetsDisjoint_of_injective hp hij))

theorem indexedSingletonSupportedIteratesCommute_of_injective
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p i} : Set α) f)
    (hg : SupportedOn ({p j} : Set α) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (singletonIndexedSetsDisjoint_of_injective hp hij) n k

theorem indexedSingletonSupportedIteratesCommute_symmSupports_of_injective
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p j} : Set α) f)
    (hg : SupportedOn ({p i} : Set α) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjoint_symm (singletonIndexedSetsDisjoint_of_injective hp hij))
    n k

theorem indexedSingletonProductSupportedMapsCommute_of_injective_pair
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij)

theorem indexedSingletonProductSupportedMapsCommute_symmSupports_of_injective_pair
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjoint_symm
      (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij))

theorem indexedSingletonProductSupportedIteratesCommute_of_injective_pair
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij)
    n k

theorem indexedSingletonProductSupportedIteratesCommute_symmSupports_of_injective_pair
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjoint_symm
      (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij))
    n k

theorem constantProjectionSupportedMapsCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjointOfConstantProjectionNe π S T a b hS hT hne)

theorem constantProjectionSupportedMapsCommute_symmSupports
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    Function.Commute f g :=
  constantProjectionSupportedMapsCommute π b a hf hg hT hS (by
    intro hba
    exact hne hba.symm)

theorem constantProjectionSupportedIteratesCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjointOfConstantProjectionNe π S T a b hS hT hne) n k

theorem constantProjectionSupportedIteratesCommute_symmSupports
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantProjectionSupportedIteratesCommute π b a hf hg hT hS (by
    intro hba
    exact hne hba.symm) n k

theorem constantProjectionAvoidsSupportedMapsCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjointOfConstantProjectionAvoids π S T value hS hT)

theorem avoidsConstantProjectionSupportedMapsCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjointOfAvoidsConstantProjection π S T value hS hT)

theorem constantProjectionAvoidsSupportedIteratesCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjointOfConstantProjectionAvoids π S T value hS hT) n k

theorem avoidsConstantProjectionSupportedIteratesCommute
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjointOfAvoidsConstantProjection π S T value hS hT) n k

theorem fiberSeparatedSupportedMapsCommute
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π value) f)
    (hg : SupportedOn S g)
    (hAvoid : ProjectionAvoids π S value) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (projectionFiberDisjointOfAvoids π value S hAvoid)

theorem fiberSeparatedSupportedMapsCommute_symmSupports
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π value) g)
    (hAvoid : ProjectionAvoids π S value) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (setsDisjoint_symm (projectionFiberDisjointOfAvoids π value S hAvoid))

theorem fiberSeparatedSupportedIteratesCommute
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π value) f)
    (hg : SupportedOn S g)
    (hAvoid : ProjectionAvoids π S value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (projectionFiberDisjointOfAvoids π value S hAvoid) n k

theorem fiberSeparatedSupportedIteratesCommute_symmSupports
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π value) g)
    (hAvoid : ProjectionAvoids π S value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (setsDisjoint_symm (projectionFiberDisjointOfAvoids π value S hAvoid))
    n k

theorem constantAgainstFiberSupportedMapsCommute
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π fiberValue) f)
    (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) :
    Function.Commute f g :=
  fiberSeparatedSupportedMapsCommute π fiberValue S hf hg
    (projectionAvoidsOfConstantProjectionNe π S supportValue fiberValue hS hne)

theorem constantAgainstFiberSupportedMapsCommute_symmSupports
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π fiberValue) g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) :
    Function.Commute f g :=
  constantProjectionSupportedMapsCommute π supportValue fiberValue
    hf hg hS (projectionFiberConstantOn π fiberValue) hne

theorem constantAgainstFiberSupportedIteratesCommute
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π fiberValue) f)
    (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  fiberSeparatedSupportedIteratesCommute π fiberValue S hf hg
    (projectionAvoidsOfConstantProjectionNe π S supportValue fiberValue hS hne)
    n k

theorem constantAgainstFiberSupportedIteratesCommute_symmSupports
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π fiberValue) g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantProjectionSupportedIteratesCommute π supportValue fiberValue
    hf hg hS (projectionFiberConstantOn π fiberValue) hne n k

end SupportSeparation

export SupportSeparation
  (projectionSeparatedSupportedMapsCommute
   projectionSeparatedSupportedMapsCommute_symmSupports
   projectionSeparatedSupportedIteratesCommute
   projectionSeparatedSupportedIteratesCommute_symmSupports
   productCylinderLeftDisjointSupportedMapsCommute
   productCylinderRightDisjointSupportedMapsCommute
   productCylinderLeftProjectionSeparatedSupportedMapsCommute
   productCylinderRightProjectionSeparatedSupportedMapsCommute
   productCylinderLeftDisjointSupportedIteratesCommute
   productCylinderRightDisjointSupportedIteratesCommute
   productCylinderLeftProjectionSeparatedSupportedIteratesCommute
   productCylinderRightProjectionSeparatedSupportedIteratesCommute
   indexedSingletonSupportedMapsCommute_of_injective
   indexedSingletonSupportedMapsCommute_symmSupports_of_injective
   indexedSingletonSupportedIteratesCommute_of_injective
   indexedSingletonSupportedIteratesCommute_symmSupports_of_injective
   indexedSingletonProductSupportedMapsCommute_of_injective_pair
   indexedSingletonProductSupportedMapsCommute_symmSupports_of_injective_pair
   indexedSingletonProductSupportedIteratesCommute_of_injective_pair
   indexedSingletonProductSupportedIteratesCommute_symmSupports_of_injective_pair
   constantProjectionSupportedMapsCommute
   constantProjectionSupportedMapsCommute_symmSupports
   constantProjectionSupportedIteratesCommute
   constantProjectionSupportedIteratesCommute_symmSupports
   constantProjectionAvoidsSupportedMapsCommute
   avoidsConstantProjectionSupportedMapsCommute
   constantProjectionAvoidsSupportedIteratesCommute
   avoidsConstantProjectionSupportedIteratesCommute
   fiberSeparatedSupportedMapsCommute
   fiberSeparatedSupportedMapsCommute_symmSupports
   fiberSeparatedSupportedIteratesCommute
   fiberSeparatedSupportedIteratesCommute_symmSupports
   constantAgainstFiberSupportedMapsCommute
   constantAgainstFiberSupportedMapsCommute_symmSupports
   constantAgainstFiberSupportedIteratesCommute
   constantAgainstFiberSupportedIteratesCommute_symmSupports)

end EvenV11
