import EvenV11.Basic
import EvenV11.SupportSeparation

namespace EvenV11
namespace WordSkew

def wordEval {ι α : Type*} (step : ι → α → α) :
    List ι → α → α
  | [], x => x
  | i :: word, x => wordEval step word (step i x)

theorem wordEval_nil {ι α : Type*} (step : ι → α → α) (x : α) :
    wordEval step [] x = x :=
  rfl

theorem wordEval_cons {ι α : Type*} (step : ι → α → α)
    (i : ι) (word : List ι) (x : α) :
    wordEval step (i :: word) x = wordEval step word (step i x) :=
  rfl

theorem wordEval_append {ι α : Type*} (step : ι → α → α)
    (left right : List ι) (x : α) :
    wordEval step (left ++ right) x =
      wordEval step right (wordEval step left x) := by
  induction left generalizing x with
  | nil =>
      simp [wordEval_nil]
  | cons i left ih =>
      simp [wordEval, ih]

theorem wordEval_bijective {ι α : Type*} (step : ι → α → α)
    (hstep : ∀ i : ι, Function.Bijective (step i)) :
    ∀ word : List ι, Function.Bijective (wordEval step word)
  | [] => by
      constructor
      · intro x y hxy
        exact hxy
      · intro y
        exact ⟨y, rfl⟩
  | i :: word =>
      (wordEval_bijective step hstep word).comp (hstep i)

theorem fixesOutside_wordEval {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, FixesOutside S (step i)) :
    ∀ word : List ι, FixesOutside S (wordEval step word)
  | [] => fixesOutside_id S
  | i :: word => by
      simpa [wordEval] using
        fixesOutside_comp (fixesOutside_wordEval step hstep word) (hstep i)

theorem mapsInto_wordEval {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, MapsInto S (step i)) :
    ∀ word : List ι, MapsInto S (wordEval step word)
  | [] => mapsInto_id S
  | i :: word => by
      simpa [wordEval] using
        mapsInto_comp (mapsInto_wordEval step hstep word) (hstep i)

theorem supportedOn_wordEval {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i)) :
    ∀ word : List ι, SupportedOn S (wordEval step word)
  | [] => supportedOn_id S
  | i :: word => by
      simpa [wordEval] using
        supportedOn_comp (supportedOn_wordEval step hstep word) (hstep i)

theorem supportedOn_wordEval_apply_of_mem_disjoint
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) {x : α} (hxT : x ∈ T) :
    wordEval step word x = x :=
  supportedOn_apply_of_mem_disjoint
    (supportedOn_wordEval step hstep word) hdisj hxT

theorem mapsInto_wordEval_of_supportedOn_disjoint
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) :
    MapsInto T (wordEval step word) := by
  intro x hxT
  rw [supportedOn_wordEval_apply_of_mem_disjoint
    step hstep hdisj word hxT]
  exact hxT

theorem supportedOn_wordEval_iterate_apply_of_mem_disjoint
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) (n : Nat) {x : α} (hxT : x ∈ T) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint
    (supportedOn_wordEval step hstep word) hdisj n hxT

theorem mapsInto_wordEval_iterate_of_supportedOn_disjoint
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) (n : Nat) :
    MapsInto T ((wordEval step word)^[n]) := by
  intro x hxT
  rw [supportedOn_wordEval_iterate_apply_of_mem_disjoint
    step hstep hdisj word n hxT]
  exact hxT

theorem commuteOfDisjointSupportedWordEvals
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedOn
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hdisj

theorem commuteOfDisjointSupportedWordEvals_symmSupports
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals
    leftStep rightStep hleft hright (setsDisjoint_symm hdisj)
    leftWord rightWord

theorem commuteOfDisjointSupportedWordEvalIterates
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedOn_iterates
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hdisj n k

theorem commuteOfDisjointSupportedWordEvalIterates_symmSupports
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright (setsDisjoint_symm hdisj)
    leftWord rightWord n k

theorem indexedSingletonSupportedWordEvalsCommute_of_injective
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p i} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p j} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (singletonIndexedSetsDisjoint_of_injective hp hij)
    leftWord rightWord

theorem indexedSingletonSupportedWordEvalsCommute_symmSupports_of_injective
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p j} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p i} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (setsDisjoint_symm (singletonIndexedSetsDisjoint_of_injective hp hij))
    leftWord rightWord

theorem indexedSingletonSupportedWordEvalIteratesCommute_of_injective
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p i} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p j} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (singletonIndexedSetsDisjoint_of_injective hp hij)
    leftWord rightWord n k

theorem indexedSingletonSupportedWordEvalIteratesCommute_symmSupports_of_injective
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p j} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p i} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (setsDisjoint_symm (singletonIndexedSetsDisjoint_of_injective hp hij))
    leftWord rightWord n k

theorem indexedSingletonProductSupportedWordEvalsCommute_of_injective_pair
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij)
    leftWord rightWord

theorem indexedSingletonProductSupportedWordEvalsCommute_symmSupports_of_injective_pair
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (setsDisjoint_symm
      (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij))
    leftWord rightWord

theorem indexedSingletonProductSupportedWordEvalIteratesCommute_of_injective_pair
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij)
    leftWord rightWord n k

theorem indexedSingletonProductSupportedWordEvalIteratesCommute_symm_of_injective_pair
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (setsDisjoint_symm
      (productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij))
    leftWord rightWord n k

theorem productCylinderLeftDisjointSupportedWordEvalsCommute
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hS : SetsDisjoint S S')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderDisjointOfLeftDisjoint S S' T T' hS)
    leftWord rightWord

theorem productCylinderRightDisjointSupportedWordEvalsCommute
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hT : SetsDisjoint T T')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderDisjointOfRightDisjoint S S' T T' hT)
    leftWord rightWord

theorem productCylinderLeftProjectionSeparatedSupportedWordEvalsCommute
    {ι κ α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π S S')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderDisjointOfLeftProjectionImagesDisjoint π S S' T T' hSep)
    leftWord rightWord

theorem productCylinderRightProjectionSeparatedSupportedWordEvalsCommute
    {ι κ α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π T T')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint π S S' T T' hSep)
    leftWord rightWord

theorem productCylinderLeftDisjointSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hS : SetsDisjoint S S')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates leftStep rightStep hleft hright
    (productCylinderDisjointOfLeftDisjoint S S' T T' hS)
    leftWord rightWord n k

theorem productCylinderRightDisjointSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hT : SetsDisjoint T T')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates leftStep rightStep hleft hright
    (productCylinderDisjointOfRightDisjoint S S' T T' hT)
    leftWord rightWord n k

theorem productCylinderLeftProjectionSeparatedSupportedWordEvalIteratesCommute
    {ι κ α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π S S')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates leftStep rightStep hleft hright
    (productCylinderDisjointOfLeftProjectionImagesDisjoint π S S' T T' hSep)
    leftWord rightWord n k

theorem productCylinderRightProjectionSeparatedSupportedWordEvalIteratesCommute
    {ι κ α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π T T')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint π S S' T T' hSep)
    leftWord rightWord n k

theorem projectionSeparatedSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedMapsCommute π
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hSep

theorem projectionSeparatedSupportedWordEvalsCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedMapsCommute_symmSupports π
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hSep

theorem projectionSeparatedSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedIteratesCommute π
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hSep n k

theorem projectionSeparatedSupportedWordEvalIteratesCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedIteratesCommute_symmSupports π
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hSep n k

theorem constantProjectionSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionSupportedMapsCommute π a b
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT hne

theorem constantProjectionSupportedWordEvalsCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionSupportedMapsCommute_symmSupports π a b
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT hne

theorem constantProjectionSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionSupportedIteratesCommute π a b
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT hne n k

theorem constantProjectionSupportedWordEvalIteratesCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionSupportedIteratesCommute_symmSupports π a b
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT hne n k

theorem constantProjectionAvoidsSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionAvoidsSupportedMapsCommute π value
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT

theorem avoidsConstantProjectionSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  avoidsConstantProjectionSupportedMapsCommute π value
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT

theorem constantProjectionAvoidsSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionAvoidsSupportedIteratesCommute π value
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT n k

theorem avoidsConstantProjectionSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  avoidsConstantProjectionSupportedIteratesCommute π value
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hT n k

theorem fiberSeparatedSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π value) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  fiberSeparatedSupportedMapsCommute π value S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hAvoid

theorem fiberSeparatedSupportedWordEvalsCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π value) (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  fiberSeparatedSupportedMapsCommute_symmSupports π value S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hAvoid

theorem fiberSeparatedSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π value) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  fiberSeparatedSupportedIteratesCommute π value S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hAvoid n k

theorem fiberSeparatedSupportedWordEvalIteratesCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π value) (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  fiberSeparatedSupportedIteratesCommute_symmSupports π value S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hAvoid n k

theorem constantAgainstFiberSupportedWordEvalsCommute
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π fiberValue) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantAgainstFiberSupportedMapsCommute π fiberValue supportValue S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hne

theorem constantAgainstFiberSupportedWordEvalsCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π fiberValue) (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantAgainstFiberSupportedMapsCommute_symmSupports π fiberValue supportValue S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hne

theorem constantAgainstFiberSupportedWordEvalIteratesCommute
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π fiberValue) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantAgainstFiberSupportedIteratesCommute π fiberValue supportValue S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hne n k

theorem constantAgainstFiberSupportedWordEvalIteratesCommute_symmSupports
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π fiberValue) (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantAgainstFiberSupportedIteratesCommute_symmSupports π fiberValue supportValue S
    (supportedOn_wordEval leftStep hleft leftWord)
    (supportedOn_wordEval rightStep hright rightWord) hS hne n k

theorem wordEvalSingleCycleOfRank
    {ι α : Type*} {N : Nat} [NeZero N]
    (step : ι → α → α) (word : List ι)
    (rank : α ≃ ZMod N)
    (hstep : ∀ x : α, rank (wordEval step word x) = rank x + 1) :
    Shared.IsSingleCycleMap (wordEval step word) :=
  Shared.single_cycle_of_zmod_rank_equiv
    (wordEval step word) rank hstep

def wordSkewStep {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (symbol : Symbol) : Base × Fiber → Base × Fiber :=
  Shared.skewProductMap (baseStep symbol) (fiberStep symbol)

def wordSkewEval {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber) :
    List Symbol → Base × Fiber → Base × Fiber :=
  wordEval (wordSkewStep baseStep fiberStep)

theorem wordSkewStep_bijective {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (hbase : ∀ symbol : Symbol, Function.Bijective (baseStep symbol))
    (hfiber : ∀ symbol : Symbol, ∀ base : Base,
      Function.Bijective (fiberStep symbol base))
    (symbol : Symbol) :
    Function.Bijective (wordSkewStep baseStep fiberStep symbol) :=
  Shared.skewProductMap_bijective
    (baseStep symbol) (fiberStep symbol)
    (hbase symbol) (hfiber symbol)

theorem wordSkewEval_bijective {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (hbase : ∀ symbol : Symbol, Function.Bijective (baseStep symbol))
    (hfiber : ∀ symbol : Symbol, ∀ base : Base,
      Function.Bijective (fiberStep symbol base)) :
    ∀ word : List Symbol,
      Function.Bijective (wordSkewEval baseStep fiberStep word) :=
  wordEval_bijective (wordSkewStep baseStep fiberStep)
    (wordSkewStep_bijective baseStep fiberStep hbase hfiber)

theorem wordSkewEvalSingleCycleOfRank
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (word : List Symbol)
    (rank : Base × Fiber ≃ ZMod N)
    (hstep : ∀ x : Base × Fiber,
      rank (wordSkewEval baseStep fiberStep word x) = rank x + 1) :
    Shared.IsSingleCycleMap (wordSkewEval baseStep fiberStep word) :=
  wordEvalSingleCycleOfRank
    (wordSkewStep baseStep fiberStep) word rank hstep

end WordSkew

export WordSkew
  (wordEval wordEval_append wordEval_bijective
   fixesOutside_wordEval mapsInto_wordEval supportedOn_wordEval
   supportedOn_wordEval_apply_of_mem_disjoint
   mapsInto_wordEval_of_supportedOn_disjoint
   supportedOn_wordEval_iterate_apply_of_mem_disjoint
   mapsInto_wordEval_iterate_of_supportedOn_disjoint
   commuteOfDisjointSupportedWordEvals
   commuteOfDisjointSupportedWordEvals_symmSupports
   commuteOfDisjointSupportedWordEvalIterates
   commuteOfDisjointSupportedWordEvalIterates_symmSupports
   indexedSingletonSupportedWordEvalsCommute_of_injective
   indexedSingletonSupportedWordEvalsCommute_symmSupports_of_injective
   indexedSingletonSupportedWordEvalIteratesCommute_of_injective
   indexedSingletonSupportedWordEvalIteratesCommute_symmSupports_of_injective
   indexedSingletonProductSupportedWordEvalsCommute_of_injective_pair
   indexedSingletonProductSupportedWordEvalsCommute_symmSupports_of_injective_pair
   indexedSingletonProductSupportedWordEvalIteratesCommute_of_injective_pair
   indexedSingletonProductSupportedWordEvalIteratesCommute_symm_of_injective_pair
   productCylinderLeftDisjointSupportedWordEvalsCommute
   productCylinderRightDisjointSupportedWordEvalsCommute
   productCylinderLeftProjectionSeparatedSupportedWordEvalsCommute
   productCylinderRightProjectionSeparatedSupportedWordEvalsCommute
   productCylinderLeftDisjointSupportedWordEvalIteratesCommute
   productCylinderRightDisjointSupportedWordEvalIteratesCommute
   productCylinderLeftProjectionSeparatedSupportedWordEvalIteratesCommute
   productCylinderRightProjectionSeparatedSupportedWordEvalIteratesCommute
   projectionSeparatedSupportedWordEvalsCommute
   projectionSeparatedSupportedWordEvalsCommute_symmSupports
   projectionSeparatedSupportedWordEvalIteratesCommute
   projectionSeparatedSupportedWordEvalIteratesCommute_symmSupports
   constantProjectionSupportedWordEvalsCommute
   constantProjectionSupportedWordEvalsCommute_symmSupports
   constantProjectionSupportedWordEvalIteratesCommute
   constantProjectionSupportedWordEvalIteratesCommute_symmSupports
   constantProjectionAvoidsSupportedWordEvalsCommute
   avoidsConstantProjectionSupportedWordEvalsCommute
   constantProjectionAvoidsSupportedWordEvalIteratesCommute
   avoidsConstantProjectionSupportedWordEvalIteratesCommute
   fiberSeparatedSupportedWordEvalsCommute
   fiberSeparatedSupportedWordEvalsCommute_symmSupports
   fiberSeparatedSupportedWordEvalIteratesCommute
   fiberSeparatedSupportedWordEvalIteratesCommute_symmSupports
   constantAgainstFiberSupportedWordEvalsCommute
   constantAgainstFiberSupportedWordEvalsCommute_symmSupports
   constantAgainstFiberSupportedWordEvalIteratesCommute
   constantAgainstFiberSupportedWordEvalIteratesCommute_symmSupports
   wordEvalSingleCycleOfRank wordSkewStep wordSkewEval
   wordSkewStep_bijective wordSkewEval_bijective
   wordSkewEvalSingleCycleOfRank)

end EvenV11
