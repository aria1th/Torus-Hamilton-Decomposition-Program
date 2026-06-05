import EvenV11.WordSkew

namespace EvenV11
namespace EndpointRowPlacement

def rowPlacementSupport {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row) :
    Set (Parent × NewCoord) :=
  ProductCylinder ({(placement row).1} : Set Parent)
    ({(placement row).2} : Set NewCoord)

theorem rowPlacementSupport_mem {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row)
    (x : Parent × NewCoord) :
    x ∈ rowPlacementSupport placement row ↔ x = placement row := by
  exact productCylinder_singleton_singleton_mem
    (placement row).1 (placement row).2 x

theorem rowPlacementSupport_eq_singleton {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row) :
    rowPlacementSupport placement row =
      ({placement row} : Set (Parent × NewCoord)) := by
  exact productCylinderSingletonSingleton_eq_singleton
    (placement row).1 (placement row).2

def rowPlacementSupportSet {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) :
    Set (Parent × NewCoord) :=
  ⋃ row, rowPlacementSupport placement row

theorem rowPlacementSupportSet_eq_iUnion
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) :
    rowPlacementSupportSet placement =
      ⋃ row, rowPlacementSupport placement row :=
  rfl

theorem rowPlacementSupport_subset_supportSet
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row) :
    rowPlacementSupport placement row ⊆
      rowPlacementSupportSet placement := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨row, hx⟩

theorem rowPlacementSupportSet_mem {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (x : Parent × NewCoord) :
    x ∈ rowPlacementSupportSet placement ↔
      ∃ row : Row, x = placement row := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨row, hrow⟩
    exact ⟨row, (rowPlacementSupport_mem placement row x).mp hrow⟩
  · rintro ⟨row, hx⟩
    exact Set.mem_iUnion.mpr
      ⟨row, (rowPlacementSupport_mem placement row x).mpr hx⟩

theorem rowPlacement_ne_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1) :
    placement leftRow ≠ placement rightRow := by
  intro hplacement
  exact hparent (congrArg Prod.fst hplacement)

theorem rowPlacement_ne_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2) :
    placement leftRow ≠ placement rightRow := by
  intro hplacement
  exact hnewCoord (congrArg Prod.snd hplacement)

theorem rowPlacementSupports_disjoint_of_injective
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) := by
  rw [rowPlacementSupport_eq_singleton, rowPlacementSupport_eq_singleton]
  exact singletonIndexedSetsDisjoint_of_injective hplacement hrow

theorem rowPlacementSupports_disjoint_of_ne_placement
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) := by
  rw [rowPlacementSupport_eq_singleton, rowPlacementSupport_eq_singleton]
  exact singletonSetsDisjoint_of_ne hplacement

theorem rowPlacementSupports_disjoint_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent)

theorem rowPlacementSupports_disjoint_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord)

theorem rowPlacementSupportedMapsCommute_of_injective
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  commuteOfDisjointSupportedOn hleft hright
    (rowPlacementSupports_disjoint_of_injective hplacement hrow)

theorem rowPlacementSupportedMapsCommute_of_ne_placement
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  commuteOfDisjointSupportedOn hleft hright
    (rowPlacementSupports_disjoint_of_ne_placement hplacement)

theorem rowPlacementSupportedMapsCommute_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent) hleft hright

theorem rowPlacementSupportedMapsCommute_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord) hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_injective
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  commuteOfDisjointSupportedOn hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_injective hplacement hrow))

theorem rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  commuteOfDisjointSupportedOn hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_ne_placement hplacement))

theorem rowPlacementSupportedMapsCommute_symmSupports_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent) hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord) hleft hright

theorem rowPlacementSupportedIteratesCommute_of_injective
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  commuteOfDisjointSupportedOn_iterates hleft hright
    (rowPlacementSupports_disjoint_of_injective hplacement hrow) n k

theorem rowPlacementSupportedIteratesCommute_of_ne_placement
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  commuteOfDisjointSupportedOn_iterates hleft hright
    (rowPlacementSupports_disjoint_of_ne_placement hplacement) n k

theorem rowPlacementSupportedIteratesCommute_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent) hleft hright n k

theorem rowPlacementSupportedIteratesCommute_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord) hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_injective
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  commuteOfDisjointSupportedOn_iterates hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_injective hplacement hrow)) n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  commuteOfDisjointSupportedOn_iterates hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_ne_placement hplacement)) n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_parent_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent) hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_newCoord_ne
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord) hleft hright n k

theorem rowPlacementSupportedWordEvalsCommute_of_injective
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (rowPlacementSupports_disjoint_of_injective hplacement hrow)
    leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_ne_placement
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (rowPlacementSupports_disjoint_of_ne_placement hplacement)
    leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_parent_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent)
    leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_newCoord_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord)
    leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_injective
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_injective hplacement hrow))
    leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_ne_placement hplacement))
    leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_parent_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent)
    leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_newCoord_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord)
    leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalIteratesCommute_of_injective
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (rowPlacementSupports_disjoint_of_injective hplacement hrow)
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (rowPlacementSupports_disjoint_of_ne_placement hplacement)
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_parent_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent)
    leftStep rightStep hleft hright leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_newCoord_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord)
    leftStep rightStep hleft hright leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_injective
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_injective hplacement hrow))
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (setsDisjoint_symm
      (rowPlacementSupports_disjoint_of_ne_placement hplacement))
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_parent_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_parent_ne hparent)
    leftStep rightStep hleft hright leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_newCoord_ne
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement
    (rowPlacement_ne_of_newCoord_ne hnewCoord)
    leftStep rightStep hleft hright leftWord rightWord n k

structure RowWordPlacementCertificate
    (Row Symbol Parent NewCoord : Type*) where
  placement : Row → Parent × NewCoord
  step : Row → Symbol → Parent × NewCoord → Parent × NewCoord
  word : Row → List Symbol
  placementInjective : Function.Injective placement
  supported :
    ∀ row : Row, ∀ symbol : Symbol,
      SupportedOn (rowPlacementSupport placement row) (step row symbol)

def RowWordPlacementCertificate.eval
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) : Parent × NewCoord → Parent × NewCoord :=
  wordEval (C.step row) (C.word row)

theorem rowWordPlacementCertificate_eval
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  rfl

theorem rowWordPlacementCertificate_eval_supported
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  supportedOn_wordEval (C.step row) (C.supported row) (C.word row)

theorem rowWordPlacementCertificate_step_supportedOn_supportSet
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  supportedOn_mono
    (rowPlacementSupport_subset_supportSet C.placement row)
    (C.supported row symbol)

theorem rowWordPlacementCertificate_eval_supportedOn_supportSet
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  supportedOn_mono
    (rowPlacementSupport_subset_supportSet C.placement row)
    (rowWordPlacementCertificate_eval_supported C row)

theorem rowWordPlacementCertificate_evalWord_supportedOn_supportSet
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (rows : List Row) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  supportedOn_wordEval C.eval
    (rowWordPlacementCertificate_eval_supportedOn_supportSet C) rows

theorem rowWordPlacementCertificate_evalWordIter_supportedOn_support
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (rows : List Row) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  supportedOn_iterate
    (rowWordPlacementCertificate_evalWord_supportedOn_supportSet C rows) n

theorem rowWordPlacementCertificate_supports_disjoint
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  rowPlacementSupports_disjoint_of_injective
    C.placementInjective hrow

theorem rowWordPlacementCertificate_evalsCommute
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  rowPlacementSupportedWordEvalsCommute_of_injective
    C.placementInjective hrow (C.step leftRow) (C.step rightRow)
    (C.supported leftRow) (C.supported rightRow)
    (C.word leftRow) (C.word rightRow)

theorem rowWordPlacementCertificate_evalIteratesCommute
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_injective
    C.placementInjective hrow (C.step leftRow) (C.step rightRow)
    (C.supported leftRow) (C.supported rightRow)
    (C.word leftRow) (C.word rightRow) n k

structure FinRowWordPlacementCertificate
    (rowCount : Nat) (Symbol Parent NewCoord : Type*) where
  placement : Fin rowCount → Parent × NewCoord
  step :
    Fin rowCount → Symbol →
      Parent × NewCoord → Parent × NewCoord
  word : Fin rowCount → List Symbol
  placementNe :
    ∀ leftRow rightRow : Fin rowCount,
      leftRow ≠ rightRow → placement leftRow ≠ placement rightRow
  supported :
    ∀ row : Fin rowCount, ∀ symbol : Symbol,
      SupportedOn (rowPlacementSupport placement row) (step row symbol)

def FinRowWordPlacementCertificate.eval
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    Parent × NewCoord → Parent × NewCoord :=
  wordEval (C.step row) (C.word row)

theorem finRowWordPlacementCertificate_eval
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  rfl

theorem finRowWordPlacementCertificate_placement_injective
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord) :
    Function.Injective C.placement := by
  intro leftRow rightRow hplacement
  by_cases hrow : leftRow = rightRow
  · exact hrow
  · exact False.elim (C.placementNe leftRow rightRow hrow hplacement)

def FinRowWordPlacementCertificate.toRowWordPlacementCertificate
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord) :
    RowWordPlacementCertificate (Fin rowCount) Symbol Parent NewCoord where
  placement := C.placement
  step := C.step
  word := C.word
  placementInjective :=
    finRowWordPlacementCertificate_placement_injective C
  supported := C.supported

theorem finRowWordPlacementCertificate_eval_supported
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  supportedOn_wordEval (C.step row) (C.supported row) (C.word row)

theorem finRowWordPlacementCertificate_step_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  rowWordPlacementCertificate_step_supportedOn_supportSet
    C.toRowWordPlacementCertificate row symbol

theorem finRowWordPlacementCertificate_eval_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  rowWordPlacementCertificate_eval_supportedOn_supportSet
    C.toRowWordPlacementCertificate row

theorem finRowWordPlacementCertificate_evalWord_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  rowWordPlacementCertificate_evalWord_supportedOn_supportSet
    C.toRowWordPlacementCertificate rows

theorem finRowWordPlacementCertificate_evalWordIter_supportedOn_support
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  rowWordPlacementCertificate_evalWordIter_supportedOn_support
    C.toRowWordPlacementCertificate rows n

theorem finRowWordPlacementCertificate_supports_disjoint
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  rowPlacementSupports_disjoint_of_ne_placement
    (C.placementNe leftRow rightRow hrow)

theorem finRowWordPlacementCertificate_evalsCommute
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  rowPlacementSupportedWordEvalsCommute_of_injective
    (finRowWordPlacementCertificate_placement_injective C)
    hrow (C.step leftRow) (C.step rightRow)
    (C.supported leftRow) (C.supported rightRow)
    (C.word leftRow) (C.word rightRow)

theorem finRowWordPlacementCertificate_evalIteratesCommute
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_injective
    (finRowWordPlacementCertificate_placement_injective C)
    hrow (C.step leftRow) (C.step rightRow)
    (C.supported leftRow) (C.supported rightRow)
    (C.word leftRow) (C.word rightRow) n k

structure CoordinateSeparatedFinRowWordPlacementCertificate
    (rowCount : Nat) (Symbol Parent NewCoord : Type*) where
  placement : Fin rowCount → Parent × NewCoord
  step :
    Fin rowCount → Symbol →
      Parent × NewCoord → Parent × NewCoord
  word : Fin rowCount → List Symbol
  coordinateSeparated :
    ∀ leftRow rightRow : Fin rowCount,
      leftRow ≠ rightRow →
        (placement leftRow).1 ≠ (placement rightRow).1 ∨
          (placement leftRow).2 ≠ (placement rightRow).2
  supported :
    ∀ row : Fin rowCount, ∀ symbol : Symbol,
      SupportedOn (rowPlacementSupport placement row) (step row symbol)

def CoordinateSeparatedFinRowWordPlacementCertificate.eval
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    Parent × NewCoord → Parent × NewCoord :=
  wordEval (C.step row) (C.word row)

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  rfl

theorem coordinateSeparatedFinRowWordPlacementCertificate_placement_ne
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    C.placement leftRow ≠ C.placement rightRow := by
  cases C.coordinateSeparated leftRow rightRow hrow with
  | inl hparent => exact rowPlacement_ne_of_parent_ne hparent
  | inr hnewCoord => exact rowPlacement_ne_of_newCoord_ne hnewCoord

def CoordinateSeparatedFinRowWordPlacementCertificate.toFinRowWordPlacementCertificate
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord) :
    FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord where
  placement := C.placement
  step := C.step
  word := C.word
  placementNe :=
    fun leftRow rightRow hrow =>
      coordinateSeparatedFinRowWordPlacementCertificate_placement_ne
        C (leftRow := leftRow) (rightRow := rightRow) hrow
  supported := C.supported

def CoordinateSeparatedFinRowWordPlacementCertificate.toRowWordPlacementCertificate
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord) :
    RowWordPlacementCertificate (Fin rowCount) Symbol Parent NewCoord :=
  C.toFinRowWordPlacementCertificate.toRowWordPlacementCertificate

theorem coordinateSeparatedFinRowWordPlacementCertificate_placement_injective
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord) :
    Function.Injective C.placement :=
  finRowWordPlacementCertificate_placement_injective
    C.toFinRowWordPlacementCertificate

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval_supported
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  finRowWordPlacementCertificate_eval_supported
    C.toFinRowWordPlacementCertificate row

theorem coordinateSeparatedFinRowWordPlacementCertificate_step_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  finRowWordPlacementCertificate_step_supportedOn_supportSet
    C.toFinRowWordPlacementCertificate row symbol

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  finRowWordPlacementCertificate_eval_supportedOn_supportSet
    C.toFinRowWordPlacementCertificate row

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalWord_supportedOn_supportSet
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  finRowWordPlacementCertificate_evalWord_supportedOn_supportSet
    C.toFinRowWordPlacementCertificate rows

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalWordIter_supportedOn_support
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  finRowWordPlacementCertificate_evalWordIter_supportedOn_support
    C.toFinRowWordPlacementCertificate rows n

theorem coordinateSeparatedFinRowWordPlacementCertificate_supports_disjoint
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  rowPlacementSupports_disjoint_of_ne_placement
    (coordinateSeparatedFinRowWordPlacementCertificate_placement_ne
      C hrow)

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalsCommute
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  finRowWordPlacementCertificate_evalsCommute
    C.toFinRowWordPlacementCertificate hrow

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalIteratesCommute
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  finRowWordPlacementCertificate_evalIteratesCommute
    C.toFinRowWordPlacementCertificate hrow n k

end EndpointRowPlacement

export EndpointRowPlacement
  (rowPlacementSupport
   rowPlacementSupport_mem
   rowPlacementSupport_eq_singleton
   rowPlacementSupportSet
   rowPlacementSupportSet_eq_iUnion
   rowPlacementSupport_subset_supportSet
   rowPlacementSupportSet_mem
   rowPlacement_ne_of_parent_ne
   rowPlacement_ne_of_newCoord_ne
   rowPlacementSupports_disjoint_of_injective
   rowPlacementSupports_disjoint_of_ne_placement
   rowPlacementSupports_disjoint_of_parent_ne
   rowPlacementSupports_disjoint_of_newCoord_ne
   rowPlacementSupportedMapsCommute_of_injective
   rowPlacementSupportedMapsCommute_of_ne_placement
   rowPlacementSupportedMapsCommute_of_parent_ne
   rowPlacementSupportedMapsCommute_of_newCoord_ne
   rowPlacementSupportedMapsCommute_symmSupports_of_injective
   rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement
   rowPlacementSupportedMapsCommute_symmSupports_of_parent_ne
   rowPlacementSupportedMapsCommute_symmSupports_of_newCoord_ne
   rowPlacementSupportedIteratesCommute_of_injective
   rowPlacementSupportedIteratesCommute_of_ne_placement
   rowPlacementSupportedIteratesCommute_of_parent_ne
   rowPlacementSupportedIteratesCommute_of_newCoord_ne
   rowPlacementSupportedIteratesCommute_symmSupports_of_injective
   rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement
   rowPlacementSupportedIteratesCommute_symmSupports_of_parent_ne
   rowPlacementSupportedIteratesCommute_symmSupports_of_newCoord_ne
   rowPlacementSupportedWordEvalsCommute_of_injective
   rowPlacementSupportedWordEvalsCommute_of_ne_placement
   rowPlacementSupportedWordEvalsCommute_of_parent_ne
   rowPlacementSupportedWordEvalsCommute_of_newCoord_ne
   rowPlacementSupportedWordEvalsCommute_symmSupports_of_injective
   rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement
   rowPlacementSupportedWordEvalsCommute_symmSupports_of_parent_ne
   rowPlacementSupportedWordEvalsCommute_symmSupports_of_newCoord_ne
   rowPlacementSupportedWordEvalIteratesCommute_of_injective
   rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement
   rowPlacementSupportedWordEvalIteratesCommute_of_parent_ne
   rowPlacementSupportedWordEvalIteratesCommute_of_newCoord_ne
   rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_injective
   rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement
   rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_parent_ne
   rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_newCoord_ne
   RowWordPlacementCertificate
   RowWordPlacementCertificate.eval
   rowWordPlacementCertificate_eval
   rowWordPlacementCertificate_eval_supported
   rowWordPlacementCertificate_step_supportedOn_supportSet
   rowWordPlacementCertificate_eval_supportedOn_supportSet
   rowWordPlacementCertificate_evalWord_supportedOn_supportSet
   rowWordPlacementCertificate_evalWordIter_supportedOn_support
   rowWordPlacementCertificate_supports_disjoint
   rowWordPlacementCertificate_evalsCommute
   rowWordPlacementCertificate_evalIteratesCommute
   FinRowWordPlacementCertificate
   FinRowWordPlacementCertificate.eval
   finRowWordPlacementCertificate_eval
   finRowWordPlacementCertificate_placement_injective
   FinRowWordPlacementCertificate.toRowWordPlacementCertificate
   finRowWordPlacementCertificate_eval_supported
   finRowWordPlacementCertificate_step_supportedOn_supportSet
   finRowWordPlacementCertificate_eval_supportedOn_supportSet
   finRowWordPlacementCertificate_evalWord_supportedOn_supportSet
   finRowWordPlacementCertificate_evalWordIter_supportedOn_support
   finRowWordPlacementCertificate_supports_disjoint
   finRowWordPlacementCertificate_evalsCommute
   finRowWordPlacementCertificate_evalIteratesCommute
   CoordinateSeparatedFinRowWordPlacementCertificate
   CoordinateSeparatedFinRowWordPlacementCertificate.eval
   coordinateSeparatedFinRowWordPlacementCertificate_eval
   coordinateSeparatedFinRowWordPlacementCertificate_placement_ne
   CoordinateSeparatedFinRowWordPlacementCertificate.toFinRowWordPlacementCertificate
   CoordinateSeparatedFinRowWordPlacementCertificate.toRowWordPlacementCertificate
   coordinateSeparatedFinRowWordPlacementCertificate_placement_injective
   coordinateSeparatedFinRowWordPlacementCertificate_eval_supported
   coordinateSeparatedFinRowWordPlacementCertificate_step_supportedOn_supportSet
   coordinateSeparatedFinRowWordPlacementCertificate_eval_supportedOn_supportSet
   coordinateSeparatedFinRowWordPlacementCertificate_evalWord_supportedOn_supportSet
   coordinateSeparatedFinRowWordPlacementCertificate_evalWordIter_supportedOn_support
   coordinateSeparatedFinRowWordPlacementCertificate_supports_disjoint
   coordinateSeparatedFinRowWordPlacementCertificate_evalsCommute
   coordinateSeparatedFinRowWordPlacementCertificate_evalIteratesCommute)

end EvenV11
