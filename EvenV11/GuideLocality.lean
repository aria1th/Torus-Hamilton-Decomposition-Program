import EvenV11.Basic

namespace EvenV11
namespace GuideLocality

def CenterAllowed {Row Center : Type*}
    (center : Row → Center) (allowedCenters : Set Center) : Set Row :=
  {row | center row ∈ allowedCenters}

def VanishesOutside {α Value : Type*} [Zero Value]
    (theta : α → Value) (allowed : Set α) : Prop :=
  ∀ x : α, x ∉ allowed → theta x = 0

def VanishesOutsideGuide {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (allowedCenters : Set Center) : Prop :=
  VanishesOutside theta (CenterAllowed center allowedCenters)

def GuideCenterListSet {Center : Type*} (centers : List Center) :
    Set Center :=
  {c | c ∈ centers}

def VanishesOutsideGuideList {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (centers : List Center) : Prop :=
  VanishesOutsideGuide theta center (GuideCenterListSet centers)

def SymmetricEndpointPairs {α : Type*} (visible : α) (zeros : List α) :
    List (α × α) :=
  List.flatMap (fun z => [(visible, z), (z, visible)]) zeros

structure BoundaryVisibleEndpointListCertificate {Center : Type*}
    (boundary : List Center) (visible : Center)
    (guideCenters : List Center) where
  centers : List Center
  endpointCert :
    ∀ c : Center, c ∈ centers →
      ∃ p : Center × Center,
        (p.1 ∈ boundary ∧ p.2 ∈ boundary) ∧
          (p.1 = visible ∨ p.2 = visible) ∧
          p.1 ≠ p.2 ∧
          c ∈ guideCenters ∧
          (c = p.1 ∨ c = p.2)

theorem mem_symmetricEndpointPairs {α : Type*}
    (visible : α) (zeros : List α) (p : α × α) :
    p ∈ SymmetricEndpointPairs visible zeros ↔
      (p.1 = visible ∧ p.2 ∈ zeros) ∨
        (p.2 = visible ∧ p.1 ∈ zeros) := by
  constructor
  · intro hp
    rw [SymmetricEndpointPairs, List.mem_flatMap] at hp
    rcases hp with ⟨z, hz, hp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · left
      exact ⟨by simp [hp], by simpa [hp] using hz⟩
    · right
      exact ⟨by simp [hp], by simpa [hp] using hz⟩
  · intro hp
    rw [SymmetricEndpointPairs, List.mem_flatMap]
    rcases p with ⟨x, y⟩
    rcases hp with hp | hp
    · rcases hp with ⟨hx, hy⟩
      have hx' : x = visible := by simpa using hx
      subst x
      refine ⟨y, hy, ?_⟩
      simp
    · rcases hp with ⟨hy, hx⟩
      have hy' : y = visible := by simpa using hy
      subst y
      refine ⟨x, hx, ?_⟩
      simp

theorem endpoints_mem_of_mem_symmetricEndpointPairs {α : Type*}
    (visible : α) (zeros boundary : List α)
    (hvisible : visible ∈ boundary)
    (hzeros : ∀ z : α, z ∈ zeros → z ∈ boundary)
    {p : α × α} (hp : p ∈ SymmetricEndpointPairs visible zeros) :
    p.1 ∈ boundary ∧ p.2 ∈ boundary := by
  have hpair := (mem_symmetricEndpointPairs visible zeros p).1 hp
  rcases hpair with hpair | hpair
  · exact ⟨by simpa [hpair.1], hzeros p.2 hpair.2⟩
  · exact ⟨hzeros p.1 hpair.2, by simpa [hpair.1]⟩

theorem mem_of_nonzero_of_vanishesOutside
    {α Value : Type*} [Zero Value]
    (theta : α → Value) (allowed : Set α)
    (hzero : VanishesOutside theta allowed) {x : α}
    (hne : theta x ≠ 0) :
    x ∈ allowed := by
  by_contra hx
  exact hne (hzero x hx)

theorem theta_eq_zero_of_not_mem_of_vanishesOutside
    {α Value : Type*} [Zero Value]
    (theta : α → Value) (allowed : Set α)
    (hzero : VanishesOutside theta allowed) {x : α}
    (hx : x ∉ allowed) :
    theta x = 0 :=
  hzero x hx

theorem theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (allowedCenters : Set Center)
    (hzero : VanishesOutsideGuide theta center allowedCenters)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  hzero row hcenter

theorem theta_eq_zero_of_center_not_mem_guideList
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (centers : List Center)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hcenter : center row ∉ centers) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    (GuideCenterListSet centers) hzero hcenter

theorem vanishesOutside_of_subset
    {α Value : Type*} [Zero Value]
    (theta : α → Value) {actual allowed : Set α}
    (hsubset : actual ⊆ allowed)
    (hzero : VanishesOutside theta actual) :
    VanishesOutside theta allowed := by
  intro x hxAllowed
  exact hzero x (fun hxActual => hxAllowed (hsubset hxActual))

theorem theta_eq_zero_of_not_mem_of_vanishesOutside_subset
    {α Value : Type*} [Zero Value]
    (theta : α → Value) {actual allowed : Set α}
    (hsubset : actual ⊆ allowed)
    (hzero : VanishesOutside theta actual) {x : α}
    (hxAllowed : x ∉ allowed) :
    theta x = 0 :=
  theta_eq_zero_of_not_mem_of_vanishesOutside theta allowed
    (vanishesOutside_of_subset theta hsubset hzero) hxAllowed

theorem vanishesOutsideGuide_of_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters) :
    VanishesOutsideGuide theta center allowedCenters :=
  vanishesOutside_of_subset theta (fun _ hrow => hsubset hrow) hzero

theorem theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hcenter

theorem vanishesOutsideGuide_of_list_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers) :
    VanishesOutsideGuide theta center allowedCenters :=
  vanishesOutsideGuide_of_subset theta center
    (fun c hc => hsubset c hc) hzero

theorem theta_eq_zero_of_center_not_mem_of_guideList_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    allowedCenters
    (vanishesOutsideGuide_of_list_subset theta center hsubset hzero)
    hcenter

theorem guideLocalityOfNonzero
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (allowedCenters : Set Center)
    (hzero : VanishesOutsideGuide theta center allowedCenters)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  mem_of_nonzero_of_vanishesOutside
    theta (CenterAllowed center allowedCenters) hzero hne

theorem guideLocalityOfNonzero_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero theta center allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hne

theorem guideLocalityOfNonzero_list
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (centers : List Center)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ centers :=
  guideLocalityOfNonzero theta center (GuideCenterListSet centers)
    hzero hne

theorem guideLocalityOfNonzero_list_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero theta center allowedCenters
    (vanishesOutsideGuide_of_list_subset theta center hsubset hzero) hne

def TripleGuideSet {Center : Type*} (left middle right : Center) :
    Set Center :=
  {c | c = left ∨ c = middle ∨ c = right}

def AdditiveTripleGuideSet {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) : Set Center :=
  TripleGuideSet (rho - delta) rho (rho + delta)

def TripleGuideList {Center : Type*} (left middle right : Center) :
    List Center :=
  [left, middle, right]

def AdditiveTripleGuideList {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) : List Center :=
  TripleGuideList (rho - delta) rho (rho + delta)

theorem mem_tripleGuideList_iff {Center : Type*}
    (left middle right c : Center) :
    c ∈ TripleGuideList left middle right ↔
      c = left ∨ c = middle ∨ c = right := by
  simp [TripleGuideList]

theorem guideCenterListSet_tripleGuideList {Center : Type*}
    (left middle right : Center) :
    GuideCenterListSet (TripleGuideList left middle right) =
      TripleGuideSet left middle right := by
  ext c
  simp [GuideCenterListSet, TripleGuideSet, TripleGuideList]

theorem mem_additiveTripleGuideList_iff
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta c : Center) :
    c ∈ AdditiveTripleGuideList rho delta ↔
      c = rho - delta ∨ c = rho ∨ c = rho + delta := by
  simp [AdditiveTripleGuideList, TripleGuideList]

theorem guideCenterListSet_additiveTripleGuideList
    {Center : Type*} [Sub Center] [Add Center] (rho delta : Center) :
    GuideCenterListSet (AdditiveTripleGuideList rho delta) =
      AdditiveTripleGuideSet rho delta := by
  simp [AdditiveTripleGuideList, AdditiveTripleGuideSet,
    guideCenterListSet_tripleGuideList]

theorem vanishesOutsideGuide_tripleGuideList_iff
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) :
    VanishesOutsideGuideList theta center
        (TripleGuideList left middle right) ↔
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right) := by
  rw [VanishesOutsideGuideList, guideCenterListSet_tripleGuideList]

theorem vanishesOutsideGuide_additiveTripleGuideList_iff
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) :
    VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta) ↔
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta) := by
  rw [VanishesOutsideGuideList,
    guideCenterListSet_additiveTripleGuideList]

theorem mem_tripleGuideSet_middle {Center : Type*}
    (left middle right : Center) :
    middle ∈ TripleGuideSet left middle right := by
  exact Or.inr (Or.inl rfl)

theorem mem_tripleGuideSet_left {Center : Type*}
    (left middle right : Center) :
    left ∈ TripleGuideSet left middle right := by
  exact Or.inl rfl

theorem mem_tripleGuideSet_right {Center : Type*}
    (left middle right : Center) :
    right ∈ TripleGuideSet left middle right := by
  exact Or.inr (Or.inr rfl)

theorem mem_additiveTripleGuideSet_middle
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho ∈ AdditiveTripleGuideSet rho delta :=
  mem_tripleGuideSet_middle (rho - delta) rho (rho + delta)

theorem mem_additiveTripleGuideSet_left
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho - delta ∈ AdditiveTripleGuideSet rho delta :=
  mem_tripleGuideSet_left (rho - delta) rho (rho + delta)

theorem mem_additiveTripleGuideSet_right
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho + delta ∈ AdditiveTripleGuideSet rho delta :=
  mem_tripleGuideSet_right (rho - delta) rho (rho + delta)

theorem theta_eq_zero_of_center_not_mem_tripleGuideList
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (TripleGuideList left middle right))
    {row : Row}
    (hcenter : center row ∉ TripleGuideList left middle right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_guideList theta center
    (TripleGuideList left middle right) hzero hcenter

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideList
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row}
    (hcenter : center row ∉ AdditiveTripleGuideList rho delta) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_guideList theta center
    (AdditiveTripleGuideList rho delta) hzero hcenter

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row}
    (hcenter : center row ∉ TripleGuideSet left middle right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    (TripleGuideSet left middle right) hzero hcenter

theorem theta_eq_zero_of_center_ne_tripleGuideSet
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row}
    (hleft : center row ≠ left)
    (hmiddle : center row ≠ middle)
    (hright : center row ≠ right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet theta center
    left middle right hzero (by
      intro hcenter
      rcases hcenter with hcenter | hcenter | hcenter
      · exact hleft hcenter
      · exact hmiddle hcenter
      · exact hright hcenter)

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hcenter :
      center row ∉ (TripleGuideSet left middle right ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    (TripleGuideSet left middle right ∩ allowedCenters) hzero hcenter

theorem theta_eq_zero_of_center_ne_tripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hleft : center row ≠ left)
    (hmiddle : center row ≠ middle)
    (hright : center row ≠ right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter theta center
    left middle right allowedCenters hzero (by
      intro hcenter
      rcases hcenter.1 with hcenter | hcenter | hcenter
      · exact hleft hcenter
      · exact hmiddle hcenter
      · exact hright hcenter)

theorem theta_eq_zero_of_center_not_mem_allowed_tripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hallowed : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter theta center
    left middle right allowedCenters hzero (by
      intro hcenter
      exact hallowed hcenter.2)

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter theta center
    (rho - delta) rho (rho + delta) allowedCenters hzero hcenter

theorem theta_eq_zero_of_center_ne_additiveTripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hleft : center row ≠ rho - delta)
    (hmiddle : center row ≠ rho)
    (hright : center row ≠ rho + delta) :
    theta row = 0 :=
  theta_eq_zero_of_center_ne_tripleGuideSet_inter theta center
    (rho - delta) rho (rho + delta) allowedCenters hzero
    hleft hmiddle hright

theorem theta_eq_zero_of_center_not_mem_allowed_additiveTripleGuideSet_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hallowed : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_allowed_tripleGuideSet_inter theta center
    (rho - delta) rho (rho + delta) allowedCenters hzero hallowed

theorem guideLocalityOfNonzero_triple
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row} (hne : theta row ≠ 0) :
    center row = left ∨ center row = middle ∨ center row = right :=
  guideLocalityOfNonzero theta center
    (TripleGuideSet left middle right) hzero hne

theorem guideLocalityOfNonzero_tripleGuideList
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (TripleGuideList left middle right))
    {row : Row} (hne : theta row ≠ 0) :
    center row = left ∨ center row = middle ∨ center row = right :=
  (mem_tripleGuideList_iff left middle right (center row)).1
    (guideLocalityOfNonzero_list theta center
      (TripleGuideList left middle right) hzero hne)

theorem guideLocalityOfNonzero_additiveTripleGuideList
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row} (hne : theta row ≠ 0) :
    center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta :=
  guideLocalityOfNonzero_tripleGuideList theta center
    (rho - delta) rho (rho + delta) hzero hne

theorem guideLocalityOfNonzero_triple_inter
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = left ∨ center row = middle ∨ center row = right) ∧
      center row ∈ allowedCenters := by
  exact guideLocalityOfNonzero theta center
    (TripleGuideSet left middle right ∩ allowedCenters) hzero hne

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet_inter_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (left middle right : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ TripleGuideSet left middle right ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter :
      center row ∉ (TripleGuideSet left middle right ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter theta center
    left middle right allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hcenter

theorem guideLocalityOfNonzero_triple_inter_subset
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (left middle right : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ TripleGuideSet left middle right ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = left ∨ center row = middle ∨ center row = right) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_triple_inter theta center
    left middle right allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hne

theorem guideLocalityOfNonzero_additiveTriple_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_triple_inter theta center
    (rho - delta) rho (rho + delta) allowedCenters hzero hne

theorem theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter theta center
    rho delta allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hcenter

theorem guideLocalityOfNonzero_additiveGuide_inter_subset
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveTriple_inter theta center
    rho delta allowedCenters
    (vanishesOutsideGuide_of_subset theta center hsubset hzero) hne

theorem theta_eq_zero_of_center_not_mem_additiveGuide_inter_list
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      ∀ c : Center, c ∈ centers →
        c ∈ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset theta center
    rho delta allowedCenters (fun c hc => hsubset c hc) hzero hcenter

theorem guideLocalityOfNonzero_additiveGuide_inter_list
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      ∀ c : Center, c ∈ centers →
        c ∈ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveGuide_inter_subset theta center
    rho delta allowedCenters (fun c hc => hsubset c hc) hzero hne

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideList_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hallowed :
      ∀ c : Center, c ∈ AdditiveTripleGuideList rho delta →
        c ∈ allowedCenters)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_list theta center
    rho delta allowedCenters
    (fun c hc => by
      have hset : c ∈ AdditiveTripleGuideSet rho delta := by
        rw [← guideCenterListSet_additiveTripleGuideList rho delta]
        exact hc
      exact ⟨hset, hallowed c hc⟩)
    hzero hcenter

theorem guideLocalityOfNonzero_additiveTripleGuideList_inter
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hallowed :
      ∀ c : Center, c ∈ AdditiveTripleGuideList rho delta →
        c ∈ allowedCenters)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveGuide_inter_list theta center
    rho delta allowedCenters
    (fun c hc => by
      have hset : c ∈ AdditiveTripleGuideSet rho delta := by
        rw [← guideCenterListSet_additiveTripleGuideList rho delta]
        exact hc
      exact ⟨hset, hallowed c hc⟩)
    hzero hne

inductive OrdinaryHighEvenRow where
  | first
  | second
  deriving DecidableEq, Repr

inductive ChainedHighEvenRow where
  | first
  | second
  deriving DecidableEq, Repr

def ordinaryHighEvenRowS {D : Nat} :
    OrdinaryHighEvenRow → ZMod D
  | OrdinaryHighEvenRow.first => 0
  | OrdinaryHighEvenRow.second => 3

def ordinaryHighEvenRowDelta {D : Nat} :
    OrdinaryHighEvenRow → ZMod D
  | OrdinaryHighEvenRow.first => 1
  | OrdinaryHighEvenRow.second => 1

def ordinaryHighEvenRowSupport {D : Nat} :
    OrdinaryHighEvenRow → List (ZMod D)
  | OrdinaryHighEvenRow.first => [0, 1, -1, -2]
  | OrdinaryHighEvenRow.second => [3, 4, 2, 1]

def ordinaryHighEvenRowBoundary {D : Nat} :
    OrdinaryHighEvenRow → List (ZMod D)
  | OrdinaryHighEvenRow.first => [1, -1, -2]
  | OrdinaryHighEvenRow.second => [4, 2, 1]

def ordinaryHighEvenRowLeafLine {D : Nat} :
    OrdinaryHighEvenRow → ZMod D × ZMod D
  | OrdinaryHighEvenRow.first => (0, 1)
  | OrdinaryHighEvenRow.second => (3, 4)

def ordinaryHighEvenRowQuotientGenerator {D : Nat} :
    OrdinaryHighEvenRow → ZMod D × ZMod D
  | OrdinaryHighEvenRow.first => (-1, -2)
  | OrdinaryHighEvenRow.second => (2, 1)

def ordinaryHighEvenRowCutVisible {D : Nat} :
    OrdinaryHighEvenRow → ZMod D
  | OrdinaryHighEvenRow.first => -1
  | OrdinaryHighEvenRow.second => 2

def ordinaryHighEvenRowCutZeroSide {D : Nat} :
    OrdinaryHighEvenRow → List (ZMod D)
  | OrdinaryHighEvenRow.first => [1, -2]
  | OrdinaryHighEvenRow.second => [4, 1]

def ordinaryHighEvenRowNonzeroPairs {D : Nat}
    (row : OrdinaryHighEvenRow) : List (ZMod D × ZMod D) :=
  SymmetricEndpointPairs (ordinaryHighEvenRowCutVisible row)
    (ordinaryHighEvenRowCutZeroSide row)

def ordinaryHighEvenRowGuideCenters {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) : List (ZMod D) :=
  AdditiveTripleGuideList rho (ordinaryHighEvenRowDelta row)

abbrev OrdinaryHighEvenBoundaryVisibleListCertificate {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) : Type :=
  BoundaryVisibleEndpointListCertificate
    (ordinaryHighEvenRowBoundary row)
    (ordinaryHighEvenRowCutVisible row)
    (ordinaryHighEvenRowGuideCenters rho row)

theorem ordinaryHighEvenRowGuideCenters_eq {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) :
    ordinaryHighEvenRowGuideCenters rho row =
      AdditiveTripleGuideList rho (ordinaryHighEvenRowDelta row) :=
  rfl

theorem mem_ordinaryHighEvenRowGuideCenters_iff {D : Nat}
    (rho c : ZMod D) (row : OrdinaryHighEvenRow) :
    c ∈ ordinaryHighEvenRowGuideCenters rho row ↔
      c = rho - ordinaryHighEvenRowDelta row ∨ c = rho ∨
        c = rho + ordinaryHighEvenRowDelta row :=
  mem_additiveTripleGuideList_iff rho
    (ordinaryHighEvenRowDelta row) c

theorem ordinaryHighEvenRowBoundary_subset_support {D : Nat}
    (row : OrdinaryHighEvenRow) :
    ∀ c : ZMod D, c ∈ ordinaryHighEvenRowBoundary row →
      c ∈ ordinaryHighEvenRowSupport row := by
  intro c hc
  cases row
  · simp only [ordinaryHighEvenRowBoundary, ordinaryHighEvenRowSupport,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    exact Or.inr hc
  · simp only [ordinaryHighEvenRowBoundary, ordinaryHighEvenRowSupport,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    exact Or.inr hc

theorem ordinaryHighEvenRowBoundary_length_le_three {D : Nat}
    (row : OrdinaryHighEvenRow) :
    (ordinaryHighEvenRowBoundary (D := D) row).length ≤ 3 := by
  cases row <;> simp [ordinaryHighEvenRowBoundary]

theorem ordinaryHighEvenRowCutVisible_mem_boundary {D : Nat}
    (row : OrdinaryHighEvenRow) :
    ordinaryHighEvenRowCutVisible (D := D) row ∈
      ordinaryHighEvenRowBoundary row := by
  cases row <;> simp [ordinaryHighEvenRowCutVisible,
    ordinaryHighEvenRowBoundary]

theorem ordinaryHighEvenRowCutZeroSide_subset_boundary {D : Nat}
    (row : OrdinaryHighEvenRow) :
  ∀ z : ZMod D, z ∈ ordinaryHighEvenRowCutZeroSide row →
      z ∈ ordinaryHighEvenRowBoundary row := by
  intro z hz
  cases row <;>
    simp only [ordinaryHighEvenRowCutZeroSide, ordinaryHighEvenRowBoundary,
      List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  · rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inr hz)
  · rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inr hz)

theorem ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
    {D : Nat} (row : OrdinaryHighEvenRow) {z : ZMod D}
    (hz : z ∈ ordinaryHighEvenRowBoundary row)
    (hne : z ≠ ordinaryHighEvenRowCutVisible row) :
    z ∈ ordinaryHighEvenRowCutZeroSide row := by
  cases row <;>
    simp only [ordinaryHighEvenRowCutZeroSide, ordinaryHighEvenRowBoundary,
      List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  · rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact False.elim (hne hz)
    · exact Or.inr hz
  · rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact False.elim (hne hz)
    · exact Or.inr hz

theorem ordinaryHighEvenRowNonzeroPairs_endpoints_mem_boundary {D : Nat}
    (row : OrdinaryHighEvenRow) {p : ZMod D × ZMod D}
    (hp : p ∈ ordinaryHighEvenRowNonzeroPairs row) :
    p.1 ∈ ordinaryHighEvenRowBoundary row ∧
      p.2 ∈ ordinaryHighEvenRowBoundary row :=
  endpoints_mem_of_mem_symmetricEndpointPairs
    (ordinaryHighEvenRowCutVisible row)
    (ordinaryHighEvenRowCutZeroSide row)
    (ordinaryHighEvenRowBoundary row)
    (ordinaryHighEvenRowCutVisible_mem_boundary row)
    (ordinaryHighEvenRowCutZeroSide_subset_boundary row) hp

theorem ordinaryHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
    {D : Nat} (row : OrdinaryHighEvenRow) {p : ZMod D × ZMod D}
    (hboundary :
      p.1 ∈ ordinaryHighEvenRowBoundary row ∧
        p.2 ∈ ordinaryHighEvenRowBoundary row)
    (hvisible :
      p.1 = ordinaryHighEvenRowCutVisible row ∨
        p.2 = ordinaryHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2) :
    p ∈ ordinaryHighEvenRowNonzeroPairs row := by
  rw [ordinaryHighEvenRowNonzeroPairs]
  refine (mem_symmetricEndpointPairs
    (ordinaryHighEvenRowCutVisible row)
    (ordinaryHighEvenRowCutZeroSide row) p).2 ?_
  rcases hvisible with hleft | hright
  · left
    have hnot : p.2 ≠ ordinaryHighEvenRowCutVisible row := by
      intro hp2
      exact hne (hleft.trans hp2.symm)
    exact ⟨hleft,
      ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
        row hboundary.2 hnot⟩
  · right
    have hnot : p.1 ≠ ordinaryHighEvenRowCutVisible row := by
      intro hp1
      exact hne (hp1.trans hright.symm)
    exact ⟨hright,
      ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
        row hboundary.1 hnot⟩

def OrdinaryHighEvenBoundaryAvoidingPhase {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) : Prop :=
  rho - ordinaryHighEvenRowDelta row ∉ ordinaryHighEvenRowBoundary row ∧
    rho ∉ ordinaryHighEvenRowBoundary row ∧
    rho + ordinaryHighEvenRowDelta row ∉ ordinaryHighEvenRowBoundary row

def ordinaryHighEvenBoundaryAvoidingPhaseChoice {D : Nat} :
    OrdinaryHighEvenRow → ZMod D
  | OrdinaryHighEvenRow.first => 3
  | OrdinaryHighEvenRow.second => 7

theorem ordinaryHighEvenBoundaryAvoidingPhaseChoice_spec
    {D : Nat} (hD : 11 ≤ D) (row : OrdinaryHighEvenRow) :
    OrdinaryHighEvenBoundaryAvoidingPhase
      (ordinaryHighEvenBoundaryAvoidingPhaseChoice (D := D) row) row := by
  have nat_ne : ∀ {a b : Nat}, a < D → b < D → a ≠ b →
      ((a : Nat) : ZMod D) ≠ (b : ZMod D) := by
    intro a b ha hb hne h
    have hmod : a ≡ b [MOD D] :=
      (ZMod.natCast_eq_natCast_iff a b D).mp h
    have heq : a = b := Nat.ModEq.eq_of_lt_of_lt hmod ha hb
    exact hne heq
  have nat_ne_neg : ∀ {a b : Nat}, 0 < a + b → a + b < D →
      ((a : Nat) : ZMod D) ≠ (-(b : ZMod D)) := by
    intro a b hpos _hlt h
    have hzero : (((a + b : Nat) : ZMod D)) = 0 := by
      calc
        (((a + b : Nat) : ZMod D)) =
            (a : ZMod D) + (b : ZMod D) := by
          norm_num [Nat.cast_add]
        _ = (-(b : ZMod D)) + (b : ZMod D) := by rw [h]
        _ = 0 := by simp
    have hdvd : D ∣ a + b :=
      (ZMod.natCast_eq_zero_iff (a + b) D).mp hzero
    have hle : D ≤ a + b := Nat.le_of_dvd hpos hdvd
    omega
  cases row
  · change (3 : ZMod D) - (1 : ZMod D) ∉ [1, -1, -2] ∧
      (3 : ZMod D) ∉ [1, -1, -2] ∧
      (3 : ZMod D) + (1 : ZMod D) ∉ [1, -1, -2]
    norm_num
    constructor
    · constructor
      · simpa using
          nat_ne (a := 2) (b := 1) (by omega) (by omega) (by omega)
      · constructor
        · simpa using nat_ne_neg (a := 2) (b := 1) (by omega) (by omega)
        · simpa using nat_ne_neg (a := 2) (b := 2) (by omega) (by omega)
    · constructor
      · constructor
        · simpa using
            nat_ne (a := 3) (b := 1) (by omega) (by omega) (by omega)
        · constructor
          · simpa using nat_ne_neg (a := 3) (b := 1) (by omega) (by omega)
          · simpa using nat_ne_neg (a := 3) (b := 2) (by omega) (by omega)
      · constructor
        · simpa using
            nat_ne (a := 4) (b := 1) (by omega) (by omega) (by omega)
        · constructor
          · simpa using nat_ne_neg (a := 4) (b := 1) (by omega) (by omega)
          · simpa using nat_ne_neg (a := 4) (b := 2) (by omega) (by omega)
  · change (7 : ZMod D) - (1 : ZMod D) ∉ [4, 2, 1] ∧
      (7 : ZMod D) ∉ [4, 2, 1] ∧
      (7 : ZMod D) + (1 : ZMod D) ∉ [4, 2, 1]
    norm_num
    constructor
    · constructor
      · simpa using
          nat_ne (a := 6) (b := 4) (by omega) (by omega) (by omega)
      · constructor
        · simpa using
            nat_ne (a := 6) (b := 2) (by omega) (by omega) (by omega)
        · simpa using
            nat_ne (a := 6) (b := 1) (by omega) (by omega) (by omega)
    · constructor
      · constructor
        · simpa using
            nat_ne (a := 7) (b := 4) (by omega) (by omega) (by omega)
        · constructor
          · simpa using
              nat_ne (a := 7) (b := 2) (by omega) (by omega) (by omega)
          · simpa using
              nat_ne (a := 7) (b := 1) (by omega) (by omega) (by omega)
      · constructor
        · simpa using
            nat_ne (a := 8) (b := 4) (by omega) (by omega) (by omega)
        · constructor
          · simpa using
              nat_ne (a := 8) (b := 2) (by omega) (by omega) (by omega)
          · simpa using
              nat_ne (a := 8) (b := 1) (by omega) (by omega) (by omega)

def ordinaryHighEvenBoundaryGuideSet {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) : Set (ZMod D) :=
  AdditiveTripleGuideSet rho (ordinaryHighEvenRowDelta row) ∩
    GuideCenterListSet (ordinaryHighEvenRowBoundary row)

theorem mem_ordinaryHighEvenBoundaryGuideSet_iff {D : Nat}
    (rho c : ZMod D) (row : OrdinaryHighEvenRow) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row ↔
      (c = rho - ordinaryHighEvenRowDelta row ∨ c = rho ∨
        c = rho + ordinaryHighEvenRowDelta row) ∧
        c ∈ ordinaryHighEvenRowBoundary row := by
  rw [ordinaryHighEvenBoundaryGuideSet]
  constructor
  · intro hc
    exact ⟨hc.1, hc.2⟩
  · intro hc
    exact ⟨hc.1, hc.2⟩

theorem not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho row)
    (c : ZMod D) :
    c ∉ ordinaryHighEvenBoundaryGuideSet rho row := by
  intro hc
  rcases hc.1 with hleft | hmiddle | hright
  · exact havoid.1 (by simpa [hleft] using hc.2)
  · exact havoid.2.1 (by simpa [hmiddle] using hc.2)
  · exact havoid.2.2 (by simpa [hright] using hc.2)

theorem ordinaryHighEvenBoundaryGuideSet_eq_empty_of_avoiding
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho row) :
    ordinaryHighEvenBoundaryGuideSet rho row = ∅ := by
  ext c
  constructor
  · intro hc
    exact False.elim
      (not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding
        rho row havoid c hc)
  · intro hc
    cases hc

theorem ordinaryHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {p : ZMod D × ZMod D} {c : ZMod D}
    (hp : p ∈ ordinaryHighEvenRowNonzeroPairs row)
    (hcGuide : c ∈ ordinaryHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row := by
  have hboundaryPair :=
    ordinaryHighEvenRowNonzeroPairs_endpoints_mem_boundary row hp
  have hboundary : c ∈ ordinaryHighEvenRowBoundary row := by
    rcases hcEndpoint with hcEndpoint | hcEndpoint
    · simpa [hcEndpoint] using hboundaryPair.1
    · simpa [hcEndpoint] using hboundaryPair.2
  exact (mem_ordinaryHighEvenBoundaryGuideSet_iff rho c row).2
    ⟨(mem_ordinaryHighEvenRowGuideCenters_iff rho c row).1 hcGuide,
      hboundary⟩

theorem ordinaryHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {p : ZMod D × ZMod D} {c : ZMod D}
    (hboundary :
      p.1 ∈ ordinaryHighEvenRowBoundary row ∧
        p.2 ∈ ordinaryHighEvenRowBoundary row)
    (hvisible :
      p.1 = ordinaryHighEvenRowCutVisible row ∨
        p.2 = ordinaryHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2)
    (hcGuide : c ∈ ordinaryHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    rho row
    (ordinaryHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
      row hboundary hvisible hne)
    hcGuide hcEndpoint

theorem ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {actualCenters : Set (ZMod D)}
    (hcert :
      ∀ c : ZMod D, c ∈ actualCenters →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary row ∧
            p.2 ∈ ordinaryHighEvenRowBoundary row) ∧
          (p.1 = ordinaryHighEvenRowCutVisible row ∨
            p.2 = ordinaryHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho row := by
  intro c hc
  rcases hcert c hc with
    ⟨p, hboundary, hvisible, hne, hcGuide, hcEndpoint⟩
  exact ordinaryHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    rho row hboundary hvisible hne hcGuide hcEndpoint

theorem ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (centers : List (ZMod D))
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary row ∧
            p.2 ∈ ordinaryHighEvenRowBoundary row) ∧
          (p.1 = ordinaryHighEvenRowCutVisible row ∨
            p.2 = ordinaryHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    ∀ c : ZMod D, c ∈ centers →
      c ∈ ordinaryHighEvenBoundaryGuideSet rho row := by
  intro c hc
  exact ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    rho row (actualCenters := GuideCenterListSet centers) hcert hc

theorem ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate rho row) :
    ∀ c : ZMod D, c ∈ C.centers →
      c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    rho row C.centers C.endpointCert

theorem theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (ordinaryHighEvenBoundaryGuideSet rho growthRow))
    {row : Row}
    (hcenter : center row ∉ ordinaryHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter theta center
    rho (ordinaryHighEvenRowDelta growthRow)
    (GuideCenterListSet (ordinaryHighEvenRowBoundary growthRow))
    hzero hcenter

theorem guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (ordinaryHighEvenBoundaryGuideSet rho growthRow))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_additiveTriple_inter theta center
    rho (ordinaryHighEvenRowDelta growthRow)
    (GuideCenterListSet (ordinaryHighEvenRowBoundary growthRow))
    hzero hne

theorem theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_subset
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter : center row ∉ ordinaryHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset theta center
    rho (ordinaryHighEvenRowDelta growthRow)
    (GuideCenterListSet (ordinaryHighEvenRowBoundary growthRow))
    hsubset hzero hcenter

theorem guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_subset
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_additiveGuide_inter_subset theta center
    rho (ordinaryHighEvenRowDelta growthRow)
    (GuideCenterListSet (ordinaryHighEvenRowBoundary growthRow))
    hsubset hzero hne

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero
    (not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding
      rho growthRow havoid (center row))

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_subset
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet
        (ordinaryHighEvenBoundaryAvoidingPhaseChoice (D := D) growthRow)
        growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset
    theta center
    (ordinaryHighEvenBoundaryAvoidingPhaseChoice (D := D) growthRow)
    growthRow
    (ordinaryHighEvenBoundaryAvoidingPhaseChoice_spec hD growthRow)
    hsubset hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (centers : List (ZMod D))
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary growthRow ∧
            p.2 ∈ ordinaryHighEvenRowBoundary growthRow) ∧
          (p.1 = ordinaryHighEvenRowCutVisible growthRow ∨
            p.2 = ordinaryHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset
    theta center rho growthRow havoid
    (ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
      rho growthRow (actualCenters := GuideCenterListSet centers) hcert)
    hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_list_boundary_visible_endpoint
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (centers : List (ZMod D))
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary growthRow ∧
            p.2 ∈ ordinaryHighEvenRowBoundary growthRow) ∧
          (p.1 = ordinaryHighEvenRowCutVisible growthRow ∨
            p.2 = ordinaryHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters
            (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
            growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_subset
    theta center hD growthRow
    (ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
      (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
      growthRow (actualCenters := GuideCenterListSet centers) hcert)
    hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_boundaryVisibleCertificate
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate rho growthRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    theta center C.centers rho growthRow havoid C.endpointCert hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate
      (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow) growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_list_boundary_visible_endpoint
    theta center C.centers hD growthRow C.endpointCert hzero row

def chainedHighEvenRowS :
    ChainedHighEvenRow → ZMod 9
  | ChainedHighEvenRow.first => 0
  | ChainedHighEvenRow.second => 1

def chainedHighEvenRowDelta :
    ChainedHighEvenRow → ZMod 9
  | ChainedHighEvenRow.first => 2
  | ChainedHighEvenRow.second => 1

def chainedHighEvenRowSupport :
    ChainedHighEvenRow → List (ZMod 9)
  | ChainedHighEvenRow.first => [0, 2, 7, 5]
  | ChainedHighEvenRow.second => [1, 2, 0, 8]

def chainedHighEvenRowBoundary :
    ChainedHighEvenRow → List (ZMod 9)
  | ChainedHighEvenRow.first => [2, 7, 5]
  | ChainedHighEvenRow.second => [2, 8]

def chainedHighEvenRowLeafLine :
    ChainedHighEvenRow → ZMod 9 × ZMod 9
  | ChainedHighEvenRow.first => (0, 2)
  | ChainedHighEvenRow.second => (1, 2)

def chainedHighEvenRowQuotientGenerator :
    ChainedHighEvenRow → ZMod 9 × ZMod 9
  | ChainedHighEvenRow.first => (7, 5)
  | ChainedHighEvenRow.second => (2, 8)

def chainedHighEvenRowCutVisible :
    ChainedHighEvenRow → ZMod 9
  | ChainedHighEvenRow.first => 7
  | ChainedHighEvenRow.second => 2

def chainedHighEvenRowCutZeroSide :
    ChainedHighEvenRow → List (ZMod 9)
  | ChainedHighEvenRow.first => [2, 5]
  | ChainedHighEvenRow.second => [8]

def chainedHighEvenRowNonzeroPairs
    (row : ChainedHighEvenRow) : List (ZMod 9 × ZMod 9) :=
  SymmetricEndpointPairs (chainedHighEvenRowCutVisible row)
    (chainedHighEvenRowCutZeroSide row)

def chainedHighEvenRowGuideCenters
    (rho : ZMod 9) (row : ChainedHighEvenRow) : List (ZMod 9) :=
  AdditiveTripleGuideList rho (chainedHighEvenRowDelta row)

abbrev ChainedHighEvenBoundaryVisibleListCertificate
    (rho : ZMod 9) (row : ChainedHighEvenRow) : Type :=
  BoundaryVisibleEndpointListCertificate
    (chainedHighEvenRowBoundary row)
    (chainedHighEvenRowCutVisible row)
    (chainedHighEvenRowGuideCenters rho row)

theorem chainedHighEvenRowGuideCenters_eq
    (rho : ZMod 9) (row : ChainedHighEvenRow) :
    chainedHighEvenRowGuideCenters rho row =
      AdditiveTripleGuideList rho (chainedHighEvenRowDelta row) :=
  rfl

theorem mem_chainedHighEvenRowGuideCenters_iff
    (rho c : ZMod 9) (row : ChainedHighEvenRow) :
    c ∈ chainedHighEvenRowGuideCenters rho row ↔
      c = rho - chainedHighEvenRowDelta row ∨ c = rho ∨
        c = rho + chainedHighEvenRowDelta row :=
  mem_additiveTripleGuideList_iff rho (chainedHighEvenRowDelta row) c

theorem chainedHighEvenRowBoundary_subset_support
    (row : ChainedHighEvenRow) :
    ∀ c : ZMod 9, c ∈ chainedHighEvenRowBoundary row →
      c ∈ chainedHighEvenRowSupport row := by
  intro c hc
  cases row
  · simp only [chainedHighEvenRowBoundary, chainedHighEvenRowSupport,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    exact Or.inr hc
  · simp only [chainedHighEvenRowBoundary, chainedHighEvenRowSupport,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with hc | hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inr hc))

theorem chainedHighEvenRowBoundary_length_le_three
    (row : ChainedHighEvenRow) :
    (chainedHighEvenRowBoundary row).length ≤ 3 := by
  cases row <;> simp [chainedHighEvenRowBoundary]

theorem chainedHighEvenRowCutVisible_mem_boundary
    (row : ChainedHighEvenRow) :
    chainedHighEvenRowCutVisible row ∈
      chainedHighEvenRowBoundary row := by
  cases row <;> simp [chainedHighEvenRowCutVisible,
    chainedHighEvenRowBoundary]

theorem chainedHighEvenRowCutZeroSide_subset_boundary
    (row : ChainedHighEvenRow) :
  ∀ z : ZMod 9, z ∈ chainedHighEvenRowCutZeroSide row →
      z ∈ chainedHighEvenRowBoundary row := by
  intro z hz
  cases row <;>
    simp only [chainedHighEvenRowCutZeroSide, chainedHighEvenRowBoundary,
      List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  · rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inr hz)
  · exact Or.inr hz

theorem chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
    (row : ChainedHighEvenRow) {z : ZMod 9}
    (hz : z ∈ chainedHighEvenRowBoundary row)
    (hne : z ≠ chainedHighEvenRowCutVisible row) :
    z ∈ chainedHighEvenRowCutZeroSide row := by
  cases row <;>
    simp only [chainedHighEvenRowCutZeroSide, chainedHighEvenRowBoundary,
      List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  · rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact False.elim (hne hz)
    · exact Or.inr hz
  · rcases hz with hz | hz
    · exact False.elim (hne hz)
    · exact hz

theorem chainedHighEvenRowNonzeroPairs_endpoints_mem_boundary
    (row : ChainedHighEvenRow) {p : ZMod 9 × ZMod 9}
    (hp : p ∈ chainedHighEvenRowNonzeroPairs row) :
    p.1 ∈ chainedHighEvenRowBoundary row ∧
      p.2 ∈ chainedHighEvenRowBoundary row :=
  endpoints_mem_of_mem_symmetricEndpointPairs
    (chainedHighEvenRowCutVisible row)
    (chainedHighEvenRowCutZeroSide row)
    (chainedHighEvenRowBoundary row)
    (chainedHighEvenRowCutVisible_mem_boundary row)
    (chainedHighEvenRowCutZeroSide_subset_boundary row) hp

theorem chainedHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
    (row : ChainedHighEvenRow) {p : ZMod 9 × ZMod 9}
    (hboundary :
      p.1 ∈ chainedHighEvenRowBoundary row ∧
        p.2 ∈ chainedHighEvenRowBoundary row)
    (hvisible :
      p.1 = chainedHighEvenRowCutVisible row ∨
        p.2 = chainedHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2) :
    p ∈ chainedHighEvenRowNonzeroPairs row := by
  rw [chainedHighEvenRowNonzeroPairs]
  refine (mem_symmetricEndpointPairs
    (chainedHighEvenRowCutVisible row)
    (chainedHighEvenRowCutZeroSide row) p).2 ?_
  rcases hvisible with hleft | hright
  · left
    have hnot : p.2 ≠ chainedHighEvenRowCutVisible row := by
      intro hp2
      exact hne (hleft.trans hp2.symm)
    exact ⟨hleft,
      chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
        row hboundary.2 hnot⟩
  · right
    have hnot : p.1 ≠ chainedHighEvenRowCutVisible row := by
      intro hp1
      exact hne (hp1.trans hright.symm)
    exact ⟨hright,
      chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
        row hboundary.1 hnot⟩

def ChainedHighEvenBoundaryAvoidingPhase
    (rho : ZMod 9) (row : ChainedHighEvenRow) : Prop :=
  rho - chainedHighEvenRowDelta row ∉ chainedHighEvenRowBoundary row ∧
    rho ∉ chainedHighEvenRowBoundary row ∧
    rho + chainedHighEvenRowDelta row ∉ chainedHighEvenRowBoundary row

def chainedHighEvenBoundaryAvoidingPhaseChoice :
    ChainedHighEvenRow → ZMod 9
  | ChainedHighEvenRow.first => 1
  | ChainedHighEvenRow.second => 5

theorem chainedHighEvenBoundaryAvoidingPhaseChoice_spec
    (row : ChainedHighEvenRow) :
    ChainedHighEvenBoundaryAvoidingPhase
      (chainedHighEvenBoundaryAvoidingPhaseChoice row) row := by
  cases row
  · change (-1 : ZMod 9) ∉ [2, 7, 5] ∧
      (1 : ZMod 9) ∉ [2, 7, 5] ∧
      (3 : ZMod 9) ∉ [2, 7, 5]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    repeat constructor <;> decide
  · change (4 : ZMod 9) ∉ [2, 8] ∧
      (5 : ZMod 9) ∉ [2, 8] ∧
      (6 : ZMod 9) ∉ [2, 8]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    repeat constructor <;> decide

def chainedHighEvenBoundaryGuideSet
    (rho : ZMod 9) (row : ChainedHighEvenRow) : Set (ZMod 9) :=
  AdditiveTripleGuideSet rho (chainedHighEvenRowDelta row) ∩
    GuideCenterListSet (chainedHighEvenRowBoundary row)

theorem mem_chainedHighEvenBoundaryGuideSet_iff
    (rho c : ZMod 9) (row : ChainedHighEvenRow) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row ↔
      (c = rho - chainedHighEvenRowDelta row ∨ c = rho ∨
        c = rho + chainedHighEvenRowDelta row) ∧
        c ∈ chainedHighEvenRowBoundary row := by
  rw [chainedHighEvenBoundaryGuideSet]
  constructor
  · intro hc
    exact ⟨hc.1, hc.2⟩
  · intro hc
    exact ⟨hc.1, hc.2⟩

theorem not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho row)
    (c : ZMod 9) :
    c ∉ chainedHighEvenBoundaryGuideSet rho row := by
  intro hc
  rcases hc.1 with hleft | hmiddle | hright
  · exact havoid.1 (by simpa [hleft] using hc.2)
  · exact havoid.2.1 (by simpa [hmiddle] using hc.2)
  · exact havoid.2.2 (by simpa [hright] using hc.2)

theorem chainedHighEvenBoundaryGuideSet_eq_empty_of_avoiding
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho row) :
    chainedHighEvenBoundaryGuideSet rho row = ∅ := by
  ext c
  constructor
  · intro hc
    exact False.elim
      (not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding
        rho row havoid c hc)
  · intro hc
    cases hc

theorem chainedHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {p : ZMod 9 × ZMod 9} {c : ZMod 9}
    (hp : p ∈ chainedHighEvenRowNonzeroPairs row)
    (hcGuide : c ∈ chainedHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row := by
  have hboundaryPair :=
    chainedHighEvenRowNonzeroPairs_endpoints_mem_boundary row hp
  have hboundary : c ∈ chainedHighEvenRowBoundary row := by
    rcases hcEndpoint with hcEndpoint | hcEndpoint
    · simpa [hcEndpoint] using hboundaryPair.1
    · simpa [hcEndpoint] using hboundaryPair.2
  exact (mem_chainedHighEvenBoundaryGuideSet_iff rho c row).2
    ⟨(mem_chainedHighEvenRowGuideCenters_iff rho c row).1 hcGuide,
      hboundary⟩

theorem chainedHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {p : ZMod 9 × ZMod 9} {c : ZMod 9}
    (hboundary :
      p.1 ∈ chainedHighEvenRowBoundary row ∧
        p.2 ∈ chainedHighEvenRowBoundary row)
    (hvisible :
      p.1 = chainedHighEvenRowCutVisible row ∨
        p.2 = chainedHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2)
    (hcGuide : c ∈ chainedHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    rho row
    (chainedHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
      row hboundary hvisible hne)
    hcGuide hcEndpoint

theorem chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {actualCenters : Set (ZMod 9)}
    (hcert :
      ∀ c : ZMod 9, c ∈ actualCenters →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary row ∧
            p.2 ∈ chainedHighEvenRowBoundary row) ∧
          (p.1 = chainedHighEvenRowCutVisible row ∨
            p.2 = chainedHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho row := by
  intro c hc
  rcases hcert c hc with
    ⟨p, hboundary, hvisible, hne, hcGuide, hcEndpoint⟩
  exact chainedHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    rho row hboundary hvisible hne hcGuide hcEndpoint

theorem chainedHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (centers : List (ZMod 9))
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary row ∧
            p.2 ∈ chainedHighEvenRowBoundary row) ∧
          (p.1 = chainedHighEvenRowCutVisible row ∨
            p.2 = chainedHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    ∀ c : ZMod 9, c ∈ centers →
      c ∈ chainedHighEvenBoundaryGuideSet rho row := by
  intro c hc
  exact chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    rho row (actualCenters := GuideCenterListSet centers) hcert hc

theorem chainedHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate rho row) :
    ∀ c : ZMod 9, c ∈ C.centers →
      c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    rho row C.centers C.endpointCert

theorem theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (chainedHighEvenBoundaryGuideSet rho growthRow))
    {row : Row}
    (hcenter : center row ∉ chainedHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter theta center
    rho (chainedHighEvenRowDelta growthRow)
    (GuideCenterListSet (chainedHighEvenRowBoundary growthRow))
    hzero hcenter

theorem guideLocalityOfNonzero_chainedHighEvenBoundaryGuide
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (chainedHighEvenBoundaryGuideSet rho growthRow))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_additiveTriple_inter theta center
    rho (chainedHighEvenRowDelta growthRow)
    (GuideCenterListSet (chainedHighEvenRowBoundary growthRow))
    hzero hne

theorem theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_subset
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter : center row ∉ chainedHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset theta center
    rho (chainedHighEvenRowDelta growthRow)
    (GuideCenterListSet (chainedHighEvenRowBoundary growthRow))
    hsubset hzero hcenter

theorem guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_subset
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_additiveGuide_inter_subset theta center
    rho (chainedHighEvenRowDelta growthRow)
    (GuideCenterListSet (chainedHighEvenRowBoundary growthRow))
    hsubset hzero hne

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero
    (not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding
      rho growthRow havoid (center row))

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_subset
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet
        (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow) growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset
    theta center
    (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
    growthRow
    (chainedHighEvenBoundaryAvoidingPhaseChoice_spec growthRow)
    hsubset hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (centers : List (ZMod 9))
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary growthRow ∧
            p.2 ∈ chainedHighEvenRowBoundary growthRow) ∧
          (p.1 = chainedHighEvenRowCutVisible growthRow ∨
            p.2 = chainedHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset
    theta center rho growthRow havoid
    (chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
      rho growthRow (actualCenters := GuideCenterListSet centers) hcert)
    hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_list_boundary_visible_endpoint
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (centers : List (ZMod 9))
    (growthRow : ChainedHighEvenRow)
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary growthRow ∧
            p.2 ∈ chainedHighEvenRowBoundary growthRow) ∧
          (p.1 = chainedHighEvenRowCutVisible growthRow ∨
            p.2 = chainedHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters
            (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
            growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_subset
    theta center growthRow
    (chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
      growthRow (actualCenters := GuideCenterListSet centers) hcert)
    hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_boundaryVisibleCertificate
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate rho growthRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    theta center C.centers rho growthRow havoid C.endpointCert hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow) growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_list_boundary_visible_endpoint
    theta center C.centers growthRow C.endpointCert hzero row

def ordinaryHighEvenOldGeneratorCenters {D : Nat}
    (_growthRow : OrdinaryHighEvenRow) : List (ZMod D) :=
  []

theorem ordinaryHighEvenOldGeneratorCenters_eq_nil {D : Nat}
    (growthRow : OrdinaryHighEvenRow) :
    ordinaryHighEvenOldGeneratorCenters (D := D) growthRow = [] :=
  rfl

def ordinaryHighEvenOldGeneratorBoundaryVisibleCertificate {D : Nat}
    (growthRow : OrdinaryHighEvenRow) :
    OrdinaryHighEvenBoundaryVisibleListCertificate
      (ordinaryHighEvenBoundaryAvoidingPhaseChoice (D := D) growthRow)
      growthRow where
  centers := ordinaryHighEvenOldGeneratorCenters growthRow
  endpointCert := by
    intro c hc
    cases hc

theorem theta_eq_zero_of_ordinaryHighEvenOldGenerator_boundaryChoice
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (ordinaryHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate
    theta center hD growthRow
    (ordinaryHighEvenOldGeneratorBoundaryVisibleCertificate growthRow)
    hzero row

def chainedHighEvenOldGeneratorCenters
    (_growthRow : ChainedHighEvenRow) : List (ZMod 9) :=
  []

theorem chainedHighEvenOldGeneratorCenters_eq_nil
    (growthRow : ChainedHighEvenRow) :
    chainedHighEvenOldGeneratorCenters growthRow = [] :=
  rfl

def chainedHighEvenOldGeneratorBoundaryVisibleCertificate
    (growthRow : ChainedHighEvenRow) :
    ChainedHighEvenBoundaryVisibleListCertificate
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
      growthRow where
  centers := chainedHighEvenOldGeneratorCenters growthRow
  endpointCert := by
    intro c hc
    cases hc

theorem theta_eq_zero_of_chainedHighEvenOldGenerator_boundaryChoice
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (chainedHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate
    theta center growthRow
    (chainedHighEvenOldGeneratorBoundaryVisibleCertificate growthRow)
    hzero row

end GuideLocality

export GuideLocality
  (CenterAllowed VanishesOutside VanishesOutsideGuide
   GuideCenterListSet VanishesOutsideGuideList
   BoundaryVisibleEndpointListCertificate
   mem_of_nonzero_of_vanishesOutside
   theta_eq_zero_of_not_mem_of_vanishesOutside
   theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide
   theta_eq_zero_of_center_not_mem_guideList
   vanishesOutside_of_subset
   theta_eq_zero_of_not_mem_of_vanishesOutside_subset
   vanishesOutsideGuide_of_subset
   theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide_subset
   vanishesOutsideGuide_of_list_subset
   theta_eq_zero_of_center_not_mem_of_guideList_subset
   guideLocalityOfNonzero
   guideLocalityOfNonzero_subset
   guideLocalityOfNonzero_list
   guideLocalityOfNonzero_list_subset
   TripleGuideSet AdditiveTripleGuideSet
   TripleGuideList AdditiveTripleGuideList
   mem_tripleGuideList_iff
   guideCenterListSet_tripleGuideList
   mem_additiveTripleGuideList_iff
   guideCenterListSet_additiveTripleGuideList
   vanishesOutsideGuide_tripleGuideList_iff
   vanishesOutsideGuide_additiveTripleGuideList_iff
   mem_tripleGuideSet_middle mem_tripleGuideSet_left
   mem_tripleGuideSet_right
   mem_additiveTripleGuideSet_middle mem_additiveTripleGuideSet_left
   mem_additiveTripleGuideSet_right
   theta_eq_zero_of_center_not_mem_tripleGuideList
   theta_eq_zero_of_center_not_mem_additiveTripleGuideList
   theta_eq_zero_of_center_not_mem_tripleGuideSet
   theta_eq_zero_of_center_not_mem_tripleGuideSet_inter
   theta_eq_zero_of_center_ne_tripleGuideSet
   theta_eq_zero_of_center_ne_tripleGuideSet_inter
   theta_eq_zero_of_center_not_mem_allowed_tripleGuideSet_inter
   theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter
   theta_eq_zero_of_center_ne_additiveTripleGuideSet_inter
   theta_eq_zero_of_center_not_mem_allowed_additiveTripleGuideSet_inter
   guideLocalityOfNonzero_triple
   guideLocalityOfNonzero_tripleGuideList
   guideLocalityOfNonzero_additiveTripleGuideList
   guideLocalityOfNonzero_triple_inter
   theta_eq_zero_of_center_not_mem_tripleGuideSet_inter_subset
   guideLocalityOfNonzero_triple_inter_subset
   guideLocalityOfNonzero_additiveTriple_inter
   theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset
   guideLocalityOfNonzero_additiveGuide_inter_subset
   theta_eq_zero_of_center_not_mem_additiveGuide_inter_list
   guideLocalityOfNonzero_additiveGuide_inter_list
   theta_eq_zero_of_center_not_mem_additiveTripleGuideList_inter
   guideLocalityOfNonzero_additiveTripleGuideList_inter
   OrdinaryHighEvenRow ChainedHighEvenRow
   ordinaryHighEvenRowS ordinaryHighEvenRowDelta
   ordinaryHighEvenRowSupport ordinaryHighEvenRowBoundary
   ordinaryHighEvenRowLeafLine ordinaryHighEvenRowQuotientGenerator
   ordinaryHighEvenRowCutVisible ordinaryHighEvenRowCutZeroSide
   ordinaryHighEvenRowNonzeroPairs
   ordinaryHighEvenRowGuideCenters
   OrdinaryHighEvenBoundaryVisibleListCertificate
   ordinaryHighEvenRowGuideCenters_eq
   mem_ordinaryHighEvenRowGuideCenters_iff
   ordinaryHighEvenRowBoundary_subset_support
   ordinaryHighEvenRowBoundary_length_le_three
   ordinaryHighEvenRowCutVisible_mem_boundary
   ordinaryHighEvenRowCutZeroSide_subset_boundary
   ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
   ordinaryHighEvenRowNonzeroPairs_endpoints_mem_boundary
   ordinaryHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
   OrdinaryHighEvenBoundaryAvoidingPhase
   ordinaryHighEvenBoundaryAvoidingPhaseChoice
   ordinaryHighEvenBoundaryAvoidingPhaseChoice_spec
   ordinaryHighEvenBoundaryGuideSet
   mem_ordinaryHighEvenBoundaryGuideSet_iff
   not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding
   ordinaryHighEvenBoundaryGuideSet_eq_empty_of_avoiding
   ordinaryHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
   ordinaryHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
   ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
   ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
   ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
   theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide
   guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide
   theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_subset
   guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_subset
   theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset
   theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_subset
   theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
   theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_list_boundary_visible_endpoint
   theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_boundaryVisibleCertificate
   theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate
   chainedHighEvenRowS chainedHighEvenRowDelta
   chainedHighEvenRowSupport chainedHighEvenRowBoundary
   chainedHighEvenRowLeafLine chainedHighEvenRowQuotientGenerator
   chainedHighEvenRowCutVisible chainedHighEvenRowCutZeroSide
   chainedHighEvenRowNonzeroPairs
   chainedHighEvenRowGuideCenters
   ChainedHighEvenBoundaryVisibleListCertificate
   chainedHighEvenRowGuideCenters_eq
   mem_chainedHighEvenRowGuideCenters_iff
   chainedHighEvenRowBoundary_subset_support
   chainedHighEvenRowBoundary_length_le_three
   chainedHighEvenRowCutVisible_mem_boundary
   chainedHighEvenRowCutZeroSide_subset_boundary
   chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible
   chainedHighEvenRowNonzeroPairs_endpoints_mem_boundary
   chainedHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
   ChainedHighEvenBoundaryAvoidingPhase
   chainedHighEvenBoundaryAvoidingPhaseChoice
   chainedHighEvenBoundaryAvoidingPhaseChoice_spec
   chainedHighEvenBoundaryGuideSet
   mem_chainedHighEvenBoundaryGuideSet_iff
   not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding
   chainedHighEvenBoundaryGuideSet_eq_empty_of_avoiding
   chainedHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
   chainedHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
   chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
   chainedHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
   chainedHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
   theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide
   guideLocalityOfNonzero_chainedHighEvenBoundaryGuide
   theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_subset
   guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_subset
   theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset
   theta_eq_zero_of_chainedHighEvenBoundaryChoice_subset
   theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
   theta_eq_zero_of_chainedHighEvenBoundaryChoice_list_boundary_visible_endpoint
   theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_boundaryVisibleCertificate
   theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate
   ordinaryHighEvenOldGeneratorCenters
   ordinaryHighEvenOldGeneratorCenters_eq_nil
   ordinaryHighEvenOldGeneratorBoundaryVisibleCertificate
   theta_eq_zero_of_ordinaryHighEvenOldGenerator_boundaryChoice
   chainedHighEvenOldGeneratorCenters
   chainedHighEvenOldGeneratorCenters_eq_nil
   chainedHighEvenOldGeneratorBoundaryVisibleCertificate
   theta_eq_zero_of_chainedHighEvenOldGenerator_boundaryChoice)

end EvenV11
