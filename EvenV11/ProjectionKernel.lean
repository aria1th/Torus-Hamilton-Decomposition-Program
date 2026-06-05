import EvenV11.Basic

namespace EvenV11
namespace ProjectionKernel

def lineSpan {m r : Nat} (e x : Vec m r) : Prop :=
  ∃ a : ZMod m, x = fun i => a * e i

def planeSpan {m r : Nat} (e g x : Vec m r) : Prop :=
  ∃ a b : ZMod m, x = fun i => a * e i + b * g i

def translatedLineSet {m r : Nat} (H : Vec m r → Prop)
    (e x : Vec m r) : Prop :=
  ∃ h : Vec m r, ∃ c : ZMod m, H h ∧ x = fun i => h i + c * e i

def translatedTwoLineSet {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 x : Vec m r) : Prop :=
  ∃ h : Vec m r, ∃ a b : ZMod m,
    H h ∧ x = fun i => h i + a * e0 i + b * e1 i

def lineCoset {m r : Nat} (e x y : Vec m r) : Prop :=
  ∃ c : ZMod m, y = fun i => x i + c * e i

def triangularPlaneGenerator {m r : Nat} (e0 g1 : Vec m r) :
    Vec m r :=
  fun i => e0 i + g1 i

def planeLineSetoid {m r : Nat} (e g : Vec m r) :
    Setoid {x : Vec m r // planeSpan e g x} where
  r x y := lineCoset e x.1 y.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine ⟨0, ?_⟩
      funext i
      simp
    · intro x y hxy
      rcases hxy with ⟨c, hxyEq⟩
      refine ⟨-c, ?_⟩
      rw [hxyEq]
      funext i
      simp [add_assoc]
    · intro x y z hxy hyz
      rcases hxy with ⟨c, hxyEq⟩
      rcases hyz with ⟨d, hyzEq⟩
      refine ⟨c + d, ?_⟩
      rw [hyzEq, hxyEq]
      funext i
      simp [add_mul, add_assoc]

abbrev PlaneLineQuotient {m r : Nat} (e g : Vec m r) : Type :=
  Quot (planeLineSetoid e g)

def planeLineQuotientMk {m r : Nat} (e g : Vec m r)
    (x : Vec m r) (hxPlane : planeSpan e g x) :
    PlaneLineQuotient e g :=
  Quot.mk (planeLineSetoid e g) ⟨x, hxPlane⟩

def planeLineQuotientZero {m r : Nat} (e g : Vec m r) :
    PlaneLineQuotient e g :=
  planeLineQuotientMk e g (0 : Vec m r)
    ⟨0, 0, by
      funext i
      simp⟩

theorem planeSpan_of_lineSpan
    {m r : Nat} (e g x : Vec m r)
    (hxLine : lineSpan e x) :
    planeSpan e g x := by
  rcases hxLine with ⟨a, hxLineEq⟩
  refine ⟨a, 0, ?_⟩
  rw [hxLineEq]
  funext i
  simp

theorem lineCoset_refl
    {m r : Nat} (e x : Vec m r) :
    lineCoset e x x := by
  refine ⟨0, ?_⟩
  funext i
  simp

theorem lineCoset_symm
    {m r : Nat} (e x y : Vec m r)
    (hxy : lineCoset e x y) :
    lineCoset e y x := by
  rcases hxy with ⟨c, hxyEq⟩
  refine ⟨-c, ?_⟩
  rw [hxyEq]
  funext i
  simp [add_assoc]

theorem lineCoset_trans
    {m r : Nat} (e x y z : Vec m r)
    (hxy : lineCoset e x y) (hyz : lineCoset e y z) :
    lineCoset e x z := by
  rcases hxy with ⟨c, hxyEq⟩
  rcases hyz with ⟨d, hyzEq⟩
  refine ⟨c + d, ?_⟩
  rw [hyzEq, hxyEq]
  funext i
  simp [add_mul, add_assoc]

theorem lineCoset_zero_iff_lineSpan
    {m r : Nat} (e x : Vec m r) :
    lineCoset e (0 : Vec m r) x ↔ lineSpan e x := by
  constructor
  · intro hxCoset
    rcases hxCoset with ⟨c, hxEq⟩
    refine ⟨c, ?_⟩
    rw [hxEq]
    funext i
    simp
  · intro hxLine
    rcases hxLine with ⟨c, hxEq⟩
    refine ⟨c, ?_⟩
    rw [hxEq]
    funext i
    simp

theorem lineCoset_zero_of_lineSpan
    {m r : Nat} (e x : Vec m r)
    (hxLine : lineSpan e x) :
    lineCoset e (0 : Vec m r) x :=
  (lineCoset_zero_iff_lineSpan e x).mpr hxLine

theorem planeLineQuotient_mk_eq_of_lineCoset
    {m r : Nat} (e g x y : Vec m r)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y)
    (hxy : lineCoset e x y) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientMk e g y hyPlane :=
  Quot.sound hxy

theorem planeLineQuotient_eq_zero_of_lineSpan
    {m r : Nat} (e g x : Vec m r)
    (hxPlane : planeSpan e g x) (hxLine : lineSpan e x) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientZero e g :=
  Quot.sound
    (lineCoset_symm e (0 : Vec m r) x
      (lineCoset_zero_of_lineSpan e x hxLine))

theorem lineSpan_of_lineCoset_zero
    {m r : Nat} (e x : Vec m r)
    (hxCoset : lineCoset e (0 : Vec m r) x) :
    lineSpan e x :=
  (lineCoset_zero_iff_lineSpan e x).mp hxCoset

theorem lineSpan_of_lineCoset_of_lineSpan
    {m r : Nat} (e x y : Vec m r)
    (hxLine : lineSpan e x) (hxy : lineCoset e x y) :
    lineSpan e y := by
  rcases hxLine with ⟨a, hxEq⟩
  rcases hxy with ⟨c, hxyEq⟩
  refine ⟨a + c, ?_⟩
  rw [hxyEq, hxEq]
  funext i
  simp [add_mul]

theorem planeSpan_of_lineCoset_of_planeSpan
    {m r : Nat} (e g x y : Vec m r)
    (hxPlane : planeSpan e g x) (hxy : lineCoset e x y) :
    planeSpan e g y := by
  rcases hxPlane with ⟨a, b, hxEq⟩
  rcases hxy with ⟨c, hxyEq⟩
  refine ⟨a + c, b, ?_⟩
  rw [hxyEq, hxEq]
  funext i
  simp [add_mul, add_assoc, add_comm, add_left_comm]

theorem theta_eq_zero_of_lineSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxLine : lineSpan e x) :
    theta x = 0 := by
  rcases hxLine with ⟨a, hxLineEq⟩
  rw [hxLineEq]
  simpa using hThetaPlane a 0

theorem lineSpan_of_planeSpan_of_theta_eq_zero
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x)
    (hThetaZero : theta x = 0) :
    lineSpan e x := by
  rcases hxPlane with ⟨a, b, hxPlaneEq⟩
  refine ⟨a, ?_⟩
  have hThetaXPlane : theta x = b := by
    rw [hxPlaneEq]
    exact hThetaPlane a b
  have hb : b = 0 := hThetaXPlane.symm.trans hThetaZero
  rw [hxPlaneEq, hb]
  funext i
  simp

theorem theta_eq_of_lineCoset_of_planeSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hxy : lineCoset e x y) :
    theta y = theta x := by
  rcases hxPlane with ⟨a, b, hxEq⟩
  rcases hxy with ⟨c, hxyEq⟩
  have hThetaX : theta x = b := by
    rw [hxEq]
    exact hThetaPlane a b
  have hThetaY : theta y = b := by
    rw [hxyEq, hxEq]
    have hrewrite :
        (fun i => a * e i + b * g i + c * e i) =
          fun i => (a + c) * e i + b * g i := by
      funext i
      simp [add_mul, add_assoc, add_comm, add_left_comm]
    rw [hrewrite]
    exact hThetaPlane (a + c) b
  exact hThetaY.trans hThetaX.symm

def planeLineQuotientTheta
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    PlaneLineQuotient e g → ZMod m :=
  Quot.lift
    (fun x : {x : Vec m r // planeSpan e g x} => theta x.1)
    (by
      intro x y hxy
      exact (theta_eq_of_lineCoset_of_planeSpan theta e g x.1 y.1
        hThetaPlane x.2 hxy).symm)

theorem planeLineQuotientTheta_mk
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    planeLineQuotientTheta theta e g hThetaPlane
      (planeLineQuotientMk e g x hxPlane) = theta x :=
  rfl

theorem planeLineQuotientTheta_zero
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    planeLineQuotientTheta theta e g hThetaPlane
      (planeLineQuotientZero e g) = 0 := by
  simpa [planeLineQuotientZero, planeLineQuotientTheta_mk]
    using hThetaPlane 0 0

theorem theta_eq_zero_of_lineCoset_of_lineSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxLine : lineSpan e x) (hxy : lineCoset e x y) :
    theta y = 0 := by
  have hyLine : lineSpan e y :=
    lineSpan_of_lineCoset_of_lineSpan e x y hxLine hxy
  exact theta_eq_zero_of_lineSpan theta e g y hThetaPlane hyLine

theorem lineCoset_of_planeSpan_of_theta_eq
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y)
    (hThetaEq : theta y = theta x) :
    lineCoset e x y := by
  rcases hxPlane with ⟨a, b, hxEq⟩
  rcases hyPlane with ⟨c, d, hyEq⟩
  have hThetaX : theta x = b := by
    rw [hxEq]
    exact hThetaPlane a b
  have hThetaY : theta y = d := by
    rw [hyEq]
    exact hThetaPlane c d
  have hd : d = b := hThetaY.symm.trans (hThetaEq.trans hThetaX)
  refine ⟨c - a, ?_⟩
  rw [hyEq, hxEq, hd]
  funext i
  ring

theorem lineCoset_iff_theta_eq_of_planeSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y) :
    lineCoset e x y ↔ theta y = theta x :=
  ⟨theta_eq_of_lineCoset_of_planeSpan theta e g x y hThetaPlane hxPlane,
    lineCoset_of_planeSpan_of_theta_eq theta e g x y
      hThetaPlane hxPlane hyPlane⟩

theorem planeLineQuotientTheta_eq_iff_lineCoset
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y) :
    planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g x hxPlane) =
      planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g y hyPlane) ↔
      lineCoset e x y := by
  rw [planeLineQuotientTheta_mk, planeLineQuotientTheta_mk]
  constructor
  · intro hThetaEq
    exact lineCoset_of_planeSpan_of_theta_eq theta e g x y
      hThetaPlane hxPlane hyPlane hThetaEq.symm
  · intro hxy
    exact (theta_eq_of_lineCoset_of_planeSpan theta e g x y
      hThetaPlane hxPlane hxy).symm

theorem planeSpan_lineCoset_subset_thetaFiber
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} ⊆
      {y : Vec m r | planeSpan e g y ∧ theta y = theta x} := by
  intro y hy
  exact ⟨hy.1,
    theta_eq_of_lineCoset_of_planeSpan theta e g x y
      hThetaPlane hxPlane hy.2⟩

theorem planeSpan_thetaFiber_subset_lineCoset
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ theta y = theta x} ⊆
      {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} := by
  intro y hy
  exact ⟨hy.1,
    lineCoset_of_planeSpan_of_theta_eq theta e g x y
      hThetaPlane hxPlane hy.1 hy.2⟩

theorem planeSpan_lineCoset_set_eq_thetaFiber
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} =
      {y : Vec m r | planeSpan e g y ∧ theta y = theta x} := by
  apply Set.Subset.antisymm
  · exact planeSpan_lineCoset_subset_thetaFiber theta e g x
      hThetaPlane hxPlane
  · exact planeSpan_thetaFiber_subset_lineCoset theta e g x
      hThetaPlane hxPlane

theorem lineSpan_iff_theta_eq_zero_of_planeSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    lineSpan e x ↔ theta x = 0 :=
  ⟨theta_eq_zero_of_lineSpan theta e g x hThetaPlane,
    lineSpan_of_planeSpan_of_theta_eq_zero theta e g x hThetaPlane hxPlane⟩

theorem planeLineQuotientTheta_eq_zero_iff_lineSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g x hxPlane) = 0 ↔
      lineSpan e x := by
  rw [planeLineQuotientTheta_mk]
  exact (lineSpan_iff_theta_eq_zero_of_planeSpan theta e g x
    hThetaPlane hxPlane).symm

theorem lineSpan_iff_planeSpan_and_theta_eq_zero
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    lineSpan e x ↔ planeSpan e g x ∧ theta x = 0 :=
  ⟨fun hxLine =>
      ⟨planeSpan_of_lineSpan e g x hxLine,
        theta_eq_zero_of_lineSpan theta e g x hThetaPlane hxLine⟩,
    fun hxPlaneAndTheta =>
      lineSpan_of_planeSpan_of_theta_eq_zero theta e g x hThetaPlane
        hxPlaneAndTheta.1 hxPlaneAndTheta.2⟩

theorem lineSpan_subset_planeSpan_thetaKernel
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | lineSpan e x} ⊆
      {x : Vec m r | planeSpan e g x ∧ theta x = 0} := by
  intro x hxLine
  exact (lineSpan_iff_planeSpan_and_theta_eq_zero theta e g x
    hThetaPlane).mp hxLine

theorem planeSpan_thetaKernel_subset_lineSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | planeSpan e g x ∧ theta x = 0} ⊆
      {x : Vec m r | lineSpan e x} := by
  intro x hxPlaneTheta
  exact (lineSpan_iff_planeSpan_and_theta_eq_zero theta e g x
    hThetaPlane).mpr hxPlaneTheta

theorem lineSpan_set_eq_planeSpan_thetaKernel
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | lineSpan e x} =
      {x : Vec m r | planeSpan e g x ∧ theta x = 0} := by
  apply Set.Subset.antisymm
  · exact lineSpan_subset_planeSpan_thetaKernel theta e g hThetaPlane
  · exact planeSpan_thetaKernel_subset_lineSpan theta e g hThetaPlane

theorem theta_eq_zero_of_translatedLineSet
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e x : Vec m r)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxTranslatedLine : translatedLineSet H e x) :
    theta x = 0 := by
  rcases hxTranslatedLine with ⟨h, c, hH, hxTranslatedEq⟩
  rw [hxTranslatedEq]
  exact hThetaTranslatedLine h c hH

theorem translatedLineSet_subset_thetaKernel
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e : Vec m r)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | translatedLineSet H e x} ⊆
      {x : Vec m r | theta x = 0} := by
  intro x hxTranslatedLine
  exact theta_eq_zero_of_translatedLineSet theta H e x
    hThetaTranslatedLine hxTranslatedLine

theorem projectionKernelCriterion_coordinate
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineSpan e x := by
  have hThetaXTranslated :
      theta x = 0 :=
    theta_eq_zero_of_translatedLineSet theta H e x
      hThetaTranslatedLine hxTranslatedLine
  exact lineSpan_of_planeSpan_of_theta_eq_zero theta e g x
    hThetaPlane hxPlane hThetaXTranslated

theorem planeSpan_translatedLineSet_subset_lineSpan
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | planeSpan e g x ∧ translatedLineSet H e x} ⊆
      {x : Vec m r | lineSpan e x} := by
  intro x hxPlaneTranslated
  exact projectionKernelCriterion_coordinate theta H e g x
    hThetaPlane hThetaTranslatedLine
    hxPlaneTranslated.1 hxPlaneTranslated.2

theorem projectionKernelCriterion_set
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | planeSpan e g x ∧ translatedLineSet H e x} ⊆
      {x : Vec m r | lineSpan e x} :=
  planeSpan_translatedLineSet_subset_lineSpan theta H e g
    hThetaPlane hThetaTranslatedLine

theorem projectionKernelCriterion_lineCosetZero
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineCoset e (0 : Vec m r) x :=
  lineCoset_zero_of_lineSpan e x
    (projectionKernelCriterion_coordinate theta H e g x
      hThetaPlane hThetaTranslatedLine hxPlane hxTranslatedLine)

theorem projectionKernelCriterion_planeLineQuotientZero
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientZero e g :=
  planeLineQuotient_eq_zero_of_lineSpan e g x hxPlane
    (projectionKernelCriterion_coordinate theta H e g x
      hThetaPlane hThetaTranslatedLine hxPlane hxTranslatedLine)

theorem triangularTwoLeafProjectionKernel_coordinate
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineSpan e1 x := by
  rcases hxPlane with ⟨a, b, hxPlaneEq⟩
  have hbTranslated :
      translatedTwoLineSet H e0 e1 (fun i => b * g1 i) := by
    rcases hxTranslated with ⟨h, c0, c1, hH, hxTranslatedEq⟩
    refine ⟨h, c0 - b, c1 - a, hH, ?_⟩
    funext i
    have hEq :
        h i + c0 * e0 i + c1 * e1 i =
          a * e1 i +
            b * triangularPlaneGenerator e0 g1 i := by
      exact (congrFun hxTranslatedEq i).symm.trans
        (congrFun hxPlaneEq i)
    calc
      b * g1 i =
          (a * e1 i +
              b * triangularPlaneGenerator e0 g1 i) -
            b * e0 i - a * e1 i := by
        simp [triangularPlaneGenerator]
        ring
      _ = (h i + c0 * e0 i + c1 * e1 i) -
            b * e0 i - a * e1 i := by
        rw [← hEq]
      _ = h i + (c0 - b) * e0 i + (c1 - a) * e1 i := by
        ring
  have hbZero : b = 0 := hkill b hbTranslated
  refine ⟨a, ?_⟩
  rw [hxPlaneEq, hbZero]
  funext i
  simp [triangularPlaneGenerator]

theorem triangularTwoLeafProjectionKernel_set
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0) :
    {x : Vec m r |
      planeSpan e1 (triangularPlaneGenerator e0 g1) x ∧
        translatedTwoLineSet H e0 e1 x} ⊆
      {x : Vec m r | lineSpan e1 x} := by
  intro x hx
  exact triangularTwoLeafProjectionKernel_coordinate H e0 e1 g1 x
    hkill hx.1 hx.2

theorem triangularTwoLeafProjectionKernel_lineCosetZero
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineCoset e1 (0 : Vec m r) x :=
  lineCoset_zero_of_lineSpan e1 x
    (triangularTwoLeafProjectionKernel_coordinate H e0 e1 g1 x
      hkill hxPlane hxTranslated)

theorem triangularTwoLeafProjectionKernel_planeLineQuotientZero
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    planeLineQuotientMk e1 (triangularPlaneGenerator e0 g1)
        x hxPlane =
      planeLineQuotientZero e1 (triangularPlaneGenerator e0 g1) :=
  planeLineQuotient_eq_zero_of_lineSpan e1
    (triangularPlaneGenerator e0 g1) x hxPlane
    (triangularTwoLeafProjectionKernel_coordinate H e0 e1 g1 x
      hkill hxPlane hxTranslated)

end ProjectionKernel

export ProjectionKernel
  (lineSpan planeSpan translatedLineSet translatedTwoLineSet lineCoset
   triangularPlaneGenerator
   planeLineSetoid PlaneLineQuotient planeLineQuotientMk
   planeLineQuotientZero planeLineQuotientTheta
   projectionKernelCriterion_coordinate
   planeSpan_of_lineSpan theta_eq_zero_of_lineSpan
   lineCoset_refl lineCoset_symm lineCoset_trans
   lineCoset_zero_iff_lineSpan lineCoset_zero_of_lineSpan
   planeLineQuotient_mk_eq_of_lineCoset
   planeLineQuotient_eq_zero_of_lineSpan
   lineSpan_of_lineCoset_zero lineSpan_of_lineCoset_of_lineSpan
   planeSpan_of_lineCoset_of_planeSpan
   lineSpan_of_planeSpan_of_theta_eq_zero
   theta_eq_of_lineCoset_of_planeSpan
   planeLineQuotientTheta_mk
   planeLineQuotientTheta_zero
   theta_eq_zero_of_lineCoset_of_lineSpan
   lineCoset_of_planeSpan_of_theta_eq
   lineCoset_iff_theta_eq_of_planeSpan
   planeLineQuotientTheta_eq_iff_lineCoset
   planeSpan_lineCoset_subset_thetaFiber
   planeSpan_thetaFiber_subset_lineCoset
   planeSpan_lineCoset_set_eq_thetaFiber
   lineSpan_iff_theta_eq_zero_of_planeSpan
   planeLineQuotientTheta_eq_zero_iff_lineSpan
   lineSpan_iff_planeSpan_and_theta_eq_zero
   lineSpan_subset_planeSpan_thetaKernel
   planeSpan_thetaKernel_subset_lineSpan
   lineSpan_set_eq_planeSpan_thetaKernel
   theta_eq_zero_of_translatedLineSet
   translatedLineSet_subset_thetaKernel
   planeSpan_translatedLineSet_subset_lineSpan
   projectionKernelCriterion_set
   projectionKernelCriterion_lineCosetZero
   projectionKernelCriterion_planeLineQuotientZero
   triangularTwoLeafProjectionKernel_coordinate
   triangularTwoLeafProjectionKernel_set
   triangularTwoLeafProjectionKernel_lineCosetZero
   triangularTwoLeafProjectionKernel_planeLineQuotientZero)

end EvenV11
