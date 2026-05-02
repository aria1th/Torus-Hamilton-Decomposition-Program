import D5Odd.Even
import Shared.Monodromy
import Shared.RankCycle

namespace D5Odd

/-!
Lean-facing interface for the D5 even Route-E track.

The program-side Route-E verifier works with one-`Lambda_E` schedules,
count/slot data, and a small seam of size `m-1`.  This file records the shape
of the certificate that should eventually be produced from those traces.  The
existing endpoint bridge remains `D5EvenSeamReturnOrbitTarget` from
`D5Odd.Even`.
-/

structure RouteECounts (m : Nat) where
  slot : Fin 5
  counts : Fin 5 → Nat
  count_sum : (Finset.univ.sum counts) = m - 1

def LambdaE (S : Mask5) : Color → Direction :=
  if S = mask5 false false false false false then row5 0 1 2 3 4
  else if S = mask5 true false false false false then row5 0 1 3 2 4
  else if S = mask5 false true false false false then row5 0 1 2 4 3
  else if S = mask5 true true false false false then row5 4 1 3 2 0
  else if S = mask5 false false true false false then row5 4 1 2 3 0
  else if S = mask5 true false true false false then row5 4 1 3 0 2
  else if S = mask5 false true true false false then row5 1 0 2 4 3
  else if S = mask5 true true true false false then row5 1 4 3 0 2
  else if S = mask5 false false false true false then row5 1 0 2 3 4
  else if S = mask5 true false false true false then row5 1 3 0 2 4
  else if S = mask5 false true false true false then row5 3 0 2 4 1
  else if S = mask5 true true false true false then row5 4 0 3 2 1
  else if S = mask5 false false true true false then row5 4 2 1 3 0
  else if S = mask5 true false true true false then row5 4 3 1 2 0
  else if S = mask5 false true true true false then row5 3 2 0 4 1
  else if S = mask5 true true true true false then row5 0 1 2 3 4
  else if S = mask5 false false false false true then row5 0 2 1 3 4
  else if S = mask5 true false false false true then row5 0 2 1 4 3
  else if S = mask5 false true false false true then row5 0 2 4 1 3
  else if S = mask5 true true false false true then row5 3 2 4 1 0
  else if S = mask5 false false true false true then row5 2 4 1 3 0
  else if S = mask5 true false true false true then row5 4 2 1 0 3
  else if S = mask5 false true true false true then row5 2 0 1 4 3
  else if S = mask5 true true true false true then row5 0 1 2 3 4
  else if S = mask5 false false false true true then row5 1 0 3 2 4
  else if S = mask5 true false false true true then row5 1 3 0 4 2
  else if S = mask5 false true false true true then row5 1 0 4 2 3
  else if S = mask5 true true false true true then row5 0 1 2 3 4
  else if S = mask5 false false true true true then row5 2 4 3 1 0
  else if S = mask5 true false true true true then row5 0 1 2 3 4
  else if S = mask5 false true true true true then row5 0 1 2 3 4
  else if S = mask5 true true true true true then row5 0 1 2 3 4
  else row5 0 1 2 3 4

set_option linter.style.nativeDecide false in
theorem LambdaE_latin : ∀ S : Mask5, Function.Bijective (LambdaE S) := by
  native_decide

set_option linter.style.nativeDecide false in
theorem LambdaE_cyclic :
    ∀ (S : Mask5) (a c : Color),
      LambdaE (rotMask c S) (fin5AddNat a c.val) =
        fin5AddNat (LambdaE S a) c.val := by
  native_decide

theorem card_vec4 (m : Nat) [NeZero m] :
    Fintype.card (Vec4 m) = m ^ 4 := by
  calc
    Fintype.card (Vec4 m) = Fintype.card (Fin 4 → ZMod m) := rfl
    _ = Fintype.card (ZMod m) ^ 4 := by
      simp
    _ = m ^ 4 := by
      rw [ZMod.card]

abbrev RouteENonzeroSeam (m : Nat) := { a : ZMod m // a ≠ 0 }

theorem card_routeENonzeroSeam (m : Nat) [NeZero m] :
    Fintype.card (RouteENonzeroSeam m) = m - 1 := by
  change Fintype.card { a : ZMod m // a ≠ 0 } = m - 1
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun a : ZMod m => a ≠ 0) =
        Finset.univ.erase (0 : ZMod m) := by
    ext a
    simp
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

structure RouteESeamTranslationBlock (m : Nat) where
  start : Nat
  stop : Nat
  delta : ZMod m
  start_pos : 0 < start
  stop_lt : stop < m
  start_le_stop : start ≤ stop

namespace RouteESeamTranslationBlock

def contains {m : Nat} (block : RouteESeamTranslationBlock m)
    (a : RouteENonzeroSeam m) : Prop :=
  block.start ≤ a.1.val ∧ a.1.val ≤ block.stop

def translationFormula {m : Nat} (block : RouteESeamTranslationBlock m)
    (f : RouteENonzeroSeam m → RouteENonzeroSeam m) : Prop :=
  ∀ a, block.contains a → (f a).1 = a.1 + block.delta

end RouteESeamTranslationBlock

def routeEOpenPortSectionPairMap {m : Nat}
    (A B : ZMod m) : ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p =>
    if p.1 + p.2 = 0 then
      (p.1 + A, p.2 + B + 1)
    else
      (p.1 + A + 1, p.2 + B)

def routeEOpenPortChart {m : Nat} :
    ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p => (p.1 + p.2, p.1)

def routeEOpenPortChartEquiv {m : Nat} :
    ZMod m × ZMod m ≃ ZMod m × ZMod m where
  toFun := routeEOpenPortChart
  invFun := fun p => (p.2, p.1 - p.2)
  left_inv := by
    intro p
    rcases p with ⟨a, b⟩
    simp [routeEOpenPortChart]
  right_inv := by
    intro p
    rcases p with ⟨sigma, a⟩
    simp [routeEOpenPortChart]

def routeEOpenPortHMap {m : Nat}
    (A C : ZMod m) : ZMod m × ZMod m → ZMod m × ZMod m :=
  fun p => (p.1 - C, p.2 + A + 1 - if p.1 = 0 then 1 else 0)

set_option linter.flexible false in
theorem routeEOpenPortChart_sectionPairMap
    {m : Nat} (A B C : ZMod m)
    (hABC : A + B + C + 1 = 0) (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap A B p) =
      routeEOpenPortHMap A C (routeEOpenPortChart p) := by
  rcases p with ⟨a, b⟩
  have hABC' : A + B + 1 = -C := by
    calc
      A + B + 1 = A + B + C + 1 - C := by ring
      _ = 0 - C := by rw [hABC]
      _ = -C := by ring
  by_cases h : a + b = 0
  · apply Prod.ext
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
      calc
        a + A + (b + B + 1) = (a + b) + (A + B + 1) := by ring
        _ = 0 + (A + B + 1) := by rw [h]
        _ = -C := by rw [hABC']; ring
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
  · apply Prod.ext
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]
      calc
        a + A + 1 + (b + B) = (a + b) + (A + B + 1) := by ring
        _ = (a + b) - C := by rw [hABC']; ring
    · simp [routeEOpenPortSectionPairMap, routeEOpenPortChart,
        routeEOpenPortHMap, h]

structure RouteEOpenPortAffineChartCertificate (m : Nat) [NeZero m] where
  A : ZMod m
  B : ZMod m
  C : ZMod m
  count_sum : A + B + C + 1 = 0
  C_unit : IsUnit C
  chartRank : ZMod m × ZMod m → ZMod (m ^ 2)
  chartRank_bijective : Function.Bijective chartRank
  chartRank_step :
    ∀ p, chartRank (routeEOpenPortHMap A C p) = chartRank p + 1

namespace RouteEOpenPortAffineChartCertificate

theorem H_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m) :
    IsSingleCycleMap (routeEOpenPortHMap cert.A cert.C) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  haveI : NeZero (m ^ 2) := ⟨ne_of_gt (pow_pos hmpos 2)⟩
  exact Shared.single_cycle_of_zmod_rank
    (routeEOpenPortHMap cert.A cert.C)
    cert.chartRank cert.chartRank_bijective cert.chartRank_step

theorem sectionPairMap_conjugates_to_H {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m)
    (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap cert.A cert.B p) =
      routeEOpenPortHMap cert.A cert.C (routeEOpenPortChart p) :=
  routeEOpenPortChart_sectionPairMap cert.A cert.B cert.C cert.count_sum p

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortAffineChartCertificate m) :
    IsSingleCycleMap (routeEOpenPortSectionPairMap cert.A cert.B) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (routeEOpenPortChartEquiv (m := m)).symm)
    (f := routeEOpenPortSectionPairMap cert.A cert.B)
    (g := routeEOpenPortHMap cert.A cert.C)
    (H_single_cycle cert) ?_
  intro p
  calc
    routeEOpenPortChart
        (routeEOpenPortSectionPairMap cert.A cert.B
          ((routeEOpenPortChartEquiv (m := m)).symm p)) =
        routeEOpenPortHMap cert.A cert.C
          (routeEOpenPortChart ((routeEOpenPortChartEquiv (m := m)).symm p)) :=
      sectionPairMap_conjugates_to_H cert ((routeEOpenPortChartEquiv (m := m)).symm p)
    _ = routeEOpenPortHMap cert.A cert.C p := by
      simpa [routeEOpenPortChartEquiv] using
        congrArg (routeEOpenPortHMap cert.A cert.C)
          ((routeEOpenPortChartEquiv (m := m)).right_inv p)

end RouteEOpenPortAffineChartCertificate

def routeEThetaPoint {m : Nat} (slot : Color) (a : ZMod m) : Vec4 m :=
  if slot = 0 then ![a, 0, 0, -a] else
  if slot = 1 then ![0, a, 0, 0] else
  if slot = 2 then ![-a, 0, a, 0] else
  if slot = 3 then ![0, -a, 0, a] else
  ![0, 0, -a, 0]

def routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) : Vec5 m :=
  if slot = 0 then ![0, a, 0, 0, -a] else
  if slot = 1 then ![-a, 0, a, 0, 0] else
  if slot = 2 then ![0, -a, 0, a, 0] else
  if slot = 3 then ![0, 0, -a, 0, a] else
  ![a, 0, 0, -a, 0]

theorem root5_routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) :
    Root5 m (routeEThetaVec slot a) := by
  fin_cases slot <;>
    simp [routeEThetaVec, Root5, sum5, Fin.sum_univ_five]

theorem rootZ_routeEThetaVec {m : Nat} (slot : Color) (a : ZMod m) :
    rootZ (routeEThetaVec slot a) = routeEThetaPoint slot a := by
  fin_cases slot <;>
    funext i <;>
    fin_cases i <;>
    simp [rootZ, routeEThetaVec, routeEThetaPoint, fin4ToFin5]

theorem rootOfZ_routeEThetaPoint {m : Nat} (slot : Color) (a : ZMod m) :
    (rootOfZ (routeEThetaPoint slot a)).1 = routeEThetaVec slot a := by
  fin_cases slot <;>
    ext i <;>
    fin_cases i <;>
    simp [rootOfZ, routeEThetaPoint, routeEThetaVec]

theorem routeEThetaVec_port_zero {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 2) = 0 := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem routeEThetaVec_pos_param {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 1) = a := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem routeEThetaVec_neg_param {m : Nat} (slot : Color) (a : ZMod m) :
    routeEThetaVec slot a (fin5AddNat slot 4) = -a := by
  fin_cases slot <;> simp [routeEThetaVec, fin5AddNat]

theorem LambdaE_routeEThetaVec {m : Nat} (slot : Color) {a : ZMod m}
    (ha : a ≠ 0) :
    LambdaE (zeroMaskMinusOne (routeEThetaVec slot a)) slot =
      fin5AddNat slot 2 := by
  have hneg : -a ≠ 0 := by
    intro h
    exact ha (neg_eq_zero.mp h)
  fin_cases slot <;>
    rw [zeroMaskMinusOne_eq_mask5] <;>
    simp [LambdaE, routeEThetaVec, mask5, row5, fin5AddNat, ha, hneg]

theorem LambdaE_routeEThetaSeam {m : Nat} (slot : Color)
    (a : RouteENonzeroSeam m) :
    LambdaE (zeroMaskMinusOne (routeEThetaVec slot a.1)) slot =
      fin5AddNat slot 2 :=
  LambdaE_routeEThetaVec slot a.2

theorem routeEThetaPoint_injective {m : Nat} (slot : Color) :
    Function.Injective (routeEThetaPoint (m := m) slot) := by
  intro a b h
  fin_cases slot
  · have h0 := congrArg (fun z : Vec4 m => z 0) h
    simpa [routeEThetaPoint] using h0
  · have h1 := congrArg (fun z : Vec4 m => z 1) h
    simpa [routeEThetaPoint] using h1
  · have h2 := congrArg (fun z : Vec4 m => z 2) h
    simpa [routeEThetaPoint] using h2
  · have h3 := congrArg (fun z : Vec4 m => z 3) h
    simpa [routeEThetaPoint] using h3
  · have h2 := congrArg (fun z : Vec4 m => z 2) h
    exact neg_injective (by simpa [routeEThetaPoint] using h2)

def routeEThetaSeamPoint {m : Nat} (slot : Color) :
    RouteENonzeroSeam m → Vec4 m :=
  fun a => routeEThetaPoint (m := m) slot a.1

theorem routeEThetaSeamPoint_injective {m : Nat} (slot : Color) :
    Function.Injective (routeEThetaSeamPoint (m := m) slot) := by
  intro a b h
  apply Subtype.ext
  exact routeEThetaPoint_injective slot h

structure RouteESmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  seam : Type
  seamFintype : Fintype seam
  seamPoint : seam → Vec4 m
  seamPoint_injective : Function.Injective seamPoint
  seamReturn : Color → seam → seam
  returnTime : Color → seam → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (seamPoint a) =
        seamPoint (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (seamPoint a) = seamPoint b
  seamReturn_single :
    ∀ c, letI := seamFintype; IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, letI := seamFintype;
      Finset.univ.sum (fun a : seam => returnTime c a) = m ^ 4

namespace RouteESmallSeamCertificate

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) := by
  letI := cert.seamFintype
  exact single_cycle_of_first_return_sum
    (f := seamRootReturn cert.data c)
    (base := cert.seamPoint)
    (next := cert.seamReturn c)
    (time := cert.returnTime c)
    (hf := seamRootReturn_bijective cert.data c)
    (hbase_inj := cert.seamPoint_injective)
    (hreturn := cert.firstReturn_equation c)
    (hfirst := cert.firstReturn_minimal c)
    (hnext := cert.seamReturn_single c)
    (hsum := by
      rw [cert.returnTime_sum c]
      exact (card_vec4 m).symm)

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data := by
  intro c x y
  exact (cert.seamRootReturn_single_cycle c).2 x y

def toSeamReturnCertificateTarget {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    D5EvenSeamReturnCertificateTarget m :=
  ⟨cert.data, D5EvenSeamReturnCompatible.of_seam_data cert.data,
    cert.orbitTarget⟩

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  D5_even_from_return_certificate cert.toSeamReturnCertificateTarget

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  D5_even_torus_from_return_certificate cert.toSeamReturnCertificateTarget

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteESmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  D5_even_cayley_from_return_certificate cert.toSeamReturnCertificateTarget

end RouteESmallSeamCertificate

structure RouteENonopenSmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  seamPoint : RouteENonzeroSeam m → Vec4 m
  seamPoint_injective : Function.Injective seamPoint
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (seamPoint a) =
        seamPoint (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (seamPoint a) = seamPoint b
  seamReturn_single :
    ∀ c, IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteENonopenSmallSeamCertificate

theorem seam_card {m : Nat} [NeZero m]
    (_cert : RouteENonopenSmallSeamCertificate m) :
    Fintype.card (RouteENonzeroSeam m) = m - 1 :=
  card_routeENonzeroSeam m

theorem returnTime_sum_card_form {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) (c : Color) :
    Finset.univ.sum (fun a : RouteENonzeroSeam m => cert.returnTime c a) =
      Fintype.card (Vec4 m) := by
  rw [cert.returnTime_sum c]
  exact (card_vec4 m).symm

def toSmallSeamCertificate {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    RouteESmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  seam := RouteENonzeroSeam m
  seamFintype := inferInstance
  seamPoint := cert.seamPoint
  seamPoint_injective := cert.seamPoint_injective
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := by
    intro c
    simpa using cert.seamReturn_single c
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteENonopenSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteENonopenSmallSeamCertificate

structure RouteEThetaSmallSeamCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  routeCounts_slot : routeCounts.slot = slot
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot b
  seamReturn_single :
    ∀ c, IsSingleCycleMap (seamReturn c)
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteEThetaSmallSeamCertificate

theorem seam_card {m : Nat} [NeZero m]
    (_cert : RouteEThetaSmallSeamCertificate m) :
    Fintype.card (RouteENonzeroSeam m) = m - 1 :=
  card_routeENonzeroSeam m

theorem returnTime_sum_card_form {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) (c : Color) :
    Finset.univ.sum (fun a : RouteENonzeroSeam m => cert.returnTime c a) =
      Fintype.card (Vec4 m) := by
  rw [cert.returnTime_sum c]
  exact (card_vec4 m).symm

def toNonopenSmallSeamCertificate {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    RouteENonopenSmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  slot := cert.slot
  seamPoint := routeEThetaSeamPoint cert.slot
  seamPoint_injective := routeEThetaSeamPoint_injective cert.slot
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := cert.seamReturn_single
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toNonopenSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toNonopenSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toNonopenSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaSmallSeamCertificate

structure RouteEThetaRankedSmallSeamCertificate (m : Nat) [NeZero m]
    [NeZero (m - 1)] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  slot : Color
  routeCounts_slot : routeCounts.slot = slot
  seamReturn : Color → RouteENonzeroSeam m → RouteENonzeroSeam m
  returnTime : Color → RouteENonzeroSeam m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot (seamReturn c a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint slot a) =
        routeEThetaSeamPoint slot b
  seamRank : Color → RouteENonzeroSeam m → ZMod (m - 1)
  seamRank_bijective : ∀ c, Function.Bijective (seamRank c)
  seamRank_step :
    ∀ c a, seamRank c (seamReturn c a) = seamRank c a + 1
  returnTime_sum :
    ∀ c, Finset.univ.sum (fun a : RouteENonzeroSeam m => returnTime c a) = m ^ 4

namespace RouteEThetaRankedSmallSeamCertificate

theorem seamReturn_single {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (cert.seamReturn c) :=
  Shared.single_cycle_of_zmod_rank
    (f := cert.seamReturn c)
    (rank := cert.seamRank c)
    (cert.seamRank_bijective c)
    (cert.seamRank_step c)

def toThetaSmallSeamCertificate {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    RouteEThetaSmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  slot := cert.slot
  routeCounts_slot := cert.routeCounts_slot
  seamReturn := cert.seamReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := cert.seamReturn_single
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toThetaSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toThetaSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedSmallSeamCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toThetaSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaRankedSmallSeamCertificate

structure RouteEThetaPiecewiseTranslationCertificate (m : Nat) [NeZero m] extends
    RouteEThetaSmallSeamCertificate m where
  blocks : Color → List (RouteESeamTranslationBlock m)
  block_cover :
    ∀ c a, ∃ block, block ∈ blocks c ∧ block.contains a
  block_disjoint :
    ∀ c a block₁ block₂,
      block₁ ∈ blocks c → block₂ ∈ blocks c →
      block₁.contains a → block₂.contains a → block₁ = block₂
  block_translation :
    ∀ c block,
      block ∈ blocks c →
        block.translationFormula (seamReturn c)

namespace RouteEThetaPiecewiseTranslationCertificate

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toRouteEThetaSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toRouteEThetaSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEThetaPiecewiseTranslationCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toRouteEThetaSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEThetaPiecewiseTranslationCertificate

structure RouteEThetaRankedPiecewiseTranslationCertificate (m : Nat) [NeZero m]
    [NeZero (m - 1)] extends RouteEThetaRankedSmallSeamCertificate m where
  blocks : Color → List (RouteESeamTranslationBlock m)
  block_cover :
    ∀ c a, ∃ block, block ∈ blocks c ∧ block.contains a
  block_disjoint :
    ∀ c a block₁ block₂,
      block₁ ∈ blocks c → block₂ ∈ blocks c →
      block₁.contains a → block₂.contains a → block₁ = block₂
  block_translation :
    ∀ c block,
      block ∈ blocks c →
        block.translationFormula (seamReturn c)

namespace RouteEThetaRankedPiecewiseTranslationCertificate

def toThetaPiecewiseTranslationCertificate {m : Nat} [NeZero m]
    [NeZero (m - 1)] (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    RouteEThetaPiecewiseTranslationCertificate m where
  toRouteEThetaSmallSeamCertificate :=
    cert.toRouteEThetaRankedSmallSeamCertificate.toThetaSmallSeamCertificate
  blocks := cert.blocks
  block_cover := cert.block_cover
  block_disjoint := cert.block_disjoint
  block_translation := cert.block_translation

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toThetaPiecewiseTranslationCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toThetaPiecewiseTranslationCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m] [NeZero (m - 1)]
    (cert : RouteEThetaRankedPiecewiseTranslationCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toThetaPiecewiseTranslationCertificate.toCayleyHamiltonDecomposition

end RouteEThetaRankedPiecewiseTranslationCertificate

def D5EvenRouteEAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteESmallSeamCertificate m)

def D5EvenRouteENonopenAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteENonopenSmallSeamCertificate m)

def D5EvenRouteEThetaAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteEThetaSmallSeamCertificate m)

def D5EvenRouteEThetaRankedAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m] [NeZero (m - 1)], Even m → 6 ≤ m →
    Nonempty (RouteEThetaRankedSmallSeamCertificate m)

def D5EvenRouteEThetaPiecewiseAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteEThetaPiecewiseTranslationCertificate m)

def D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m] [NeZero (m - 1)], Even m → 6 ≤ m →
    Nonempty (RouteEThetaRankedPiecewiseTranslationCertificate m)

def D5EvenRouteEM4FiniteTarget : Prop :=
  Nonempty (HamiltonDecompositionD5 4)

def D5EvenRouteEAllEvenHamiltonTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (HamiltonDecompositionD5 m)

def D5EvenRouteEAllEvenTorusTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (TorusHamiltonDecompositionD5 m)

def D5EvenRouteEAllEvenCayleyTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 4 ≤ m →
    Nonempty (CayleyHamiltonDecompositionD5 m)

theorem D5EvenRouteEAllLargeEvenTarget.of_nonopen
    (h : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (h : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toNonopenSmallSeamCertificate⟩

theorem D5EvenRouteEAllLargeEvenTarget.of_theta
    (h : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_nonopen
    (D5EvenRouteENonopenAllLargeEvenTarget.of_theta h)

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  letI : NeZero (m - 1) := ⟨by omega⟩
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toThetaSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked h)

theorem D5EvenRouteEAllLargeEvenTarget.of_ranked
    (h : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked h)

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  rcases h m hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toRouteEThetaSmallSeamCertificate⟩

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise h)

theorem D5EvenRouteEAllLargeEvenTarget.of_piecewise
    (h : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_piecewise h)

theorem D5EvenRouteEThetaRankedAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaRankedAllLargeEvenTarget := by
  intro m _hm0 _hm1 hmEven hm6
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toRouteEThetaRankedSmallSeamCertificate⟩

theorem D5EvenRouteEThetaPiecewiseAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaPiecewiseAllLargeEvenTarget := by
  intro m _hm0 hmEven hm6
  letI : NeZero (m - 1) := ⟨by omega⟩
  rcases h (m := m) hmEven hm6 with ⟨cert⟩
  exact ⟨cert.toThetaPiecewiseTranslationCertificate⟩

theorem D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEThetaAllLargeEvenTarget :=
  D5EvenRouteEThetaAllLargeEvenTarget.of_ranked
    (D5EvenRouteEThetaRankedAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteENonopenAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteENonopenAllLargeEvenTarget :=
  D5EvenRouteENonopenAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise
    (h : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllLargeEvenTarget :=
  D5EvenRouteEAllLargeEvenTarget.of_theta
    (D5EvenRouteEThetaAllLargeEvenTarget.of_ranked_piecewise h)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · exact hm4
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toTorusHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · rcases hm4 with ⟨h4⟩
      exact ⟨torusHamiltonDecomposition_of_model h4⟩
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenTorusTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget := by
  intro m _hm0 hmEven hm4le
  by_cases hm6 : 6 ≤ m
  · rcases hlarge m hmEven hm6 with ⟨cert⟩
    exact ⟨cert.toCayleyHamiltonDecomposition⟩
  · have hmle5 : m ≤ 5 := by omega
    interval_cases m
    · rcases hm4 with ⟨h4⟩
      exact ⟨cayleyHamiltonDecomposition_of_torus
        (torusHamiltonDecomposition_of_model h4)⟩
    · norm_num at hmEven

theorem D5EvenRouteEAllEvenCayleyTarget.of_nonopen_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_nonopen hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_theta_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_theta hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_piecewise hlarge)

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_piecewise_and_m4
    (hm4 : D5EvenRouteEM4FiniteTarget)
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4 hm4
    (D5EvenRouteEAllLargeEvenTarget.of_ranked_piecewise hlarge)

end D5Odd
