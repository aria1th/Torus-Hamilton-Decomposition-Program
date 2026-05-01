import D5Odd.Even

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

def routeEThetaPoint {m : Nat} (slot : Color) (a : ZMod m) : Vec4 m :=
  if slot = 0 then ![a, 0, 0, -a] else
  if slot = 1 then ![0, a, 0, 0] else
  if slot = 2 then ![-a, 0, a, 0] else
  if slot = 3 then ![0, -a, 0, a] else
  ![0, 0, -a, 0]

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

def D5EvenRouteEAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteESmallSeamCertificate m)

def D5EvenRouteENonopenAllLargeEvenTarget : Prop :=
  ∀ (m : Nat) [NeZero m], Even m → 6 ≤ m →
    Nonempty (RouteENonopenSmallSeamCertificate m)

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

end D5Odd
