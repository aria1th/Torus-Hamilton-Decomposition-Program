import D5Odd.Cayley

namespace D5Odd

abbrev Vec4 (m : Nat) := Fin 4 -> ZMod m

def fin4ToFin5 (k : Fin 4) : Fin 5 :=
  ⟨k.val + 1, by omega⟩

def b4 (m : Nat) (i : Direction) : Vec4 m :=
  fun k => if i.val = k.val + 1 then 1 else 0

def rootZ (w : Vec5 m) : Vec4 m :=
  fun k => w (fin4ToFin5 k)

def zAtLayer {m : Nat} (t : Fin m) (w : Vec5 m) : Vec4 m :=
  fun k => rootZ w k + if k.val = 3 then (t.val : ZMod m) else 0

structure D5EvenSeamData (m : Nat) where
  sigma : Color -> Vec4 m -> Direction
  latin : forall z : Vec4 m, Function.Bijective fun c : Color => sigma c z
  step_bijective : forall c : Color,
    Function.Bijective fun z : Vec4 m => z + b4 m (sigma c z)

def evenDir {m : Nat} (S : D5EvenSeamData m) (t : Fin m) (c : Color) (w : Vec5 m) :
    Direction :=
  if t.val + 1 = m then S.sigma c (zAtLayer t w) else c

def evenSchedule {m : Nat} (S : D5EvenSeamData m) : LayerSchedule m where
  dir := evenDir S

theorem zmod_val_eq_neg_one_of_fin_is_last {m : Nat} [NeZero m] {t : Fin m}
    (ht : t.val + 1 = m) :
    ((t.val : Nat) : ZMod m) = -1 := by
  have hcast : (((t.val + 1 : Nat) : ZMod m)) = 0 := by
    rw [ht]
    exact ZMod.natCast_self m
  have hsum : ((t.val : Nat) : ZMod m) + 1 = 0 := by
    simpa [Nat.cast_add] using hcast
  linear_combination hsum

theorem zAtLayer_last_sub_q5_add_b4 {m : Nat} [NeZero m] {t : Fin m}
    (ht : t.val + 1 = m) (y : Vec5 m) (i : Direction) :
    zAtLayer t (y - q5 m i) + b4 m i = rootZ y := by
  have htval := zmod_val_eq_neg_one_of_fin_is_last (m := m) (t := t) ht
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [zAtLayer, rootZ, fin4ToFin5, b4, q5, e5, htval]

theorem evenSchedule_latin {m : Nat} (S : D5EvenSeamData m) :
    IsScheduleLatin (evenSchedule S) := by
  intro t w
  unfold evenSchedule evenDir
  by_cases ht : t.val + 1 = m
  · simpa [ht] using S.latin (zAtLayer t w)
  · simp [ht]

theorem evenSchedule_exact {m : Nat} [NeZero m] (S : D5EvenSeamData m) :
    IsLayerExactCover (evenSchedule S) := by
  intro t c y
  unfold evenSchedule evenDir
  by_cases ht : t.val + 1 = m
  · let target : Vec4 m := rootZ y.1
    rcases (S.step_bijective c).2 target with ⟨z, hz⟩
    let i : Direction := S.sigma c z
    refine ⟨i, ?_, ?_⟩
    · have hpre : zAtLayer t (y.1 - q5 m i) = z := by
        have hgeom := zAtLayer_last_sub_q5_add_b4 (m := m) (t := t) ht y.1 i
        have hz' : z + b4 m i = target := by
          simpa [target, i] using hz
        apply add_right_cancel (b := b4 m i)
        calc
          zAtLayer t (y.1 - q5 m i) + b4 m i = rootZ y.1 := hgeom
          _ = target := rfl
          _ = z + b4 m i := hz'.symm
      simp [ht, i, hpre]
    · intro j hj
      have hjsigma : S.sigma c (zAtLayer t (y.1 - q5 m j)) = j := by
        simpa [ht] using hj
      have hprej : (fun z : Vec4 m => z + b4 m (S.sigma c z))
          (zAtLayer t (y.1 - q5 m j)) = target := by
        have hgeom := zAtLayer_last_sub_q5_add_b4 (m := m) (t := t) ht y.1 j
        dsimp
        rw [hjsigma]
        simpa [target] using hgeom
      have hzfun : (fun z : Vec4 m => z + b4 m (S.sigma c z)) z = target := by
        simpa [target] using hz
      have hfun_eq :
          (fun z : Vec4 m => z + b4 m (S.sigma c z)) (zAtLayer t (y.1 - q5 m j)) =
            (fun z : Vec4 m => z + b4 m (S.sigma c z)) z := by
        rw [hprej, hzfun]
      have hzinj := (S.step_bijective c).1 hfun_eq
      calc
        j = S.sigma c (zAtLayer t (y.1 - q5 m j)) := hjsigma.symm
        _ = S.sigma c z := by rw [hzinj]
        _ = i := rfl
  · refine ⟨c, ?_, ?_⟩
    · simp [ht]
    · intro i hi
      simpa [ht] using hi.symm

def seamStepMap {m : Nat} (S : D5EvenSeamData m) (c : Color) :
    Vec4 m → Vec4 m :=
  fun z => z + b4 m (S.sigma c z)

def seamRootReturn {m : Nat} (S : D5EvenSeamData m) (c : Color) :
    Vec4 m → Vec4 m :=
  fun z => seamStepMap S c (z - b4 m c)

theorem vec4_sub_const_bijective {m : Nat} (v : Vec4 m) :
    Function.Bijective fun z : Vec4 m => z - v := by
  constructor
  · intro x y hxy
    funext k
    have hk := congrArg (fun z : Vec4 m => z k) hxy
    have hc := congrArg (fun a : ZMod m => a + v k) hk
    simpa using hc
  · intro y
    exact ⟨y + v, by simp⟩

theorem seamStepMap_bijective {m : Nat} (S : D5EvenSeamData m) (c : Color) :
    Function.Bijective (seamStepMap S c) := by
  simpa [seamStepMap] using S.step_bijective c

theorem seamRootReturn_bijective {m : Nat} (S : D5EvenSeamData m) (c : Color) :
    Function.Bijective (seamRootReturn S c) := by
  exact (seamStepMap_bijective S c).comp
    (vec4_sub_const_bijective (b4 m c))

def D5EvenSeamReturnOrbitTarget (S : D5EvenSeamData m) : Prop :=
  ∀ c : Color, ∀ x y : Vec4 m, ∃ n : Nat,
    (seamRootReturn S c)^[n] x = y

theorem seamRootReturn_single_cycle_of_orbit_target {m : Nat}
    (S : D5EvenSeamData m) (hOrbit : D5EvenSeamReturnOrbitTarget S)
    (c : Color) :
    IsSingleCycleMap (seamRootReturn S c) := by
  exact ⟨seamRootReturn_bijective S c, hOrbit c⟩

def D5EvenSeamHamiltonian (S : D5EvenSeamData m) : Prop :=
  AllColorHamiltonian (evenSchedule S)

def D5EvenCertificateTarget (m : Nat) : Prop :=
  exists S : D5EvenSeamData m, D5EvenSeamHamiltonian S

theorem D5_even_from_seam_data {m : Nat} [NeZero m] (S : D5EvenSeamData m)
    (hHam : D5EvenSeamHamiltonian S) :
    HamiltonDecompositionD5 m := by
  exact ⟨evenSchedule S, evenSchedule_exact S, evenSchedule_latin S, hHam⟩

theorem D5_even_from_target {m : Nat} [NeZero m] (h : D5EvenCertificateTarget m) :
    HamiltonDecompositionD5 m := by
  rcases h with ⟨S, hHam⟩
  exact D5_even_from_seam_data S hHam

theorem D5_even_torus_from_seam_data {m : Nat} [NeZero m] (S : D5EvenSeamData m)
    (hHam : D5EvenSeamHamiltonian S) :
    TorusHamiltonDecompositionD5 m := by
  exact torusHamiltonDecomposition_of_model
    (D5_even_from_seam_data S hHam)

theorem D5_even_torus_from_target {m : Nat} [NeZero m]
    (h : D5EvenCertificateTarget m) :
    TorusHamiltonDecompositionD5 m := by
  exact torusHamiltonDecomposition_of_model (D5_even_from_target h)

theorem D5_even_cayley_from_seam_data {m : Nat} [NeZero m] (S : D5EvenSeamData m)
    (hHam : D5EvenSeamHamiltonian S) :
    CayleyHamiltonDecompositionD5 m := by
  exact cayleyHamiltonDecomposition_of_torus
    (D5_even_torus_from_seam_data S hHam)

theorem D5_even_cayley_from_target {m : Nat} [NeZero m]
    (h : D5EvenCertificateTarget m) :
    CayleyHamiltonDecompositionD5 m := by
  exact cayleyHamiltonDecomposition_of_torus
    (D5_even_torus_from_target h)

end D5Odd
