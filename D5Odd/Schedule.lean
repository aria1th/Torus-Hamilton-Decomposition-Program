import D5Odd.ZeroSetTable

namespace D5Odd

structure LayerSchedule (m : Nat) where
  dir : Fin m -> Color -> Vec5 m -> Direction

def layerMap {m : Nat} (F : LayerSchedule m) (t : Fin m) (c : Color) (w : ARoot5 m) :
    ARoot5 m :=
  ⟨w.1 + q5 m (F.dir t c w.1), root5_add_q5 w.2 _⟩

def IsLayerExactCover {m : Nat} (F : LayerSchedule m) : Prop :=
  forall t : Fin m, forall c : Color, forall y : ARoot5 m,
    ∃! i : Direction, F.dir t c (y.1 - q5 m i) = i

theorem layerMap_surjective_of_exactCover {m : Nat} {F : LayerSchedule m}
    (hF : IsLayerExactCover F) (t : Fin m) (c : Color) :
    Function.Surjective (layerMap F t c) := by
  intro y
  rcases hF t c y with ⟨i, hi, _⟩
  refine ⟨⟨y.1 - q5 m i, root5_sub_q5 y.2 i⟩, ?_⟩
  apply Subtype.ext
  simp [layerMap, hi]

theorem layerMap_injective_of_exactCover {m : Nat} {F : LayerSchedule m}
    (hF : IsLayerExactCover F) (t : Fin m) (c : Color) :
    Function.Injective (layerMap F t c) := by
  intro x x' hxx'
  let y : ARoot5 m := layerMap F t c x
  let i : Direction := F.dir t c x.1
  let i' : Direction := F.dir t c x'.1
  have hi : F.dir t c (y.1 - q5 m i) = i := by
    change F.dir t c ((x.1 + q5 m i) - q5 m i) = i
    simp [i]
  have hi' : F.dir t c (y.1 - q5 m i') = i' := by
    have hy : y = layerMap F t c x' := by simpa [y] using hxx'
    change F.dir t c (y.1 - q5 m i') = i'
    rw [hy]
    change F.dir t c (((x'.1 + q5 m i') - q5 m i')) = i'
    simp [i']
  rcases hF t c y with ⟨k, hk, huniq⟩
  have hik : i = k := huniq i hi
  have hi'k : i' = k := huniq i' hi'
  apply Subtype.ext
  have hx : y.1 - q5 m i = x.1 := by
    change (x.1 + q5 m i) - q5 m i = x.1
    simp
  have hx' : y.1 - q5 m i' = x'.1 := by
    have hy : y = layerMap F t c x' := by simpa [y] using hxx'
    rw [hy]
    change (x'.1 + q5 m i') - q5 m i' = x'.1
    simp
  calc
    x.1 = y.1 - q5 m i := hx.symm
    _ = y.1 - q5 m i' := by rw [hik, hi'k]
    _ = x'.1 := hx'

theorem layerMap_bijective_of_exactCover {m : Nat} {F : LayerSchedule m}
    (hF : IsLayerExactCover F) (t : Fin m) (c : Color) :
    Function.Bijective (layerMap F t c) :=
  ⟨layerMap_injective_of_exactCover hF t c, layerMap_surjective_of_exactCover hF t c⟩

def IsScheduleLatin {m : Nat} (F : LayerSchedule m) : Prop :=
  forall t : Fin m, forall w : Vec5 m, Function.Bijective fun c : Color => F.dir t c w

def IsSingleCycleMap {alpha : Type*} (f : alpha -> alpha) : Prop :=
  Function.Bijective f ∧ forall x y : alpha, exists n : Nat, f^[n] x = y

def colorReturn {m : Nat} (F : LayerSchedule m) (c : Color) (w : ARoot5 m) : ARoot5 m :=
  (List.finRange m).foldl (fun x t => layerMap F t c x) w

def AllColorHamiltonian {m : Nat} (F : LayerSchedule m) : Prop :=
  forall c : Color, IsSingleCycleMap (colorReturn F c)

def ge5Dir {m : Nat} (t : Fin m) (c : Color) (w : Vec5 m) : Direction :=
  if t.val = 1 then Lambda1 (zeroMaskMinusOne w) c else
  if t.val = 2 then fin5AddNat c 3 else
  if t.val = 3 then fin5AddNat c 4 else
  c

def ge5Schedule (m : Nat) : LayerSchedule m where
  dir := ge5Dir

def m3Dir (t : Fin 3) (c : Color) (w : Vec5 3) : Direction :=
  if t.val = 1 then Lambda1 (zeroMaskMinusOne w) c else
  if t.val = 0 then fin5AddNat c 4 else
  fin5AddNat c 3

def m3Schedule : LayerSchedule 3 where
  dir := m3Dir

theorem ge5Dir_latin {m : Nat} (t : Fin m) (w : Vec5 m) :
    Function.Bijective fun c : Color => ge5Dir t c w := by
  unfold ge5Dir
  by_cases h1 : t.val = 1
  · simpa [h1] using Lambda1_latin (zeroMaskMinusOne w)
  · by_cases h2 : t.val = 2
    · simpa [h1, h2] using fin5AddNat_three_bijective
    · by_cases h3 : t.val = 3
      · simpa [h1, h2, h3] using fin5AddNat_four_bijective
      · simp [h1, h2, h3]

theorem ge5Schedule_latin (m : Nat) : IsScheduleLatin (ge5Schedule m) := by
  intro t w
  exact ge5Dir_latin t w

theorem m3Dir_latin (t : Fin 3) (w : Vec5 3) :
    Function.Bijective fun c : Color => m3Dir t c w := by
  unfold m3Dir
  by_cases h1 : t.val = 1
  · simpa [h1] using Lambda1_latin (zeroMaskMinusOne w)
  · by_cases h0 : t.val = 0
    · simpa [h1, h0] using fin5AddNat_four_bijective
    · simpa [h1, h0] using fin5AddNat_three_bijective

theorem m3Schedule_latin : IsScheduleLatin m3Schedule := by
  intro t w
  exact m3Dir_latin t w

end D5Odd
