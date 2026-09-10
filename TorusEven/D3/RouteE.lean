-- STATUS: main-path (D_3(m) for even m ≥ 6 via the vendored Route E odometer library)
import TorusD3Odometer
import Shared.D3Seed
import TorusEven.Goals

/-!
# `D_3(m)` for even `m ≥ 6`

The vendored `TorusD3Odometer` library proves, colour by colour, that the Route E
direction assignment of arXiv:2603.24708 yields an `m^3`-cycle:
`cycleOn_fullMap0CaseI_caseI`, `cycleOn_fullMap0CaseII_caseII_mod_{four,ten}`,
`cycleOn_fullMap1CaseI_caseI`, `cycleOn_fullMap1CaseII_caseII`, `cycleOn_fullMap2XY`.
Colours 0 and 1 are stated in `(i,k)` root coordinates, colour 2 in `(x,y) = (i, i+k)`.
This file puts the three colours on one coordinate system, proves that the three
directions are distinct at every vertex (the Latin condition, Lemma 7 of the paper),
and assembles `Shared.CayleyHamiltonDecomposition 3 m`.
-/

namespace TorusEven
namespace D3RouteE

open TorusD3Odometer
open TorusD4 (CycleOn slicePoint cycleOn_conj)

variable {m : ℕ}

/-! ### Colour 2 in `(i,k)` coordinates -/

/-- `((i,k),s) ↦ ((i, i+k), s)`. -/
def toXYFull (m : ℕ) : FullCoord m ≃ FullCoord m where
  toFun z := ((z.1.1, z.1.1 + z.1.2), z.2)
  invFun z := ((z.1.1, z.1.2 - z.1.1), z.2)
  left_inv z := by
    rcases z with ⟨⟨i, k⟩, s⟩
    simp
  right_inv z := by
    rcases z with ⟨⟨x, y⟩, s⟩
    simp

theorem toXYFull_KMap (c : TorusD3Odometer.Color) (z : FullCoord m) :
    toXYFull m (KMap c z) = KMapXY c (toXYFull m z) := by
  rcases z with ⟨⟨i, k⟩, s⟩
  fin_cases c <;> simp [toXYFull, KMap, KMapXY, add_assoc, add_comm, add_left_comm]

def dir2IK (z : FullCoord m) : TorusD3Odometer.Color := dir2XY (toXYFull m z)

def fullMap2 (z : FullCoord m) : FullCoord m := KMap (dir2IK z) z

theorem toXYFull_semiconj_fullMap2 :
    Function.Semiconj (toXYFull m) (fullMap2 (m := m)) (fullMap2XY (m := m)) := by
  intro z
  simp only [fullMap2, fullMap2XY, dir2IK]
  exact toXYFull_KMap _ _

theorem cycleOn_fullMap2 [Fact (Even m)] [Fact (5 < m)] :
    CycleOn (m ^ 3) (fullMap2 (m := m))
      ((toXYFull m).symm (slicePoint (0 : ZMod m) (linePoint2 (m := m) (0 : ZMod m)))) :=
  cycleOn_conj (toXYFull m).symm
    ((toXYFull_semiconj_fullMap2 (m := m)).inverse_left (toXYFull m).left_inv
      (toXYFull m).right_inv)
    (cycleOn_fullMap2XY (m := m))

/-! ### Colours 0 and 1: the two residue cases -/

def dir0 (m : ℕ) (z : FullCoord m) : TorusD3Odometer.Color :=
  if m % 6 = 4 then dir0CaseII (m := m) z else dir0CaseI (m := m) z

def dir1 (m : ℕ) (z : FullCoord m) : TorusD3Odometer.Color :=
  if m % 6 = 4 then dir1CaseII (m := m) z else dir1CaseI (m := m) z

def fullMap0 (m : ℕ) (z : FullCoord m) : FullCoord m := KMap (dir0 m z) z

def fullMap1 (m : ℕ) (z : FullCoord m) : FullCoord m := KMap (dir1 m z) z

theorem fullMap0_eq_caseI (h : m % 6 ≠ 4) : fullMap0 m = fullMap0CaseI (m := m) := by
  funext z
  simp [fullMap0, dir0, h, fullMap0CaseI]

theorem fullMap0_eq_caseII (h : m % 6 = 4) : fullMap0 m = fullMap0CaseII (m := m) := by
  funext z
  simp [fullMap0, dir0, h, fullMap0CaseII, fullMapColor0, dir0CaseII]

theorem fullMap1_eq_caseI (h : m % 6 ≠ 4) : fullMap1 m = fullMap1CaseI (m := m) := by
  funext z
  simp [fullMap1, dir1, h, fullMap1CaseI]

theorem fullMap1_eq_caseII (h : m % 6 = 4) : fullMap1 m = fullMap1CaseII (m := m) := by
  funext z
  simp [fullMap1, dir1, h, fullMap1CaseII, fullMapColor1, dir1CaseII]

theorem mod_six_cases (hm : Even m) : m % 6 = 0 ∨ m % 6 = 2 ∨ m % 6 = 4 :=
  TorusD3Odometer.mod_six_eq_zero_or_two_or_four_of_even hm

theorem mod_twelve_of_mod_six_four (h : m % 6 = 4) : m % 12 = 4 ∨ m % 12 = 10 := by
  omega

theorem hasCycle_fullMap0 (hm : Even m) (h6 : 6 ≤ m) :
    ∃ z, CycleOn (m ^ 3) (fullMap0 m) z := by
  haveI : Fact (5 < m) := ⟨by omega⟩
  by_cases h4 : m % 6 = 4
  · haveI : Fact (9 < m) := ⟨by
      rcases hm with ⟨r, hr⟩
      omega⟩
    rw [fullMap0_eq_caseII h4]
    rcases mod_twelve_of_mod_six_four h4 with h12 | h12
    · exact ⟨_, cycleOn_fullMap0CaseII_caseII_mod_four (m := m) h12⟩
    · exact ⟨_, cycleOn_fullMap0CaseII_caseII_mod_ten (m := m) h12⟩
  · rw [fullMap0_eq_caseI h4]
    have hcase : m % 6 = 0 ∨ m % 6 = 2 := by
      rcases mod_six_cases hm with h | h | h <;> omega
    exact ⟨_, cycleOn_fullMap0CaseI_caseI (m := m) hcase⟩

theorem hasCycle_fullMap1 (hm : Even m) (h6 : 6 ≤ m) :
    ∃ z, CycleOn (m ^ 3) (fullMap1 m) z := by
  haveI : Fact (5 < m) := ⟨by omega⟩
  by_cases h4 : m % 6 = 4
  · haveI : Fact (9 < m) := ⟨by
      rcases hm with ⟨r, hr⟩
      omega⟩
    rw [fullMap1_eq_caseII h4]
    exact ⟨_, cycleOn_fullMap1CaseII_caseII (m := m) h4⟩
  · rw [fullMap1_eq_caseI h4]
    exact ⟨_, cycleOn_fullMap1CaseI_caseI (m := m) hm h4⟩

theorem hasCycle_fullMap2 (hm : Even m) (h6 : 6 ≤ m) :
    ∃ z, CycleOn (m ^ 3) (fullMap2 (m := m)) z := by
  haveI : Fact (5 < m) := ⟨by omega⟩
  haveI : Fact (Even m) := ⟨hm⟩
  exact ⟨_, cycleOn_fullMap2 (m := m)⟩

/-! ### The Latin condition -/

/-- The three colour directions at a root-height point. -/
def dirs (m : ℕ) (z : FullCoord m) : TorusD3Odometer.Color → TorusD3Odometer.Color :=
  ![dir0 m z, dir1 m z, dir2IK z]

theorem bijective_of_distinct :
    ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → Function.Bijective ![a, b, c] := by
  decide

/-- Nonzero small constants in `ZMod m` for `6 ≤ m`. -/
theorem natCast_ne_zero_of_lt (h6 : 6 ≤ m) {n : ℕ} (hn0 : 0 < n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hn0 hnm ((ZMod.natCast_eq_zero_iff n m).1 h)

/-- Pairwise inequalities among the constants `0, 1, 2, 3, -1, -2, -3, -4` in `ZMod m`,
`6 ≤ m` (differences at most `5`), in both orientations, packaged for `simp`. -/
theorem small_constants (h6 : 6 ≤ m) :
    ((0 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (3 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (-3 : ZMod m)) ∧
    ((0 : ZMod m) ≠ (-4 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (3 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (-3 : ZMod m)) ∧
    ((1 : ZMod m) ≠ (-4 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (3 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((2 : ZMod m) ≠ (-3 : ZMod m)) ∧
    ((3 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((3 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((3 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((3 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((3 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (3 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (-3 : ZMod m)) ∧
    ((-1 : ZMod m) ≠ (-4 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (3 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (-3 : ZMod m)) ∧
    ((-2 : ZMod m) ≠ (-4 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (2 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((-3 : ZMod m) ≠ (-4 : ZMod m)) ∧
    ((-4 : ZMod m) ≠ (0 : ZMod m)) ∧
    ((-4 : ZMod m) ≠ (1 : ZMod m)) ∧
    ((-4 : ZMod m) ≠ (-1 : ZMod m)) ∧
    ((-4 : ZMod m) ≠ (-2 : ZMod m)) ∧
    ((-4 : ZMod m) ≠ (-3 : ZMod m)) := by
  have h1 : ((1 : ℕ) : ZMod m) ≠ 0 := natCast_ne_zero_of_lt h6 (by omega) (by omega)
  have h2 : ((2 : ℕ) : ZMod m) ≠ 0 := natCast_ne_zero_of_lt h6 (by omega) (by omega)
  have h3 : ((3 : ℕ) : ZMod m) ≠ 0 := natCast_ne_zero_of_lt h6 (by omega) (by omega)
  have h4 : ((4 : ℕ) : ZMod m) ≠ 0 := natCast_ne_zero_of_lt h6 (by omega) (by omega)
  have h5 : ((5 : ℕ) : ZMod m) ≠ 0 := natCast_ne_zero_of_lt h6 (by omega) (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h3 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h3 (by linear_combination h)
  · exact fun h => h4 (by linear_combination h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h3 (by linear_combination h)
  · exact fun h => h4 (by linear_combination h)
  · exact fun h => h5 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h3 (by linear_combination h)
  · exact fun h => h4 (by linear_combination h)
  · exact fun h => h5 (by linear_combination h)
  · exact fun h => h3 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h4 (by linear_combination h)
  · exact fun h => h5 (by linear_combination h)
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h3 (by linear_combination -h)
  · exact fun h => h4 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h3 (by linear_combination h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h3 (by linear_combination -h)
  · exact fun h => h4 (by linear_combination -h)
  · exact fun h => h5 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h2 (by linear_combination h)
  · exact fun h => h3 (by linear_combination -h)
  · exact fun h => h4 (by linear_combination -h)
  · exact fun h => h5 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination h)
  · exact fun h => h4 (by linear_combination -h)
  · exact fun h => h5 (by linear_combination -h)
  · exact fun h => h3 (by linear_combination -h)
  · exact fun h => h2 (by linear_combination -h)
  · exact fun h => h1 (by linear_combination -h)

theorem const_add_eq_iff (c d i : ZMod m) : c + i = d ↔ i = d - c := by
  constructor <;> intro h <;> linear_combination h

theorem add_const_eq_iff (c d i : ZMod m) : i + c = d ↔ i = d - c := by
  constructor <;> intro h <;> linear_combination h

theorem neg_eq_const_iff (c i : ZMod m) : -i = c ↔ i = -c := by
  constructor <;> intro h <;> linear_combination -h

theorem const_sub_eq_const_iff (a b i : ZMod m) : a - i = b ↔ i = a - b := by
  constructor <;> intro h <;> linear_combination -h

theorem cases_i (i : ZMod m) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = -1 ∨ i = -2 ∨
      (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ -1 ∧ i ≠ -2 ∧
        (0 : ZMod m) ≠ i ∧ (1 : ZMod m) ≠ i ∧ (2 : ZMod m) ≠ i ∧
        (-1 : ZMod m) ≠ i ∧ (-2 : ZMod m) ≠ i) := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : i = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases hn1 : i = -1
  · exact Or.inr (Or.inr (Or.inr (Or.inl hn1)))
  by_cases hn2 : i = -2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn2))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1, h2, hn1, hn2,
    fun h => h0 h.symm, fun h => h1 h.symm, fun h => h2 h.symm,
    fun h => hn1 h.symm, fun h => hn2 h.symm⟩))))

theorem cases_k (k : ZMod m) :
    k = 0 ∨ k = 1 ∨ k = -1 ∨ k = -2 ∨
      (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧ k ≠ -2 ∧
        (0 : ZMod m) ≠ k ∧ (1 : ZMod m) ≠ k ∧ (-1 : ZMod m) ≠ k ∧
        (-2 : ZMod m) ≠ k) := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  by_cases h1 : k = 1
  · exact Or.inr (Or.inl h1)
  by_cases hn1 : k = -1
  · exact Or.inr (Or.inr (Or.inl hn1))
  by_cases hn2 : k = -2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hn2)))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1, hn1, hn2,
    fun h => h0 h.symm, fun h => h1 h.symm, fun h => hn1 h.symm, fun h => hn2 h.symm⟩)))

set_option maxHeartbeats 4000000 in
/-- Layer `0`, Case I (`m % 6 ∈ {0, 2}`): the three directions are distinct. -/
theorem distinct_layer_zero_caseI (h6 : 6 ≤ m) (i k : ZMod m) :
    dir0CaseILayerZero (m := m) (i, k) ≠ dir1CaseILayerZero (m := m) (i, k) ∧
    dir0CaseILayerZero (m := m) (i, k) ≠ dir2LayerZeroXY (m := m) (i, i + k) ∧
    dir1CaseILayerZero (m := m) (i, k) ≠ dir2LayerZeroXY (m := m) (i, i + k) := by
  have hc := small_constants h6
  simp only [dir0CaseILayerZero, dir1CaseILayerZero, dir2LayerZeroXY]
  by_cases hs : i + k = -1
  · obtain rfl : k = -1 - i := by linear_combination hs
    rcases cases_i i with rfl | rfl | rfl | rfl | rfl |
      ⟨hi0, hi1, hi2, hin1, hin2, hi0', hi1', hi2', hin1', hin2'⟩ <;>
    simp_all [const_sub_eq_const_iff] <;> (try ring_nf at *) <;> (try simp_all)
  · rcases cases_i i with rfl | rfl | rfl | rfl | rfl |
      ⟨hi0, hi1, hi2, hin1, hin2, hi0', hi1', hi2', hin1', hin2'⟩ <;>
    rcases cases_k k with rfl | rfl | rfl | rfl |
      ⟨hk0, hk1, hkn1, hkn2, hk0', hk1', hkn1', hkn2'⟩ <;>
    simp_all [const_add_eq_iff] <;> (try ring_nf at *) <;> (try simp_all)

set_option maxHeartbeats 4000000 in
/-- Layer `0`, Case II (`m % 6 = 4`): the three directions are distinct. -/
theorem distinct_layer_zero_caseII (h6 : 6 ≤ m) (i k : ZMod m) :
    dir0CaseIILayerZero (m := m) (i, k) ≠ dir1CaseIILayerZero (m := m) (i, k) ∧
    dir0CaseIILayerZero (m := m) (i, k) ≠ dir2LayerZeroXY (m := m) (i, i + k) ∧
    dir1CaseIILayerZero (m := m) (i, k) ≠ dir2LayerZeroXY (m := m) (i, i + k) := by
  have hc := small_constants h6
  simp only [dir0CaseIILayerZero, dir1CaseIILayerZero, dir2LayerZeroXY]
  by_cases hs : i + k = -1
  · obtain rfl : k = -1 - i := by linear_combination hs
    rcases cases_i i with rfl | rfl | rfl | rfl | rfl |
      ⟨hi0, hi1, hi2, hin1, hin2, hi0', hi1', hi2', hin1', hin2'⟩ <;>
    simp_all [const_sub_eq_const_iff] <;> (try ring_nf at *) <;> (try simp_all)
  · rcases cases_i i with rfl | rfl | rfl | rfl | rfl |
      ⟨hi0, hi1, hi2, hin1, hin2, hi0', hi1', hi2', hin1', hin2'⟩ <;>
    rcases cases_k k with rfl | rfl | rfl | rfl |
      ⟨hk0, hk1, hkn1, hkn2, hk0', hk1', hkn1', hkn2'⟩ <;>
    simp_all [const_add_eq_iff] <;> (try ring_nf at *) <;> (try simp_all)

/-- Layers `s ≠ 0`: the three directions are distinct (same rule in both cases). -/
theorem distinct_upper_layers (h6 : 6 ≤ m) (i k s : ZMod m) (hs : s ≠ 0) :
    dir0 m ((i, k), s) ≠ dir1 m ((i, k), s) ∧
    dir0 m ((i, k), s) ≠ dir2IK ((i, k), s) ∧
    dir1 m ((i, k), s) ≠ dir2IK ((i, k), s) := by
  have hc := small_constants h6
  simp only [dir0, dir1, dir2IK, dir0CaseI, dir0CaseII, dir0FromLayerZero, dir1CaseI,
    dir1CaseII, dir1FromLayerZero, dir2XY, toXYFull, Equiv.coe_fn_mk]
  by_cases hs1 : s = 1
  · subst hs1
    by_cases hi : i = 0 <;> by_cases h4 : m % 6 = 4 <;> simp [hi, h4, hc]
  by_cases hs2 : s = 2
  · subst hs2
    by_cases hik : i + k = 2 <;> by_cases h4 : m % 6 = 4 <;> simp [hik, h4, hc]
  by_cases h4 : m % 6 = 4 <;> simp [hs, hs1, hs2, h4]

theorem distinct_dirs (h6 : 6 ≤ m) (z : FullCoord m) :
    dir0 m z ≠ dir1 m z ∧ dir0 m z ≠ dir2IK z ∧ dir1 m z ≠ dir2IK z := by
  rcases z with ⟨⟨i, k⟩, s⟩
  by_cases hs : s = 0
  · subst hs
    by_cases h4 : m % 6 = 4
    · have h := distinct_layer_zero_caseII h6 i k
      simpa [dir0, dir1, dir2IK, dir0CaseII, dir0FromLayerZero, dir1CaseII, dir1FromLayerZero,
        dir2XY, toXYFull, h4] using h
    · have h := distinct_layer_zero_caseI h6 i k
      simpa [dir0, dir1, dir2IK, dir0CaseI, dir1CaseI, dir2XY, toXYFull, h4] using h
  · exact distinct_upper_layers h6 i k s hs

theorem dirs_bijective (h6 : 6 ≤ m) (z : FullCoord m) : Function.Bijective (dirs m z) := by
  obtain ⟨h01, h02, h12⟩ := distinct_dirs h6 z
  exact bijective_of_distinct _ _ _ h01 h02 h12

/-! ### Assembly in the shared Cayley interface -/

/-- Colour-`c` direction at a physical vertex. -/
def colorDir (m : ℕ) (c : Fin 3) (x : Shared.TorusVertex 3 m) : Fin 3 :=
  dirs m (splitPointEquiv (m := m) x) c

/-- The colour maps in root-height coordinates, indexed by colour. -/
def fullMapC (m : ℕ) (c : Fin 3) (z : FullCoord m) : FullCoord m :=
  KMap (dirs m z c) z

theorem fullMapC_zero : fullMapC m 0 = fullMap0 m := by
  funext z
  rfl

theorem fullMapC_one : fullMapC m 1 = fullMap1 m := by
  funext z
  rfl

theorem fullMapC_two : fullMapC m 2 = fullMap2 (m := m) := by
  funext z
  rfl

theorem torusBasis_eq_bump (x : Shared.TorusVertex 3 m) (d : Fin 3) :
    x + Shared.torusBasis 3 m d = bump x d := by
  funext j
  simp [Shared.torusBasis, bump]

theorem semiconj_colorStep (c : Fin 3) :
    Function.Semiconj (splitPointEquiv (m := m))
      (Shared.cayleyColorStep (colorDir m) c) (fullMapC m c) := by
  intro x
  simp only [Shared.cayleyColorStep, colorDir, fullMapC, torusBasis_eq_bump]
  exact splitPointEquiv_bump (m := m) _ x

theorem hasCycle_fullMapC (hm : Even m) (h6 : 6 ≤ m) (c : Fin 3) :
    ∃ z, CycleOn (m ^ 3) (fullMapC m c) z := by
  fin_cases c
  · simpa [fullMapC_zero] using hasCycle_fullMap0 hm h6
  · simpa [fullMapC_one] using hasCycle_fullMap1 hm h6
  · simpa [fullMapC_two] using hasCycle_fullMap2 hm h6

theorem colorHamiltonian (hm : Even m) (h6 : 6 ≤ m) :
    Shared.IsCayleyColorHamiltonian (colorDir m) := by
  intro c
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (m ^ 3) := ⟨by positivity⟩
  obtain ⟨z, hz⟩ := hasCycle_fullMapC hm h6 c
  have hconj : CycleOn (m ^ 3) (Shared.cayleyColorStep (colorDir m) c)
      ((splitPointEquiv (m := m)).symm z) :=
    cycleOn_conj (splitPointEquiv (m := m)).symm
      ((semiconj_colorStep (m := m) c).inverse_left (splitPointEquiv (m := m)).left_inv
        (splitPointEquiv (m := m)).right_inv) hz
  have h1 : 1 < m ^ 3 := by
    have : 6 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left h6 3
    omega
  exact Shared.D3.singleCycleOfCycleOn h1 hconj

theorem edgePartition (h6 : 6 ≤ m) : Shared.IsCayleyEdgePartition (colorDir m) := by
  intro x i
  have hb := dirs_bijective h6 (splitPointEquiv (m := m) x)
  rcases hb.2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact hb.1 (hc'.trans hc.symm)

end D3RouteE

/-- `D_3(m)` for every even `m ≥ 6`, from the Route E odometer library. -/
theorem d3_even_of_six_le {m : ℕ} (hm : Even m) (h6 : 6 ≤ m) : Solved 3 m :=
  ⟨{ colorDir := D3RouteE.colorDir m
     edgePartition := D3RouteE.edgePartition h6
     colorHamiltonian := D3RouteE.colorHamiltonian hm h6 }⟩

end TorusEven
