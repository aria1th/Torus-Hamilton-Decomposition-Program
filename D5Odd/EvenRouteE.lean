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

namespace RouteEB20

/-!
Arithmetic data for the first extracted D5 even Route-E branch.

The branch is `m = 24*q + 20`, slot zero, with count vector
`(r,0,0,h+r,r)` where `h = m/2 = 12*q+10` and `r = (h-1)/3 = 4*q+3`.
The program verifier `scripts/verify_d5_routeE_b20_branch.py` checks the
corresponding first-return and pointwise return-time formulas.  The lemmas
below record the count-sum and return-time weighted-sum arithmetic needed by
the eventual symbolic certificate.
-/

def modulus (q : Nat) : Nat := 24 * q + 20

def half (q : Nat) : Nat := 12 * q + 10

def quarter (q : Nat) : Nat := 6 * q + 5

def third (q : Nat) : Nat := 4 * q + 3

def repeatedTimeCount (q : Nat) : Nat := 12 * q + 6

def counts (q : Nat) : Fin 5 → Nat :=
  ![third q, 0, 0, half q + third q, third q]

theorem counts_sum (q : Nat) :
    Finset.univ.sum (counts q) = modulus q - 1 := by
  simp [counts, Fin.sum_univ_five, third, half, modulus]
  omega

def routeCounts (q : Nat) : RouteECounts (modulus q) where
  slot := 0
  counts := counts q
  count_sum := counts_sum q

def timeA (q : Nat) : Nat :=
  13824 * q ^ 3 + 34272 * q ^ 2 + 28320 * q + 7806

def timeC (q : Nat) : Nat :=
  timeA q + modulus q * (modulus q + 1)

def timeE (q : Nat) : Nat :=
  20736 * q ^ 3 + 50976 * q ^ 2 + 41772 * q + 11416

def timeF (q : Nat) : Nat :=
  20736 * q ^ 3 + 51552 * q ^ 2 + 42780 * q + 11862

def returnTimeWeightedSum (q : Nat) : Nat :=
  2 * timeA q +
  repeatedTimeCount q * (timeA q + modulus q) +
  3 * timeC q +
  repeatedTimeCount q * (timeC q + modulus q) +
  timeE q +
  timeF q

theorem repeatedTimeCount_eq_half_sub_four (q : Nat) :
    repeatedTimeCount q = half q - 4 := by
  simp [repeatedTimeCount, half]

theorem three_third_eq_half_sub_one (q : Nat) :
    3 * third q = half q - 1 := by
  simp [third, half]
  ring

theorem returnTimeWeightedSum_eq_modulus_pow_four (q : Nat) :
    returnTimeWeightedSum q = modulus q ^ 4 := by
  simp [returnTimeWeightedSum, timeA, timeC, timeE, timeF,
    repeatedTimeCount, modulus]
  ring

theorem modulus_eq_four_quarter (q : Nat) :
    modulus q = 4 * quarter q := by
  simp [modulus, quarter]
  ring

theorem half_eq_two_quarter (q : Nat) :
    half q = 2 * quarter q := by
  simp [half, quarter]
  ring

/-!
All-pair label time-mass formulas extracted in the Route-E v3.6 bundle.
The `03` and `04` entries are explicitly named as boundary-clock targets:
the bundle isolates and sample-checks their polynomials, while the direct
boundary-clock derivation remains a symbolic proof obligation.
-/

def allPairTimeZ (q : Nat) : Nat :=
  12 * q + 13

def allPairTime01 (q : Nat) : Nat :=
  108 * q ^ 2 + 180 * q + 75

def allPairTime02 (q : Nat) : Nat :=
  6912 * q ^ 3 + 16992 * q ^ 2 + 13920 * q + 3800

def allPairTime03Target (q : Nat) : Nat :=
  5184 * q ^ 3 + 12528 * q ^ 2 + 10080 * q + 2703

def allPairTime04Target (q : Nat) : Nat :=
  5184 * q ^ 3 + 11898 * q ^ 2 + 9099 * q + 2335

def allPairTime12 (q : Nat) : Nat :=
  576 * q ^ 2 + 912 * q + 363

def allPairTime13 (q : Nat) : Nat :=
  234 * q ^ 2 + 393 * q + 162

def allPairTime14 (q : Nat) : Nat :=
  82944 * q ^ 4 + 273024 * q ^ 3 + 337104 * q ^ 2 +
    185058 * q + 38115

def allPairTime23 (q : Nat) : Nat :=
  124416 * q ^ 4 + 409536 * q ^ 3 + 505008 * q ^ 2 +
    276492 * q + 56707

def allPairTime24 (q : Nat) : Nat :=
  124416 * q ^ 4 + 406080 * q ^ 3 + 496800 * q ^ 2 +
    269994 * q + 54995

def allPairTime34 (q : Nat) : Nat :=
  1152 * q ^ 2 + 1860 * q + 732

inductive AllPairLabel where
  | Z
  | L01
  | L02
  | L03
  | L04
  | L12
  | L13
  | L14
  | L23
  | L24
  | L34
deriving DecidableEq, Fintype

def allPairTimeMass (q : Nat) : AllPairLabel → Nat
  | AllPairLabel.Z => allPairTimeZ q
  | AllPairLabel.L01 => allPairTime01 q
  | AllPairLabel.L02 => allPairTime02 q
  | AllPairLabel.L03 => allPairTime03Target q
  | AllPairLabel.L04 => allPairTime04Target q
  | AllPairLabel.L12 => allPairTime12 q
  | AllPairLabel.L13 => allPairTime13 q
  | AllPairLabel.L14 => allPairTime14 q
  | AllPairLabel.L23 => allPairTime23 q
  | AllPairLabel.L24 => allPairTime24 q
  | AllPairLabel.L34 => allPairTime34 q

def allPairTimeMassTotal (q : Nat) : Nat :=
  allPairTimeZ q +
  allPairTime01 q +
  allPairTime02 q +
  allPairTime03Target q +
  allPairTime04Target q +
  allPairTime12 q +
  allPairTime13 q +
  allPairTime14 q +
  allPairTime23 q +
  allPairTime24 q +
  allPairTime34 q

theorem allPairTime01_eq_three_quarter_sq (q : Nat) :
    allPairTime01 q = 3 * quarter q ^ 2 := by
  simp [allPairTime01, quarter]
  ring

theorem allPairTimeZ_eq_half_add_three (q : Nat) :
    allPairTimeZ q = half q + 3 := by
  simp [allPairTimeZ, half]

theorem allPairTime02_lane_sum_eq (q : Nat) :
    2 * allPairTime02 q = modulus q ^ 2 * (modulus q - 1) := by
  have hpred : modulus q - 1 = 24 * q + 19 := by
    simp [modulus]
  rw [hpred]
  simp [allPairTime02, modulus]
  ring

theorem allPairTime12_lane_sum_eq (q : Nat) :
    allPairTime12 q = (modulus q - 2) * modulus q + 3 := by
  have hsub : modulus q - 2 = 24 * q + 18 := by
    simp [modulus]
  rw [hsub]
  simp [allPairTime12, modulus]
  ring

theorem allPairTime13_two_clock_eq (q : Nat) :
    2 * (allPairTime13 q + 3) = 13 * quarter q ^ 2 + quarter q := by
  simp [allPairTime13, quarter]
  ring

theorem allPairTime34_boundary_defect_eq (q : Nat) :
    allPairTime34 q =
      (modulus q - 8) * (2 * modulus q + 6) +
      4 * (modulus q + 6) +
      (modulus q + half q + 3) +
      (modulus q + 3) +
      modulus q := by
  have hsub : modulus q - 8 = 24 * q + 12 := by
    simp [modulus]
  rw [hsub]
  simp [allPairTime34, modulus, half]
  ring

-- The v3.6 draft displays the `q` coefficient as `19079`; adding the two
-- target polynomials gives `19179`, which is also forced by total time mass.
theorem allPairTime03Target_add_allPairTime04Target (q : Nat) :
    allPairTime03Target q + allPairTime04Target q =
      10368 * q ^ 3 + 24426 * q ^ 2 + 19179 * q + 5038 := by
  simp [allPairTime03Target, allPairTime04Target]
  ring

theorem allPairTimeMassTotal_eq_modulus_pow_four (q : Nat) :
    allPairTimeMassTotal q = modulus q ^ 4 := by
  simp [allPairTimeMassTotal, allPairTimeZ, allPairTime01,
    allPairTime02, allPairTime03Target, allPairTime04Target,
    allPairTime12, allPairTime13, allPairTime14, allPairTime23,
    allPairTime24, allPairTime34, modulus]
  ring

theorem allPairTimeMass_sum_eq_modulus_pow_four (q : Nat) :
    Finset.univ.sum (allPairTimeMass q) = modulus q ^ 4 := by
  have huniv :
      (Finset.univ : Finset AllPairLabel) =
        ({ AllPairLabel.Z, AllPairLabel.L01, AllPairLabel.L02,
          AllPairLabel.L03, AllPairLabel.L04, AllPairLabel.L12,
          AllPairLabel.L13, AllPairLabel.L14, AllPairLabel.L23,
          AllPairLabel.L24, AllPairLabel.L34 } : Finset AllPairLabel) := by
    ext x
    fin_cases x <;> simp
  rw [huniv]
  simp [allPairTimeMass, allPairTimeZ, allPairTime01, allPairTime02,
    allPairTime03Target, allPairTime04Target, allPairTime12,
    allPairTime13, allPairTime14, allPairTime23, allPairTime24,
    allPairTime34, modulus]
  ring

end RouteEB20

namespace RouteEB16

/-!
Route-E B16 branch surface from the v3.6 bundle.

This records count admissibility and the interpolated all-pair label
time-mass target.  The bundle leaves the non-boundary lane catalogue,
boundary quotient derivation, one-cycle proof, and lane/core derivation of the
time polynomials as symbolic obligations.
-/

def modulus (q : Nat) : Nat := 24 * q + 16

def half (q : Nat) : Nat := 12 * q + 8

def z (q : Nat) : Nat := 12 * q + 5

def counts (q : Nat) : Fin 5 → Nat :=
  ![1, 12 * q + 9, 0, z q, 0]

theorem counts_sum (q : Nat) :
    Finset.univ.sum (counts q) = modulus q - 1 := by
  simp [counts, Fin.sum_univ_five, z, modulus]
  omega

def routeCounts (q : Nat) : RouteECounts (modulus q) where
  slot := 0
  counts := counts q
  count_sum := counts_sum q

def allPairTimeZTarget (q : Nat) : Nat :=
  24 * q + 15

def allPairTime01Target (q : Nat) : Nat :=
  162 * q ^ 2 + 216 * q + 72

def allPairTime02Target (q : Nat) : Nat :=
  6912 * q ^ 3 + 13536 * q ^ 2 + 8832 * q + 1920

def allPairTime03Target (q : Nat) : Nat :=
  3888 * q ^ 3 + 7770 * q ^ 2 + 5171 * q + 1146

def allPairTime04Target (q : Nat) : Nat :=
  3888 * q ^ 3 + 7461 * q ^ 2 + 4767 * q + 1014

def allPairTime12Target (q : Nat) : Nat :=
  576 * q ^ 2 + 732 * q + 231

def allPairTime13Target (q : Nat) : Nat :=
  207 * q ^ 2 + 270 * q + 89

def allPairTime14Target (q : Nat) : Nat :=
  112896 * q ^ 4 + 295776 * q ^ 3 + 290818 * q ^ 2 +
    127190 * q + 20878

def allPairTime23Target (q : Nat) : Nat :=
  111744 * q ^ 4 + 287904 * q ^ 3 + 277220 * q ^ 2 +
    118211 * q + 18831

def allPairTime24Target (q : Nat) : Nat :=
  107136 * q ^ 4 + 283776 * q ^ 3 + 281850 * q ^ 2 +
    124403 * q + 20588

def allPairTime34Target (q : Nat) : Nat :=
  2592 * q ^ 3 + 5136 * q ^ 2 + 3400 * q + 752

def allPairTimeMassTotalTarget (q : Nat) : Nat :=
  allPairTimeZTarget q +
  allPairTime01Target q +
  allPairTime02Target q +
  allPairTime03Target q +
  allPairTime04Target q +
  allPairTime12Target q +
  allPairTime13Target q +
  allPairTime14Target q +
  allPairTime23Target q +
  allPairTime24Target q +
  allPairTime34Target q

def allPairTimeMassTarget (q : Nat) : RouteEB20.AllPairLabel → Nat
  | .Z => allPairTimeZTarget q
  | .L01 => allPairTime01Target q
  | .L02 => allPairTime02Target q
  | .L03 => allPairTime03Target q
  | .L04 => allPairTime04Target q
  | .L12 => allPairTime12Target q
  | .L13 => allPairTime13Target q
  | .L14 => allPairTime14Target q
  | .L23 => allPairTime23Target q
  | .L24 => allPairTime24Target q
  | .L34 => allPairTime34Target q

theorem allPairTimeMassTarget_sum_eq_total (q : Nat) :
    Finset.univ.sum (allPairTimeMassTarget q) =
      allPairTimeMassTotalTarget q := by
  have huniv :
      (Finset.univ : Finset RouteEB20.AllPairLabel) =
        ({ RouteEB20.AllPairLabel.Z, RouteEB20.AllPairLabel.L01,
          RouteEB20.AllPairLabel.L02, RouteEB20.AllPairLabel.L03,
          RouteEB20.AllPairLabel.L04, RouteEB20.AllPairLabel.L12,
          RouteEB20.AllPairLabel.L13, RouteEB20.AllPairLabel.L14,
          RouteEB20.AllPairLabel.L23, RouteEB20.AllPairLabel.L24,
          RouteEB20.AllPairLabel.L34 } : Finset RouteEB20.AllPairLabel) := by
    ext x
    fin_cases x <;> simp
  rw [huniv]
  simp [allPairTimeMassTarget, allPairTimeMassTotalTarget]
  ac_rfl

theorem allPairTimeMassTotalTarget_eq_modulus_pow_four (q : Nat) :
    allPairTimeMassTotalTarget q = modulus q ^ 4 := by
  simp [allPairTimeMassTotalTarget, allPairTimeZTarget,
    allPairTime01Target, allPairTime02Target, allPairTime03Target,
    allPairTime04Target, allPairTime12Target, allPairTime13Target,
    allPairTime14Target, allPairTime23Target, allPairTime24Target,
    allPairTime34Target, modulus]
  ring

theorem allPairTimeMassTarget_sum_eq_modulus_pow_four (q : Nat) :
    Finset.univ.sum (allPairTimeMassTarget q) = modulus q ^ 4 := by
  rw [allPairTimeMassTarget_sum_eq_total,
    allPairTimeMassTotalTarget_eq_modulus_pow_four]

end RouteEB16

namespace RouteER14e

/-!
Route-E R14e branch surface from the v3.6 bundle.

This branch has `m = 48*k + 14` and a boundary quotient type distinct from
B20/B16.  The time-mass polynomials below are evidence targets; the symbolic
boundary quotient formula and one-cycle derivation remain open.
-/

def modulus (k : Nat) : Nat := 48 * k + 14

def half (k : Nat) : Nat := 24 * k + 7

def z (k : Nat) : Nat := 24 * k + 5

def counts (k : Nat) : Fin 5 → Nat :=
  ![1, 24 * k + 7, 0, z k, 0]

theorem counts_sum (k : Nat) :
    Finset.univ.sum (counts k) = modulus k - 1 := by
  simp [counts, Fin.sum_univ_five, z, modulus]
  omega

def routeCounts (k : Nat) : RouteECounts (modulus k) where
  slot := 0
  counts := counts k
  count_sum := counts_sum k

def allPairTimeZTarget (_k : Nat) : Nat :=
  2

def allPairTime01Target (k : Nat) : Nat :=
  864 * k ^ 2 + 468 * k + 64

def allPairTime02Target (k : Nat) : Nat :=
  55296 * k ^ 3 + 47232 * k ^ 2 + 13440 * k + 1274

def allPairTime03Target (k : Nat) : Nat :=
  10944 * k ^ 3 + 10016 * k ^ 2 + 3036 * k + 305

def allPairTime04Target (k : Nat) : Nat :=
  59904 * k ^ 3 + 50432 * k ^ 2 + 14152 * k + 1323

def allPairTime12Target (k : Nat) : Nat :=
  2304 * k ^ 2 + 1296 * k + 182

def allPairTime13Target (k : Nat) : Nat :=
  1440 * k ^ 2 + 732 * k + 94

def allPairTime14Target (k : Nat) : Nat :=
  1824768 * k ^ 4 + 2042496 * k ^ 3 + 856008 * k ^ 2 +
    159192 * k + 11084

def allPairTime23Target (k : Nat) : Nat :=
  1824768 * k ^ 4 + 2097792 * k ^ 3 + 902640 * k ^ 2 +
    172412 * k + 12346

def allPairTime24Target (k : Nat) : Nat :=
  1658880 * k ^ 4 + 1914624 * k ^ 3 + 827624 * k ^ 2 +
    158756 * k + 11396

def allPairTime34Target (k : Nat) : Nat :=
  12096 * k ^ 3 + 10944 * k ^ 2 + 3364 * k + 346

def allPairTimeMassTotalTarget (k : Nat) : Nat :=
  allPairTimeZTarget k +
  allPairTime01Target k +
  allPairTime02Target k +
  allPairTime03Target k +
  allPairTime04Target k +
  allPairTime12Target k +
  allPairTime13Target k +
  allPairTime14Target k +
  allPairTime23Target k +
  allPairTime24Target k +
  allPairTime34Target k

def allPairTimeMassTarget (k : Nat) : RouteEB20.AllPairLabel → Nat
  | .Z => allPairTimeZTarget k
  | .L01 => allPairTime01Target k
  | .L02 => allPairTime02Target k
  | .L03 => allPairTime03Target k
  | .L04 => allPairTime04Target k
  | .L12 => allPairTime12Target k
  | .L13 => allPairTime13Target k
  | .L14 => allPairTime14Target k
  | .L23 => allPairTime23Target k
  | .L24 => allPairTime24Target k
  | .L34 => allPairTime34Target k

theorem allPairTimeMassTarget_sum_eq_total (k : Nat) :
    Finset.univ.sum (allPairTimeMassTarget k) =
      allPairTimeMassTotalTarget k := by
  have huniv :
      (Finset.univ : Finset RouteEB20.AllPairLabel) =
        ({ RouteEB20.AllPairLabel.Z, RouteEB20.AllPairLabel.L01,
          RouteEB20.AllPairLabel.L02, RouteEB20.AllPairLabel.L03,
          RouteEB20.AllPairLabel.L04, RouteEB20.AllPairLabel.L12,
          RouteEB20.AllPairLabel.L13, RouteEB20.AllPairLabel.L14,
          RouteEB20.AllPairLabel.L23, RouteEB20.AllPairLabel.L24,
          RouteEB20.AllPairLabel.L34 } : Finset RouteEB20.AllPairLabel) := by
    ext x
    fin_cases x <;> simp
  rw [huniv]
  simp [allPairTimeMassTarget, allPairTimeMassTotalTarget]
  ac_rfl

theorem allPairTimeMassTotalTarget_eq_modulus_pow_four (k : Nat) :
    allPairTimeMassTotalTarget k = modulus k ^ 4 := by
  simp [allPairTimeMassTotalTarget, allPairTimeZTarget,
    allPairTime01Target, allPairTime02Target, allPairTime03Target,
    allPairTime04Target, allPairTime12Target, allPairTime13Target,
    allPairTime14Target, allPairTime23Target, allPairTime24Target,
    allPairTime34Target, modulus]
  ring

theorem allPairTimeMassTarget_sum_eq_modulus_pow_four (k : Nat) :
    Finset.univ.sum (allPairTimeMassTarget k) = modulus k ^ 4 := by
  rw [allPairTimeMassTarget_sum_eq_total,
    allPairTimeMassTotalTarget_eq_modulus_pow_four]

end RouteER14e

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

namespace RouteENonzeroSeam

def toIndex {m : Nat} [NeZero m] (a : RouteENonzeroSeam m) : Fin (m - 1) :=
  ⟨a.1.val - 1, by
    have hpos : 0 < a.1.val := by
      by_contra hnot
      have hzero : a.1.val = 0 := by omega
      exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
    have hlt := ZMod.val_lt a.1
    omega⟩

def ofIndex {m : Nat} [NeZero m] (i : Fin (m - 1)) : RouteENonzeroSeam m :=
  ⟨((i.val + 1 : Nat) : ZMod m), by
    exact zmod_nat_ne_zero (m := m) (k := i.val + 1) (by omega) (by omega)⟩

def ofNat {m : Nat} [NeZero m] (k : Nat) (hpos : 0 < k)
    (hlt : k < m) : RouteENonzeroSeam m :=
  ⟨((k : Nat) : ZMod m), zmod_nat_ne_zero (m := m) (k := k) hpos hlt⟩

theorem ofNat_val {m : Nat} [NeZero m] (k : Nat) (hpos : 0 < k)
    (hlt : k < m) :
    ((ofNat k hpos hlt).1).val = k := by
  exact ZMod.val_natCast_of_lt hlt

set_option linter.flexible false in
theorem ofIndex_toIndex {m : Nat} [NeZero m] (a : RouteENonzeroSeam m) :
    ofIndex (toIndex a) = a := by
  apply Subtype.ext
  simp [ofIndex, toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hsub : a.1.val - 1 + 1 = a.1.val :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  calc
    (((a.1.val - 1 : Nat) : ZMod m) + 1) =
        (((a.1.val - 1 + 1 : Nat) : ZMod m)) := by
      simp [Nat.cast_add]
    _ = ((a.1.val : Nat) : ZMod m) := by rw [hsub]
    _ = a.1 := ZMod.natCast_zmod_val a.1

set_option linter.flexible false in
theorem toIndex_ofIndex {m : Nat} [NeZero m] (i : Fin (m - 1)) :
    toIndex (ofIndex i) = i := by
  apply Fin.ext
  simp [toIndex, ofIndex]
  have hcast : (((i.val : Nat) : ZMod m) + 1) =
      (((i.val + 1 : Nat) : ZMod m)) := by
    simp [Nat.cast_add]
  rw [hcast]
  rw [ZMod.val_natCast_of_lt]
  · omega
  · omega

noncomputable def indexEquiv {m : Nat} [NeZero m] :
    RouteENonzeroSeam m ≃ Fin (m - 1) where
  toFun := toIndex
  invFun := ofIndex
  left_inv := ofIndex_toIndex
  right_inv := toIndex_ofIndex

end RouteENonzeroSeam

inductive RouteEBoundaryLabel where
  | L03
  | L04
  | L34
deriving DecidableEq, Fintype

abbrev RouteEBoundaryNode (m : Nat) :=
  Unit ⊕ (RouteEBoundaryLabel × RouteENonzeroSeam m)

def routeEBoundaryZero {m : Nat} : RouteEBoundaryNode m :=
  Sum.inl ()

def routeEBoundaryNode {m : Nat} (label : RouteEBoundaryLabel)
    (a : RouteENonzeroSeam m) : RouteEBoundaryNode m :=
  Sum.inr (label, a)

def routeEBoundaryNodeOfNat {m : Nat} [NeZero m]
    (label : RouteEBoundaryLabel) (k : Nat) (hpos : 0 < k)
    (hlt : k < m) : RouteEBoundaryNode m :=
  routeEBoundaryNode label (RouteENonzeroSeam.ofNat k hpos hlt)

theorem routeEBoundaryNodeOfNat_val {m : Nat} [NeZero m]
    (_label : RouteEBoundaryLabel) (k : Nat) (hpos : 0 < k)
    (hlt : k < m) :
    (RouteENonzeroSeam.ofNat k hpos hlt).1.val = k :=
  RouteENonzeroSeam.ofNat_val k hpos hlt

theorem card_routeEBoundaryLabel :
    Fintype.card RouteEBoundaryLabel = 3 := by
  change (Finset.univ : Finset RouteEBoundaryLabel).card = 3
  have huniv :
      (Finset.univ : Finset RouteEBoundaryLabel) =
        ({ RouteEBoundaryLabel.L03, RouteEBoundaryLabel.L04,
          RouteEBoundaryLabel.L34 } : Finset RouteEBoundaryLabel) := by
    ext x
    fin_cases x <;> simp
  rw [huniv]
  simp

theorem card_routeEBoundaryNode (m : Nat) [NeZero m] :
    Fintype.card (RouteEBoundaryNode m) = 1 + 3 * (m - 1) := by
  simp [RouteEBoundaryNode, Fintype.card_sum, Fintype.card_prod,
    card_routeEBoundaryLabel]

structure RouteEReturnTimeBlock where
  start : Nat
  stop : Nat
  time : Nat

namespace RouteEReturnTimeBlock

def contains {m : Nat} (block : RouteEReturnTimeBlock)
    (a : RouteENonzeroSeam m) : Prop :=
  block.start ≤ a.1.val ∧ a.1.val ≤ block.stop

def timeFormula {m : Nat} (block : RouteEReturnTimeBlock)
    (f : RouteENonzeroSeam m → Nat) : Prop :=
  ∀ a, block.contains a → f a = block.time

end RouteEReturnTimeBlock

namespace RouteEB20

instance modulus_neZero (q : Nat) : NeZero (modulus q) :=
  ⟨by simp [modulus]⟩

instance modulus_pred_neZero (q : Nat) : NeZero (modulus q - 1) :=
  ⟨by simp [modulus]⟩

structure BoundaryQuotientFormulaTarget (q : Nat)
    (Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)) : Prop where
  zero_to_A :
    ∃ a : RouteENonzeroSeam (modulus q),
      a.1 = (half q : ZMod (modulus q)) ∧
        Q routeEBoundaryZero =
          routeEBoundaryNode RouteEBoundaryLabel.L03 a
  A_h_to_C_last :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((modulus q - 1 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  A_h_succ_to_A_h_sub_two :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q + 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((half q - 2 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  A_even_to_B_same :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ half q → a.1.val % 2 = 0 →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
          routeEBoundaryNode RouteEBoundaryLabel.L04 a
  A_odd_to_B_shift :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ half q + 1 → a.1.val % 2 = 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = a.1 + ((half q - 2 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  B_h_sub_one_to_C_same :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q - 1 →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
          routeEBoundaryNode RouteEBoundaryLabel.L34 a
  B_last_to_C_pred :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = modulus q - 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((modulus q - 2 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_h_add_two_to_zero :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q + 2 →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
          routeEBoundaryZero
  B_odd_to_A_same :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ half q - 1 → a.1.val ≠ modulus q - 1 →
        a.1.val % 2 = 1 →
          Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
            routeEBoundaryNode RouteEBoundaryLabel.L03 a
  B_two_to_A_h_sub_one :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = 2 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((half q - 1 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_even_to_A_shift :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ 2 → a.1.val ≠ half q + 2 →
        a.1.val % 2 = 0 →
          ∃ b : RouteENonzeroSeam (modulus q),
            b.1 = a.1 + ((half q - 2 : Nat) : ZMod (modulus q)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_one_to_A_last :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((modulus q - 1 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_h_to_B_same :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
          routeEBoundaryNode RouteEBoundaryLabel.L04 a
  C_last_to_B_same :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = modulus q - 1 →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
          routeEBoundaryNode RouteEBoundaryLabel.L04 a
  C_generic_to_C_pred :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ 1 → a.1.val ≠ half q → a.1.val ≠ modulus q - 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = a.1 - 1 ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b

def BoundaryQuotientOneCycleTarget (q : Nat) : Prop :=
  ∃ Q : RouteEBoundaryNode (modulus q) → RouteEBoundaryNode (modulus q),
    BoundaryQuotientFormulaTarget q Q ∧ IsSingleCycleMap Q

def boundaryParamOne (q : Nat) : RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat 1 (by omega) (by simp [modulus])

def boundaryParamTwo (q : Nat) : RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat 2 (by omega) (by simp [modulus])

def boundaryParamHalfSubTwo (q : Nat) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (half q - 2) (by simp [half]) (by
    simp [half, modulus]
    omega)

def boundaryParamHalfSubOne (q : Nat) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (half q - 1) (by simp [half]) (by
    simp [half, modulus]
    omega)

def boundaryParamHalf (q : Nat) : RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (half q) (by simp [half]) (by
    simp [half, modulus]
    omega)

def boundaryParamHalfAddOne (q : Nat) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (half q + 1) (by simp [half]) (by
    simp [half, modulus]
    omega)

def boundaryParamHalfAddTwo (q : Nat) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (half q + 2) (by simp [half]) (by
    simp [half, modulus]
    omega)

def boundaryParamPenultimate (q : Nat) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (modulus q - 2) (by simp [modulus]) (by
    simp [modulus])

def boundaryParamLast (q : Nat) : RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (modulus q - 1) (by simp [modulus]) (by
    simp [modulus])

theorem boundaryParamHalf_val (q : Nat) :
    (boundaryParamHalf q).1 = (half q : ZMod (modulus q)) := rfl

theorem boundaryParamHalfSubTwo_val (q : Nat) :
    (boundaryParamHalfSubTwo q).1 =
      ((half q - 2 : Nat) : ZMod (modulus q)) := rfl

theorem boundaryParamHalfSubOne_val (q : Nat) :
    (boundaryParamHalfSubOne q).1 =
      ((half q - 1 : Nat) : ZMod (modulus q)) := rfl

theorem boundaryParamOne_val (q : Nat) :
    (boundaryParamOne q).1 = (1 : ZMod (modulus q)) := rfl

theorem boundaryParamTwo_val (q : Nat) :
    (boundaryParamTwo q).1 = (2 : ZMod (modulus q)) := rfl

theorem boundaryParamHalfAddOne_val (q : Nat) :
    (boundaryParamHalfAddOne q).1 =
      ((half q + 1 : Nat) : ZMod (modulus q)) := rfl

theorem boundaryParamHalfAddTwo_val (q : Nat) :
    (boundaryParamHalfAddTwo q).1 =
      ((half q + 2 : Nat) : ZMod (modulus q)) := rfl

theorem boundaryParamLast_val (q : Nat) :
    (boundaryParamLast q).1 =
      ((modulus q - 1 : Nat) : ZMod (modulus q)) := rfl

theorem boundaryParamPenultimate_val (q : Nat) :
    (boundaryParamPenultimate q).1 =
      ((modulus q - 2 : Nat) : ZMod (modulus q)) := rfl

theorem boundary_shift_ne_zero (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ half q + 2) :
    a.1 + ((half q - 2 : Nat) : ZMod (modulus q)) ≠ 0 := by
  intro hzero
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero_val : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero_val)
  have hlt := ZMod.val_lt a.1
  have hconst_lt : half q - 2 < modulus q := by
    simp [half, modulus]
    omega
  have hconst_val :
      (((half q - 2 : Nat) : ZMod (modulus q))).val = half q - 2 := by
    rw [ZMod.val_natCast_of_lt hconst_lt]
  have hval :
      (a.1 + ((half q - 2 : Nat) : ZMod (modulus q))).val =
        (0 : ZMod (modulus q)).val :=
    congrArg (fun z : ZMod (modulus q) => z.val) hzero
  have hmod :
      (a.1.val + (half q - 2)) % modulus q = 0 := by
    rw [ZMod.val_add, hconst_val] at hval
    simpa using hval
  have hdiv : modulus q ∣ a.1.val + (half q - 2) :=
    Nat.dvd_of_mod_eq_zero hmod
  rcases hdiv with ⟨t, ht⟩
  have hsum_pos : 0 < a.1.val + (half q - 2) := by
    have hhalf : 0 < half q - 2 := by simp [half]
    omega
  have hsum_lt_two :
      a.1.val + (half q - 2) < 2 * modulus q := by
    simp [half, modulus] at hlt ⊢
    omega
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    rw [htzero, mul_zero] at ht
    omega
  have htlt_two : t < 2 := by
    by_contra hnot
    have htwo : 2 ≤ t := by omega
    have hge : 2 * modulus q ≤ modulus q * t := by
      rw [mul_comm 2 (modulus q)]
      exact Nat.mul_le_mul_left (modulus q) htwo
    omega
  have ht_eq_one : t = 1 := by omega
  have hsum_eq : a.1.val + (half q - 2) = modulus q := by
    rw [ht, ht_eq_one, mul_one]
  apply hne
  simp [half, modulus] at hsum_eq ⊢
  omega

def boundaryShiftParam (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ half q + 2) :
    RouteENonzeroSeam (modulus q) :=
  ⟨a.1 + ((half q - 2 : Nat) : ZMod (modulus q)),
    boundary_shift_ne_zero q a hne⟩

theorem boundaryShiftParam_val (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ half q + 2) :
    (boundaryShiftParam q a hne).1 =
      a.1 + ((half q - 2 : Nat) : ZMod (modulus q)) := rfl

theorem boundary_pred_ne_zero (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ 1) :
    a.1 - 1 ≠ 0 := by
  intro hzero
  have hone : a.1 = (1 : ZMod (modulus q)) := by
    have h := congrArg (fun z : ZMod (modulus q) => z + 1) hzero
    simpa [sub_eq_add_neg, add_assoc] using h
  apply hne
  have hval := congrArg (fun z : ZMod (modulus q) => z.val) hone
  simpa [modulus] using hval

def boundaryPredParam (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ 1) :
    RouteENonzeroSeam (modulus q) :=
  ⟨a.1 - 1, boundary_pred_ne_zero q a hne⟩

theorem boundaryPredParam_val (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hne : a.1.val ≠ 1) :
    (boundaryPredParam q a hne).1 = a.1 - 1 := rfl

noncomputable def boundaryQuotient (q : Nat) :
    RouteEBoundaryNode (modulus q) → RouteEBoundaryNode (modulus q)
  | Sum.inl _ =>
      routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalf q)
  | Sum.inr (RouteEBoundaryLabel.L03, a) =>
      if _hh : a.1.val = half q then
        routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamLast q)
      else if _hsucc : a.1.val = half q + 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalfSubTwo q)
      else if hev : a.1.val % 2 = 0 then
        routeEBoundaryNode RouteEBoundaryLabel.L04 a
      else
        have hodd : a.1.val % 2 = 1 := by
          have hlt : a.1.val % 2 < 2 := Nat.mod_lt _ (by omega)
          omega
        have hne_shift : a.1.val ≠ half q + 2 := by
          intro h
          rw [h] at hodd
          have heven : (half q + 2) % 2 = 0 := by
            simp [half, Nat.add_mod, Nat.mul_mod]
          omega
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q a hne_shift)
  | Sum.inr (RouteEBoundaryLabel.L04, a) =>
      if _hpred : a.1.val = half q - 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L34 a
      else if _hlast : a.1.val = modulus q - 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamPenultimate q)
      else if _hclose : a.1.val = half q + 2 then
        routeEBoundaryZero
      else if _hodd : a.1.val % 2 = 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L03 a
      else if _htwo : a.1.val = 2 then
        routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalfSubOne q)
      else
        routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryShiftParam q a _hclose)
  | Sum.inr (RouteEBoundaryLabel.L34, a) =>
      if h_one : a.1.val = 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamLast q)
      else if _hh : a.1.val = half q then
        routeEBoundaryNode RouteEBoundaryLabel.L04 a
      else if _hlast : a.1.val = modulus q - 1 then
        routeEBoundaryNode RouteEBoundaryLabel.L04 a
      else
        routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundaryPredParam q a h_one)

@[simp] theorem boundaryQuotient_zero (q : Nat) :
    boundaryQuotient q routeEBoundaryZero =
      routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalf q) := rfl

theorem boundaryQuotient_A_h (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamLast q) := by
  simp [boundaryQuotient, routeEBoundaryNode, ha]

theorem boundaryQuotient_A_h_succ (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q + 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryParamHalfSubTwo q) := by
  have hnot_h : a.1.val ≠ half q := by
    rw [ha]
    simp [half]
  simp [boundaryQuotient, routeEBoundaryNode, ha]

theorem boundaryQuotient_B_h_sub_one (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q - 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L34 a := by
  simp [boundaryQuotient, routeEBoundaryNode, ha]

theorem boundaryQuotient_B_last (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = modulus q - 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L34
        (boundaryParamPenultimate q) := by
  have hnot_pred : a.1.val ≠ half q - 1 := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnot_pred_const : ¬ modulus q - 1 = half q - 1 := by
    simp [half, modulus]
    omega
  simp [boundaryQuotient, routeEBoundaryNode, ha, hnot_pred_const]

theorem boundaryQuotient_B_close (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q + 2) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryZero := by
  have hnot_pred : a.1.val ≠ half q - 1 := by
    rw [ha]
    simp [half]
  have hnot_last : a.1.val ≠ modulus q - 1 := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnot_pred_const : ¬ half q + 2 = half q - 1 := by
    simp [half]
  have hnot_last_const : ¬ half q + 2 = modulus q - 1 := by
    simp [half, modulus]
    omega
  simp [boundaryQuotient, routeEBoundaryNode, ha, hnot_pred_const,
    hnot_last_const]

theorem boundaryQuotient_C_one (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamLast q) := by
  simp [boundaryQuotient, routeEBoundaryNode, ha]

theorem boundaryQuotient_C_h (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L04 a := by
  have hnot_one : a.1.val ≠ 1 := by
    rw [ha]
    simp [half]
  have hnot_one_const : ¬ half q = 1 := by
    simp [half]
  simp [boundaryQuotient, routeEBoundaryNode, ha, hnot_one_const]

theorem boundaryQuotient_C_last (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = modulus q - 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L04 a := by
  have hnot_one : a.1.val ≠ 1 := by
    rw [ha]
    simp [modulus]
  have hnot_h : a.1.val ≠ half q := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnot_one_const : ¬ modulus q - 1 = 1 := by
    simp [modulus]
  have hnot_h_const : ¬ modulus q - 1 = half q := by
    simp [half, modulus]
    omega
  simp [boundaryQuotient, routeEBoundaryNode, ha, hnot_one_const,
    hnot_h_const]

theorem boundaryQuotient_A_even (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hnot_h : a.1.val ≠ half q)
    (heven : a.1.val % 2 = 0) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L04 a := by
  have hnot_succ : a.1.val ≠ half q + 1 := by
    intro h
    rw [h] at heven
    have hodd : (half q + 1) % 2 = 1 := by
      simp [half, Nat.add_mod, Nat.mul_mod]
    omega
  simp [boundaryQuotient, routeEBoundaryNode, hnot_h, hnot_succ, heven]

theorem boundaryQuotient_A_odd_shift (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hnot_succ : a.1.val ≠ half q + 1)
    (hodd : a.1.val % 2 = 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L04
        (boundaryShiftParam q a (by
          intro h
          rw [h] at hodd
          have heven : (half q + 2) % 2 = 0 := by
            simp [half, Nat.add_mod, Nat.mul_mod]
          omega)) := by
  have hnot_h : a.1.val ≠ half q := by
    intro h
    rw [h] at hodd
    have heven : (half q) % 2 = 0 := by
      simp [half, Nat.add_mod, Nat.mul_mod]
    omega
  have hnot_even : a.1.val % 2 ≠ 0 := by omega
  simp [boundaryQuotient, routeEBoundaryNode, hnot_h, hnot_succ, hnot_even]

theorem boundaryQuotient_B_odd (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hnot_pred : a.1.val ≠ half q - 1)
    (hnot_last : a.1.val ≠ modulus q - 1)
    (hodd : a.1.val % 2 = 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L03 a := by
  have hnot_close : a.1.val ≠ half q + 2 := by
    intro h
    rw [h] at hodd
    have heven : (half q + 2) % 2 = 0 := by
      simp [half, Nat.add_mod, Nat.mul_mod]
    omega
  simp [boundaryQuotient, routeEBoundaryNode, hnot_pred, hnot_last,
    hnot_close, hodd]

theorem boundaryQuotient_B_two (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = 2) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryParamHalfSubOne q) := by
  have hnot_pred_const : ¬ 2 = half q - 1 := by
    simp [half]
  have hnot_last_const : ¬ 2 = modulus q - 1 := by
    simp [modulus]
  have hnot_close_const : ¬ half q = 0 := by
    simp [half]
  simp [boundaryQuotient, routeEBoundaryNode, ha, hnot_pred_const,
    hnot_last_const, hnot_close_const]

theorem boundaryQuotient_B_even_shift (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hnot_two : a.1.val ≠ 2)
    (hnot_close : a.1.val ≠ half q + 2)
    (heven : a.1.val % 2 = 0) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryShiftParam q a hnot_close) := by
  have hnot_pred : a.1.val ≠ half q - 1 := by
    intro h
    rw [h] at heven
    have hodd : (half q - 1) % 2 = 1 := by
      simp [half, Nat.add_mod, Nat.mul_mod]
    omega
  have hnot_last : a.1.val ≠ modulus q - 1 := by
    intro h
    rw [h] at heven
    have hodd : (modulus q - 1) % 2 = 1 := by
      simp [modulus, Nat.add_mod, Nat.mul_mod]
    omega
  have hnot_odd : a.1.val % 2 ≠ 1 := by omega
  simp [boundaryQuotient, routeEBoundaryNode, hnot_pred, hnot_last,
    hnot_close, hnot_odd, hnot_two]

theorem boundaryQuotient_C_generic (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hnot_one : a.1.val ≠ 1)
    (hnot_h : a.1.val ≠ half q)
    (hnot_last : a.1.val ≠ modulus q - 1) :
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
      routeEBoundaryNode RouteEBoundaryLabel.L34
        (boundaryPredParam q a hnot_one) := by
  simp [boundaryQuotient, routeEBoundaryNode, hnot_one, hnot_h, hnot_last]

theorem boundaryQuotient_formulaTarget (q : Nat) :
    BoundaryQuotientFormulaTarget q (boundaryQuotient q) where
  zero_to_A :=
    ⟨boundaryParamHalf q, boundaryParamHalf_val q, boundaryQuotient_zero q⟩
  A_h_to_C_last := by
    intro a ha
    exact ⟨boundaryParamLast q, boundaryParamLast_val q,
      boundaryQuotient_A_h q a ha⟩
  A_h_succ_to_A_h_sub_two := by
    intro a ha
    exact ⟨boundaryParamHalfSubTwo q, boundaryParamHalfSubTwo_val q,
      boundaryQuotient_A_h_succ q a ha⟩
  A_even_to_B_same := by
    intro a hnot_h heven
    exact boundaryQuotient_A_even q a hnot_h heven
  A_odd_to_B_shift := by
    intro a hnot_succ hodd
    have hnot_close : a.1.val ≠ half q + 2 := by
      intro h
      rw [h] at hodd
      have heven : (half q + 2) % 2 = 0 := by
        simp [half, Nat.add_mod, Nat.mul_mod]
      omega
    refine ⟨boundaryShiftParam q a hnot_close,
      boundaryShiftParam_val q a hnot_close, ?_⟩
    simpa [boundaryShiftParam] using
      boundaryQuotient_A_odd_shift q a hnot_succ hodd
  B_h_sub_one_to_C_same := by
    intro a ha
    exact boundaryQuotient_B_h_sub_one q a ha
  B_last_to_C_pred := by
    intro a ha
    exact ⟨boundaryParamPenultimate q, boundaryParamPenultimate_val q,
      boundaryQuotient_B_last q a ha⟩
  B_h_add_two_to_zero := by
    intro a ha
    exact boundaryQuotient_B_close q a ha
  B_odd_to_A_same := by
    intro a hnot_pred hnot_last hodd
    exact boundaryQuotient_B_odd q a hnot_pred hnot_last hodd
  B_two_to_A_h_sub_one := by
    intro a ha
    exact ⟨boundaryParamHalfSubOne q, boundaryParamHalfSubOne_val q,
      boundaryQuotient_B_two q a ha⟩
  B_even_to_A_shift := by
    intro a hnot_two hnot_close heven
    exact ⟨boundaryShiftParam q a hnot_close,
      boundaryShiftParam_val q a hnot_close,
      boundaryQuotient_B_even_shift q a hnot_two hnot_close heven⟩
  C_one_to_A_last := by
    intro a ha
    exact ⟨boundaryParamLast q, boundaryParamLast_val q,
      boundaryQuotient_C_one q a ha⟩
  C_h_to_B_same := by
    intro a ha
    exact boundaryQuotient_C_h q a ha
  C_last_to_B_same := by
    intro a ha
    exact boundaryQuotient_C_last q a ha
  C_generic_to_C_pred := by
    intro a hnot_one hnot_h hnot_last
    exact ⟨boundaryPredParam q a hnot_one,
      boundaryPredParam_val q a hnot_one,
      boundaryQuotient_C_generic q a hnot_one hnot_h hnot_last⟩

theorem card_boundaryNode_eq_three_modulus_sub_two (q : Nat) :
    Fintype.card (RouteEBoundaryNode (modulus q)) = 3 * modulus q - 2 := by
  rw [card_routeEBoundaryNode]
  simp [modulus]
  omega

def boundaryCycleLength (q : Nat) : Nat :=
  3 * modulus q - 2

theorem boundaryCycleLength_eq_card (q : Nat) :
    boundaryCycleLength q =
      Fintype.card (RouteEBoundaryNode (modulus q)) := by
  rw [boundaryCycleLength, card_boundaryNode_eq_three_modulus_sub_two]

theorem boundaryCycleLength_eq_twelve_quarter_sub_two (q : Nat) :
    boundaryCycleLength q = 12 * quarter q - 2 := by
  simp [boundaryCycleLength, quarter, modulus]
  omega

def boundaryCycleSpineCount (q : Nat) : Nat :=
  half q + 4

def boundaryCycleFirstEvenTailCount (q : Nat) : Nat :=
  2 * (quarter q - 1)

def boundaryCycleB2BridgeCount (_q : Nat) : Nat := 1

def boundaryCycleFirstOddTailCount (q : Nat) : Nat :=
  2 * (quarter q - 1) + 1 + (half q - 1)

def boundaryCycleALastBridgeCount (_q : Nat) : Nat := 1

def boundaryCycleSecondOddTailCount (q : Nat) : Nat :=
  2 * quarter q - 1

def boundaryCycleSecondEvenTailCount (q : Nat) : Nat :=
  2 * quarter q - 3

def boundaryCycleHandCountTotal (q : Nat) : Nat :=
  boundaryCycleSpineCount q +
  boundaryCycleFirstEvenTailCount q +
  boundaryCycleB2BridgeCount q +
  boundaryCycleFirstOddTailCount q +
  boundaryCycleALastBridgeCount q +
  boundaryCycleSecondOddTailCount q +
  boundaryCycleSecondEvenTailCount q

def boundaryCycleFirstEvenStart (q : Nat) : Nat :=
  boundaryCycleSpineCount q

def boundaryCycleB2BridgeStart (q : Nat) : Nat :=
  boundaryCycleFirstEvenStart q + boundaryCycleFirstEvenTailCount q

def boundaryCycleFirstOddStart (q : Nat) : Nat :=
  boundaryCycleB2BridgeStart q + boundaryCycleB2BridgeCount q

def boundaryCycleALastBridgeStart (q : Nat) : Nat :=
  boundaryCycleFirstOddStart q + boundaryCycleFirstOddTailCount q

def boundaryCycleSecondOddStart (q : Nat) : Nat :=
  boundaryCycleALastBridgeStart q + boundaryCycleALastBridgeCount q

def boundaryCycleSecondEvenStart (q : Nat) : Nat :=
  boundaryCycleSecondOddStart q + boundaryCycleSecondOddTailCount q

theorem boundaryCycleFirstEvenStart_eq_half_add_four (q : Nat) :
    boundaryCycleFirstEvenStart q = half q + 4 := rfl

theorem boundaryCycleB2BridgeStart_eq_modulus_add_two (q : Nat) :
    boundaryCycleB2BridgeStart q = modulus q + 2 := by
  simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
    boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
    quarter, half, modulus]
  omega

theorem boundaryCycleFirstOddStart_eq_modulus_add_three (q : Nat) :
    boundaryCycleFirstOddStart q = modulus q + 3 := by
  rw [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart_eq_modulus_add_two]
  simp [boundaryCycleB2BridgeCount]

theorem boundaryCycleALastBridgeStart_eq_two_modulus_add_one (q : Nat) :
    boundaryCycleALastBridgeStart q = 2 * modulus q + 1 := by
  rw [boundaryCycleALastBridgeStart,
    boundaryCycleFirstOddStart_eq_modulus_add_three]
  simp [boundaryCycleFirstOddTailCount, quarter, half, modulus]
  omega

theorem boundaryCycleSecondOddStart_eq_two_modulus_add_two (q : Nat) :
    boundaryCycleSecondOddStart q = 2 * modulus q + 2 := by
  rw [boundaryCycleSecondOddStart,
    boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
  simp [boundaryCycleALastBridgeCount]

theorem boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one
    (q : Nat) :
    boundaryCycleSecondEvenStart q = 2 * modulus q + half q + 1 := by
  rw [boundaryCycleSecondEvenStart,
    boundaryCycleSecondOddStart_eq_two_modulus_add_two]
  simp [boundaryCycleSecondOddTailCount, quarter, half, modulus]
  omega

theorem boundaryCycleSecondEvenEnd_eq_length (q : Nat) :
    boundaryCycleSecondEvenStart q + boundaryCycleSecondEvenTailCount q =
      boundaryCycleLength q := by
  rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one]
  simp [boundaryCycleSecondEvenTailCount, boundaryCycleLength,
    quarter, half, modulus]
  omega

def boundarySpineCValue (q i : Nat) : Nat :=
  modulus q - (i - 2)

theorem boundarySpineCValue_range (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i ≤ half q + 2) :
    0 < boundarySpineCValue q i ∧
      boundarySpineCValue q i < modulus q := by
  simp [boundarySpineCValue, half, modulus] at hhi ⊢
  omega

def boundarySpineCParam (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i ≤ half q + 2) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundarySpineCValue q i)
    (boundarySpineCValue_range q i hlo hhi).1
    (boundarySpineCValue_range q i hlo hhi).2

theorem boundarySpineCParam_val (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i ≤ half q + 2) :
    (boundarySpineCParam q i hlo hhi).1.val =
      boundarySpineCValue q i := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

noncomputable def boundaryCycleSpineNode (q i : Nat)
    (hi : i < boundaryCycleSpineCount q) :
    RouteEBoundaryNode (modulus q) :=
  if h0 : i = 0 then
    routeEBoundaryZero
  else if h1 : i = 1 then
    routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalf q)
  else if h2 : i = 2 then
    routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamLast q)
  else if h3 : i = 3 then
    routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamLast q)
  else if h4 : i = 4 then
    routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamPenultimate q)
  else if hlast : i = half q + 3 then
    routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamHalf q)
  else
    have hlo : 5 ≤ i := by omega
    have hhi : i ≤ half q + 2 := by
      simp [boundaryCycleSpineCount] at hi
      omega
    routeEBoundaryNode RouteEBoundaryLabel.L34
      (boundarySpineCParam q i hlo hhi)

theorem boundaryCycleSpineNode_zero (q : Nat)
    (hi : 0 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q 0 hi = routeEBoundaryZero := by
  simp [boundaryCycleSpineNode]

theorem boundaryCycleSpineNode_one (q : Nat)
    (hi : 1 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q 1 hi =
      routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalf q) := by
  simp [boundaryCycleSpineNode]

theorem boundaryCycleSpineNode_two (q : Nat)
    (hi : 2 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q 2 hi =
      routeEBoundaryNode RouteEBoundaryLabel.L34 (boundaryParamLast q) := by
  simp [boundaryCycleSpineNode]

theorem boundaryCycleSpineNode_three (q : Nat)
    (hi : 3 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q 3 hi =
      routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamLast q) := by
  simp [boundaryCycleSpineNode]

theorem boundaryCycleSpineNode_four (q : Nat)
    (hi : 4 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q 4 hi =
      routeEBoundaryNode RouteEBoundaryLabel.L34
        (boundaryParamPenultimate q) := by
  simp [boundaryCycleSpineNode]

theorem boundaryCycleSpine_step_zero (q : Nat)
    (h0 : 0 < boundaryCycleSpineCount q)
    (h1 : 1 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q 0 h0) =
      boundaryCycleSpineNode q 1 h1 := by
  rw [boundaryCycleSpineNode_zero q h0, boundaryCycleSpineNode_one q h1]
  exact boundaryQuotient_zero q

theorem boundaryCycleSpine_step_one (q : Nat)
    (h1 : 1 < boundaryCycleSpineCount q)
    (h2 : 2 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q 1 h1) =
      boundaryCycleSpineNode q 2 h2 := by
  rw [boundaryCycleSpineNode_one q h1, boundaryCycleSpineNode_two q h2]
  exact boundaryQuotient_A_h q (boundaryParamHalf q) (by
    simp [boundaryParamHalf, RouteENonzeroSeam.ofNat_val])

theorem boundaryCycleSpine_step_two (q : Nat)
    (h2 : 2 < boundaryCycleSpineCount q)
    (h3 : 3 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q 2 h2) =
      boundaryCycleSpineNode q 3 h3 := by
  rw [boundaryCycleSpineNode_two q h2, boundaryCycleSpineNode_three q h3]
  exact boundaryQuotient_C_last q (boundaryParamLast q) (by
    simp [boundaryParamLast, RouteENonzeroSeam.ofNat_val])

theorem boundaryCycleSpine_step_three (q : Nat)
    (h3 : 3 < boundaryCycleSpineCount q)
    (h4 : 4 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q 3 h3) =
      boundaryCycleSpineNode q 4 h4 := by
  rw [boundaryCycleSpineNode_three q h3, boundaryCycleSpineNode_four q h4]
  exact boundaryQuotient_B_last q (boundaryParamLast q) (by
    simp [boundaryParamLast, RouteENonzeroSeam.ofNat_val])

def boundaryFirstEvenValue (q j : Nat) : Nat :=
  if j % 2 = 0 then half q - 2 * j else modulus q - 2 * j

def boundaryFirstOddValue (q j : Nat) : Nat :=
  if j % 2 = 0 then half q - 1 - 2 * j else modulus q - 1 - 2 * j

def boundarySecondOddValue (q j : Nat) : Nat :=
  if j % 2 = 0 then modulus q - 1 - 2 * j else half q - 1 - 2 * j

def boundarySecondEvenValue (q j : Nat) : Nat :=
  if j % 2 = 0 then half q - 2 - 2 * j else modulus q - 2 - 2 * j

theorem boundaryFirstEvenValue_range (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    0 < boundaryFirstEvenValue q j ∧
      boundaryFirstEvenValue q j < modulus q := by
  have hhalf_pos : 0 < half q - 2 * j := by
    simp [half, quarter] at hjlt ⊢
    omega
  have hhalf_lt : half q - 2 * j < modulus q := by
    simp [half, modulus]
    omega
  have hmod_pos : 0 < modulus q - 2 * j := by
    simp [modulus, quarter] at hjlt ⊢
    omega
  have hmod_lt : modulus q - 2 * j < modulus q := by
    simp [modulus]
    omega
  by_cases hpar : j % 2 = 0
  · simpa [boundaryFirstEvenValue, hpar] using And.intro hhalf_pos hhalf_lt
  · simpa [boundaryFirstEvenValue, hpar] using And.intro hmod_pos hmod_lt

theorem boundaryFirstOddValue_range (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    0 < boundaryFirstOddValue q j ∧
      boundaryFirstOddValue q j < modulus q := by
  have hhalf_pos : 0 < half q - 1 - 2 * j := by
    simp [half, quarter] at hjlt ⊢
    omega
  have hhalf_lt : half q - 1 - 2 * j < modulus q := by
    simp [half, modulus]
    omega
  have hmod_pos : 0 < modulus q - 1 - 2 * j := by
    simp [modulus, quarter] at hjlt ⊢
    omega
  have hmod_lt : modulus q - 1 - 2 * j < modulus q := by
    simp [modulus]
    omega
  by_cases hpar : j % 2 = 0
  · simpa [boundaryFirstOddValue, hpar] using And.intro hhalf_pos hhalf_lt
  · simpa [boundaryFirstOddValue, hpar] using And.intro hmod_pos hmod_lt

theorem boundarySecondOddValue_range (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    0 < boundarySecondOddValue q j ∧
      boundarySecondOddValue q j < modulus q := by
  have hhalf_pos : 0 < half q - 1 - 2 * j := by
    simp [half, quarter] at hjlt ⊢
    omega
  have hhalf_lt : half q - 1 - 2 * j < modulus q := by
    simp [half, modulus]
    omega
  have hmod_pos : 0 < modulus q - 1 - 2 * j := by
    simp [modulus, quarter] at hjlt ⊢
    omega
  have hmod_lt : modulus q - 1 - 2 * j < modulus q := by
    simp [modulus]
    omega
  by_cases hpar : j % 2 = 0
  · simpa [boundarySecondOddValue, hpar] using And.intro hmod_pos hmod_lt
  · simpa [boundarySecondOddValue, hpar] using And.intro hhalf_pos hhalf_lt

theorem boundarySecondEvenValue_range (q j : Nat)
    (hjlt : j < quarter q - 1) :
    0 < boundarySecondEvenValue q j ∧
      boundarySecondEvenValue q j < modulus q := by
  have hhalf_pos : 0 < half q - 2 - 2 * j := by
    simp [half, quarter] at hjlt ⊢
    omega
  have hhalf_lt : half q - 2 - 2 * j < modulus q := by
    simp [half, modulus]
    omega
  have hmod_pos : 0 < modulus q - 2 - 2 * j := by
    simp [modulus, quarter] at hjlt ⊢
    omega
  have hmod_lt : modulus q - 2 - 2 * j < modulus q := by
    simp [modulus]
    omega
  by_cases hpar : j % 2 = 0
  · simpa [boundarySecondEvenValue, hpar] using And.intro hhalf_pos hhalf_lt
  · simpa [boundarySecondEvenValue, hpar] using And.intro hmod_pos hmod_lt

def boundaryFirstEvenParam (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundaryFirstEvenValue q j)
    (boundaryFirstEvenValue_range q j hjpos hjlt).1
    (boundaryFirstEvenValue_range q j hjpos hjlt).2

theorem boundaryFirstEvenParam_val (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstEvenParam q j hjpos hjlt).1.val =
      boundaryFirstEvenValue q j := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

def boundaryFirstOddParam (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundaryFirstOddValue q j)
    (boundaryFirstOddValue_range q j hjpos hjlt).1
    (boundaryFirstOddValue_range q j hjpos hjlt).2

theorem boundaryFirstOddParam_val (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstOddParam q j hjpos hjlt).1.val =
      boundaryFirstOddValue q j := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

def boundarySecondOddParam (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundarySecondOddValue q j)
    (boundarySecondOddValue_range q j hjpos hjlt).1
    (boundarySecondOddValue_range q j hjpos hjlt).2

theorem boundarySecondOddParam_val (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundarySecondOddParam q j hjpos hjlt).1.val =
      boundarySecondOddValue q j := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

def boundarySecondEvenParam (q j : Nat)
    (hjlt : j < quarter q - 1) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundarySecondEvenValue q j)
    (boundarySecondEvenValue_range q j hjlt).1
    (boundarySecondEvenValue_range q j hjlt).2

theorem boundarySecondEvenParam_val (q j : Nat)
    (hjlt : j < quarter q - 1) :
    (boundarySecondEvenParam q j hjlt).1.val =
      boundarySecondEvenValue q j := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

theorem boundaryCycleHandCountTotal_eq_card (q : Nat) :
    boundaryCycleHandCountTotal q =
      Fintype.card (RouteEBoundaryNode (modulus q)) := by
  rw [← boundaryCycleLength_eq_card, ← boundaryCycleSecondEvenEnd_eq_length]
  simp [boundaryCycleHandCountTotal, boundaryCycleSpineCount,
    boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
    boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
    boundaryCycleSecondOddTailCount, boundaryCycleSecondEvenTailCount,
    boundaryCycleFirstEvenStart, boundaryCycleB2BridgeStart,
    boundaryCycleFirstOddStart, boundaryCycleALastBridgeStart,
    boundaryCycleSecondOddStart, boundaryCycleSecondEvenStart]

/-!
The verifier's B20 return-time formula, written pointwise on the nonzero
Theta seam.  The labels match the bundle note: `B = A + m` and
`D = C + m`.
-/

def returnTimeFormula (q : Nat)
    (a : RouteENonzeroSeam (modulus q)) : Nat :=
  if a.1.val ≤ half q - 2 then
    if a.1.val = third q ∨ a.1.val = 2 * third q then
      timeC q
    else
      timeC q + modulus q
  else if a.1.val = half q - 1 then
    timeF q
  else if a.1.val = half q then
    timeC q
  else if a.1.val ≤ modulus q - 2 then
    if a.1.val = half q + third q ∨
        a.1.val = half q + 2 * third q then
      timeA q
    else
      timeA q + modulus q
  else
    timeE q

theorem returnTimeFormula_pos (q : Nat)
    (a : RouteENonzeroSeam (modulus q)) :
    0 < returnTimeFormula q a := by
  unfold returnTimeFormula
  split_ifs <;> simp [timeA, timeC, timeE, timeF, modulus]

theorem returnTimeFormula_lower_exception (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val ≤ half q - 2)
    (hex : a.1.val = third q ∨ a.1.val = 2 * third q) :
    returnTimeFormula q a = timeC q := by
  simp [returnTimeFormula, ha, hex]

theorem returnTimeFormula_lower_generic (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val ≤ half q - 2)
    (hne₁ : a.1.val ≠ third q)
    (hne₂ : a.1.val ≠ 2 * third q) :
    returnTimeFormula q a = timeC q + modulus q := by
  simp [returnTimeFormula, ha, hne₁, hne₂]

theorem returnTimeFormula_leftBoundary (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q - 1) :
    returnTimeFormula q a = timeF q := by
  unfold returnTimeFormula
  rw [ha]
  have hnotLower : ¬ half q - 1 ≤ half q - 2 := by
    simp [half]
  rw [if_neg hnotLower]
  rw [if_pos rfl]

theorem returnTimeFormula_midpoint (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = half q) :
    returnTimeFormula q a = timeC q := by
  unfold returnTimeFormula
  rw [ha]
  have hnotLower : ¬ half q ≤ half q - 2 := by
    simp [half]
  have hnotLeft : half q ≠ half q - 1 := by
    simp [half]
  rw [if_neg hnotLower]
  rw [if_neg hnotLeft]
  rw [if_pos rfl]

theorem returnTimeFormula_upper_exception (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hlo : half q + 1 ≤ a.1.val)
    (hhi : a.1.val ≤ modulus q - 2)
    (hex : a.1.val = half q + third q ∨
      a.1.val = half q + 2 * third q) :
    returnTimeFormula q a = timeA q := by
  have hnotLower : ¬ a.1.val ≤ half q - 2 := by omega
  have hnotLeft : a.1.val ≠ half q - 1 := by omega
  have hnotMid : a.1.val ≠ half q := by omega
  simp [returnTimeFormula, hnotLower, hnotLeft, hnotMid, hhi, hex]

theorem returnTimeFormula_upper_generic (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (hlo : half q + 1 ≤ a.1.val)
    (hhi : a.1.val ≤ modulus q - 2)
    (hne₁ : a.1.val ≠ half q + third q)
    (hne₂ : a.1.val ≠ half q + 2 * third q) :
    returnTimeFormula q a = timeA q + modulus q := by
  have hnotLower : ¬ a.1.val ≤ half q - 2 := by omega
  have hnotLeft : a.1.val ≠ half q - 1 := by omega
  have hnotMid : a.1.val ≠ half q := by omega
  simp [returnTimeFormula, hnotLower, hnotLeft, hnotMid, hhi, hne₁,
    hne₂]

theorem returnTimeFormula_last (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val = modulus q - 1) :
    returnTimeFormula q a = timeE q := by
  have hnotLower : ¬ a.1.val ≤ half q - 2 := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnotLeft : a.1.val ≠ half q - 1 := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnotMid : a.1.val ≠ half q := by
    rw [ha]
    simp [half, modulus]
    omega
  have hnotUpper : ¬ a.1.val ≤ modulus q - 2 := by
    rw [ha]
    simp [modulus]
  simp [returnTimeFormula, hnotLower, hnotLeft, hnotMid, hnotUpper]

def returnTimeLowerLeftBlock (q : Nat) : RouteEReturnTimeBlock where
  start := 1
  stop := third q - 1
  time := timeC q + modulus q

def returnTimeLowerFirstExceptionBlock (q : Nat) :
    RouteEReturnTimeBlock where
  start := third q
  stop := third q
  time := timeC q

def returnTimeLowerMiddleBlock (q : Nat) : RouteEReturnTimeBlock where
  start := third q + 1
  stop := 2 * third q - 1
  time := timeC q + modulus q

def returnTimeLowerSecondExceptionBlock (q : Nat) :
    RouteEReturnTimeBlock where
  start := 2 * third q
  stop := 2 * third q
  time := timeC q

def returnTimeLowerRightBlock (q : Nat) : RouteEReturnTimeBlock where
  start := 2 * third q + 1
  stop := half q - 2
  time := timeC q + modulus q

def returnTimeLeftBoundaryBlock (q : Nat) : RouteEReturnTimeBlock where
  start := half q - 1
  stop := half q - 1
  time := timeF q

def returnTimeMidpointBlock (q : Nat) : RouteEReturnTimeBlock where
  start := half q
  stop := half q
  time := timeC q

def returnTimeUpperLeftBlock (q : Nat) : RouteEReturnTimeBlock where
  start := half q + 1
  stop := half q + third q - 1
  time := timeA q + modulus q

def returnTimeUpperFirstExceptionBlock (q : Nat) :
    RouteEReturnTimeBlock where
  start := half q + third q
  stop := half q + third q
  time := timeA q

def returnTimeUpperMiddleBlock (q : Nat) : RouteEReturnTimeBlock where
  start := half q + third q + 1
  stop := half q + 2 * third q - 1
  time := timeA q + modulus q

def returnTimeUpperSecondExceptionBlock (q : Nat) :
    RouteEReturnTimeBlock where
  start := half q + 2 * third q
  stop := half q + 2 * third q
  time := timeA q

def returnTimeUpperRightBlock (q : Nat) : RouteEReturnTimeBlock where
  start := half q + 2 * third q + 1
  stop := modulus q - 2
  time := timeA q + modulus q

def returnTimeLastBlock (q : Nat) : RouteEReturnTimeBlock where
  start := modulus q - 1
  stop := modulus q - 1
  time := timeE q

def returnTimeBlocks (q : Nat) : List RouteEReturnTimeBlock :=
  [ returnTimeLowerLeftBlock q
  , returnTimeLowerFirstExceptionBlock q
  , returnTimeLowerMiddleBlock q
  , returnTimeLowerSecondExceptionBlock q
  , returnTimeLowerRightBlock q
  , returnTimeLeftBoundaryBlock q
  , returnTimeMidpointBlock q
  , returnTimeUpperLeftBlock q
  , returnTimeUpperFirstExceptionBlock q
  , returnTimeUpperMiddleBlock q
  , returnTimeUpperSecondExceptionBlock q
  , returnTimeUpperRightBlock q
  , returnTimeLastBlock q
  ]

theorem returnTimeBlocks_cover (q : Nat)
    (a : RouteENonzeroSeam (modulus q)) :
    ∃ block, block ∈ returnTimeBlocks q ∧ block.contains a := by
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hle_last : a.1.val ≤ modulus q - 1 := by
    have hlt := ZMod.val_lt a.1
    omega
  by_cases h₁ : a.1.val ≤ third q - 1
  · refine ⟨returnTimeLowerLeftBlock q, ?_, ?_⟩
    · simp [returnTimeBlocks]
    · change 1 ≤ a.1.val ∧ a.1.val ≤ third q - 1
      exact ⟨Nat.succ_le_of_lt hpos, h₁⟩
  · by_cases h₂ : a.1.val = third q
    · refine ⟨returnTimeLowerFirstExceptionBlock q, ?_, ?_⟩
      · simp [returnTimeBlocks]
      · simp [RouteEReturnTimeBlock.contains,
          returnTimeLowerFirstExceptionBlock, h₂]
    · by_cases h₃ : a.1.val ≤ 2 * third q - 1
      · refine ⟨returnTimeLowerMiddleBlock q, ?_, ?_⟩
        · simp [returnTimeBlocks]
        · simp [RouteEReturnTimeBlock.contains, returnTimeLowerMiddleBlock,
            third] at *
          omega
      · by_cases h₄ : a.1.val = 2 * third q
        · refine ⟨returnTimeLowerSecondExceptionBlock q, ?_, ?_⟩
          · simp [returnTimeBlocks]
          · simp [RouteEReturnTimeBlock.contains,
              returnTimeLowerSecondExceptionBlock, h₄]
        · by_cases h₅ : a.1.val ≤ half q - 2
          · refine ⟨returnTimeLowerRightBlock q, ?_, ?_⟩
            · simp [returnTimeBlocks]
            · simp [RouteEReturnTimeBlock.contains,
                returnTimeLowerRightBlock, third, half] at *
              omega
          · by_cases h₆ : a.1.val = half q - 1
            · refine ⟨returnTimeLeftBoundaryBlock q, ?_, ?_⟩
              · simp [returnTimeBlocks]
              · simp [RouteEReturnTimeBlock.contains,
                  returnTimeLeftBoundaryBlock, h₆]
            · by_cases h₇ : a.1.val = half q
              · refine ⟨returnTimeMidpointBlock q, ?_, ?_⟩
                · simp [returnTimeBlocks]
                · simp [RouteEReturnTimeBlock.contains,
                    returnTimeMidpointBlock, h₇]
              · by_cases h₈ : a.1.val ≤ half q + third q - 1
                · refine ⟨returnTimeUpperLeftBlock q, ?_, ?_⟩
                  · simp [returnTimeBlocks]
                  · simp [RouteEReturnTimeBlock.contains,
                      returnTimeUpperLeftBlock, third, half] at *
                    omega
                · by_cases h₉ : a.1.val = half q + third q
                  · refine ⟨returnTimeUpperFirstExceptionBlock q, ?_, ?_⟩
                    · simp [returnTimeBlocks]
                    · simp [RouteEReturnTimeBlock.contains,
                        returnTimeUpperFirstExceptionBlock, h₉]
                  · by_cases h₁₀ :
                        a.1.val ≤ half q + 2 * third q - 1
                    · refine ⟨returnTimeUpperMiddleBlock q, ?_, ?_⟩
                      · simp [returnTimeBlocks]
                      · simp [RouteEReturnTimeBlock.contains,
                          returnTimeUpperMiddleBlock, third, half] at *
                        omega
                    · by_cases h₁₁ :
                          a.1.val = half q + 2 * third q
                      · refine ⟨returnTimeUpperSecondExceptionBlock q, ?_, ?_⟩
                        · simp [returnTimeBlocks]
                        · simp [RouteEReturnTimeBlock.contains,
                            returnTimeUpperSecondExceptionBlock, h₁₁]
                      · by_cases h₁₂ : a.1.val ≤ modulus q - 2
                        · refine ⟨returnTimeUpperRightBlock q, ?_, ?_⟩
                          · simp [returnTimeBlocks]
                          · simp [RouteEReturnTimeBlock.contains,
                              returnTimeUpperRightBlock, third, half,
                              modulus] at *
                            omega
                        · refine ⟨returnTimeLastBlock q, ?_, ?_⟩
                          · simp [returnTimeBlocks]
                          · simp [RouteEReturnTimeBlock.contains,
                              returnTimeLastBlock, modulus] at *
                            omega

def seamStep (q : Nat) : Nat := half q + 1

theorem seamStep_lt_modulus_pred (q : Nat) :
    seamStep q < modulus q - 1 := by
  simp [seamStep, half, modulus]
  omega

theorem seamStep_coprime (q : Nat) :
    Nat.Coprime (seamStep q) (modulus q - 1) := by
  rw [seamStep, half, modulus]
  have hN : 24 * q + 20 - 1 = (12 * q + 8) + (12 * q + 11) := by
    omega
  rw [hN]
  rw [Nat.coprime_add_self_right]
  have hA : 12 * q + 11 = 3 + (12 * q + 8) := by
    omega
  rw [hA]
  rw [Nat.coprime_add_self_left]
  have hB : 12 * q + 8 = 2 + (4 * q + 2) * 3 := by
    omega
  rw [hB]
  rw [Nat.coprime_add_mul_right_right]
  norm_num

noncomputable def seamIndexAdd (q : Nat) :
    Fin (modulus q - 1) → Fin (modulus q - 1) :=
  fun i => (finZModEquiv (modulus q - 1)).symm
    ((finZModEquiv (modulus q - 1)) i +
      (seamStep q : ZMod (modulus q - 1)))

set_option linter.flexible false in
theorem seamIndexAdd_val (q : Nat) (i : Fin (modulus q - 1)) :
    (seamIndexAdd q i).val =
      (i.val + seamStep q) % (modulus q - 1) := by
  simp [seamIndexAdd, finZModEquiv]
  rw [ZMod.val_add]
  rw [ZMod.val_natCast_of_lt (show i.val < modulus q - 1 from i.isLt)]
  rw [ZMod.val_natCast_of_lt (seamStep_lt_modulus_pred q)]

theorem seamIndexAdd_single_cycle (q : Nat) :
    IsSingleCycleMap (seamIndexAdd q) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (finZModEquiv (modulus q - 1)).symm)
    (f := seamIndexAdd q)
    (g := fun x : ZMod (modulus q - 1) =>
      x + (seamStep q : ZMod (modulus q - 1)))
    ?_ ?_
  · exact Shared.zmod_add_single_cycle_of_coprime (seamStep_coprime q)
  · intro x
    simp [seamIndexAdd]

noncomputable def seamMap (q : Nat) :
    RouteENonzeroSeam (modulus q) → RouteENonzeroSeam (modulus q) :=
  fun a => RouteENonzeroSeam.ofIndex
    (seamIndexAdd q (RouteENonzeroSeam.toIndex a))

theorem seamMap_single_cycle (q : Nat) :
    IsSingleCycleMap (seamMap q) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := (RouteENonzeroSeam.indexEquiv (m := modulus q)).symm)
    (f := seamMap q)
    (g := seamIndexAdd q)
    (seamIndexAdd_single_cycle q) ?_
  intro i
  change RouteENonzeroSeam.toIndex
      (seamMap q (RouteENonzeroSeam.ofIndex i)) =
    seamIndexAdd q i
  simp [seamMap, RouteENonzeroSeam.toIndex_ofIndex]

set_option linter.flexible false in
theorem seamMap_lower_translation (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : a.1.val ≤ half q - 2) :
    (seamMap q a).1 = a.1 + (seamStep q : ZMod (modulus q)) := by
  simp [seamMap, RouteENonzeroSeam.ofIndex]
  rw [seamIndexAdd_val]
  simp [RouteENonzeroSeam.toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hlt : a.1.val - 1 + seamStep q < modulus q - 1 := by
    simp [seamStep, half, modulus] at ha ⊢
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hsub : a.1.val - 1 + seamStep q + 1 =
      a.1.val + seamStep q := by
    simp [seamStep]
    omega
  calc
    (((a.1.val - 1 + seamStep q : Nat) : ZMod (modulus q)) + 1) =
        (((a.1.val - 1 + seamStep q + 1 : Nat) :
          ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((a.1.val + seamStep q : Nat) : ZMod (modulus q))) := by
      rw [hsub]
    _ = ((a.1.val : Nat) : ZMod (modulus q)) +
        (seamStep q : ZMod (modulus q)) := by
      simp [Nat.cast_add]
    _ = a.1 + (seamStep q : ZMod (modulus q)) := by
      rw [ZMod.natCast_zmod_val a.1]

set_option linter.flexible false in
theorem seamMap_upper_translation (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (ha : half q - 1 ≤ a.1.val) :
    (seamMap q a).1 =
      a.1 + ((seamStep q + 1 : Nat) : ZMod (modulus q)) := by
  simp [seamMap, RouteENonzeroSeam.ofIndex]
  rw [seamIndexAdd_val]
  simp [RouteENonzeroSeam.toIndex]
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  let N := modulus q - 1
  let s := a.1.val - 1 + seamStep q
  have hge : N ≤ s := by
    simp [N, s, seamStep, half, modulus] at ha ⊢
    omega
  have hlt : s - N < N := by
    have aval_lt := ZMod.val_lt a.1
    simp [N, s, seamStep, half, modulus] at ha aval_lt ⊢
    omega
  have hs : s = N + (s - N) := by
    omega
  have hmod : (a.1.val - 1 + seamStep q) %
      (modulus q - 1) = s - N := by
    change s % N = s - N
    rw [hs, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    omega
  rw [hmod]
  have hsum : s - N + 1 + modulus q =
      a.1.val + seamStep q + 1 := by
    dsimp [s, N]
    omega
  calc
    (((s - N : Nat) : ZMod (modulus q)) + 1) =
        (((s - N + 1 : Nat) : ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((s - N + 1 + modulus q : Nat) : ZMod (modulus q))) := by
      simp [Nat.cast_add]
    _ = (((a.1.val + seamStep q + 1 : Nat) :
        ZMod (modulus q))) := by
      rw [hsum]
    _ = ((a.1.val : Nat) : ZMod (modulus q)) +
        (seamStep q : ZMod (modulus q)) + 1 := by
      simp [Nat.cast_add]
    _ = a.1 + (seamStep q : ZMod (modulus q)) + 1 := by
      rw [ZMod.natCast_zmod_val a.1]
    _ = a.1 + ((seamStep q : ZMod (modulus q)) + 1) := by
      ring

end RouteEB20

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

namespace RouteEB20

def lowerBlock (q : Nat) : RouteESeamTranslationBlock (modulus q) where
  start := 1
  stop := half q - 2
  delta := (seamStep q : ZMod (modulus q))
  start_pos := by omega
  stop_lt := by
    simp [half, modulus]
    omega
  start_le_stop := by
    simp [half]

def upperBlock (q : Nat) : RouteESeamTranslationBlock (modulus q) where
  start := half q - 1
  stop := modulus q - 1
  delta := ((seamStep q + 1 : Nat) : ZMod (modulus q))
  start_pos := by
    simp [half]
  stop_lt := by
    simp [modulus]
  start_le_stop := by
    simp [half, modulus]
    omega

def seamBlocks (q : Nat) : List (RouteESeamTranslationBlock (modulus q)) :=
  [lowerBlock q, upperBlock q]

theorem seamBlocks_cover (q : Nat)
    (a : RouteENonzeroSeam (modulus q)) :
    ∃ block, block ∈ seamBlocks q ∧ block.contains a := by
  have hpos : 0 < a.1.val := by
    by_contra hnot
    have hzero : a.1.val = 0 := by omega
    exact a.2 ((ZMod.val_eq_zero a.1).mp hzero)
  have hle_last : a.1.val ≤ modulus q - 1 := by
    have hlt := ZMod.val_lt a.1
    omega
  by_cases ha : a.1.val ≤ half q - 2
  · refine ⟨lowerBlock q, ?_, ?_⟩
    · simp [seamBlocks]
    · exact ⟨by simpa [lowerBlock] using Nat.succ_le_of_lt hpos, ha⟩
  · have hupper : half q - 1 ≤ a.1.val := by
      simp [half] at ha ⊢
      omega
    refine ⟨upperBlock q, ?_, ?_⟩
    · simp [seamBlocks]
    · exact ⟨hupper, hle_last⟩

set_option linter.flexible false in
theorem seamBlocks_disjoint (q : Nat)
    (a : RouteENonzeroSeam (modulus q))
    (block₁ block₂ : RouteESeamTranslationBlock (modulus q)) :
    block₁ ∈ seamBlocks q → block₂ ∈ seamBlocks q →
    block₁.contains a → block₂.contains a → block₁ = block₂ := by
  intro hmem₁ hmem₂ hcontains₁ hcontains₂
  simp [seamBlocks] at hmem₁ hmem₂
  rcases hmem₁ with h₁ | h₁ <;> rcases hmem₂ with h₂ | h₂
  · rw [h₁, h₂]
  · subst block₁
    subst block₂
    exfalso
    simp [RouteESeamTranslationBlock.contains, lowerBlock] at hcontains₁
    simp [RouteESeamTranslationBlock.contains, upperBlock] at hcontains₂
    omega
  · subst block₁
    subst block₂
    exfalso
    simp [RouteESeamTranslationBlock.contains, upperBlock] at hcontains₁
    simp [RouteESeamTranslationBlock.contains, lowerBlock] at hcontains₂
    omega
  · rw [h₁, h₂]

set_option linter.flexible false in
theorem seamBlocks_translation (q : Nat)
    (block : RouteESeamTranslationBlock (modulus q)) :
    block ∈ seamBlocks q →
      block.translationFormula (seamMap q) := by
  intro hmem
  simp [seamBlocks] at hmem
  rcases hmem with hmem | hmem
  · subst block
    intro a hcontains
    exact seamMap_lower_translation q a hcontains.2
  · subst block
    intro a hcontains
    exact seamMap_upper_translation q a hcontains.1

end RouteEB20

def routeEOpenPortFinSquareSucc {m : Nat} (I : Fin m × Fin m) : Fin m × Fin m :=
  (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I)) :
    Fin m × Fin m)

theorem routeEOpenPortFinSquareSucc_single_cycle (m : Nat) :
    IsSingleCycleMap (routeEOpenPortFinSquareSucc (m := m)) := by
  exact single_cycle_of_bijective_semiconj
    (f := finRotate (m * m))
    (g := routeEOpenPortFinSquareSucc (m := m))
    (phi := (finProdFinEquiv.symm : Fin (m * m) → Fin m × Fin m))
    (Equiv.bijective finProdFinEquiv.symm)
    (by
      intro x
      change finProdFinEquiv.symm ((finRotate (m * m)) x) =
        finProdFinEquiv.symm
          ((finRotate (m * m))
            (finProdFinEquiv (finProdFinEquiv.symm x)))
      rw [Equiv.apply_symm_apply])
    (finRotate_single_cycle (m * m))

theorem routeEOpenPortFinSquareSucc_of_col_lt {m : Nat} [NeZero m]
    (I : Fin m × Fin m) (hcol : I.2.val + 1 < m) :
    routeEOpenPortFinSquareSucc I = (I.1, ⟨I.2.val + 1, hcol⟩) := by
  apply (Equiv.injective finProdFinEquiv)
  change finProdFinEquiv
      (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I))) =
    finProdFinEquiv (I.1, ⟨I.2.val + 1, hcol⟩)
  rw [Equiv.apply_symm_apply]
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  have hNpos : 0 < m * m := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact Nat.mul_pos hmpos hmpos
  haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
  have hNgt1 : 1 < m * m := by
    by_cases hm1 : m = 1
    · subst m
      have hbad : I.2.val + 1 < 1 := hcol
      omega
    · have hmge2 : 2 ≤ m := by omega
      nlinarith
  have hone : ((1 : Fin (m * m)).val) = 1 := by
    rw [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt hNgt1
  rw [hone]
  have hlt : (finProdFinEquiv I).val + 1 < m * m := by
    calc
      (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
        simp [finProdFinEquiv]
      _ = (I.2.val + 1) + m * I.1.val := by omega
      _ < m + m * I.1.val := Nat.add_lt_add_right hcol _
      _ = m * (I.1.val + 1) := by rw [Nat.mul_succ, add_comm]
      _ ≤ m * m := Nat.mul_le_mul_left m (Nat.succ_le_of_lt I.1.isLt)
  rw [Nat.mod_eq_of_lt hlt]
  simp [finProdFinEquiv]
  omega

set_option linter.flexible false in
theorem routeEOpenPortFinSquareSucc_of_last_col {m : Nat} [NeZero m]
    (I : Fin m × Fin m) (hcol : I.2.val + 1 = m) :
    routeEOpenPortFinSquareSucc I =
      ((finRotate m) I.1, (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m)) := by
  by_cases hm1 : m = 1
  · subst m
    rcases I with ⟨i, j⟩
    fin_cases i
    fin_cases j
    rfl
  apply (Equiv.injective finProdFinEquiv)
  change finProdFinEquiv
      (finProdFinEquiv.symm ((finRotate (m * m)) (finProdFinEquiv I))) =
    finProdFinEquiv
      ((finRotate m) I.1, (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m))
  rw [Equiv.apply_symm_apply]
  by_cases hrow : I.1.val + 1 < m
  · rw [finRotate_of_lt I.1 hrow]
    rw [finRotate_apply]
    apply Fin.ext
    rw [Fin.val_add]
    have hNpos : 0 < m * m := by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact Nat.mul_pos hmpos hmpos
    haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
    have hNgt1 : 1 < m * m := by
      have hmge2 : 2 ≤ m := by omega
      nlinarith
    have hone : ((1 : Fin (m * m)).val) = 1 := by
      rw [Fin.coe_ofNat_eq_mod]
      exact Nat.mod_eq_of_lt hNgt1
    rw [hone]
    have hlt : (finProdFinEquiv I).val + 1 < m * m := by
      calc
        (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
          simp [finProdFinEquiv]
        _ = m * (I.1.val + 1) := by
          rw [Nat.mul_succ]
          omega
        _ < m * m :=
          Nat.mul_lt_mul_of_pos_left hrow (Nat.pos_of_ne_zero (NeZero.ne m))
    rw [Nat.mod_eq_of_lt hlt]
    simp [finProdFinEquiv]
    rw [Nat.mul_succ]
    omega
  · have hroweq : I.1.val + 1 = m := by
      have hle : I.1.val + 1 ≤ m := Nat.succ_le_of_lt I.1.isLt
      omega
    rw [finRotate_of_last I.1 hroweq]
    rw [finRotate_apply]
    apply Fin.ext
    rw [Fin.val_add]
    have hNpos : 0 < m * m := by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact Nat.mul_pos hmpos hmpos
    haveI : NeZero (m * m) := ⟨Nat.ne_of_gt hNpos⟩
    have hNgt1 : 1 < m * m := by
      have hmge2 : 2 ≤ m := by omega
      nlinarith
    have hone : ((1 : Fin (m * m)).val) = 1 := by
      rw [Fin.coe_ofNat_eq_mod]
      exact Nat.mod_eq_of_lt hNgt1
    rw [hone]
    have heqN : (finProdFinEquiv I).val + 1 = m * m := by
      calc
        (finProdFinEquiv I).val + 1 = I.2.val + m * I.1.val + 1 := by
          simp [finProdFinEquiv]
        _ = m * (I.1.val + 1) := by
          rw [Nat.mul_succ]
          omega
        _ = m * m := by rw [hroweq]
    rw [heqN]
    simp [Nat.mod_self, finProdFinEquiv]

theorem finZModEquiv_symm_add_one {m : Nat} [NeZero m] (x : ZMod m) :
    (finZModEquiv m).symm (x + 1) =
      (finRotate m) ((finZModEquiv m).symm x) := by
  apply (Equiv.injective (finZModEquiv m))
  simp [finZModEquiv, finRotate_apply, Fin.val_add]

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

structure RouteEOpenPortFiniteOdometerCertificate (m : Nat) [NeZero m] where
  A : ZMod m
  B : ZMod m
  C : ZMod m
  count_sum : A + B + C + 1 = 0
  chartIdx : ZMod m × ZMod m ≃ Fin m × Fin m
  chartIdx_step :
    ∀ p, chartIdx (routeEOpenPortHMap A C p) =
      routeEOpenPortFinSquareSucc (chartIdx p)

namespace RouteEOpenPortFiniteOdometerCertificate

theorem H_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m) :
    IsSingleCycleMap (routeEOpenPortHMap cert.A cert.C) := by
  refine Shared.single_cycle_of_equiv_conj
    (e := cert.chartIdx.symm)
    (f := routeEOpenPortHMap cert.A cert.C)
    (g := routeEOpenPortFinSquareSucc (m := m))
    (routeEOpenPortFinSquareSucc_single_cycle m) ?_
  intro I
  calc
    cert.chartIdx
        (routeEOpenPortHMap cert.A cert.C (cert.chartIdx.symm I)) =
        routeEOpenPortFinSquareSucc (cert.chartIdx (cert.chartIdx.symm I)) :=
      cert.chartIdx_step (cert.chartIdx.symm I)
    _ = routeEOpenPortFinSquareSucc I := by simp

theorem sectionPairMap_conjugates_to_H {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m)
    (p : ZMod m × ZMod m) :
    routeEOpenPortChart (routeEOpenPortSectionPairMap cert.A cert.B p) =
      routeEOpenPortHMap cert.A cert.C (routeEOpenPortChart p) :=
  routeEOpenPortChart_sectionPairMap cert.A cert.B cert.C cert.count_sum p

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEOpenPortFiniteOdometerCertificate m) :
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

end RouteEOpenPortFiniteOdometerCertificate

noncomputable def routeEOpenPortCanonicalChartIdx {m : Nat} [NeZero m] :
    ZMod m × ZMod m ≃ Fin m × Fin m where
  toFun p :=
    ((finZModEquiv m).symm (-p.2 - p.1),
      (finZModEquiv m).symm (-1 - p.1))
  invFun I :=
    let sigma : ZMod m := -1 - (finZModEquiv m I.2)
    (sigma, -(finZModEquiv m I.1) - sigma)
  left_inv := by
    intro p
    rcases p with ⟨sigma, a⟩
    simp [finZModEquiv]
  right_inv := by
    intro I
    rcases I with ⟨i, j⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [neg_sub, sub_neg_eq_add, add_sub_cancel_left, Equiv.symm_apply_apply]
    · apply Fin.ext
      simp only [sub_sub_cancel, Equiv.symm_apply_apply]

theorem routeEOpenPortCanonicalColumn_last {m : Nat} [NeZero m] :
    ((finZModEquiv m).symm (-1 : ZMod m)).val + 1 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hcast :
      ((((finZModEquiv m).symm (-1 : ZMod m)).val : Nat) : ZMod m) = -1 := by
    simp [finZModEquiv]
  have htarget : (((m - 1 : Nat) : ZMod m)) = -1 := by
    have hsum : (((m - 1) + 1 : Nat) : ZMod m) = (0 : ZMod m) := by
      rw [show (m - 1) + 1 = m by omega]
      simp
    rw [Nat.cast_add, Nat.cast_one] at hsum
    rw [add_comm] at hsum
    exact eq_neg_of_add_eq_zero_right hsum
  have hv : ((finZModEquiv m).symm (-1 : ZMod m)).val = m - 1 := by
    apply zmod_nat_eq_of_lt (m := m)
    · exact ((finZModEquiv m).symm (-1 : ZMod m)).isLt
    · exact Nat.sub_lt hmpos Nat.one_pos
    · simpa [htarget] using hcast
  omega

theorem routeEOpenPortCanonicalColumn_lt_of_ne_zero {m : Nat} [NeZero m]
    {sigma : ZMod m} (hsigma : sigma ≠ 0) :
    ((finZModEquiv m).symm (-1 - sigma)).val + 1 < m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  by_contra hlt
  have hjle : ((finZModEquiv m).symm (-1 - sigma)).val + 1 ≤ m :=
    Nat.succ_le_of_lt ((finZModEquiv m).symm (-1 - sigma)).isLt
  have hj : ((finZModEquiv m).symm (-1 - sigma)).val + 1 = m := by omega
  have hcast :
      ((((finZModEquiv m).symm (-1 - sigma)).val : Nat) : ZMod m) =
        -1 - sigma := by
    simp [finZModEquiv]
  have htarget :
      ((((finZModEquiv m).symm (-1 - sigma)).val : Nat) : ZMod m) = -1 := by
    have hv : ((finZModEquiv m).symm (-1 - sigma)).val = m - 1 := by omega
    rw [hv]
    have hsum : (((m - 1) + 1 : Nat) : ZMod m) = (0 : ZMod m) := by
      rw [show (m - 1) + 1 = m by omega]
      simp
    rw [Nat.cast_add, Nat.cast_one] at hsum
    rw [add_comm] at hsum
    exact eq_neg_of_add_eq_zero_right hsum
  have hsigma0 : sigma = 0 := by
    have h : (-1 : ZMod m) = -1 - sigma := htarget.symm.trans hcast
    have h2 := congrArg (fun x : ZMod m => x + 1) h
    have hneg : -sigma = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2.symm
    exact neg_eq_zero.mp hneg
  exact hsigma hsigma0

structure RouteEOpenPortCanonicalChartStepTarget (m : Nat) [NeZero m] : Prop where
  chartIdx_step :
    ∀ p, routeEOpenPortCanonicalChartIdx
        (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m) p) =
      routeEOpenPortFinSquareSucc (routeEOpenPortCanonicalChartIdx p)

namespace RouteEOpenPortCanonicalChartStepTarget

set_option linter.flexible false in
theorem unconditional {m : Nat} [NeZero m] :
    RouteEOpenPortCanonicalChartStepTarget m := by
  refine ⟨?_⟩
  intro p
  rcases p with ⟨sigma, a⟩
  by_cases hsigma : sigma = 0
  · subst sigma
    have hcol :
        (routeEOpenPortCanonicalChartIdx ((0 : ZMod m), a)).2.val + 1 = m := by
      simpa [routeEOpenPortCanonicalChartIdx] using
        routeEOpenPortCanonicalColumn_last (m := m)
    rw [routeEOpenPortFinSquareSucc_of_last_col _ hcol]
    apply Prod.ext
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap]
      simpa [finRotate_apply] using finZModEquiv_symm_add_one (-a)
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, finZModEquiv]
  · have hcol :
        (routeEOpenPortCanonicalChartIdx (sigma, a)).2.val + 1 < m := by
      simpa [routeEOpenPortCanonicalChartIdx] using
        routeEOpenPortCanonicalColumn_lt_of_ne_zero (m := m) hsigma
    rw [routeEOpenPortFinSquareSucc_of_col_lt _ hcol]
    apply Prod.ext
    · apply (Equiv.injective (finZModEquiv m))
      simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, hsigma, finZModEquiv]
      ring
    · simp [routeEOpenPortCanonicalChartIdx, routeEOpenPortHMap, hsigma]
      rw [← finRotate_of_lt ((finZModEquiv m).symm (-1 - sigma)) hcol]
      rw [← finZModEquiv_symm_add_one (-1 - sigma)]
      apply (Equiv.injective (finZModEquiv m))
      simp [finZModEquiv]
      ring

noncomputable def finiteOdometerCertificate {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    RouteEOpenPortFiniteOdometerCertificate m where
  A := 0
  B := -2
  C := 1
  count_sum := by ring
  chartIdx := routeEOpenPortCanonicalChartIdx
  chartIdx_step := target.chartIdx_step

theorem H_single_cycle {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    IsSingleCycleMap (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m)) :=
  RouteEOpenPortFiniteOdometerCertificate.H_single_cycle
    (finiteOdometerCertificate target)

theorem sectionPairMap_single_cycle {m : Nat} [NeZero m]
    (target : RouteEOpenPortCanonicalChartStepTarget m) :
    IsSingleCycleMap (routeEOpenPortSectionPairMap (0 : ZMod m) (-2 : ZMod m)) :=
  RouteEOpenPortFiniteOdometerCertificate.sectionPairMap_single_cycle
    (finiteOdometerCertificate target)

end RouteEOpenPortCanonicalChartStepTarget

theorem routeEOpenPortCanonicalH_single_cycle {m : Nat} [NeZero m] :
    IsSingleCycleMap (routeEOpenPortHMap (0 : ZMod m) (1 : ZMod m)) :=
  RouteEOpenPortCanonicalChartStepTarget.H_single_cycle
    RouteEOpenPortCanonicalChartStepTarget.unconditional

theorem routeEOpenPortCanonicalSectionPairMap_single_cycle {m : Nat} [NeZero m] :
    IsSingleCycleMap (routeEOpenPortSectionPairMap (0 : ZMod m) (-2 : ZMod m)) :=
  RouteEOpenPortCanonicalChartStepTarget.sectionPairMap_single_cycle
    RouteEOpenPortCanonicalChartStepTarget.unconditional

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

def RouteEAllPairVecSupport {m : Nat} (w : Vec5 m) : Prop :=
  w = 0 ∨
    ∃ (i j : Color), i.val < j.val ∧
      ∃ a : ZMod m, a ≠ 0 ∧
        w i = a ∧ w j = -a ∧
          ∀ k : Color, k ≠ i → k ≠ j → w k = 0

def RouteEAllPairSectionPoint {m : Nat} (z : Vec4 m) : Prop :=
  RouteEAllPairVecSupport (rootOfZ z).1

abbrev RouteEAllPairSection (m : Nat) :=
  { z : Vec4 m // RouteEAllPairSectionPoint z }

noncomputable instance routeEAllPairSectionFintype (m : Nat) [NeZero m] :
    Fintype (RouteEAllPairSection m) := by
  classical
  infer_instance

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

structure RouteEAllPairSectionCertificate (m : Nat) [NeZero m] where
  data : D5EvenSeamData m
  routeCounts : RouteECounts m
  sectionReturn : Color → RouteEAllPairSection m → RouteEAllPairSection m
  returnTime : Color → RouteEAllPairSection m → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] a.1 =
        (sectionReturn c a).1
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b : RouteEAllPairSection m,
        (seamRootReturn data c)^[k] a.1 = b.1
  sectionReturn_single :
    ∀ c, IsSingleCycleMap (sectionReturn c)
  returnTime_sum :
    ∀ c,
      Finset.univ.sum (fun a : RouteEAllPairSection m => returnTime c a) =
        m ^ 4

namespace RouteEAllPairSectionCertificate

noncomputable def toSmallSeamCertificate {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) :
    RouteESmallSeamCertificate m where
  data := cert.data
  routeCounts := cert.routeCounts
  seam := RouteEAllPairSection m
  seamFintype := by
    classical
    infer_instance
  seamPoint := fun a => a.1
  seamPoint_injective := by
    intro a b h
    exact Subtype.ext h
  seamReturn := cert.sectionReturn
  returnTime := cert.returnTime
  returnTime_pos := cert.returnTime_pos
  firstReturn_equation := cert.firstReturn_equation
  firstReturn_minimal := cert.firstReturn_minimal
  seamReturn_single := by
    intro c
    exact cert.sectionReturn_single c
  returnTime_sum := cert.returnTime_sum

theorem seamRootReturn_single_cycle {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) (c : Color) :
    IsSingleCycleMap (seamRootReturn cert.data c) :=
  cert.toSmallSeamCertificate.seamRootReturn_single_cycle c

theorem orbitTarget {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) :
    D5EvenSeamReturnOrbitTarget cert.data :=
  cert.toSmallSeamCertificate.orbitTarget

theorem toHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) :
    HamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toHamiltonDecomposition

theorem toTorusHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) :
    TorusHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toTorusHamiltonDecomposition

theorem toCayleyHamiltonDecomposition {m : Nat} [NeZero m]
    (cert : RouteEAllPairSectionCertificate m) :
    CayleyHamiltonDecompositionD5 m :=
  cert.toSmallSeamCertificate.toCayleyHamiltonDecomposition

end RouteEAllPairSectionCertificate

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

namespace RouteEB20

/-!
Trace-facing B20 target.

The expected B20 seam map, block cover, and cycle proof are already closed
above.  The remaining branch-specific work is to prove that the concrete
Route-E trace first-returns to this map with the claimed positive return
times and no earlier seam hits.  Once those trace facts and the return-time
sum are supplied, the theorem below packages them as the existing
piecewise-translation certificate.
-/

structure ThetaTraceTarget (q : Nat) where
  data : D5EvenSeamData (modulus q)
  returnTime : Color → RouteENonzeroSeam (modulus q) → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 (seamMap q a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 b
  returnTime_sum :
    ∀ c,
      Finset.univ.sum (fun a : RouteENonzeroSeam (modulus q) =>
        returnTime c a) = modulus q ^ 4

structure ThetaPointwiseTraceTarget (q : Nat) where
  data : D5EvenSeamData (modulus q)
  returnTimeFormula_weightedSum :
    Finset.univ.sum (fun a : RouteENonzeroSeam (modulus q) =>
      returnTimeFormula q a) = returnTimeWeightedSum q
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTimeFormula q a]
          (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 (seamMap q a)
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTimeFormula q a →
      ¬ ∃ b, (seamRootReturn data c)^[k] (routeEThetaSeamPoint 0 a) =
        routeEThetaSeamPoint 0 b

noncomputable def thetaTraceTargetOfPointwise (q : Nat)
    (target : ThetaPointwiseTraceTarget q) :
    ThetaTraceTarget q where
  data := target.data
  returnTime := fun _ => returnTimeFormula q
  returnTime_pos := by
    intro _c a
    exact returnTimeFormula_pos q a
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  returnTime_sum := by
    intro _c
    calc
      Finset.univ.sum (fun a : RouteENonzeroSeam (modulus q) =>
          returnTimeFormula q a) = returnTimeWeightedSum q :=
        target.returnTimeFormula_weightedSum
      _ = modulus q ^ 4 := returnTimeWeightedSum_eq_modulus_pow_four q

noncomputable def thetaPiecewiseCertificateOfTraceTarget (q : Nat)
    (target : ThetaTraceTarget q) :
    RouteEThetaPiecewiseTranslationCertificate (modulus q) where
  data := target.data
  routeCounts := routeCounts q
  slot := 0
  routeCounts_slot := rfl
  seamReturn := fun _ => seamMap q
  returnTime := target.returnTime
  returnTime_pos := target.returnTime_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  seamReturn_single := by
    intro _c
    exact seamMap_single_cycle q
  returnTime_sum := target.returnTime_sum
  blocks := fun _ => seamBlocks q
  block_cover := by
    intro _c a
    exact seamBlocks_cover q a
  block_disjoint := by
    intro _c a block₁ block₂ hmem₁ hmem₂ hcontains₁ hcontains₂
    exact seamBlocks_disjoint q a block₁ block₂ hmem₁ hmem₂ hcontains₁
      hcontains₂
  block_translation := by
    intro _c block hmem
    exact seamBlocks_translation q block hmem

theorem thetaPiecewiseTarget_of_traceTarget (q : Nat)
    (h : Nonempty (ThetaTraceTarget q)) :
    Nonempty (RouteEThetaPiecewiseTranslationCertificate (modulus q)) := by
  rcases h with ⟨target⟩
  exact ⟨thetaPiecewiseCertificateOfTraceTarget q target⟩

theorem thetaPiecewiseTarget_of_pointwiseTraceTarget (q : Nat)
    (h : Nonempty (ThetaPointwiseTraceTarget q)) :
    Nonempty (RouteEThetaPiecewiseTranslationCertificate (modulus q)) := by
  rcases h with ⟨target⟩
  exact ⟨thetaPiecewiseCertificateOfTraceTarget q
    (thetaTraceTargetOfPointwise q target)⟩

end RouteEB20

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
