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

/-!
`03` boundary-clock branch masses recovered from the v3.6 all-pair dumper.
These are aggregate targets for the five calendar branches:
low/high even lanes, the special even tie `a = h`, and low/high odd lanes.
They do not by themselves prove the pointwise clock formula.
-/

def allPairTime03LowEvenBranchMass (q : Nat) : Nat :=
  2592 * q ^ 3 + 6132 * q ^ 2 + 4798 * q + 1240

def allPairTime03SpecialEvenBranchMass (q : Nat) : Nat :=
  24 * q + 23

def allPairTime03HighEvenBranchMass (q : Nat) : Nat :=
  864 * q ^ 3 + 2076 * q ^ 2 + 1658 * q + 440

def allPairTime03LowOddBranchMass (q : Nat) : Nat :=
  432 * q ^ 3 + 1068 * q ^ 2 + 872 * q + 235

def allPairTime03HighOddBranchMass (q : Nat) : Nat :=
  1296 * q ^ 3 + 3252 * q ^ 2 + 2728 * q + 765

def allPairTime03OddLowClock (q i : Nat) : Nat :=
  144 * q ^ 2 + 228 * q + 87 -
    i * (modulus q + 6) +
      if 2 * q + 2 ≤ i then modulus q else 0

def allPairTime03OddHighClock (q i : Nat) : Nat :=
  288 * q ^ 2 + 480 * q + 197 -
    i * (modulus q + 6) +
      if third q ≤ i then modulus q else 0

def allPairTime03EvenLowClock (q i : Nat) : Nat :=
  576 * q ^ 2 + 936 * q + 374 -
    i * (2 * modulus q + 6) +
      if third q ≤ i then modulus q else 0

def allPairTime03EvenSpecialClock (q : Nat) : Nat :=
  modulus q + 3

def allPairTime03EvenHighClock (q i : Nat) : Nat :=
  288 * q ^ 2 + 444 * q + 164 -
    i * (2 * modulus q + 6) +
      if 2 * q + 1 ≤ i then modulus q else 0

theorem allPairTime03SpecialEvenBranchMass_eq_special_clock (q : Nat) :
    allPairTime03SpecialEvenBranchMass q =
      allPairTime03EvenSpecialClock q := by
  simp [allPairTime03SpecialEvenBranchMass, allPairTime03EvenSpecialClock,
    modulus]

def allPairTime03BoundaryClockBranchMassTotal (q : Nat) : Nat :=
  allPairTime03LowEvenBranchMass q +
  allPairTime03SpecialEvenBranchMass q +
  allPairTime03HighEvenBranchMass q +
  allPairTime03LowOddBranchMass q +
  allPairTime03HighOddBranchMass q

theorem allPairTime03BoundaryClockBranchMassTotal_eq_target (q : Nat) :
    allPairTime03BoundaryClockBranchMassTotal q = allPairTime03Target q := by
  simp [allPairTime03BoundaryClockBranchMassTotal,
    allPairTime03LowEvenBranchMass, allPairTime03SpecialEvenBranchMass,
    allPairTime03HighEvenBranchMass, allPairTime03LowOddBranchMass,
    allPairTime03HighOddBranchMass, allPairTime03Target]
  ring

/-!
`04` boundary-clock branch masses recovered from the same exact all-pair
samples.  The even lane has a pointwise clock formula `m * a / 2`; the odd
lanes are currently recorded by destination class (`01`, `13`, and the two
`34` ties).  These remain aggregate clock targets until the odd pointwise
derivation is formalized.
-/

def allPairTime04EvenBranchMass (q : Nat) : Nat :=
  1728 * q ^ 3 + 4176 * q ^ 2 + 3360 * q + 900

def allPairTime04EvenClock (q i : Nat) : Nat :=
  modulus q * (i + 1)

def boundaryClockTime03Formula (q k : Nat) : Nat :=
  if k = half q then
    allPairTime03EvenSpecialClock q
  else if k % 2 = 1 then
    if k < half q then
      allPairTime03OddLowClock q ((k - 1) / 2)
    else
      allPairTime03OddHighClock q ((k - (half q + 1)) / 2)
  else if k < half q then
    allPairTime03EvenLowClock q ((k - 2) / 2)
  else
    allPairTime03EvenHighClock q ((k - (half q + 2)) / 2)

def allPairTime04OddTo01BranchMass (q : Nat) : Nat :=
  1728 * q ^ 3 + 3834 * q ^ 2 + 2829 * q + 698

def allPairTime04OddTo13BranchMass (q : Nat) : Nat :=
  1728 * q ^ 3 + 3888 * q ^ 2 + 2886 * q + 708

def allPairTime04OddTo34BranchMass (q : Nat) : Nat :=
  24 * q + 29

def allPairTime04ModOneBranchMass (q : Nat) : Nat :=
  1728 * q ^ 3 + 3834 * q ^ 2 + 2829 * q + 701

def allPairTime04ModThreeBranchMass (q : Nat) : Nat :=
  1728 * q ^ 3 + 3888 * q ^ 2 + 2910 * q + 734

def allPairTime04OddHSubOneClock (_q : Nat) : Nat :=
  3

def allPairTime04OddLastClock (q : Nat) : Nat :=
  modulus q + 6

def allPairTime04ModOneLowCorrection (q s : Nat) : Nat :=
  (if q < s then quarter q else 0) +
    if 2 * q + 1 < s then modulus q + quarter q else 0

def allPairTime04ModOneHighCorrection (q s : Nat) : Nat :=
  (if 4 * q + 2 < s then quarter q else 0) +
  (if 4 * q + 3 < s then modulus q else 0) +
    if 5 * q + 3 < s then quarter q else 0

def allPairTime04ModOneClock (q s : Nat) : Nat :=
  if s = 3 * q + 2 then
    allPairTime04OddHSubOneClock q
  else if s < 3 * q + 2 then
    6 + s * (4 * modulus q + 18) -
      allPairTime04ModOneLowCorrection q s
  else
    288 * q ^ 2 + 540 * q + 265 +
      (s - (3 * q + 3)) * (4 * modulus q + 18) -
        allPairTime04ModOneHighCorrection q s

def allPairTime04ModThreeDefectCount (q s : Nat) : Nat :=
  (if q - 1 < s then 1 else 0) +
  (if 2 * q < s then 1 else 0) +
  (if 3 * q + 1 < s then 1 else 0) +
  (if 4 * q + 2 < s then 1 else 0) +
    if 5 * q + 3 < s then 1 else 0

def allPairTime04ModThreeClock (q s : Nat) : Nat :=
  if s = quarter q - 1 then
    allPairTime04OddLastClock q
  else
    60 * q + 71 + s * (4 * modulus q + 24) -
      modulus q * allPairTime04ModThreeDefectCount q s

def boundaryClockTime04Formula (q k : Nat) : Nat :=
  if k % 2 = 0 then
    allPairTime04EvenClock q (k / 2 - 1)
  else if k % 4 = 1 then
    allPairTime04ModOneClock q (k / 4)
  else
    allPairTime04ModThreeClock q (k / 4)

theorem two_mul_allPairTime04EvenBranchMass_eq_even_clock_sum_closed
    (q : Nat) :
    2 * allPairTime04EvenBranchMass q =
      modulus q * half q * (half q - 1) := by
  have hsub : half q - 1 = 12 * q + 9 := by
    simp [half]
  rw [hsub]
  simp [allPairTime04EvenBranchMass, modulus, half]
  ring

theorem allPairTime04OddTo34BranchMass_eq_special_clock_sum
    (q : Nat) :
    allPairTime04OddTo34BranchMass q =
      allPairTime04OddHSubOneClock q + allPairTime04OddLastClock q := by
  simp [allPairTime04OddTo34BranchMass, allPairTime04OddHSubOneClock,
    allPairTime04OddLastClock, modulus]
  ring

theorem allPairTime04OddDestinationBranchMass_eq_modClassBranchMass
    (q : Nat) :
    allPairTime04OddTo01BranchMass q +
        allPairTime04OddTo13BranchMass q +
        allPairTime04OddTo34BranchMass q =
      allPairTime04ModOneBranchMass q +
        allPairTime04ModThreeBranchMass q := by
  simp [allPairTime04OddTo01BranchMass, allPairTime04OddTo13BranchMass,
    allPairTime04OddTo34BranchMass, allPairTime04ModOneBranchMass,
    allPairTime04ModThreeBranchMass]
  ring

def allPairTime04BoundaryClockBranchMassTotal (q : Nat) : Nat :=
  allPairTime04EvenBranchMass q +
  allPairTime04OddTo01BranchMass q +
  allPairTime04OddTo13BranchMass q +
  allPairTime04OddTo34BranchMass q

def allPairTime04BoundaryClockModClassMassTotal (q : Nat) : Nat :=
  allPairTime04EvenBranchMass q +
  allPairTime04ModOneBranchMass q +
  allPairTime04ModThreeBranchMass q

theorem allPairTime04BoundaryClockBranchMassTotal_eq_modClassTotal
    (q : Nat) :
    allPairTime04BoundaryClockBranchMassTotal q =
      allPairTime04BoundaryClockModClassMassTotal q := by
  simp [allPairTime04BoundaryClockBranchMassTotal,
    allPairTime04BoundaryClockModClassMassTotal,
    allPairTime04EvenBranchMass, allPairTime04OddTo01BranchMass,
    allPairTime04OddTo13BranchMass, allPairTime04OddTo34BranchMass,
    allPairTime04ModOneBranchMass, allPairTime04ModThreeBranchMass]
  ring

theorem allPairTime04BoundaryClockBranchMassTotal_eq_target (q : Nat) :
    allPairTime04BoundaryClockBranchMassTotal q = allPairTime04Target q := by
  simp [allPairTime04BoundaryClockBranchMassTotal,
    allPairTime04EvenBranchMass, allPairTime04OddTo01BranchMass,
    allPairTime04OddTo13BranchMass, allPairTime04OddTo34BranchMass,
    allPairTime04Target]
  ring

theorem allPairTime04BoundaryClockModClassMassTotal_eq_target (q : Nat) :
    allPairTime04BoundaryClockModClassMassTotal q = allPairTime04Target q := by
  rw [← allPairTime04BoundaryClockBranchMassTotal_eq_modClassTotal]
  exact allPairTime04BoundaryClockBranchMassTotal_eq_target q

def allPairTime0304BoundaryClockBranchMassTotal (q : Nat) : Nat :=
  allPairTime03BoundaryClockBranchMassTotal q +
  allPairTime04BoundaryClockBranchMassTotal q

theorem allPairTime0304BoundaryClockBranchMassTotal_eq_target_sum
    (q : Nat) :
    allPairTime0304BoundaryClockBranchMassTotal q =
      allPairTime03Target q + allPairTime04Target q := by
  simp [allPairTime0304BoundaryClockBranchMassTotal,
    allPairTime03BoundaryClockBranchMassTotal_eq_target,
    allPairTime04BoundaryClockBranchMassTotal_eq_target]

-- The v3.6 draft displays the `q` coefficient as `19079`; adding the two
-- target polynomials gives `19179`, which is also forced by total time mass.
theorem allPairTime03Target_add_allPairTime04Target (q : Nat) :
    allPairTime03Target q + allPairTime04Target q =
      10368 * q ^ 3 + 24426 * q ^ 2 + 19179 * q + 5038 := by
  simp [allPairTime03Target, allPairTime04Target]
  ring

theorem allPairTime03Target_add_allPairTime04Target_v36_draft_defect
    (q : Nat) :
    allPairTime03Target q + allPairTime04Target q =
      (10368 * q ^ 3 + 24426 * q ^ 2 + 19079 * q + 5038) +
        100 * q := by
  simp [allPairTime03Target, allPairTime04Target]
  ring

theorem allPairTime03Target_add_allPairTime04Target_ne_v36_draft
    (q : Nat) (hq : 0 < q) :
    allPairTime03Target q + allPairTime04Target q ≠
      10368 * q ^ 3 + 24426 * q ^ 2 + 19079 * q + 5038 := by
  intro h
  have hdefect :=
    allPairTime03Target_add_allPairTime04Target_v36_draft_defect q
  omega

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

def allPairLabelDstTimeMassTarget (q : Nat) :
    RouteEB20.AllPairLabel × RouteEB20.AllPairLabel → Nat
  | (.Z, .L13) => 24 * q + 15
  | (.L01, .L01) => 72 * q ^ 2 + 96 * q + 32
  | (.L01, .L03) => 45 * q ^ 2 + 54 * q + 16
  | (.L01, .L13) => 45 * q ^ 2 + 54 * q + 16
  | (.L01, .Z) => 12 * q + 8
  | (.L02, .L24) =>
      6912 * q ^ 3 + 13536 * q ^ 2 + 8832 * q + 1920
  | (.L03, .L04) =>
      1728 * q ^ 3 + 3528 * q ^ 2 + 2400 * q + 544
  | (.L03, .L14) =>
      1728 * q ^ 3 + 3456 * q ^ 2 + 2304 * q + 512
  | (.L03, .L34) => 432 * q ^ 3 + 786 * q ^ 2 + 467 * q + 90
  | (.L04, .L01) =>
      1008 * q ^ 3 + 1827 * q ^ 2 + 1091 * q + 214
  | (.L04, .L13) => 720 * q ^ 3 + 1440 * q ^ 2 + 967 * q + 218
  | (.L04, .L14) =>
      1728 * q ^ 3 + 3312 * q ^ 2 + 2112 * q + 448
  | (.L04, .L34) => 432 * q ^ 3 + 882 * q ^ 2 + 597 * q + 134
  | (.L12, .L03) => 12 * q + 7
  | (.L12, .L12) => 576 * q ^ 2 + 720 * q + 224
  | (.L13, .L01) => 45 * q ^ 2 + 66 * q + 24
  | (.L13, .L03) => 162 * q ^ 2 + 204 * q + 65
  | (.L14, .L02) =>
      54144 * q ^ 4 + 142368 * q ^ 3 + 140832 * q ^ 2 +
        62112 * q + 10304
  | (.L14, .L23) =>
      58752 * q ^ 4 + 153408 * q ^ 3 + 149986 * q ^ 2 +
        65078 * q + 10574
  | (.L23, .L02) =>
      52992 * q ^ 4 + 139680 * q ^ 3 + 137726 * q ^ 2 +
        60202 * q + 9842
  | (.L23, .L04) =>
      8640 * q ^ 4 + 19416 * q ^ 3 + 15633 * q ^ 2 +
        5206 * q + 569
  | (.L23, .L13) =>
      50112 * q ^ 4 + 128808 * q ^ 3 + 123861 * q ^ 2 +
        52803 * q + 8420
  | (.L24, .L04) =>
      27072 * q ^ 4 + 74640 * q ^ 3 + 77256 * q ^ 2 +
        35544 * q + 6128
  | (.L24, .L12) => 24 * q + 16
  | (.L24, .L13) =>
      27072 * q ^ 4 + 74112 * q ^ 3 + 75876 * q ^ 2 +
        34429 * q + 5842
  | (.L24, .L23) =>
      52992 * q ^ 4 + 135024 * q ^ 3 + 128718 * q ^ 2 +
        54406 * q + 8602
  | (.L34, .L01) => 432 * q ^ 3 + 822 * q ^ 2 + 509 * q + 102
  | (.L34, .L04) => 432 * q ^ 3 + 882 * q ^ 2 + 603 * q + 138
  | (.L34, .L34) =>
      1728 * q ^ 3 + 3432 * q ^ 2 + 2288 * q + 512
  | _ => 0

theorem allPairLabelDstTimeMassTarget_sum_by_src (q : Nat) :
    ∀ src : RouteEB20.AllPairLabel,
      Finset.univ.sum (fun dst : RouteEB20.AllPairLabel =>
        allPairLabelDstTimeMassTarget q (src, dst)) =
          allPairTimeMassTarget q src := by
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
  intro src
  rw [huniv]
  fin_cases src <;>
    simp [allPairLabelDstTimeMassTarget, allPairTimeMassTarget,
      allPairTimeZTarget, allPairTime01Target, allPairTime02Target,
      allPairTime03Target, allPairTime04Target, allPairTime12Target,
      allPairTime13Target, allPairTime14Target, allPairTime23Target,
      allPairTime24Target, allPairTime34Target] <;>
    ring

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

def allPairLabelDstTimeMassTarget (k : Nat) :
    RouteEB20.AllPairLabel × RouteEB20.AllPairLabel → Nat
  | (.Z, .L03) => 2
  | (.L01, .L01) => 576 * k ^ 2 + 312 * k + 42
  | (.L01, .L03) => 1
  | (.L01, .L13) => 288 * k ^ 2 + 156 * k + 21
  | (.L02, .L24) =>
      55296 * k ^ 3 + 47232 * k ^ 2 + 13440 * k + 1274
  | (.L03, .L04) => 432 * k ^ 2 + 236 * k + 32
  | (.L03, .L14) =>
      10944 * k ^ 3 + 9360 * k ^ 2 + 2680 * k + 257
  | (.L03, .L34) => 224 * k ^ 2 + 120 * k + 16
  | (.L04, .L03) =>
      27648 * k ^ 3 + 22704 * k ^ 2 + 6220 * k + 568
  | (.L04, .L14) =>
      13824 * k ^ 3 + 11520 * k ^ 2 + 3192 * k + 294
  | (.L04, .L34) =>
      18432 * k ^ 3 + 16208 * k ^ 2 + 4740 * k + 461
  | (.L12, .L12) => 2304 * k ^ 2 + 1248 * k + 168
  | (.L12, .L13) => 48 * k + 14
  | (.L13, .L01) => 288 * k ^ 2 + 156 * k + 21
  | (.L13, .L03) => 3
  | (.L13, .L13) => 1152 * k ^ 2 + 576 * k + 70
  | (.L14, .L02) =>
      829440 * k ^ 4 + 905472 * k ^ 3 + 368640 * k ^ 2 +
        66240 * k + 4424
  | (.L14, .L23) =>
      995328 * k ^ 4 + 1137024 * k ^ 3 + 487368 * k ^ 2 +
        92952 * k + 6660
  | (.L23, .L02) =>
      829440 * k ^ 4 + 998784 * k ^ 3 + 450360 * k ^ 2 +
        90120 * k + 6752
  | (.L23, .L03) =>
      677376 * k ^ 4 + 725184 * k ^ 3 + 284313 * k ^ 2 +
        47989 * k + 2902
  | (.L23, .L04) =>
      55296 * k ^ 4 + 55296 * k ^ 3 + 18372 * k ^ 2 + 2028 * k
  | (.L23, .L34) =>
      262656 * k ^ 4 + 318528 * k ^ 3 + 149595 * k ^ 2 +
        32275 * k + 2692
  | (.L24, .L03) =>
      214272 * k ^ 4 + 183456 * k ^ 3 + 52038 * k ^ 2 + 4893 * k
  | (.L24, .L04) =>
      138240 * k ^ 4 + 183168 * k ^ 3 + 90336 * k ^ 2 +
        19668 * k + 1596
  | (.L24, .L12) => 48 * k + 14
  | (.L24, .L23) =>
      829440 * k ^ 4 + 960768 * k ^ 3 + 417384 * k ^ 2 +
        80592 * k + 5835
  | (.L24, .L34) =>
      476928 * k ^ 4 + 587232 * k ^ 3 + 267866 * k ^ 2 +
        53555 * k + 3951
  | (.L34, .L01) => 16 * k + 5
  | (.L34, .L03) => 9216 * k ^ 3 + 6752 * k ^ 2 + 1584 * k + 111
  | (.L34, .L04) => 464 * k ^ 2 + 300 * k + 48
  | (.L34, .L13) => 1152 * k ^ 2 + 672 * k + 98
  | (.L34, .L14) => 2880 * k ^ 3 + 2576 * k ^ 2 + 760 * k + 74
  | (.L34, .Z) => 32 * k + 10
  | _ => 0

theorem allPairLabelDstTimeMassTarget_sum_by_src (k : Nat) :
    ∀ src : RouteEB20.AllPairLabel,
      Finset.univ.sum (fun dst : RouteEB20.AllPairLabel =>
        allPairLabelDstTimeMassTarget k (src, dst)) =
          allPairTimeMassTarget k src := by
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
  intro src
  rw [huniv]
  fin_cases src <;>
    simp [allPairLabelDstTimeMassTarget, allPairTimeMassTarget,
      allPairTimeZTarget, allPairTime01Target, allPairTime02Target,
      allPairTime03Target, allPairTime04Target, allPairTime12Target,
      allPairTime13Target, allPairTime14Target, allPairTime23Target,
      allPairTime24Target, allPairTime34Target] <;>
    ring

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

def routeEBoundaryMacroBase {m : Nat}
    {p : RouteENonzeroSeam m → Prop}
    (x : Unit ⊕ { a : RouteENonzeroSeam m // p a }) :
    RouteEBoundaryNode m :=
  match x with
  | Sum.inl _ => routeEBoundaryZero
  | Sum.inr a => routeEBoundaryNode RouteEBoundaryLabel.L34 a.1

theorem routeEBoundaryMacroBase_injective {m : Nat}
    {p : RouteENonzeroSeam m → Prop} :
    Function.Injective (routeEBoundaryMacroBase (m := m) (p := p)) := by
  intro x y h
  cases x <;> cases y
  · rfl
  · cases h
  · cases h
  · apply congrArg Sum.inr
    apply Subtype.ext
    injection h with hpair
    exact congrArg Prod.snd hpair

/--
Generic boundary first-return adapter.  If a boundary quotient `Q` has a
smaller first-return section whose return map is one cycle and whose excursions
cover the whole boundary by cardinality, then `Q` itself is one cycle.
-/
structure RouteEBoundaryFirstReturnTarget (m : Nat) [NeZero m]
    (sigma : Type*) [Fintype sigma] where
  Q : RouteEBoundaryNode m → RouteEBoundaryNode m
  Q_bijective : Function.Bijective Q
  base : sigma → RouteEBoundaryNode m
  base_injective : Function.Injective base
  next : sigma → sigma
  time : sigma → Nat
  time_pos : ∀ x, 0 < time x
  firstReturn_equation :
    ∀ x, Q^[time x] (base x) = base (next x)
  firstReturn_minimal :
    ∀ x k, 0 < k → k < time x →
      ¬ ∃ y, Q^[k] (base x) = base y
  next_single : IsSingleCycleMap next
  time_sum :
    Finset.univ.sum time = Fintype.card (RouteEBoundaryNode m)

namespace RouteEBoundaryFirstReturnTarget

theorem boundaryMap_singleCycle {m : Nat} [NeZero m]
    {sigma : Type*} [Fintype sigma]
    (target : RouteEBoundaryFirstReturnTarget m sigma) :
    IsSingleCycleMap target.Q :=
  single_cycle_of_first_return_sum target.Q target.base target.next target.time
    target.Q_bijective target.base_injective target.firstReturn_equation
    target.firstReturn_minimal target.next_single target.time_sum

end RouteEBoundaryFirstReturnTarget

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

/--
Boundary-clock mass endpoint for the two B20 labels still isolated by the
v3.6 bundle.  An eventual clock derivation should instantiate `time03` and
`time04` pointwise; this adapter then feeds their sums into the existing
all-pair exhaustion arithmetic.
-/
structure BoundaryClockMassTarget (q : Nat) where
  time03 : RouteENonzeroSeam (modulus q) → Nat
  time04 : RouteENonzeroSeam (modulus q) → Nat
  time03_pos : ∀ a, 0 < time03 a
  time04_pos : ∀ a, 0 < time04 a
  time03_sum : Finset.univ.sum time03 = allPairTime03Target q
  time04_sum : Finset.univ.sum time04 = allPairTime04Target q

/--
Pointwise symbolic formulas for the B20 boundary clocks.  The closure package
uses these formulas only for the stable range `q > 0`; the exceptional `q = 0`
row remains the separate finite `m = 20` target.
-/
structure BoundaryClockPointwiseFormulaTarget (q : Nat) where
  hq : 0 < q
  time03 : RouteENonzeroSeam (modulus q) → Nat
  time04 : RouteENonzeroSeam (modulus q) → Nat
  time03_eq_formula :
    ∀ a, time03 a = boundaryClockTime03Formula q a.1.val
  time04_eq_formula :
    ∀ a, time04 a = boundaryClockTime04Formula q a.1.val

/--
Symbolic B20 boundary-clock endpoint after the pointwise formulas have been
matched to actual return clocks and summed.
-/
structure BoundaryClockSymbolicMassTarget (q : Nat) where
  pointwise : BoundaryClockPointwiseFormulaTarget q
  time03_pos : ∀ a, 0 < pointwise.time03 a
  time04_pos : ∀ a, 0 < pointwise.time04 a
  time03_sum : Finset.univ.sum pointwise.time03 = allPairTime03Target q
  time04_sum : Finset.univ.sum pointwise.time04 = allPairTime04Target q

def BoundaryClockSymbolicMassTarget.toBoundaryClockMassTarget {q : Nat}
    (target : BoundaryClockSymbolicMassTarget q) :
    BoundaryClockMassTarget q where
  time03 := target.pointwise.time03
  time04 := target.pointwise.time04
  time03_pos := target.time03_pos
  time04_pos := target.time04_pos
  time03_sum := target.time03_sum
  time04_sum := target.time04_sum

def SymbolicBoundaryClockFamilyTarget : Prop :=
  ∀ q, 0 < q → Nonempty (BoundaryClockSymbolicMassTarget q)

def allPairTimeMassFromBoundaryClocks (q : Nat)
    (target : BoundaryClockMassTarget q) : AllPairLabel → Nat
  | AllPairLabel.Z => allPairTimeZ q
  | AllPairLabel.L01 => allPairTime01 q
  | AllPairLabel.L02 => allPairTime02 q
  | AllPairLabel.L03 => Finset.univ.sum target.time03
  | AllPairLabel.L04 => Finset.univ.sum target.time04
  | AllPairLabel.L12 => allPairTime12 q
  | AllPairLabel.L13 => allPairTime13 q
  | AllPairLabel.L14 => allPairTime14 q
  | AllPairLabel.L23 => allPairTime23 q
  | AllPairLabel.L24 => allPairTime24 q
  | AllPairLabel.L34 => allPairTime34 q

theorem allPairTimeMassFromBoundaryClocks_eq (q : Nat)
    (target : BoundaryClockMassTarget q) :
    allPairTimeMassFromBoundaryClocks q target = allPairTimeMass q := by
  funext label
  cases label <;>
    simp [allPairTimeMassFromBoundaryClocks, allPairTimeMass,
      target.time03_sum, target.time04_sum]

theorem allPairTimeMassFromBoundaryClocks_sum_eq_modulus_pow_four
    (q : Nat) (target : BoundaryClockMassTarget q) :
    Finset.univ.sum (allPairTimeMassFromBoundaryClocks q target) =
      modulus q ^ 4 := by
  rw [allPairTimeMassFromBoundaryClocks_eq q target]
  exact allPairTimeMass_sum_eq_modulus_pow_four q

theorem allPairTimeMassFromSymbolicBoundaryClocks_sum_eq_modulus_pow_four
    (q : Nat) (target : BoundaryClockSymbolicMassTarget q) :
    Finset.univ.sum
        (allPairTimeMassFromBoundaryClocks q
          target.toBoundaryClockMassTarget) =
      modulus q ^ 4 :=
  allPairTimeMassFromBoundaryClocks_sum_eq_modulus_pow_four q
    target.toBoundaryClockMassTarget

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

theorem boundarySpineCValue_succ (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i + 1 ≤ half q + 2) :
    boundarySpineCValue q (i + 1) =
      boundarySpineCValue q i - 1 := by
  simp [boundarySpineCValue, half, modulus] at hhi ⊢
  omega

theorem boundarySpineCParam_pred_eq (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i ≤ half q + 2)
    (hnext : i + 1 ≤ half q + 2)
    (hnot_one :
      (boundarySpineCParam q i hlo hhi).1.val ≠ 1) :
    boundaryPredParam q (boundarySpineCParam q i hlo hhi) hnot_one =
      boundarySpineCParam q (i + 1) (by omega) hnext := by
  apply Subtype.ext
  rw [boundaryPredParam_val]
  change (((boundarySpineCValue q i : Nat) : ZMod (modulus q)) - 1) =
    ((boundarySpineCValue q (i + 1) : Nat) : ZMod (modulus q))
  rw [boundarySpineCValue_succ q i hlo hnext]
  rw [Nat.cast_pred
    (R := ZMod (modulus q))
    (boundarySpineCValue_range q i hlo hhi).1]

theorem boundarySpineCValue_last (q : Nat) :
    boundarySpineCValue q (half q + 2) = half q := by
  simp [boundarySpineCValue, half, modulus]
  omega

theorem boundarySpineCParam_last_eq_half (q : Nat)
    (hlo : 5 ≤ half q + 2)
    (hhi : half q + 2 ≤ half q + 2) :
    boundarySpineCParam q (half q + 2) hlo hhi =
      boundaryParamHalf q := by
  apply Subtype.ext
  apply ZMod.val_injective (modulus q)
  rw [boundarySpineCParam_val, boundaryParamHalf, RouteENonzeroSeam.ofNat_val,
    boundarySpineCValue_last]

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

theorem boundaryCycleSpineNode_C_run (q i : Nat)
    (hlo : 5 ≤ i) (hhi : i ≤ half q + 2)
    (hi : i < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q i hi =
      routeEBoundaryNode RouteEBoundaryLabel.L34
        (boundarySpineCParam q i hlo hhi) := by
  have hnot0 : ¬ i = 0 := by omega
  have hnot1 : ¬ i = 1 := by omega
  have hnot2 : ¬ i = 2 := by omega
  have hnot3 : ¬ i = 3 := by omega
  have hnot4 : ¬ i = 4 := by omega
  have hnotLast : ¬ i = half q + 3 := by omega
  simp [boundaryCycleSpineNode, hnot0, hnot1, hnot2, hnot3, hnot4,
    hnotLast]

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

theorem boundaryParamPenultimate_pred_eq_spine_five (q : Nat)
    (hnot_one : (boundaryParamPenultimate q).1.val ≠ 1) :
    boundaryPredParam q (boundaryParamPenultimate q) hnot_one =
      boundarySpineCParam q 5 (by omega) (by simp [half]) := by
  apply Subtype.ext
  rw [boundaryPredParam_val]
  change (((modulus q - 2 : Nat) : ZMod (modulus q)) - 1) =
    ((boundarySpineCValue q 5 : Nat) : ZMod (modulus q))
  have hval :
      boundarySpineCValue q 5 = (modulus q - 2) - 1 := by
    simp [boundarySpineCValue, modulus]
  rw [hval]
  rw [Nat.cast_pred (R := ZMod (modulus q)) (by simp [modulus])]

set_option linter.flexible false in
theorem boundaryCycleSpine_step_four (q : Nat)
    (h4 : 4 < boundaryCycleSpineCount q)
    (h5 : 5 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q 4 h4) =
      boundaryCycleSpineNode q 5 h5 := by
  rw [boundaryCycleSpineNode_four q h4,
    boundaryCycleSpineNode_C_run q 5 (by omega) (by simp [half]) h5]
  let a := boundaryParamPenultimate q
  have hnot_one : a.1.val ≠ 1 := by
    dsimp [a]
    simp [boundaryParamPenultimate, RouteENonzeroSeam.ofNat_val, modulus]
  have hnot_h : a.1.val ≠ half q := by
    dsimp [a]
    simp [boundaryParamPenultimate, RouteENonzeroSeam.ofNat_val, half,
      modulus]
    omega
  have hnot_last : a.1.val ≠ modulus q - 1 := by
    dsimp [a]
    simp [boundaryParamPenultimate, RouteENonzeroSeam.ofNat_val, modulus]
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundaryPredParam q a hnot_one) :=
      boundaryQuotient_C_generic q a hnot_one hnot_h hnot_last
    _ = routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundarySpineCParam q 5 (by omega) (by simp [half])) := by
      rw [boundaryParamPenultimate_pred_eq_spine_five q hnot_one]

theorem boundaryCycleSpine_step_C_run (q i : Nat)
    (hlo : 5 ≤ i) (hnext : i + 1 ≤ half q + 2)
    (hi : i < boundaryCycleSpineCount q)
    (his : i + 1 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q i hi) =
      boundaryCycleSpineNode q (i + 1) his := by
  have hhi : i ≤ half q + 2 := by omega
  rw [boundaryCycleSpineNode_C_run q i hlo hhi hi,
    boundaryCycleSpineNode_C_run q (i + 1) (by omega) hnext his]
  let a := boundarySpineCParam q i hlo hhi
  have hnot_one : a.1.val ≠ 1 := by
    dsimp [a]
    rw [boundarySpineCParam_val]
    have hrange := boundarySpineCValue_range q i hlo hhi
    simp [boundarySpineCValue, half, modulus] at hnext ⊢
    omega
  have hnot_h : a.1.val ≠ half q := by
    dsimp [a]
    rw [boundarySpineCParam_val]
    simp [boundarySpineCValue, half, modulus] at hnext ⊢
    omega
  have hnot_last : a.1.val ≠ modulus q - 1 := by
    dsimp [a]
    rw [boundarySpineCParam_val]
    simp [boundarySpineCValue, modulus] at hlo ⊢
    omega
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundaryPredParam q a hnot_one) :=
      boundaryQuotient_C_generic q a hnot_one hnot_h hnot_last
    _ = routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundarySpineCParam q (i + 1) (by omega) hnext) := by
      rw [boundarySpineCParam_pred_eq q i hlo hhi hnext hnot_one]

theorem boundaryCycleSpine_step_C_last (q : Nat)
    (hi : half q + 2 < boundaryCycleSpineCount q)
    (his : half q + 3 < boundaryCycleSpineCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q (half q + 2) hi) =
      boundaryCycleSpineNode q (half q + 3) his := by
  rw [boundaryCycleSpineNode_C_run q (half q + 2) (by simp [half])
      (by omega) hi]
  have hlast :
      boundaryCycleSpineNode q (half q + 3) his =
        routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamHalf q) := by
    have hnot1 : ¬ half q + 3 = 1 := by simp [half]
    have hnot2 : ¬ half q + 3 = 2 := by simp [half]
    have hhalf_ne_zero : ¬ half q = 0 := by simp [half]
    have hnot4 : ¬ half q + 3 = 4 := by simp [half]
    simp [boundaryCycleSpineNode, hnot1, hnot2, hhalf_ne_zero, hnot4]
  rw [hlast]
  have hparam :
      boundarySpineCParam q (half q + 2) (by simp [half]) (by omega) =
        boundaryParamHalf q :=
    boundarySpineCParam_last_eq_half q (by simp [half]) (by omega)
  rw [hparam]
  exact boundaryQuotient_C_h q (boundaryParamHalf q) (by
    simp [boundaryParamHalf, RouteENonzeroSeam.ofNat_val])

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

def boundaryCycleFirstEvenTailIndex (k : Nat) : Nat :=
  k / 2 + 1

theorem boundaryCycleFirstEvenTailIndex_pos (k : Nat) :
    1 ≤ boundaryCycleFirstEvenTailIndex k := by
  simp [boundaryCycleFirstEvenTailIndex]

theorem boundaryCycleFirstEvenTailIndex_lt (q k : Nat)
    (hk : k < boundaryCycleFirstEvenTailCount q) :
    boundaryCycleFirstEvenTailIndex k < quarter q := by
  simp [boundaryCycleFirstEvenTailIndex, boundaryCycleFirstEvenTailCount,
    quarter] at hk ⊢
  omega

theorem boundaryCycleFirstEvenTailIndex_succ_of_even (k : Nat)
    (heven : k % 2 = 0) :
    boundaryCycleFirstEvenTailIndex (k + 1) =
      boundaryCycleFirstEvenTailIndex k := by
  simp [boundaryCycleFirstEvenTailIndex]
  omega

theorem boundaryCycleFirstEvenTailIndex_succ_of_odd (k : Nat)
    (hodd : k % 2 ≠ 0) :
    boundaryCycleFirstEvenTailIndex (k + 1) =
      boundaryCycleFirstEvenTailIndex k + 1 := by
  simp [boundaryCycleFirstEvenTailIndex]
  omega

theorem boundaryFirstEvenValue_even (q j : Nat) :
    boundaryFirstEvenValue q j % 2 = 0 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstEvenValue, hpar, half]
    omega
  · simp [boundaryFirstEvenValue, hpar, modulus]
    omega

theorem boundaryFirstEvenParam_even (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstEvenParam q j hjpos hjlt).1.val % 2 = 0 := by
  rw [boundaryFirstEvenParam_val]
  exact boundaryFirstEvenValue_even q j

theorem boundaryFirstEvenValue_ne_half (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    boundaryFirstEvenValue q j ≠ half q := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstEvenValue, hpar, half]
    omega
  · simp [boundaryFirstEvenValue, hpar, half, modulus] at hjlt ⊢
    simp [quarter] at hjlt
    omega

theorem boundaryFirstEvenParam_ne_half (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstEvenParam q j hjpos hjlt).1.val ≠ half q := by
  rw [boundaryFirstEvenParam_val]
  exact boundaryFirstEvenValue_ne_half q j hjpos hjlt

theorem boundaryFirstEvenValue_ne_two_of_succ (q j : Nat)
    (_hjpos : 1 ≤ j) (hjnext : j + 1 < quarter q) :
    boundaryFirstEvenValue q j ≠ 2 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstEvenValue, hpar, half]
    simp [quarter] at hjnext
    omega
  · simp [boundaryFirstEvenValue, hpar, modulus]
    simp [quarter] at hjnext
    omega

theorem boundaryFirstEvenParam_ne_two_of_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q) :
    (boundaryFirstEvenParam q j hjpos hjlt).1.val ≠ 2 := by
  rw [boundaryFirstEvenParam_val]
  exact boundaryFirstEvenValue_ne_two_of_succ q j hjpos hjnext

theorem boundaryFirstEvenValue_ne_half_add_two_of_succ (q j : Nat)
    (_hjpos : 1 ≤ j) (hjnext : j + 1 < quarter q) :
    boundaryFirstEvenValue q j ≠ half q + 2 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstEvenValue, hpar, half]
    omega
  · simp [boundaryFirstEvenValue, hpar, half, modulus]
    simp [quarter] at hjnext
    omega

theorem boundaryFirstEvenParam_ne_half_add_two_of_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q) :
    (boundaryFirstEvenParam q j hjpos hjlt).1.val ≠ half q + 2 := by
  rw [boundaryFirstEvenParam_val]
  exact boundaryFirstEvenValue_ne_half_add_two_of_succ q j hjpos hjnext

theorem boundaryFirstEvenValue_shift_succ_zmod (q j : Nat)
    (_hjpos : 1 ≤ j) (hjnext : j + 1 < quarter q) :
    (((boundaryFirstEvenValue q j : Nat) : ZMod (modulus q)) +
        ((half q - 2 : Nat) : ZMod (modulus q))) =
      ((boundaryFirstEvenValue q (j + 1) : Nat) : ZMod (modulus q)) := by
  rw [← Nat.cast_add]
  by_cases hpar : j % 2 = 0
  · have hpar_next : (j + 1) % 2 ≠ 0 := by omega
    have hnat :
        boundaryFirstEvenValue q j + (half q - 2) =
          boundaryFirstEvenValue q (j + 1) := by
      simp [boundaryFirstEvenValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
  · have hpar_next : (j + 1) % 2 = 0 := by omega
    have hnat :
        boundaryFirstEvenValue q j + (half q - 2) =
          modulus q + boundaryFirstEvenValue q (j + 1) := by
      simp [boundaryFirstEvenValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
    simp

theorem boundaryFirstEvenParam_shift_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q)
    (hne : (boundaryFirstEvenParam q j hjpos hjlt).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundaryFirstEvenParam q j hjpos hjlt) hne =
      boundaryFirstEvenParam q (j + 1) (by omega) hjnext := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((boundaryFirstEvenValue q j : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundaryFirstEvenValue q (j + 1) : Nat) : ZMod (modulus q))
  exact boundaryFirstEvenValue_shift_succ_zmod q j hjpos hjnext

noncomputable def boundaryCycleFirstEvenTailNode (q k : Nat)
    (hk : k < boundaryCycleFirstEvenTailCount q) :
    RouteEBoundaryNode (modulus q) :=
  let j := boundaryCycleFirstEvenTailIndex k
  if _heven : k % 2 = 0 then
    routeEBoundaryNode RouteEBoundaryLabel.L03
      (boundaryFirstEvenParam q j
        (boundaryCycleFirstEvenTailIndex_pos k)
        (boundaryCycleFirstEvenTailIndex_lt q k hk))
  else
    routeEBoundaryNode RouteEBoundaryLabel.L04
      (boundaryFirstEvenParam q j
        (boundaryCycleFirstEvenTailIndex_pos k)
        (boundaryCycleFirstEvenTailIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleFirstEvenTail_step_even (q k : Nat)
    (hk : k < boundaryCycleFirstEvenTailCount q)
    (hks : k + 1 < boundaryCycleFirstEvenTailCount q)
    (heven : k % 2 = 0) :
    boundaryQuotient q (boundaryCycleFirstEvenTailNode q k hk) =
      boundaryCycleFirstEvenTailNode q (k + 1) hks := by
  have hnext_odd : ¬ (k + 1) % 2 = 0 := by omega
  simp [boundaryCycleFirstEvenTailNode, heven, hnext_odd,
    boundaryCycleFirstEvenTailIndex_succ_of_even k heven]
  exact boundaryQuotient_A_even q
    (boundaryFirstEvenParam q (boundaryCycleFirstEvenTailIndex k)
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk))
    (boundaryFirstEvenParam_ne_half q (boundaryCycleFirstEvenTailIndex k)
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk))
    (boundaryFirstEvenParam_even q (boundaryCycleFirstEvenTailIndex k)
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleFirstEvenTail_step_odd (q k : Nat)
    (hk : k < boundaryCycleFirstEvenTailCount q)
    (hks : k + 1 < boundaryCycleFirstEvenTailCount q)
    (hodd : k % 2 ≠ 0) :
    boundaryQuotient q (boundaryCycleFirstEvenTailNode q k hk) =
      boundaryCycleFirstEvenTailNode q (k + 1) hks := by
  have hnext_even : (k + 1) % 2 = 0 := by omega
  have hjnext : boundaryCycleFirstEvenTailIndex k + 1 < quarter q := by
    rw [← boundaryCycleFirstEvenTailIndex_succ_of_odd k hodd]
    exact boundaryCycleFirstEvenTailIndex_lt q (k + 1) hks
  simp [boundaryCycleFirstEvenTailNode, hodd, hnext_even,
    boundaryCycleFirstEvenTailIndex_succ_of_odd k hodd]
  let j := boundaryCycleFirstEvenTailIndex k
  let a := boundaryFirstEvenParam q j
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk)
  have hnot_two : a.1.val ≠ 2 := by
    dsimp [a, j]
    exact boundaryFirstEvenParam_ne_two_of_succ q
      (boundaryCycleFirstEvenTailIndex k)
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk)
      hjnext
  have hnot_close : a.1.val ≠ half q + 2 := by
    dsimp [a, j]
    exact boundaryFirstEvenParam_ne_half_add_two_of_succ q
      (boundaryCycleFirstEvenTailIndex k)
      (boundaryCycleFirstEvenTailIndex_pos k)
      (boundaryCycleFirstEvenTailIndex_lt q k hk)
      hjnext
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryShiftParam q a hnot_close) :=
      boundaryQuotient_B_even_shift q a hnot_two hnot_close
        (boundaryFirstEvenParam_even q j
          (boundaryCycleFirstEvenTailIndex_pos k)
          (boundaryCycleFirstEvenTailIndex_lt q k hk))
    _ = routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryFirstEvenParam q (j + 1) (by omega) hjnext) := by
      rw [boundaryFirstEvenParam_shift_succ q j
        (boundaryCycleFirstEvenTailIndex_pos k)
        (boundaryCycleFirstEvenTailIndex_lt q k hk) hjnext hnot_close]

theorem boundaryCycleSpineNode_last (q : Nat)
    (hi : half q + 3 < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q (half q + 3) hi =
      routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamHalf q) := by
  have hnot1 : ¬ half q + 3 = 1 := by simp [half]
  have hnot2 : ¬ half q + 3 = 2 := by simp [half]
  have hhalf_ne_zero : ¬ half q = 0 := by simp [half]
  have hnot4 : ¬ half q + 3 = 4 := by simp [half]
  simp [boundaryCycleSpineNode, hnot1, hnot2, hhalf_ne_zero, hnot4]

theorem boundaryCycleFirstEvenTailNode_zero (q : Nat)
    (hk : 0 < boundaryCycleFirstEvenTailCount q) :
    boundaryCycleFirstEvenTailNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryFirstEvenParam q 1 (by omega) (by simp [quarter])) := by
  simp [boundaryCycleFirstEvenTailNode, boundaryCycleFirstEvenTailIndex]

theorem boundaryParamHalf_shift_eq_firstEven_one (q : Nat)
    (hne : (boundaryParamHalf q).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundaryParamHalf q) hne =
      boundaryFirstEvenParam q 1 (by omega) (by simp [quarter]) := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((half q : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundaryFirstEvenValue q 1 : Nat) : ZMod (modulus q))
  rw [← Nat.cast_add]
  have hnat : half q + (half q - 2) = boundaryFirstEvenValue q 1 := by
    simp [boundaryFirstEvenValue, half, modulus]
    omega
  rw [hnat]

theorem boundaryCycleSpine_to_firstEvenTail (q : Nat)
    (hsp : half q + 3 < boundaryCycleSpineCount q)
    (htail : 0 < boundaryCycleFirstEvenTailCount q) :
    boundaryQuotient q (boundaryCycleSpineNode q (half q + 3) hsp) =
      boundaryCycleFirstEvenTailNode q 0 htail := by
  rw [boundaryCycleSpineNode_last q hsp,
    boundaryCycleFirstEvenTailNode_zero q htail]
  have hnot_two : (boundaryParamHalf q).1.val ≠ 2 := by
    simp [boundaryParamHalf, RouteENonzeroSeam.ofNat_val, half]
  have hnot_close : (boundaryParamHalf q).1.val ≠ half q + 2 := by
    simp [boundaryParamHalf, RouteENonzeroSeam.ofNat_val, half]
  calc
    boundaryQuotient q
        (routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamHalf q)) =
        routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryShiftParam q (boundaryParamHalf q) hnot_close) :=
      boundaryQuotient_B_even_shift q (boundaryParamHalf q) hnot_two hnot_close
        (by
          simp [boundaryParamHalf, RouteENonzeroSeam.ofNat_val, half]
          omega)
    _ = routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryFirstEvenParam q 1 (by omega) (by simp [quarter])) := by
      rw [boundaryParamHalf_shift_eq_firstEven_one q hnot_close]

noncomputable def boundaryCycleB2BridgeNode (q k : Nat)
    (_hk : k < boundaryCycleB2BridgeCount q) :
    RouteEBoundaryNode (modulus q) :=
  routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalfSubOne q)

theorem boundaryCycleFirstEvenTailLastIndex_eq (q : Nat) :
    boundaryCycleFirstEvenTailIndex (boundaryCycleFirstEvenTailCount q - 1) =
      quarter q - 1 := by
  simp [boundaryCycleFirstEvenTailIndex, boundaryCycleFirstEvenTailCount,
    quarter]
  omega

theorem boundaryCycleFirstEvenTailLast_odd (q : Nat) :
    (boundaryCycleFirstEvenTailCount q - 1) % 2 ≠ 0 := by
  simp [boundaryCycleFirstEvenTailCount, quarter]
  omega

theorem boundaryFirstEvenValue_last_eq_two (q : Nat) :
    boundaryFirstEvenValue q (quarter q - 1) = 2 := by
  have hpar : (quarter q - 1) % 2 = 0 := by
    simp [quarter]
    omega
  rw [boundaryFirstEvenValue, if_pos hpar]
  simp [quarter, half]
  omega

theorem boundaryFirstEvenParam_last_val_two (q : Nat) :
    (boundaryFirstEvenParam q (quarter q - 1) (by simp [quarter])
      (by simp [quarter])).1.val = 2 := by
  rw [boundaryFirstEvenParam_val]
  exact boundaryFirstEvenValue_last_eq_two q

set_option linter.flexible false in
theorem boundaryCycleFirstEvenTail_to_B2Bridge (q : Nat)
    (hlast : boundaryCycleFirstEvenTailCount q - 1 <
      boundaryCycleFirstEvenTailCount q)
    (hbridge : 0 < boundaryCycleB2BridgeCount q) :
    boundaryQuotient q
        (boundaryCycleFirstEvenTailNode q
          (boundaryCycleFirstEvenTailCount q - 1) hlast) =
      boundaryCycleB2BridgeNode q 0 hbridge := by
  have hodd := boundaryCycleFirstEvenTailLast_odd q
  simp [boundaryCycleFirstEvenTailNode, boundaryCycleB2BridgeNode, hodd,
    boundaryCycleFirstEvenTailLastIndex_eq q]
  exact boundaryQuotient_B_two q
    (boundaryFirstEvenParam q (quarter q - 1) (by simp [quarter])
      (by simp [quarter]))
    (boundaryFirstEvenParam_last_val_two q)

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

def boundaryCycleFirstOddLaneCount (q : Nat) : Nat :=
  2 * (quarter q - 1)

def boundaryCycleFirstOddLaneIndex (k : Nat) : Nat :=
  k / 2 + 1

theorem boundaryCycleFirstOddLaneIndex_pos (k : Nat) :
    1 ≤ boundaryCycleFirstOddLaneIndex k := by
  simp [boundaryCycleFirstOddLaneIndex]

theorem boundaryCycleFirstOddLaneIndex_lt (q k : Nat)
    (hk : k < boundaryCycleFirstOddLaneCount q) :
    boundaryCycleFirstOddLaneIndex k < quarter q := by
  simp [boundaryCycleFirstOddLaneIndex, boundaryCycleFirstOddLaneCount,
    quarter] at hk ⊢
  omega

theorem boundaryCycleFirstOddLaneIndex_succ_of_even (k : Nat)
    (heven : k % 2 = 0) :
    boundaryCycleFirstOddLaneIndex (k + 1) =
      boundaryCycleFirstOddLaneIndex k := by
  simp [boundaryCycleFirstOddLaneIndex]
  omega

theorem boundaryCycleFirstOddLaneIndex_succ_of_odd (k : Nat)
    (hodd : k % 2 ≠ 0) :
    boundaryCycleFirstOddLaneIndex (k + 1) =
      boundaryCycleFirstOddLaneIndex k + 1 := by
  simp [boundaryCycleFirstOddLaneIndex]
  omega

theorem boundaryFirstOddValue_odd (q j : Nat)
    (_hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    boundaryFirstOddValue q j % 2 = 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstOddValue, hpar, half]
    simp [quarter] at hjlt
    omega
  · simp [boundaryFirstOddValue, hpar, modulus]
    simp [quarter] at hjlt
    omega

theorem boundaryFirstOddParam_odd (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstOddParam q j hjpos hjlt).1.val % 2 = 1 := by
  rw [boundaryFirstOddParam_val]
  exact boundaryFirstOddValue_odd q j hjpos hjlt

theorem boundaryFirstOddValue_ne_half_sub_one_of_pos (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    boundaryFirstOddValue q j ≠ half q - 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstOddValue, hpar, half]
    omega
  · simp [boundaryFirstOddValue, hpar, half, modulus]
    simp [quarter] at hjlt
    omega

theorem boundaryFirstOddParam_ne_half_sub_one_of_pos (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstOddParam q j hjpos hjlt).1.val ≠ half q - 1 := by
  rw [boundaryFirstOddParam_val]
  exact boundaryFirstOddValue_ne_half_sub_one_of_pos q j hjpos hjlt

theorem boundaryFirstOddValue_ne_last (q j : Nat)
    (_hjpos : 1 ≤ j) (_hjlt : j < quarter q) :
    boundaryFirstOddValue q j ≠ modulus q - 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstOddValue, hpar, modulus, half]
    omega
  · simp [boundaryFirstOddValue, hpar, modulus]
    omega

theorem boundaryFirstOddParam_ne_last (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstOddParam q j hjpos hjlt).1.val ≠ modulus q - 1 := by
  rw [boundaryFirstOddParam_val]
  exact boundaryFirstOddValue_ne_last q j hjpos hjlt

theorem boundaryFirstOddValue_ne_half_add_one (q j : Nat)
    (_hjpos : 1 ≤ j) (_hjlt : j < quarter q) :
    boundaryFirstOddValue q j ≠ half q + 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundaryFirstOddValue, hpar, half]
    omega
  · simp [boundaryFirstOddValue, hpar, half, modulus]
    omega

theorem boundaryFirstOddParam_ne_half_add_one (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundaryFirstOddParam q j hjpos hjlt).1.val ≠ half q + 1 := by
  rw [boundaryFirstOddParam_val]
  exact boundaryFirstOddValue_ne_half_add_one q j hjpos hjlt

theorem boundaryFirstOddValue_shift_succ_zmod (q j : Nat)
    (_hjpos : 1 ≤ j) (hjnext : j + 1 < quarter q) :
    (((boundaryFirstOddValue q j : Nat) : ZMod (modulus q)) +
        ((half q - 2 : Nat) : ZMod (modulus q))) =
      ((boundaryFirstOddValue q (j + 1) : Nat) : ZMod (modulus q)) := by
  rw [← Nat.cast_add]
  by_cases hpar : j % 2 = 0
  · have hpar_next : (j + 1) % 2 ≠ 0 := by omega
    have hnat :
        boundaryFirstOddValue q j + (half q - 2) =
          boundaryFirstOddValue q (j + 1) := by
      simp [boundaryFirstOddValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
  · have hpar_next : (j + 1) % 2 = 0 := by omega
    have hnat :
        boundaryFirstOddValue q j + (half q - 2) =
          modulus q + boundaryFirstOddValue q (j + 1) := by
      simp [boundaryFirstOddValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
    simp

theorem boundaryFirstOddParam_shift_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q)
    (hne : (boundaryFirstOddParam q j hjpos hjlt).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundaryFirstOddParam q j hjpos hjlt) hne =
      boundaryFirstOddParam q (j + 1) (by omega) hjnext := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((boundaryFirstOddValue q j : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundaryFirstOddValue q (j + 1) : Nat) : ZMod (modulus q))
  exact boundaryFirstOddValue_shift_succ_zmod q j hjpos hjnext

noncomputable def boundaryCycleFirstOddLaneNode (q k : Nat)
    (hk : k < boundaryCycleFirstOddLaneCount q) :
    RouteEBoundaryNode (modulus q) :=
  let j := boundaryCycleFirstOddLaneIndex k
  if _heven : k % 2 = 0 then
    routeEBoundaryNode RouteEBoundaryLabel.L04
      (boundaryFirstOddParam q j
        (boundaryCycleFirstOddLaneIndex_pos k)
        (boundaryCycleFirstOddLaneIndex_lt q k hk))
  else
    routeEBoundaryNode RouteEBoundaryLabel.L03
      (boundaryFirstOddParam q j
        (boundaryCycleFirstOddLaneIndex_pos k)
        (boundaryCycleFirstOddLaneIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleFirstOddLane_step_even (q k : Nat)
    (hk : k < boundaryCycleFirstOddLaneCount q)
    (hks : k + 1 < boundaryCycleFirstOddLaneCount q)
    (heven : k % 2 = 0) :
    boundaryQuotient q (boundaryCycleFirstOddLaneNode q k hk) =
      boundaryCycleFirstOddLaneNode q (k + 1) hks := by
  have hnext_odd : ¬ (k + 1) % 2 = 0 := by omega
  simp [boundaryCycleFirstOddLaneNode, heven, hnext_odd,
    boundaryCycleFirstOddLaneIndex_succ_of_even k heven]
  exact boundaryQuotient_B_odd q
    (boundaryFirstOddParam q (boundaryCycleFirstOddLaneIndex k)
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk))
    (boundaryFirstOddParam_ne_half_sub_one_of_pos q
      (boundaryCycleFirstOddLaneIndex k)
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk))
    (boundaryFirstOddParam_ne_last q (boundaryCycleFirstOddLaneIndex k)
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk))
    (boundaryFirstOddParam_odd q (boundaryCycleFirstOddLaneIndex k)
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleFirstOddLane_step_odd (q k : Nat)
    (hk : k < boundaryCycleFirstOddLaneCount q)
    (hks : k + 1 < boundaryCycleFirstOddLaneCount q)
    (hodd : k % 2 ≠ 0) :
    boundaryQuotient q (boundaryCycleFirstOddLaneNode q k hk) =
      boundaryCycleFirstOddLaneNode q (k + 1) hks := by
  have hnext_even : (k + 1) % 2 = 0 := by omega
  have hjnext : boundaryCycleFirstOddLaneIndex k + 1 < quarter q := by
    rw [← boundaryCycleFirstOddLaneIndex_succ_of_odd k hodd]
    exact boundaryCycleFirstOddLaneIndex_lt q (k + 1) hks
  simp [boundaryCycleFirstOddLaneNode, hodd, hnext_even,
    boundaryCycleFirstOddLaneIndex_succ_of_odd k hodd]
  let j := boundaryCycleFirstOddLaneIndex k
  let a := boundaryFirstOddParam q j
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk)
  have hnot_succ : a.1.val ≠ half q + 1 := by
    dsimp [a, j]
    exact boundaryFirstOddParam_ne_half_add_one q
      (boundaryCycleFirstOddLaneIndex k)
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk)
  have hnot_close : a.1.val ≠ half q + 2 := by
    intro h
    have hoddv := boundaryFirstOddParam_odd q j
      (boundaryCycleFirstOddLaneIndex_pos k)
      (boundaryCycleFirstOddLaneIndex_lt q k hk)
    rw [h] at hoddv
    have heven : (half q + 2) % 2 = 0 := by
      simp [half]
      omega
    omega
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q a hnot_close) :=
      boundaryQuotient_A_odd_shift q a hnot_succ
        (boundaryFirstOddParam_odd q j
          (boundaryCycleFirstOddLaneIndex_pos k)
          (boundaryCycleFirstOddLaneIndex_lt q k hk))
    _ = routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryFirstOddParam q (j + 1) (by omega) hjnext) := by
      rw [boundaryFirstOddParam_shift_succ q j
        (boundaryCycleFirstOddLaneIndex_pos k)
        (boundaryCycleFirstOddLaneIndex_lt q k hk) hjnext hnot_close]

theorem boundaryCycleB2BridgeNode_zero (q : Nat)
    (hk : 0 < boundaryCycleB2BridgeCount q) :
    boundaryCycleB2BridgeNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryParamHalfSubOne q) := rfl

theorem boundaryCycleFirstOddLaneNode_zero (q : Nat)
    (hk : 0 < boundaryCycleFirstOddLaneCount q) :
    boundaryCycleFirstOddLaneNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L04
        (boundaryFirstOddParam q 1 (by omega) (by simp [quarter])) := by
  simp [boundaryCycleFirstOddLaneNode, boundaryCycleFirstOddLaneIndex]

theorem boundaryParamHalfSubOne_shift_eq_firstOdd_one (q : Nat)
    (hne : (boundaryParamHalfSubOne q).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundaryParamHalfSubOne q) hne =
      boundaryFirstOddParam q 1 (by omega) (by simp [quarter]) := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((half q - 1 : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundaryFirstOddValue q 1 : Nat) : ZMod (modulus q))
  rw [← Nat.cast_add]
  have hnat :
      (half q - 1) + (half q - 2) = boundaryFirstOddValue q 1 := by
    simp [boundaryFirstOddValue, half, modulus]
    omega
  rw [hnat]

theorem boundaryCycleB2Bridge_to_firstOddLane (q : Nat)
    (hb : 0 < boundaryCycleB2BridgeCount q)
    (ho : 0 < boundaryCycleFirstOddLaneCount q) :
    boundaryQuotient q (boundaryCycleB2BridgeNode q 0 hb) =
      boundaryCycleFirstOddLaneNode q 0 ho := by
  rw [boundaryCycleB2BridgeNode_zero q hb,
    boundaryCycleFirstOddLaneNode_zero q ho]
  have hnot_succ : (boundaryParamHalfSubOne q).1.val ≠ half q + 1 := by
    simp [boundaryParamHalfSubOne, RouteENonzeroSeam.ofNat_val, half]
  have hnot_close : (boundaryParamHalfSubOne q).1.val ≠ half q + 2 := by
    simp [boundaryParamHalfSubOne, RouteENonzeroSeam.ofNat_val, half]
  calc
    boundaryQuotient q
        (routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryParamHalfSubOne q)) =
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q (boundaryParamHalfSubOne q) hnot_close) :=
      boundaryQuotient_A_odd_shift q (boundaryParamHalfSubOne q) hnot_succ
        (by
          simp [boundaryParamHalfSubOne, RouteENonzeroSeam.ofNat_val, half]
          omega)
    _ = routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryFirstOddParam q 1 (by omega) (by simp [quarter])) := by
      rw [boundaryParamHalfSubOne_shift_eq_firstOdd_one q hnot_close]

def boundaryCycleFirstOddBSubOneCount (_q : Nat) : Nat := 1

noncomputable def boundaryCycleFirstOddBSubOneNode (q k : Nat)
    (_hk : k < boundaryCycleFirstOddBSubOneCount q) :
    RouteEBoundaryNode (modulus q) :=
  routeEBoundaryNode RouteEBoundaryLabel.L04 (boundaryParamHalfSubOne q)

theorem boundaryCycleFirstOddLaneLastIndex_eq (q : Nat) :
    boundaryCycleFirstOddLaneIndex (boundaryCycleFirstOddLaneCount q - 1) =
      quarter q - 1 := by
  simp [boundaryCycleFirstOddLaneIndex, boundaryCycleFirstOddLaneCount,
    quarter]
  omega

theorem boundaryCycleFirstOddLaneLast_odd (q : Nat) :
    (boundaryCycleFirstOddLaneCount q - 1) % 2 ≠ 0 := by
  simp [boundaryCycleFirstOddLaneCount, quarter]
  omega

theorem boundaryFirstOddValue_last_eq_one (q : Nat) :
    boundaryFirstOddValue q (quarter q - 1) = 1 := by
  have hpar : (quarter q - 1) % 2 = 0 := by
    simp [quarter]
    omega
  rw [boundaryFirstOddValue, if_pos hpar]
  simp [quarter, half]
  omega

theorem boundaryFirstOddParam_last_val_one (q : Nat) :
    (boundaryFirstOddParam q (quarter q - 1) (by simp [quarter])
      (by simp [quarter])).1.val = 1 := by
  rw [boundaryFirstOddParam_val]
  exact boundaryFirstOddValue_last_eq_one q

set_option linter.flexible false in
theorem boundaryCycleFirstOddLane_to_BSubOne (q : Nat)
    (hlast : boundaryCycleFirstOddLaneCount q - 1 <
      boundaryCycleFirstOddLaneCount q)
    (hbridge : 0 < boundaryCycleFirstOddBSubOneCount q) :
    boundaryQuotient q
        (boundaryCycleFirstOddLaneNode q
          (boundaryCycleFirstOddLaneCount q - 1) hlast) =
      boundaryCycleFirstOddBSubOneNode q 0 hbridge := by
  have hodd := boundaryCycleFirstOddLaneLast_odd q
  simp [boundaryCycleFirstOddLaneNode, boundaryCycleFirstOddBSubOneNode, hodd,
    boundaryCycleFirstOddLaneLastIndex_eq q]
  have hnot_succ :
      (boundaryFirstOddParam q (quarter q - 1) (by simp [quarter])
        (by simp [quarter])).1.val ≠ half q + 1 := by
    rw [boundaryFirstOddParam_last_val_one q]
    simp [half]
  calc
    boundaryQuotient q
        (routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryFirstOddParam q (quarter q - 1) (by simp [quarter])
            (by simp [quarter]))) =
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q
            (boundaryFirstOddParam q (quarter q - 1) (by simp [quarter])
              (by simp [quarter])) (by
                rw [boundaryFirstOddParam_last_val_one q]
                simp [half])) :=
      boundaryQuotient_A_odd_shift q
        (boundaryFirstOddParam q (quarter q - 1) (by simp [quarter])
          (by simp [quarter])) hnot_succ (by
            rw [boundaryFirstOddParam_last_val_one q])
    _ = routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryParamHalfSubOne q) := by
      apply congrArg (routeEBoundaryNode RouteEBoundaryLabel.L04)
      apply Subtype.ext
      rw [boundaryShiftParam_val]
      unfold boundaryFirstOddParam boundaryParamHalfSubOne
        RouteENonzeroSeam.ofNat
      simp [boundaryFirstOddValue_last_eq_one]
      have hnat : 1 + (half q - 2) = half q - 1 := by
        simp [half]
        omega
      rw [← Nat.cast_one, ← Nat.cast_add, hnat]

def boundaryCycleFirstOddCRunCount (q : Nat) : Nat :=
  half q - 1

def boundaryFirstOddCValue (q k : Nat) : Nat :=
  half q - 1 - k

theorem boundaryFirstOddCValue_range (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q) :
    0 < boundaryFirstOddCValue q k ∧
      boundaryFirstOddCValue q k < modulus q := by
  simp [boundaryFirstOddCValue, boundaryCycleFirstOddCRunCount, half,
    modulus] at hk ⊢
  omega

def boundaryFirstOddCParam (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q) :
    RouteENonzeroSeam (modulus q) :=
  RouteENonzeroSeam.ofNat (boundaryFirstOddCValue q k)
    (boundaryFirstOddCValue_range q k hk).1
    (boundaryFirstOddCValue_range q k hk).2

theorem boundaryFirstOddCParam_val (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q) :
    (boundaryFirstOddCParam q k hk).1.val =
      boundaryFirstOddCValue q k := by
  exact RouteENonzeroSeam.ofNat_val _ _ _

noncomputable def boundaryCycleFirstOddCRunNode (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q) :
    RouteEBoundaryNode (modulus q) :=
  routeEBoundaryNode RouteEBoundaryLabel.L34
    (boundaryFirstOddCParam q k hk)

theorem boundaryFirstOddCParam_zero_eq_halfSubOne (q : Nat)
    (hk : 0 < boundaryCycleFirstOddCRunCount q) :
    boundaryFirstOddCParam q 0 hk = boundaryParamHalfSubOne q := by
  apply Subtype.ext
  apply ZMod.val_injective (modulus q)
  rw [boundaryFirstOddCParam_val, boundaryParamHalfSubOne,
    RouteENonzeroSeam.ofNat_val]
  simp [boundaryFirstOddCValue]

theorem boundaryCycleFirstOddCRunNode_zero (q : Nat)
    (hk : 0 < boundaryCycleFirstOddCRunCount q) :
    boundaryCycleFirstOddCRunNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L34
        (boundaryParamHalfSubOne q) := by
  simp [boundaryCycleFirstOddCRunNode,
    boundaryFirstOddCParam_zero_eq_halfSubOne q hk]

theorem boundaryCycleFirstOddBSubOne_to_CRun (q : Nat)
    (hb : 0 < boundaryCycleFirstOddBSubOneCount q)
    (hc : 0 < boundaryCycleFirstOddCRunCount q) :
    boundaryQuotient q (boundaryCycleFirstOddBSubOneNode q 0 hb) =
      boundaryCycleFirstOddCRunNode q 0 hc := by
  rw [boundaryCycleFirstOddCRunNode_zero q hc]
  change boundaryQuotient q
      (routeEBoundaryNode RouteEBoundaryLabel.L04
        (boundaryParamHalfSubOne q)) =
    routeEBoundaryNode RouteEBoundaryLabel.L34
      (boundaryParamHalfSubOne q)
  exact boundaryQuotient_B_h_sub_one q (boundaryParamHalfSubOne q) (by
    simp [boundaryParamHalfSubOne, RouteENonzeroSeam.ofNat_val])

theorem boundaryFirstOddCValue_succ (q k : Nat)
    (hnext : k + 1 < boundaryCycleFirstOddCRunCount q) :
    boundaryFirstOddCValue q (k + 1) =
      boundaryFirstOddCValue q k - 1 := by
  simp [boundaryFirstOddCValue, boundaryCycleFirstOddCRunCount, half] at hnext ⊢
  omega

theorem boundaryFirstOddCParam_pred_eq (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q)
    (hnext : k + 1 < boundaryCycleFirstOddCRunCount q)
    (hnot_one : (boundaryFirstOddCParam q k hk).1.val ≠ 1) :
    boundaryPredParam q (boundaryFirstOddCParam q k hk) hnot_one =
      boundaryFirstOddCParam q (k + 1) hnext := by
  apply Subtype.ext
  rw [boundaryPredParam_val]
  change (((boundaryFirstOddCValue q k : Nat) : ZMod (modulus q)) - 1) =
    ((boundaryFirstOddCValue q (k + 1) : Nat) : ZMod (modulus q))
  rw [boundaryFirstOddCValue_succ q k hnext]
  rw [Nat.cast_pred (R := ZMod (modulus q))
    (boundaryFirstOddCValue_range q k hk).1]

set_option linter.flexible false in
theorem boundaryCycleFirstOddCRun_step (q k : Nat)
    (hk : k < boundaryCycleFirstOddCRunCount q)
    (hks : k + 1 < boundaryCycleFirstOddCRunCount q) :
    boundaryQuotient q (boundaryCycleFirstOddCRunNode q k hk) =
      boundaryCycleFirstOddCRunNode q (k + 1) hks := by
  simp [boundaryCycleFirstOddCRunNode]
  let a := boundaryFirstOddCParam q k hk
  have hnot_one : a.1.val ≠ 1 := by
    dsimp [a]
    rw [boundaryFirstOddCParam_val]
    simp [boundaryFirstOddCValue, boundaryCycleFirstOddCRunCount, half] at hks ⊢
    omega
  have hnot_h : a.1.val ≠ half q := by
    dsimp [a]
    rw [boundaryFirstOddCParam_val]
    simp [boundaryFirstOddCValue, boundaryCycleFirstOddCRunCount, half] at hk ⊢
    omega
  have hnot_last : a.1.val ≠ modulus q - 1 := by
    dsimp [a]
    rw [boundaryFirstOddCParam_val]
    simp [boundaryFirstOddCValue, half, modulus]
    omega
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundaryPredParam q a hnot_one) :=
      boundaryQuotient_C_generic q a hnot_one hnot_h hnot_last
    _ = routeEBoundaryNode RouteEBoundaryLabel.L34
          (boundaryFirstOddCParam q (k + 1) hks) := by
      rw [boundaryFirstOddCParam_pred_eq q k hk hks hnot_one]

def boundaryCycleALastBridgeNode (q k : Nat)
    (_hk : k < boundaryCycleALastBridgeCount q) :
    RouteEBoundaryNode (modulus q) :=
  routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamLast q)

theorem boundaryCycleFirstOddCRunLastIndex_eq (q : Nat) :
    boundaryCycleFirstOddCRunCount q - 1 = half q - 2 := by
  simp [boundaryCycleFirstOddCRunCount, half]

theorem boundaryFirstOddCValue_last_eq_one (q : Nat) :
    boundaryFirstOddCValue q (boundaryCycleFirstOddCRunCount q - 1) =
      1 := by
  simp [boundaryFirstOddCValue, boundaryCycleFirstOddCRunCount, half]

theorem boundaryFirstOddCParam_last_val_one (q : Nat)
    (hk : boundaryCycleFirstOddCRunCount q - 1 <
      boundaryCycleFirstOddCRunCount q) :
    (boundaryFirstOddCParam q (boundaryCycleFirstOddCRunCount q - 1)
      hk).1.val = 1 := by
  rw [boundaryFirstOddCParam_val]
  exact boundaryFirstOddCValue_last_eq_one q

set_option linter.flexible false in
theorem boundaryCycleFirstOddCRun_to_ALast (q : Nat)
    (hlast : boundaryCycleFirstOddCRunCount q - 1 <
      boundaryCycleFirstOddCRunCount q)
    (ha : 0 < boundaryCycleALastBridgeCount q) :
    boundaryQuotient q
        (boundaryCycleFirstOddCRunNode q
          (boundaryCycleFirstOddCRunCount q - 1) hlast) =
      boundaryCycleALastBridgeNode q 0 ha := by
  simp [boundaryCycleFirstOddCRunNode, boundaryCycleALastBridgeNode]
  exact boundaryQuotient_C_one q
    (boundaryFirstOddCParam q (boundaryCycleFirstOddCRunCount q - 1) hlast)
    (boundaryFirstOddCParam_last_val_one q hlast)

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

def boundaryCycleSecondOddLaneCount (q : Nat) : Nat :=
  2 * (quarter q - 1)

def boundaryCycleSecondOddFinalCount (_q : Nat) : Nat := 1

theorem boundaryCycleSecondOddLaneCount_add_final_eq_tailCount (q : Nat) :
    boundaryCycleSecondOddLaneCount q +
      boundaryCycleSecondOddFinalCount q =
    boundaryCycleSecondOddTailCount q := by
  simp [boundaryCycleSecondOddLaneCount, boundaryCycleSecondOddFinalCount,
    boundaryCycleSecondOddTailCount, quarter]
  omega

def boundaryCycleSecondOddLaneIndex (k : Nat) : Nat :=
  k / 2 + 1

theorem boundaryCycleSecondOddLaneIndex_pos (k : Nat) :
    1 ≤ boundaryCycleSecondOddLaneIndex k := by
  simp [boundaryCycleSecondOddLaneIndex]

theorem boundaryCycleSecondOddLaneIndex_lt (q k : Nat)
    (hk : k < boundaryCycleSecondOddLaneCount q) :
    boundaryCycleSecondOddLaneIndex k < quarter q := by
  simp [boundaryCycleSecondOddLaneIndex, boundaryCycleSecondOddLaneCount,
    quarter] at hk ⊢
  omega

theorem boundaryCycleSecondOddLaneIndex_succ_of_even (k : Nat)
    (heven : k % 2 = 0) :
    boundaryCycleSecondOddLaneIndex (k + 1) =
      boundaryCycleSecondOddLaneIndex k := by
  simp [boundaryCycleSecondOddLaneIndex]
  omega

theorem boundaryCycleSecondOddLaneIndex_succ_of_odd (k : Nat)
    (hodd : k % 2 ≠ 0) :
    boundaryCycleSecondOddLaneIndex (k + 1) =
      boundaryCycleSecondOddLaneIndex k + 1 := by
  simp [boundaryCycleSecondOddLaneIndex]
  omega

theorem boundarySecondOddValue_odd (q j : Nat)
    (_hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    boundarySecondOddValue q j % 2 = 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondOddValue, hpar, modulus]
    simp [quarter] at hjlt
    omega
  · simp [boundarySecondOddValue, hpar, half]
    simp [quarter] at hjlt
    omega

theorem boundarySecondOddParam_odd (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundarySecondOddParam q j hjpos hjlt).1.val % 2 = 1 := by
  rw [boundarySecondOddParam_val]
  exact boundarySecondOddValue_odd q j hjpos hjlt

theorem boundarySecondOddValue_ne_half_sub_one_of_pos (q j : Nat)
    (_hjpos : 1 ≤ j) (_hjlt : j < quarter q) :
    boundarySecondOddValue q j ≠ half q - 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondOddValue, hpar, half, modulus]
    omega
  · simp [boundarySecondOddValue, hpar, half]
    omega

theorem boundarySecondOddParam_ne_half_sub_one_of_pos (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundarySecondOddParam q j hjpos hjlt).1.val ≠ half q - 1 := by
  rw [boundarySecondOddParam_val]
  exact boundarySecondOddValue_ne_half_sub_one_of_pos q j hjpos hjlt

theorem boundarySecondOddValue_ne_last (q j : Nat)
    (hjpos : 1 ≤ j) (_hjlt : j < quarter q) :
    boundarySecondOddValue q j ≠ modulus q - 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondOddValue, hpar, modulus]
    omega
  · simp [boundarySecondOddValue, hpar, half, modulus]
    omega

theorem boundarySecondOddParam_ne_last (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q) :
    (boundarySecondOddParam q j hjpos hjlt).1.val ≠ modulus q - 1 := by
  rw [boundarySecondOddParam_val]
  exact boundarySecondOddValue_ne_last q j hjpos hjlt

theorem boundarySecondOddValue_ne_half_add_one_of_succ (q j : Nat)
    (_hjpos : 1 ≤ j) (_hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q) :
    boundarySecondOddValue q j ≠ half q + 1 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondOddValue, hpar, half, modulus]
    simp [quarter] at hjnext
    omega
  · simp [boundarySecondOddValue, hpar, half]
    omega

theorem boundarySecondOddParam_ne_half_add_one_of_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q) :
    (boundarySecondOddParam q j hjpos hjlt).1.val ≠ half q + 1 := by
  rw [boundarySecondOddParam_val]
  exact boundarySecondOddValue_ne_half_add_one_of_succ q j hjpos hjlt hjnext

theorem boundarySecondOddValue_shift_succ_zmod (q j : Nat)
    (_hjpos : 1 ≤ j) (hjnext : j + 1 < quarter q) :
    (((boundarySecondOddValue q j : Nat) : ZMod (modulus q)) +
        ((half q - 2 : Nat) : ZMod (modulus q))) =
      ((boundarySecondOddValue q (j + 1) : Nat) : ZMod (modulus q)) := by
  rw [← Nat.cast_add]
  by_cases hpar : j % 2 = 0
  · have hpar_next : (j + 1) % 2 ≠ 0 := by omega
    have hnat :
        boundarySecondOddValue q j + (half q - 2) =
          modulus q + boundarySecondOddValue q (j + 1) := by
      simp [boundarySecondOddValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
    simp
  · have hpar_next : (j + 1) % 2 = 0 := by omega
    have hnat :
        boundarySecondOddValue q j + (half q - 2) =
          boundarySecondOddValue q (j + 1) := by
      simp [boundarySecondOddValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]

theorem boundarySecondOddParam_shift_succ (q j : Nat)
    (hjpos : 1 ≤ j) (hjlt : j < quarter q)
    (hjnext : j + 1 < quarter q)
    (hne : (boundarySecondOddParam q j hjpos hjlt).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundarySecondOddParam q j hjpos hjlt) hne =
      boundarySecondOddParam q (j + 1) (by omega) hjnext := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((boundarySecondOddValue q j : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundarySecondOddValue q (j + 1) : Nat) : ZMod (modulus q))
  exact boundarySecondOddValue_shift_succ_zmod q j hjpos hjnext

noncomputable def boundaryCycleSecondOddLaneNode (q k : Nat)
    (hk : k < boundaryCycleSecondOddLaneCount q) :
    RouteEBoundaryNode (modulus q) :=
  let j := boundaryCycleSecondOddLaneIndex k
  if _heven : k % 2 = 0 then
    routeEBoundaryNode RouteEBoundaryLabel.L04
      (boundarySecondOddParam q j
        (boundaryCycleSecondOddLaneIndex_pos k)
        (boundaryCycleSecondOddLaneIndex_lt q k hk))
  else
    routeEBoundaryNode RouteEBoundaryLabel.L03
      (boundarySecondOddParam q j
        (boundaryCycleSecondOddLaneIndex_pos k)
        (boundaryCycleSecondOddLaneIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleSecondOddLane_step_even (q k : Nat)
    (hk : k < boundaryCycleSecondOddLaneCount q)
    (hks : k + 1 < boundaryCycleSecondOddLaneCount q)
    (heven : k % 2 = 0) :
    boundaryQuotient q (boundaryCycleSecondOddLaneNode q k hk) =
      boundaryCycleSecondOddLaneNode q (k + 1) hks := by
  have hnext_odd : ¬ (k + 1) % 2 = 0 := by omega
  simp [boundaryCycleSecondOddLaneNode, heven, hnext_odd,
    boundaryCycleSecondOddLaneIndex_succ_of_even k heven]
  exact boundaryQuotient_B_odd q
    (boundarySecondOddParam q (boundaryCycleSecondOddLaneIndex k)
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk))
    (boundarySecondOddParam_ne_half_sub_one_of_pos q
      (boundaryCycleSecondOddLaneIndex k)
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk))
    (boundarySecondOddParam_ne_last q (boundaryCycleSecondOddLaneIndex k)
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk))
    (boundarySecondOddParam_odd q (boundaryCycleSecondOddLaneIndex k)
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk))

set_option linter.flexible false in
theorem boundaryCycleSecondOddLane_step_odd (q k : Nat)
    (hk : k < boundaryCycleSecondOddLaneCount q)
    (hks : k + 1 < boundaryCycleSecondOddLaneCount q)
    (hodd : k % 2 ≠ 0) :
    boundaryQuotient q (boundaryCycleSecondOddLaneNode q k hk) =
      boundaryCycleSecondOddLaneNode q (k + 1) hks := by
  have hnext_even : (k + 1) % 2 = 0 := by omega
  have hjnext : boundaryCycleSecondOddLaneIndex k + 1 < quarter q := by
    rw [← boundaryCycleSecondOddLaneIndex_succ_of_odd k hodd]
    exact boundaryCycleSecondOddLaneIndex_lt q (k + 1) hks
  simp [boundaryCycleSecondOddLaneNode, hodd, hnext_even,
    boundaryCycleSecondOddLaneIndex_succ_of_odd k hodd]
  let j := boundaryCycleSecondOddLaneIndex k
  let a := boundarySecondOddParam q j
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk)
  have hnot_succ : a.1.val ≠ half q + 1 := by
    dsimp [a, j]
    exact boundarySecondOddParam_ne_half_add_one_of_succ q
      (boundaryCycleSecondOddLaneIndex k)
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk) hjnext
  have hnot_close : a.1.val ≠ half q + 2 := by
    intro h
    have hoddv := boundarySecondOddParam_odd q j
      (boundaryCycleSecondOddLaneIndex_pos k)
      (boundaryCycleSecondOddLaneIndex_lt q k hk)
    rw [h] at hoddv
    have heven : (half q + 2) % 2 = 0 := by
      simp [half]
      omega
    omega
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q a hnot_close) :=
      boundaryQuotient_A_odd_shift q a hnot_succ
        (boundarySecondOddParam_odd q j
          (boundaryCycleSecondOddLaneIndex_pos k)
          (boundaryCycleSecondOddLaneIndex_lt q k hk))
    _ = routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundarySecondOddParam q (j + 1) (by omega) hjnext) := by
      rw [boundarySecondOddParam_shift_succ q j
        (boundaryCycleSecondOddLaneIndex_pos k)
        (boundaryCycleSecondOddLaneIndex_lt q k hk) hjnext hnot_close]

theorem boundaryCycleALastBridgeNode_zero (q : Nat)
    (hk : 0 < boundaryCycleALastBridgeCount q) :
    boundaryCycleALastBridgeNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryParamLast q) := rfl

theorem boundaryCycleSecondOddLaneNode_zero (q : Nat)
    (hk : 0 < boundaryCycleSecondOddLaneCount q) :
    boundaryCycleSecondOddLaneNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L04
        (boundarySecondOddParam q 1 (by omega) (by simp [quarter])) := by
  simp [boundaryCycleSecondOddLaneNode, boundaryCycleSecondOddLaneIndex]

theorem boundaryParamLast_shift_eq_secondOdd_one (q : Nat)
    (hne : (boundaryParamLast q).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundaryParamLast q) hne =
      boundarySecondOddParam q 1 (by omega) (by simp [quarter]) := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((modulus q - 1 : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundarySecondOddValue q 1 : Nat) : ZMod (modulus q))
  rw [← Nat.cast_add]
  have hnat :
      (modulus q - 1) + (half q - 2) =
        modulus q + boundarySecondOddValue q 1 := by
    simp [boundarySecondOddValue, half, modulus]
    omega
  rw [hnat]
  simp

theorem boundaryCycleALastBridge_to_secondOddLane (q : Nat)
    (ha : 0 < boundaryCycleALastBridgeCount q)
    (ho : 0 < boundaryCycleSecondOddLaneCount q) :
    boundaryQuotient q (boundaryCycleALastBridgeNode q 0 ha) =
      boundaryCycleSecondOddLaneNode q 0 ho := by
  rw [boundaryCycleALastBridgeNode_zero q ha,
    boundaryCycleSecondOddLaneNode_zero q ho]
  have hnot_succ : (boundaryParamLast q).1.val ≠ half q + 1 := by
    simp [boundaryParamLast, RouteENonzeroSeam.ofNat_val, half, modulus]
    omega
  have hnot_close : (boundaryParamLast q).1.val ≠ half q + 2 := by
    simp [boundaryParamLast, RouteENonzeroSeam.ofNat_val, half, modulus]
    omega
  calc
    boundaryQuotient q
        (routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamLast q)) =
        routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundaryShiftParam q (boundaryParamLast q) hnot_close) :=
      boundaryQuotient_A_odd_shift q (boundaryParamLast q) hnot_succ (by
        simp [boundaryParamLast, RouteENonzeroSeam.ofNat_val, modulus,
          Nat.add_mod, Nat.mul_mod])
    _ = routeEBoundaryNode RouteEBoundaryLabel.L04
          (boundarySecondOddParam q 1 (by omega) (by simp [quarter])) := by
      rw [boundaryParamLast_shift_eq_secondOdd_one q hnot_close]

noncomputable def boundaryCycleSecondOddFinalNode (q k : Nat)
    (_hk : k < boundaryCycleSecondOddFinalCount q) :
    RouteEBoundaryNode (modulus q) :=
  routeEBoundaryNode RouteEBoundaryLabel.L03 (boundaryParamHalfSubTwo q)

theorem boundaryCycleSecondOddLaneLastIndex_eq (q : Nat) :
    boundaryCycleSecondOddLaneIndex (boundaryCycleSecondOddLaneCount q - 1) =
      quarter q - 1 := by
  simp [boundaryCycleSecondOddLaneIndex, boundaryCycleSecondOddLaneCount,
    quarter]
  omega

theorem boundaryCycleSecondOddLaneLast_odd (q : Nat) :
    (boundaryCycleSecondOddLaneCount q - 1) % 2 ≠ 0 := by
  simp [boundaryCycleSecondOddLaneCount, quarter]
  omega

theorem boundarySecondOddValue_last_eq_half_add_one (q : Nat) :
    boundarySecondOddValue q (quarter q - 1) = half q + 1 := by
  have hpar : (quarter q - 1) % 2 = 0 := by
    simp [quarter]
    omega
  rw [boundarySecondOddValue, if_pos hpar]
  simp [quarter, half, modulus]
  omega

theorem boundarySecondOddParam_last_val_half_add_one (q : Nat) :
    (boundarySecondOddParam q (quarter q - 1) (by simp [quarter])
      (by simp [quarter])).1.val = half q + 1 := by
  rw [boundarySecondOddParam_val]
  exact boundarySecondOddValue_last_eq_half_add_one q

set_option linter.flexible false in
theorem boundaryCycleSecondOddLane_to_final (q : Nat)
    (hlast : boundaryCycleSecondOddLaneCount q - 1 <
      boundaryCycleSecondOddLaneCount q)
    (hfinal : 0 < boundaryCycleSecondOddFinalCount q) :
    boundaryQuotient q
        (boundaryCycleSecondOddLaneNode q
          (boundaryCycleSecondOddLaneCount q - 1) hlast) =
      boundaryCycleSecondOddFinalNode q 0 hfinal := by
  have hodd := boundaryCycleSecondOddLaneLast_odd q
  simp [boundaryCycleSecondOddLaneNode, boundaryCycleSecondOddFinalNode, hodd,
    boundaryCycleSecondOddLaneLastIndex_eq q]
  exact boundaryQuotient_A_h_succ q
    (boundarySecondOddParam q (quarter q - 1) (by simp [quarter])
      (by simp [quarter]))
    (boundarySecondOddParam_last_val_half_add_one q)

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

def boundaryCycleSecondEvenTailIndex (k : Nat) : Nat :=
  k / 2

theorem boundaryCycleSecondEvenTailIndex_lt (q k : Nat)
    (hk : k < boundaryCycleSecondEvenTailCount q) :
    boundaryCycleSecondEvenTailIndex k < quarter q - 1 := by
  simp [boundaryCycleSecondEvenTailIndex, boundaryCycleSecondEvenTailCount,
    quarter] at hk ⊢
  omega

theorem boundaryCycleSecondEvenTailIndex_succ_lt (q k : Nat)
    (hk : k < boundaryCycleSecondEvenTailCount q)
    (hodd : k % 2 ≠ 0) :
    boundaryCycleSecondEvenTailIndex k + 1 < quarter q - 1 := by
  simp [boundaryCycleSecondEvenTailIndex, boundaryCycleSecondEvenTailCount,
    quarter] at hk ⊢
  omega

theorem boundaryCycleSecondEvenTailIndex_succ_of_even (k : Nat)
    (heven : k % 2 = 0) :
    boundaryCycleSecondEvenTailIndex (k + 1) =
      boundaryCycleSecondEvenTailIndex k := by
  simp [boundaryCycleSecondEvenTailIndex]
  omega

theorem boundaryCycleSecondEvenTailIndex_succ_of_odd (k : Nat)
    (hodd : k % 2 ≠ 0) :
    boundaryCycleSecondEvenTailIndex (k + 1) =
      boundaryCycleSecondEvenTailIndex k + 1 := by
  simp [boundaryCycleSecondEvenTailIndex]
  omega

theorem boundarySecondEvenValue_even (q j : Nat)
    (hjlt : j < quarter q - 1) :
    boundarySecondEvenValue q j % 2 = 0 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondEvenValue, hpar, half]
    simp [quarter] at hjlt
    omega
  · simp [boundarySecondEvenValue, hpar, modulus]
    simp [quarter] at hjlt
    omega

theorem boundarySecondEvenParam_even (q j : Nat)
    (hjlt : j < quarter q - 1) :
    (boundarySecondEvenParam q j hjlt).1.val % 2 = 0 := by
  rw [boundarySecondEvenParam_val]
  exact boundarySecondEvenValue_even q j hjlt

theorem boundarySecondEvenValue_ne_half (q j : Nat)
    (hjlt : j < quarter q - 1) :
    boundarySecondEvenValue q j ≠ half q := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondEvenValue, hpar, half]
    omega
  · simp [boundarySecondEvenValue, hpar, half, modulus]
    simp [quarter] at hjlt
    omega

theorem boundarySecondEvenParam_ne_half (q j : Nat)
    (hjlt : j < quarter q - 1) :
    (boundarySecondEvenParam q j hjlt).1.val ≠ half q := by
  rw [boundarySecondEvenParam_val]
  exact boundarySecondEvenValue_ne_half q j hjlt

theorem boundarySecondEvenValue_ne_two (q j : Nat)
    (hjlt : j < quarter q - 1) :
    boundarySecondEvenValue q j ≠ 2 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondEvenValue, hpar, half]
    simp [quarter] at hjlt
    omega
  · simp [boundarySecondEvenValue, hpar, modulus]
    simp [quarter] at hjlt
    omega

theorem boundarySecondEvenParam_ne_two (q j : Nat)
    (hjlt : j < quarter q - 1) :
    (boundarySecondEvenParam q j hjlt).1.val ≠ 2 := by
  rw [boundarySecondEvenParam_val]
  exact boundarySecondEvenValue_ne_two q j hjlt

theorem boundarySecondEvenValue_ne_half_add_two_of_succ (q j : Nat)
    (_hjlt : j < quarter q - 1) (hjnext : j + 1 < quarter q - 1) :
    boundarySecondEvenValue q j ≠ half q + 2 := by
  by_cases hpar : j % 2 = 0
  · simp [boundarySecondEvenValue, hpar, half]
    simp [quarter] at hjnext
    omega
  · simp [boundarySecondEvenValue, hpar, half, modulus]
    simp [quarter] at hjnext
    omega

theorem boundarySecondEvenParam_ne_half_add_two_of_succ (q j : Nat)
    (hjlt : j < quarter q - 1) (hjnext : j + 1 < quarter q - 1) :
    (boundarySecondEvenParam q j hjlt).1.val ≠ half q + 2 := by
  rw [boundarySecondEvenParam_val]
  exact boundarySecondEvenValue_ne_half_add_two_of_succ q j hjlt hjnext

theorem boundarySecondEvenValue_shift_succ_zmod (q j : Nat)
    (hjnext : j + 1 < quarter q - 1) :
    (((boundarySecondEvenValue q j : Nat) : ZMod (modulus q)) +
        ((half q - 2 : Nat) : ZMod (modulus q))) =
      ((boundarySecondEvenValue q (j + 1) : Nat) : ZMod (modulus q)) := by
  rw [← Nat.cast_add]
  by_cases hpar : j % 2 = 0
  · have hpar_next : (j + 1) % 2 ≠ 0 := by omega
    have hnat :
        boundarySecondEvenValue q j + (half q - 2) =
          boundarySecondEvenValue q (j + 1) := by
      simp [boundarySecondEvenValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
  · have hpar_next : (j + 1) % 2 = 0 := by omega
    have hnat :
        boundarySecondEvenValue q j + (half q - 2) =
          modulus q + boundarySecondEvenValue q (j + 1) := by
      simp [boundarySecondEvenValue, hpar, hpar_next, half, modulus]
      simp [quarter] at hjnext
      omega
    rw [hnat]
    simp

theorem boundarySecondEvenParam_shift_succ (q j : Nat)
    (hjlt : j < quarter q - 1) (hjnext : j + 1 < quarter q - 1)
    (hne : (boundarySecondEvenParam q j hjlt).1.val ≠ half q + 2) :
    boundaryShiftParam q (boundarySecondEvenParam q j hjlt) hne =
      boundarySecondEvenParam q (j + 1) hjnext := by
  apply Subtype.ext
  rw [boundaryShiftParam_val]
  change (((boundarySecondEvenValue q j : Nat) : ZMod (modulus q)) +
      ((half q - 2 : Nat) : ZMod (modulus q))) =
        ((boundarySecondEvenValue q (j + 1) : Nat) : ZMod (modulus q))
  exact boundarySecondEvenValue_shift_succ_zmod q j hjnext

noncomputable def boundaryCycleSecondEvenTailNode (q k : Nat)
    (hk : k < boundaryCycleSecondEvenTailCount q) :
    RouteEBoundaryNode (modulus q) :=
  let j := boundaryCycleSecondEvenTailIndex k
  if _heven : k % 2 = 0 then
    routeEBoundaryNode RouteEBoundaryLabel.L04
      (boundarySecondEvenParam q j
        (boundaryCycleSecondEvenTailIndex_lt q k hk))
  else
    routeEBoundaryNode RouteEBoundaryLabel.L03
      (boundarySecondEvenParam q (j + 1)
        (boundaryCycleSecondEvenTailIndex_succ_lt q k hk _heven))

set_option linter.flexible false in
theorem boundaryCycleSecondEvenTail_step_even (q k : Nat)
    (hk : k < boundaryCycleSecondEvenTailCount q)
    (hks : k + 1 < boundaryCycleSecondEvenTailCount q)
    (heven : k % 2 = 0) :
    boundaryQuotient q (boundaryCycleSecondEvenTailNode q k hk) =
      boundaryCycleSecondEvenTailNode q (k + 1) hks := by
  have hnext_odd : (k + 1) % 2 ≠ 0 := by omega
  have hjnext : boundaryCycleSecondEvenTailIndex k + 1 <
      quarter q - 1 := by
    rw [← boundaryCycleSecondEvenTailIndex_succ_of_even k heven]
    exact boundaryCycleSecondEvenTailIndex_succ_lt q (k + 1) hks hnext_odd
  simp [boundaryCycleSecondEvenTailNode, heven, hnext_odd,
    boundaryCycleSecondEvenTailIndex_succ_of_even k heven]
  let j := boundaryCycleSecondEvenTailIndex k
  let a := boundarySecondEvenParam q j
      (boundaryCycleSecondEvenTailIndex_lt q k hk)
  have hnot_two : a.1.val ≠ 2 := by
    dsimp [a, j]
    exact boundarySecondEvenParam_ne_two q
      (boundaryCycleSecondEvenTailIndex k)
      (boundaryCycleSecondEvenTailIndex_lt q k hk)
  have hnot_close : a.1.val ≠ half q + 2 := by
    dsimp [a, j]
    exact boundarySecondEvenParam_ne_half_add_two_of_succ q
      (boundaryCycleSecondEvenTailIndex k)
      (boundaryCycleSecondEvenTailIndex_lt q k hk) hjnext
  calc
    boundaryQuotient q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
        routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundaryShiftParam q a hnot_close) :=
      boundaryQuotient_B_even_shift q a hnot_two hnot_close
        (boundarySecondEvenParam_even q j
          (boundaryCycleSecondEvenTailIndex_lt q k hk))
    _ = routeEBoundaryNode RouteEBoundaryLabel.L03
          (boundarySecondEvenParam q (j + 1) hjnext) := by
      rw [boundarySecondEvenParam_shift_succ q j
        (boundaryCycleSecondEvenTailIndex_lt q k hk) hjnext hnot_close]

set_option linter.flexible false in
theorem boundaryCycleSecondEvenTail_step_odd (q k : Nat)
    (hk : k < boundaryCycleSecondEvenTailCount q)
    (hks : k + 1 < boundaryCycleSecondEvenTailCount q)
    (hodd : k % 2 ≠ 0) :
    boundaryQuotient q (boundaryCycleSecondEvenTailNode q k hk) =
      boundaryCycleSecondEvenTailNode q (k + 1) hks := by
  have hnext_even : (k + 1) % 2 = 0 := by omega
  simp [boundaryCycleSecondEvenTailNode, hodd, hnext_even,
    boundaryCycleSecondEvenTailIndex_succ_of_odd k hodd]
  let j := boundaryCycleSecondEvenTailIndex k + 1
  let a := boundarySecondEvenParam q j
      (boundaryCycleSecondEvenTailIndex_succ_lt q k hk hodd)
  exact boundaryQuotient_A_even q a
    (by
      dsimp [a, j]
      exact boundarySecondEvenParam_ne_half q
        (boundaryCycleSecondEvenTailIndex k + 1)
        (boundaryCycleSecondEvenTailIndex_succ_lt q k hk hodd))
    (by
      dsimp [a, j]
      exact boundarySecondEvenParam_even q
        (boundaryCycleSecondEvenTailIndex k + 1)
        (boundaryCycleSecondEvenTailIndex_succ_lt q k hk hodd))

theorem boundarySecondEvenParam_zero_eq_halfSubTwo (q : Nat)
    (hk : 0 < quarter q - 1) :
    boundarySecondEvenParam q 0 hk = boundaryParamHalfSubTwo q := by
  apply Subtype.ext
  apply ZMod.val_injective (modulus q)
  rw [boundarySecondEvenParam_val, boundaryParamHalfSubTwo,
    RouteENonzeroSeam.ofNat_val]
  simp [boundarySecondEvenValue]

theorem boundaryCycleSecondOddFinalNode_zero (q : Nat)
    (hk : 0 < boundaryCycleSecondOddFinalCount q) :
    boundaryCycleSecondOddFinalNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L03
        (boundaryParamHalfSubTwo q) := rfl

theorem boundaryCycleSecondEvenTailNode_zero (q : Nat)
    (hk : 0 < boundaryCycleSecondEvenTailCount q) :
    boundaryCycleSecondEvenTailNode q 0 hk =
      routeEBoundaryNode RouteEBoundaryLabel.L04
        (boundarySecondEvenParam q 0 (by simp [quarter])) := by
  simp [boundaryCycleSecondEvenTailNode, boundaryCycleSecondEvenTailIndex]

theorem boundaryCycleSecondOddFinal_to_secondEvenTail (q : Nat)
    (hf : 0 < boundaryCycleSecondOddFinalCount q)
    (he : 0 < boundaryCycleSecondEvenTailCount q) :
    boundaryQuotient q (boundaryCycleSecondOddFinalNode q 0 hf) =
      boundaryCycleSecondEvenTailNode q 0 he := by
  rw [boundaryCycleSecondOddFinalNode_zero q hf,
    boundaryCycleSecondEvenTailNode_zero q he]
  rw [boundarySecondEvenParam_zero_eq_halfSubTwo q (by simp [quarter])]
  exact boundaryQuotient_A_even q (boundaryParamHalfSubTwo q) (by
    simp [boundaryParamHalfSubTwo, RouteENonzeroSeam.ofNat_val, half])
    (by
      simp [boundaryParamHalfSubTwo, RouteENonzeroSeam.ofNat_val, half,
        Nat.add_mod, Nat.mul_mod])

theorem boundaryCycleSecondEvenTailLastIndex_eq (q : Nat) :
    boundaryCycleSecondEvenTailIndex
        (boundaryCycleSecondEvenTailCount q - 1) =
      quarter q - 2 := by
  simp [boundaryCycleSecondEvenTailIndex, boundaryCycleSecondEvenTailCount,
    quarter]
  omega

theorem boundaryCycleSecondEvenTailLast_even (q : Nat) :
    (boundaryCycleSecondEvenTailCount q - 1) % 2 = 0 := by
  simp [boundaryCycleSecondEvenTailCount, quarter]
  omega

theorem boundarySecondEvenValue_last_eq_half_add_two (q : Nat) :
    boundarySecondEvenValue q (quarter q - 2) = half q + 2 := by
  have hpar : (quarter q - 2) % 2 ≠ 0 := by
    simp [quarter]
    omega
  rw [boundarySecondEvenValue, if_neg hpar]
  simp [quarter, half, modulus]
  omega

theorem boundarySecondEvenParam_last_val_half_add_two (q : Nat) :
    (boundarySecondEvenParam q (quarter q - 2)
      (by simp [quarter])).1.val = half q + 2 := by
  rw [boundarySecondEvenParam_val]
  exact boundarySecondEvenValue_last_eq_half_add_two q

set_option linter.flexible false in
theorem boundaryCycleSecondEvenTail_to_zero (q : Nat)
    (hlast : boundaryCycleSecondEvenTailCount q - 1 <
      boundaryCycleSecondEvenTailCount q) :
    boundaryQuotient q
        (boundaryCycleSecondEvenTailNode q
          (boundaryCycleSecondEvenTailCount q - 1) hlast) =
      routeEBoundaryZero := by
  have heven := boundaryCycleSecondEvenTailLast_even q
  simp [boundaryCycleSecondEvenTailNode, heven,
    boundaryCycleSecondEvenTailLastIndex_eq q]
  exact boundaryQuotient_B_close q
    (boundarySecondEvenParam q (quarter q - 2) (by simp [quarter]))
    (boundarySecondEvenParam_last_val_half_add_two q)

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

def boundaryCycleFirstOddBSubOneStart (q : Nat) : Nat :=
  boundaryCycleFirstOddStart q + boundaryCycleFirstOddLaneCount q

def boundaryCycleFirstOddCRunStart (q : Nat) : Nat :=
  boundaryCycleFirstOddBSubOneStart q + boundaryCycleFirstOddBSubOneCount q

def boundaryCycleSecondOddFinalStart (q : Nat) : Nat :=
  boundaryCycleSecondOddStart q + boundaryCycleSecondOddLaneCount q

theorem boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one
    (q : Nat) :
    boundaryCycleFirstOddBSubOneStart q = modulus q + half q + 1 := by
  rw [boundaryCycleFirstOddBSubOneStart,
    boundaryCycleFirstOddStart_eq_modulus_add_three]
  simp [boundaryCycleFirstOddLaneCount, quarter, half]
  omega

theorem boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two
    (q : Nat) :
    boundaryCycleFirstOddCRunStart q = modulus q + half q + 2 := by
  rw [boundaryCycleFirstOddCRunStart,
    boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
  simp [boundaryCycleFirstOddBSubOneCount]

theorem boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half
    (q : Nat) :
    boundaryCycleSecondOddFinalStart q = 2 * modulus q + half q := by
  rw [boundaryCycleSecondOddFinalStart,
    boundaryCycleSecondOddStart_eq_two_modulus_add_two]
  simp [boundaryCycleSecondOddLaneCount, quarter, half]
  omega

noncomputable def boundaryCycleNodeAt (q n : Nat)
    (hn : n < boundaryCycleLength q) :
    RouteEBoundaryNode (modulus q) :=
  if hsp : n < boundaryCycleSpineCount q then
    boundaryCycleSpineNode q n hsp
  else if hfe : n < boundaryCycleB2BridgeStart q then
    boundaryCycleFirstEvenTailNode q
      (n - boundaryCycleFirstEvenStart q) (by
        simp_all [boundaryCycleFirstEvenStart, boundaryCycleB2BridgeStart]
        omega)
  else if hb2 : n < boundaryCycleFirstOddStart q then
    boundaryCycleB2BridgeNode q
      (n - boundaryCycleB2BridgeStart q) (by
        simp_all [boundaryCycleB2BridgeStart, boundaryCycleFirstOddStart,
          boundaryCycleB2BridgeCount])
  else if hfo : n < boundaryCycleFirstOddBSubOneStart q then
    boundaryCycleFirstOddLaneNode q
      (n - boundaryCycleFirstOddStart q) (by
        simp_all [boundaryCycleFirstOddBSubOneStart]
        omega)
  else if hfb : n < boundaryCycleFirstOddCRunStart q then
    boundaryCycleFirstOddBSubOneNode q
      (n - boundaryCycleFirstOddBSubOneStart q) (by
        simp_all [boundaryCycleFirstOddCRunStart,
          boundaryCycleFirstOddBSubOneCount])
  else if hfc : n < boundaryCycleALastBridgeStart q then
    boundaryCycleFirstOddCRunNode q
      (n - boundaryCycleFirstOddCRunStart q) (by
        simp_all [boundaryCycleFirstOddCRunStart,
          boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
          boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
          boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
          boundaryCycleFirstOddCRunCount, quarter, half]
        omega)
  else if ha : n < boundaryCycleSecondOddStart q then
    boundaryCycleALastBridgeNode q
      (n - boundaryCycleALastBridgeStart q) (by
        simp_all [boundaryCycleALastBridgeStart, boundaryCycleSecondOddStart,
          boundaryCycleALastBridgeCount])
  else if hso : n < boundaryCycleSecondOddFinalStart q then
    boundaryCycleSecondOddLaneNode q
      (n - boundaryCycleSecondOddStart q) (by
        simp_all [boundaryCycleSecondOddFinalStart]
        omega)
  else if hsf : n < boundaryCycleSecondEvenStart q then
    boundaryCycleSecondOddFinalNode q
      (n - boundaryCycleSecondOddFinalStart q) (by
        simp_all [boundaryCycleSecondOddFinalStart,
          boundaryCycleSecondEvenStart, boundaryCycleSecondOddTailCount,
          boundaryCycleSecondOddLaneCount, boundaryCycleSecondOddFinalCount]
        omega)
  else
    boundaryCycleSecondEvenTailNode q
      (n - boundaryCycleSecondEvenStart q) (by
        have hi : n < boundaryCycleSecondEvenStart q +
            boundaryCycleSecondEvenTailCount q := by
          have hilen : n < boundaryCycleLength q := by
            exact hn
          simp [boundaryCycleLength, boundaryCycleSecondEvenStart,
            boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
            boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
            boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
            boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
            boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
            boundaryCycleSecondOddTailCount, boundaryCycleSecondEvenTailCount,
            quarter, half, modulus] at hilen ⊢
          omega
        omega)

noncomputable def boundaryCycleNode (q : Nat)
    (i : Fin (boundaryCycleLength q)) :
    RouteEBoundaryNode (modulus q) :=
  boundaryCycleNodeAt q i.val i.2

theorem boundaryCycleNode_zero (q : Nat) :
    boundaryCycleNode q
        ⟨0, by simp [boundaryCycleLength, modulus]; omega⟩ =
      routeEBoundaryZero := by
  simp [boundaryCycleNode, boundaryCycleNodeAt, boundaryCycleSpineNode,
    boundaryCycleSpineCount, half]

theorem boundaryCycleNodeAt_last (q : Nat)
    (hn : boundaryCycleLength q - 1 < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleLength q - 1) hn =
      boundaryCycleSecondEvenTailNode q
        (boundaryCycleSecondEvenTailCount q - 1)
        (by simp [boundaryCycleSecondEvenTailCount, quarter]; omega) := by
  have hsp :
      ¬ boundaryCycleLength q - 1 < boundaryCycleSpineCount q := by
    simp [boundaryCycleLength, boundaryCycleSpineCount, half, modulus]
    omega
  have hfe :
      ¬ boundaryCycleLength q - 1 < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleLength, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, quarter, half, modulus]
    omega
  have hb2 :
      ¬ boundaryCycleLength q - 1 < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleLength, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, quarter, half, modulus]
    omega
  have hfo :
      ¬ boundaryCycleLength q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleLength, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddLaneCount, quarter, half, modulus]
    omega
  have hfb :
      ¬ boundaryCycleLength q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleLength, boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter, half, modulus]
    omega
  have hfc :
      ¬ boundaryCycleLength q - 1 <
        boundaryCycleALastBridgeStart q := by
    simp [boundaryCycleLength, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, quarter, half, modulus]
    omega
  have ha :
      ¬ boundaryCycleLength q - 1 < boundaryCycleSecondOddStart q := by
    simp [boundaryCycleLength, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, quarter, half, modulus]
    omega
  have hso :
      ¬ boundaryCycleLength q - 1 <
        boundaryCycleSecondOddFinalStart q := by
    simp [boundaryCycleLength, boundaryCycleSecondOddFinalStart,
      boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleSecondOddLaneCount, quarter, half, modulus]
    omega
  have hsf :
      ¬ boundaryCycleLength q - 1 < boundaryCycleSecondEvenStart q := by
    simp [boundaryCycleLength, boundaryCycleSecondEvenStart,
      boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleSecondOddTailCount, quarter, half, modulus]
    omega
  have hidx :
      boundaryCycleLength q - 1 - boundaryCycleSecondEvenStart q =
        boundaryCycleSecondEvenTailCount q - 1 := by
    simp [boundaryCycleLength, boundaryCycleSecondEvenStart,
      boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleSecondOddTailCount, boundaryCycleSecondEvenTailCount,
      quarter, half, modulus]
    omega
  simp [boundaryCycleNodeAt, hsp, hfe, hb2, hfo, hfb, hfc, ha, hso, hsf,
    hidx]

theorem boundaryCycleNode_last_to_zero (q : Nat) :
    boundaryQuotient q
        (boundaryCycleNode q
          ⟨boundaryCycleLength q - 1,
            by simp [boundaryCycleLength, modulus]; omega⟩) =
      boundaryCycleNode q
        ⟨0, by simp [boundaryCycleLength, modulus]; omega⟩ := by
  rw [boundaryCycleNode, boundaryCycleNodeAt_last q,
    boundaryCycleNode_zero q]
  exact boundaryCycleSecondEvenTail_to_zero q
    (by simp [boundaryCycleSecondEvenTailCount, quarter]; omega)

theorem boundaryCycleNodeAt_succ_spine (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hsp : n < boundaryCycleSpineCount q)
    (hsps : n + 1 < boundaryCycleSpineCount q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hn_node :
      boundaryCycleNodeAt q n hn = boundaryCycleSpineNode q n hsp := by
    simp [boundaryCycleNodeAt, hsp]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleSpineNode q (n + 1) hsps := by
    simp [boundaryCycleNodeAt, hsps]
  rw [hn_node, hns_node]
  symm
  by_cases h0 : n = 0
  · subst n
    exact boundaryCycleSpine_step_zero q hsp hsps
  by_cases h1 : n = 1
  · subst n
    exact boundaryCycleSpine_step_one q hsp hsps
  by_cases h2 : n = 2
  · subst n
    exact boundaryCycleSpine_step_two q hsp hsps
  by_cases h3 : n = 3
  · subst n
    exact boundaryCycleSpine_step_three q hsp hsps
  by_cases h4 : n = 4
  · subst n
    exact boundaryCycleSpine_step_four q hsp hsps
  by_cases hlast : n = half q + 2
  · subst n
    exact boundaryCycleSpine_step_C_last q hsp hsps
  exact boundaryCycleSpine_step_C_run q n (by omega) (by
      simp [boundaryCycleSpineCount] at hsps
      omega) hsp hsps

theorem boundaryCycleNodeAt_spine_to_firstEven (q : Nat)
    (hn : boundaryCycleFirstEvenStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleFirstEvenStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleFirstEvenStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleFirstEvenStart q - 1) hn) := by
  have hprev :
      boundaryCycleFirstEvenStart q - 1 = half q + 3 := by
    simp [boundaryCycleFirstEvenStart, boundaryCycleSpineCount, half]
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleFirstEvenStart q - 1) hn =
        boundaryCycleSpineNode q (half q + 3)
          (by simp [boundaryCycleSpineCount, half]) := by
    simp [boundaryCycleNodeAt, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, half]
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleFirstEvenStart q) hns =
        boundaryCycleFirstEvenTailNode q 0
          (by simp [boundaryCycleFirstEvenTailCount, quarter]) := by
    simp [boundaryCycleNodeAt, boundaryCycleFirstEvenStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenTailCount,
      boundaryCycleSpineCount, quarter]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleSpine_to_firstEvenTail q
    (by simp [boundaryCycleSpineCount, half])
    (by simp [boundaryCycleFirstEvenTailCount, quarter])

theorem boundaryCycleNodeAt_succ_firstEven (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hstart : boundaryCycleFirstEvenStart q ≤ n)
    (hnext : n + 1 < boundaryCycleB2BridgeStart q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hsp : ¬ n < boundaryCycleSpineCount q := by
    simpa [boundaryCycleFirstEvenStart] using not_lt.mpr hstart
  have hsps : ¬ n + 1 < boundaryCycleSpineCount q := by
    exact not_lt.mpr (by
      simpa [boundaryCycleFirstEvenStart] using
        Nat.le_trans hstart (Nat.le_succ n))
  have hfe : n < boundaryCycleB2BridgeStart q := by omega
  have htail : n - boundaryCycleFirstEvenStart q <
      boundaryCycleFirstEvenTailCount q := by
    rw [boundaryCycleB2BridgeStart] at hfe
    omega
  have hnext_tail : n + 1 - boundaryCycleFirstEvenStart q <
      boundaryCycleFirstEvenTailCount q := by
    rw [boundaryCycleB2BridgeStart] at hnext
    omega
  have hidx :
      n + 1 - boundaryCycleFirstEvenStart q =
        (n - boundaryCycleFirstEvenStart q) + 1 := by omega
  have htail_succ : (n - boundaryCycleFirstEvenStart q) + 1 <
      boundaryCycleFirstEvenTailCount q := by
    rw [← hidx]
    exact hnext_tail
  have hn_node :
      boundaryCycleNodeAt q n hn =
        boundaryCycleFirstEvenTailNode q
          (n - boundaryCycleFirstEvenStart q) htail := by
    simp [boundaryCycleNodeAt, hsp, hfe]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleFirstEvenTailNode q
          ((n - boundaryCycleFirstEvenStart q) + 1) htail_succ := by
    trans boundaryCycleFirstEvenTailNode q
      (n + 1 - boundaryCycleFirstEvenStart q) hnext_tail
    · simp [boundaryCycleNodeAt, hsps, hnext]
    · simp [hidx]
  rw [hn_node, hns_node]
  symm
  by_cases heven : (n - boundaryCycleFirstEvenStart q) % 2 = 0
  · exact boundaryCycleFirstEvenTail_step_even q
      (n - boundaryCycleFirstEvenStart q)
      htail
      htail_succ
      heven
  · exact boundaryCycleFirstEvenTail_step_odd q
      (n - boundaryCycleFirstEvenStart q)
      htail
      htail_succ
      heven

theorem boundaryCycleNodeAt_firstEven_to_B2Bridge (q : Nat)
    (hn : boundaryCycleB2BridgeStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleB2BridgeStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleB2BridgeStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleB2BridgeStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleB2BridgeStart q - 1 < boundaryCycleSpineCount q := by
    simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount, quarter, half]
    omega
  have hprev_fe :
      boundaryCycleB2BridgeStart q - 1 < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount, quarter, half]
  have hprev_idx :
      boundaryCycleB2BridgeStart q - 1 - boundaryCycleFirstEvenStart q =
        boundaryCycleFirstEvenTailCount q - 1 := by
    simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount, quarter, half]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleB2BridgeStart q - 1) hn =
        boundaryCycleFirstEvenTailNode q
          (boundaryCycleFirstEvenTailCount q - 1)
          (by simp [boundaryCycleFirstEvenTailCount, quarter]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleB2BridgeStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount, quarter, half]
  have hnext_fe :
      ¬ boundaryCycleB2BridgeStart q < boundaryCycleB2BridgeStart q := by
    omega
  have hnext_b2 :
      boundaryCycleB2BridgeStart q < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeCount]
  have hnext_idx :
      boundaryCycleB2BridgeStart q - boundaryCycleB2BridgeStart q = 0 := by
    omega
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleB2BridgeStart q) hns =
        boundaryCycleB2BridgeNode q 0
          (by simp [boundaryCycleB2BridgeCount]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_b2]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleFirstEvenTail_to_B2Bridge q
    (by simp [boundaryCycleFirstEvenTailCount, quarter])
    (by simp [boundaryCycleB2BridgeCount])

theorem boundaryCycleNodeAt_B2Bridge_to_firstOdd (q : Nat)
    (hn : boundaryCycleFirstOddStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleFirstOddStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleFirstOddStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleFirstOddStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleFirstOddStart q - 1 < boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      quarter, half]
  have hprev_fe :
      ¬ boundaryCycleFirstOddStart q - 1 < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleB2BridgeCount]
  have hprev_b2 :
      boundaryCycleFirstOddStart q - 1 < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      quarter, half]
  have hprev_idx :
      boundaryCycleFirstOddStart q - 1 - boundaryCycleB2BridgeStart q = 0 := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeCount]
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddStart q - 1) hn =
        boundaryCycleB2BridgeNode q 0 (by simp [boundaryCycleB2BridgeCount]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleFirstOddStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      quarter, half]
    omega
  have hnext_fe :
      ¬ boundaryCycleFirstOddStart q < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeCount]
  have hnext_b2 :
      ¬ boundaryCycleFirstOddStart q < boundaryCycleFirstOddStart q := by
    omega
  have hnext_fo :
      boundaryCycleFirstOddStart q < boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter]
  have hnext_idx :
      boundaryCycleFirstOddStart q - boundaryCycleFirstOddStart q = 0 := by
    omega
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddStart q) hns =
        boundaryCycleFirstOddLaneNode q 0
          (by simp [boundaryCycleFirstOddLaneCount, quarter]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_fo]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleB2Bridge_to_firstOddLane q
    (by simp [boundaryCycleB2BridgeCount])
    (by simp [boundaryCycleFirstOddLaneCount, quarter])

theorem boundaryCycleNodeAt_succ_firstOddLane (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hstart : boundaryCycleFirstOddStart q ≤ n)
    (hnext : n + 1 < boundaryCycleFirstOddBSubOneStart q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hsp : ¬ n < boundaryCycleSpineCount q := by
    have hle : boundaryCycleSpineCount q ≤ n := by
      have hs := hstart
      simp [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
        boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
        boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
        quarter, half] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfe : ¬ n < boundaryCycleB2BridgeStart q := by
    rw [boundaryCycleFirstOddStart] at hstart
    omega
  have hb2 : ¬ n < boundaryCycleFirstOddStart q := not_lt.mpr hstart
  have hsps : ¬ n + 1 < boundaryCycleSpineCount q := by
    exact not_lt.mpr (by
      exact Nat.le_trans (not_lt.mp hsp) (Nat.le_succ n))
  have hfes : ¬ n + 1 < boundaryCycleB2BridgeStart q := by
    exact not_lt.mpr (by
      exact Nat.le_trans (not_lt.mp hfe) (Nat.le_succ n))
  have hb2s : ¬ n + 1 < boundaryCycleFirstOddStart q := by
    exact not_lt.mpr (Nat.le_trans hstart (Nat.le_succ n))
  have hfo : n < boundaryCycleFirstOddBSubOneStart q := by omega
  have hlane : n - boundaryCycleFirstOddStart q <
      boundaryCycleFirstOddLaneCount q := by
    rw [boundaryCycleFirstOddBSubOneStart] at hfo
    omega
  have hnext_lane : n + 1 - boundaryCycleFirstOddStart q <
      boundaryCycleFirstOddLaneCount q := by
    rw [boundaryCycleFirstOddBSubOneStart] at hnext
    omega
  have hidx :
      n + 1 - boundaryCycleFirstOddStart q =
        (n - boundaryCycleFirstOddStart q) + 1 := by omega
  have hlane_succ : (n - boundaryCycleFirstOddStart q) + 1 <
      boundaryCycleFirstOddLaneCount q := by
    rw [← hidx]
    exact hnext_lane
  have hn_node :
      boundaryCycleNodeAt q n hn =
        boundaryCycleFirstOddLaneNode q
          (n - boundaryCycleFirstOddStart q) hlane := by
    simp [boundaryCycleNodeAt, hsp, hfe, hb2, hfo]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleFirstOddLaneNode q
          ((n - boundaryCycleFirstOddStart q) + 1) hlane_succ := by
    trans boundaryCycleFirstOddLaneNode q
      (n + 1 - boundaryCycleFirstOddStart q) hnext_lane
    · simp [boundaryCycleNodeAt, hsps, hfes, hb2s, hnext]
    · simp [hidx]
  rw [hn_node, hns_node]
  symm
  by_cases heven : (n - boundaryCycleFirstOddStart q) % 2 = 0
  · exact boundaryCycleFirstOddLane_step_even q
      (n - boundaryCycleFirstOddStart q) hlane hlane_succ heven
  · exact boundaryCycleFirstOddLane_step_odd q
      (n - boundaryCycleFirstOddStart q) hlane hlane_succ heven

theorem boundaryCycleNodeAt_firstOddLane_to_BSubOne (q : Nat)
    (hn : boundaryCycleFirstOddBSubOneStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleFirstOddBSubOneStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleFirstOddBSubOneStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q
          (boundaryCycleFirstOddBSubOneStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleFirstOddBSubOneStart q - 1 <
        boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hprev_fe :
      ¬ boundaryCycleFirstOddBSubOneStart q - 1 <
        boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount, quarter]
  have hprev_b2 :
      ¬ boundaryCycleFirstOddBSubOneStart q - 1 <
        boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter]
    omega
  have hprev_fo :
      boundaryCycleFirstOddBSubOneStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      quarter, half]
  have hprev_idx :
      boundaryCycleFirstOddBSubOneStart q - 1 -
          boundaryCycleFirstOddStart q =
        boundaryCycleFirstOddLaneCount q - 1 := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddBSubOneStart q - 1) hn =
        boundaryCycleFirstOddLaneNode q
          (boundaryCycleFirstOddLaneCount q - 1)
          (by simp [boundaryCycleFirstOddLaneCount, quarter]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleFirstOddBSubOneStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hnext_fe :
      ¬ boundaryCycleFirstOddBSubOneStart q < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount, quarter]
    omega
  have hnext_b2 :
      ¬ boundaryCycleFirstOddBSubOneStart q < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter]
  have hnext_fo :
      ¬ boundaryCycleFirstOddBSubOneStart q <
        boundaryCycleFirstOddBSubOneStart q := by omega
  have hnext_fb :
      boundaryCycleFirstOddBSubOneStart q <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneCount]
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddBSubOneStart q) hns =
        boundaryCycleFirstOddBSubOneNode q 0
          (by simp [boundaryCycleFirstOddBSubOneCount]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fb]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleFirstOddLane_to_BSubOne q
    (by simp [boundaryCycleFirstOddLaneCount, quarter])
    (by simp [boundaryCycleFirstOddBSubOneCount])

theorem boundaryCycleNodeAt_BSubOne_to_CRun (q : Nat)
    (hn : boundaryCycleFirstOddCRunStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleFirstOddCRunStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleFirstOddCRunStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleFirstOddCRunStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleFirstOddCRunStart q - 1 < boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter, half]
    omega
  have hprev_fe :
      ¬ boundaryCycleFirstOddCRunStart q - 1 < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter]
    omega
  have hprev_b2 :
      ¬ boundaryCycleFirstOddCRunStart q - 1 < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter]
  have hprev_fo :
      ¬ boundaryCycleFirstOddCRunStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneCount]
  have hprev_fb :
      boundaryCycleFirstOddCRunStart q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter, half]
  have hprev_idx :
      boundaryCycleFirstOddCRunStart q - 1 -
          boundaryCycleFirstOddBSubOneStart q = 0 := by
    simp [boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneCount]
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddCRunStart q - 1) hn =
        boundaryCycleFirstOddBSubOneNode q 0
          (by simp [boundaryCycleFirstOddBSubOneCount]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_fb, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleFirstOddCRunStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter, half]
    omega
  have hnext_fe :
      ¬ boundaryCycleFirstOddCRunStart q < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter]
    omega
  have hnext_b2 :
      ¬ boundaryCycleFirstOddCRunStart q < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, quarter]
    omega
  have hnext_fo :
      ¬ boundaryCycleFirstOddCRunStart q <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneCount]
  have hnext_fb :
      ¬ boundaryCycleFirstOddCRunStart q <
        boundaryCycleFirstOddCRunStart q := by omega
  have hnext_fc :
      boundaryCycleFirstOddCRunStart q <
        boundaryCycleALastBridgeStart q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
    omega
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleFirstOddCRunStart q) hns =
        boundaryCycleFirstOddCRunNode q 0
          (by simp [boundaryCycleFirstOddCRunCount, half]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fo,
      hnext_fc]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleFirstOddBSubOne_to_CRun q
    (by simp [boundaryCycleFirstOddBSubOneCount])
    (by simp [boundaryCycleFirstOddCRunCount, half])

theorem boundaryCycleNodeAt_succ_firstOddCRun (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hstart : boundaryCycleFirstOddCRunStart q ≤ n)
    (hnext : n + 1 < boundaryCycleALastBridgeStart q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hsp : ¬ n < boundaryCycleSpineCount q := by
    have hle : boundaryCycleSpineCount q ≤ n := by
      have hs := hstart
      rw [boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two] at hs
      simp [boundaryCycleSpineCount, half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfe : ¬ n < boundaryCycleB2BridgeStart q := by
    have hle : boundaryCycleB2BridgeStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two] at hs
      rw [boundaryCycleB2BridgeStart_eq_modulus_add_two]
      simp [half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hb2 : ¬ n < boundaryCycleFirstOddStart q := by
    have hle : boundaryCycleFirstOddStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two] at hs
      rw [boundaryCycleFirstOddStart_eq_modulus_add_three]
      simp [half] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfo : ¬ n < boundaryCycleFirstOddBSubOneStart q := by
    have hle : boundaryCycleFirstOddBSubOneStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleFirstOddCRunStart] at hs
      omega
    exact not_lt.mpr hle
  have hfb : ¬ n < boundaryCycleFirstOddCRunStart q := not_lt.mpr hstart
  have hsps : ¬ n + 1 < boundaryCycleSpineCount q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hsp) (Nat.le_succ n))
  have hfes : ¬ n + 1 < boundaryCycleB2BridgeStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfe) (Nat.le_succ n))
  have hb2s : ¬ n + 1 < boundaryCycleFirstOddStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hb2) (Nat.le_succ n))
  have hfos : ¬ n + 1 < boundaryCycleFirstOddBSubOneStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfo) (Nat.le_succ n))
  have hfbs : ¬ n + 1 < boundaryCycleFirstOddCRunStart q :=
    not_lt.mpr (Nat.le_trans hstart (Nat.le_succ n))
  have hfc : n < boundaryCycleALastBridgeStart q := by omega
  have hrun : n - boundaryCycleFirstOddCRunStart q <
      boundaryCycleFirstOddCRunCount q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      boundaryCycleFirstOddCRunCount, quarter, half] at hfc ⊢
    omega
  have hnext_run : n + 1 - boundaryCycleFirstOddCRunStart q <
      boundaryCycleFirstOddCRunCount q := by
    simp [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      boundaryCycleFirstOddCRunCount, quarter, half] at hnext ⊢
    omega
  have hidx :
      n + 1 - boundaryCycleFirstOddCRunStart q =
        (n - boundaryCycleFirstOddCRunStart q) + 1 := by omega
  have hrun_succ : (n - boundaryCycleFirstOddCRunStart q) + 1 <
      boundaryCycleFirstOddCRunCount q := by
    rw [← hidx]
    exact hnext_run
  have hn_node :
      boundaryCycleNodeAt q n hn =
        boundaryCycleFirstOddCRunNode q
          (n - boundaryCycleFirstOddCRunStart q) hrun := by
    simp [boundaryCycleNodeAt, hsp, hfe, hb2, hfo, hfb, hfc]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleFirstOddCRunNode q
          ((n - boundaryCycleFirstOddCRunStart q) + 1) hrun_succ := by
    trans boundaryCycleFirstOddCRunNode q
      (n + 1 - boundaryCycleFirstOddCRunStart q) hnext_run
    · simp [boundaryCycleNodeAt, hsps, hfes, hb2s, hfos, hfbs, hnext]
    · simp [hidx]
  rw [hn_node, hns_node]
  symm
  exact boundaryCycleFirstOddCRun_step q
    (n - boundaryCycleFirstOddCRunStart q) hrun hrun_succ

theorem boundaryCycleNodeAt_firstOddCRun_to_ALast (q : Nat)
    (hn : boundaryCycleALastBridgeStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleALastBridgeStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleALastBridgeStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleALastBridgeStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleALastBridgeStart q - 1 < boundaryCycleSpineCount q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hprev_fe :
      ¬ boundaryCycleALastBridgeStart q - 1 < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
  have hprev_b2 :
      ¬ boundaryCycleALastBridgeStart q - 1 < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hprev_fo :
      ¬ boundaryCycleALastBridgeStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hprev_fb :
      ¬ boundaryCycleALastBridgeStart q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
    omega
  have hprev_fc :
      boundaryCycleALastBridgeStart q - 1 <
        boundaryCycleALastBridgeStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
  have hprev_idx :
      boundaryCycleALastBridgeStart q - 1 -
          boundaryCycleFirstOddCRunStart q =
        boundaryCycleFirstOddCRunCount q - 1 := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      boundaryCycleFirstOddCRunCount, quarter, half]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleALastBridgeStart q - 1) hn =
        boundaryCycleFirstOddCRunNode q
          (boundaryCycleFirstOddCRunCount q - 1)
          (by simp [boundaryCycleFirstOddCRunCount, half]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_fb, hprev_fc, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleALastBridgeStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hnext_fe :
      ¬ boundaryCycleALastBridgeStart q < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hnext_b2 :
      ¬ boundaryCycleALastBridgeStart q < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      quarter, half]
  have hnext_fo :
      ¬ boundaryCycleALastBridgeStart q <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hnext_fb :
      ¬ boundaryCycleALastBridgeStart q <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
    omega
  have hnext_fc :
      ¬ boundaryCycleALastBridgeStart q < boundaryCycleALastBridgeStart q := by
    omega
  have hnext_a :
      boundaryCycleALastBridgeStart q < boundaryCycleSecondOddStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeCount]
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleALastBridgeStart q) hns =
        boundaryCycleALastBridgeNode q 0
          (by simp [boundaryCycleALastBridgeCount]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fo,
      hnext_fb, hnext_a]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleFirstOddCRun_to_ALast q
    (by simp [boundaryCycleFirstOddCRunCount, half])
    (by simp [boundaryCycleALastBridgeCount])

theorem boundaryCycleNodeAt_ALast_to_secondOdd (q : Nat)
    (hn : boundaryCycleSecondOddStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleSecondOddStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleSecondOddStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleSecondOddStart q - 1) hn) := by
  have hprev_eq :
      boundaryCycleSecondOddStart q - 1 =
        boundaryCycleALastBridgeStart q := by
    rw [boundaryCycleSecondOddStart]
    simp [boundaryCycleALastBridgeCount]
  have hprev_sp :
      ¬ boundaryCycleSecondOddStart q - 1 < boundaryCycleSpineCount q := by
    rw [hprev_eq]
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hprev_fe :
      ¬ boundaryCycleSecondOddStart q - 1 < boundaryCycleB2BridgeStart q := by
    rw [hprev_eq]
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      quarter, half]
    omega
  have hprev_b2 :
      ¬ boundaryCycleSecondOddStart q - 1 < boundaryCycleFirstOddStart q := by
    rw [hprev_eq]
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      quarter, half]
  have hprev_fo :
      ¬ boundaryCycleSecondOddStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    rw [hprev_eq]
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hprev_fb :
      ¬ boundaryCycleSecondOddStart q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    rw [hprev_eq]
    simp [boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
    omega
  have hprev_fc :
      ¬ boundaryCycleSecondOddStart q - 1 <
        boundaryCycleALastBridgeStart q := by
    rw [hprev_eq]
    omega
  have hprev_a :
      boundaryCycleSecondOddStart q - 1 <
        boundaryCycleSecondOddStart q := by
    rw [hprev_eq]
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeCount]
  have hprev_idx :
      boundaryCycleSecondOddStart q - 1 -
          boundaryCycleALastBridgeStart q = 0 := by
    rw [hprev_eq]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleSecondOddStart q - 1) hn =
        boundaryCycleALastBridgeNode q 0
          (by simp [boundaryCycleALastBridgeCount]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_fb, hprev_fc, hprev_a, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleSecondOddStart q < boundaryCycleSpineCount q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleFirstEvenStart, boundaryCycleSpineCount,
      boundaryCycleFirstEvenTailCount, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      quarter, half]
    omega
  have hnext_fe :
      ¬ boundaryCycleSecondOddStart q < boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddStart, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      quarter, half]
    omega
  have hnext_b2 :
      ¬ boundaryCycleSecondOddStart q < boundaryCycleFirstOddStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      quarter, half]
    omega
  have hnext_fo :
      ¬ boundaryCycleSecondOddStart q <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter, half]
    omega
  have hnext_fb :
      ¬ boundaryCycleSecondOddStart q <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeStart,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
    omega
  have hnext_fc :
      ¬ boundaryCycleSecondOddStart q < boundaryCycleALastBridgeStart q := by
    simp [boundaryCycleSecondOddStart, boundaryCycleALastBridgeCount]
  have hnext_a :
      ¬ boundaryCycleSecondOddStart q < boundaryCycleSecondOddStart q := by
    omega
  have hnext_so :
      boundaryCycleSecondOddStart q < boundaryCycleSecondOddFinalStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddLaneCount,
      quarter]
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleSecondOddStart q) hns =
        boundaryCycleSecondOddLaneNode q 0
          (by simp [boundaryCycleSecondOddLaneCount, quarter]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fo,
      hnext_fb, hnext_fc, hnext_so]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleALastBridge_to_secondOddLane q
    (by simp [boundaryCycleALastBridgeCount])
    (by simp [boundaryCycleSecondOddLaneCount, quarter])

theorem boundaryCycleNodeAt_succ_secondOddLane (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hstart : boundaryCycleSecondOddStart q ≤ n)
    (hnext : n + 1 < boundaryCycleSecondOddFinalStart q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hsp : ¬ n < boundaryCycleSpineCount q := by
    have hle : boundaryCycleSpineCount q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      simp [boundaryCycleSpineCount, half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfe : ¬ n < boundaryCycleB2BridgeStart q := by
    have hle : boundaryCycleB2BridgeStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      rw [boundaryCycleB2BridgeStart_eq_modulus_add_two]
      simp [modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hb2 : ¬ n < boundaryCycleFirstOddStart q := by
    have hle : boundaryCycleFirstOddStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      rw [boundaryCycleFirstOddStart_eq_modulus_add_three]
      simp [modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfo : ¬ n < boundaryCycleFirstOddBSubOneStart q := by
    have hle : boundaryCycleFirstOddBSubOneStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      rw [boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
      simp [half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfb : ¬ n < boundaryCycleFirstOddCRunStart q := by
    have hle : boundaryCycleFirstOddCRunStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      rw [boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two]
      simp [half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfc : ¬ n < boundaryCycleALastBridgeStart q := by
    have hle : boundaryCycleALastBridgeStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two] at hs
      rw [boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
      omega
    exact not_lt.mpr hle
  have ha : ¬ n < boundaryCycleSecondOddStart q := not_lt.mpr hstart
  have hsps : ¬ n + 1 < boundaryCycleSpineCount q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hsp) (Nat.le_succ n))
  have hfes : ¬ n + 1 < boundaryCycleB2BridgeStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfe) (Nat.le_succ n))
  have hb2s : ¬ n + 1 < boundaryCycleFirstOddStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hb2) (Nat.le_succ n))
  have hfos : ¬ n + 1 < boundaryCycleFirstOddBSubOneStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfo) (Nat.le_succ n))
  have hfbs : ¬ n + 1 < boundaryCycleFirstOddCRunStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfb) (Nat.le_succ n))
  have hfcs : ¬ n + 1 < boundaryCycleALastBridgeStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfc) (Nat.le_succ n))
  have has : ¬ n + 1 < boundaryCycleSecondOddStart q :=
    not_lt.mpr (Nat.le_trans hstart (Nat.le_succ n))
  have hso : n < boundaryCycleSecondOddFinalStart q := by omega
  have hlane : n - boundaryCycleSecondOddStart q <
      boundaryCycleSecondOddLaneCount q := by
    rw [boundaryCycleSecondOddFinalStart] at hso
    omega
  have hnext_lane : n + 1 - boundaryCycleSecondOddStart q <
      boundaryCycleSecondOddLaneCount q := by
    rw [boundaryCycleSecondOddFinalStart] at hnext
    omega
  have hidx :
      n + 1 - boundaryCycleSecondOddStart q =
        (n - boundaryCycleSecondOddStart q) + 1 := by omega
  have hlane_succ : (n - boundaryCycleSecondOddStart q) + 1 <
      boundaryCycleSecondOddLaneCount q := by
    rw [← hidx]
    exact hnext_lane
  have hn_node :
      boundaryCycleNodeAt q n hn =
        boundaryCycleSecondOddLaneNode q
          (n - boundaryCycleSecondOddStart q) hlane := by
    simp [boundaryCycleNodeAt, hsp, hfe, hb2, hfo, hfb, hfc, ha, hso]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleSecondOddLaneNode q
          ((n - boundaryCycleSecondOddStart q) + 1) hlane_succ := by
    trans boundaryCycleSecondOddLaneNode q
      (n + 1 - boundaryCycleSecondOddStart q) hnext_lane
    · simp [boundaryCycleNodeAt, hsps, hfes, hb2s, hfos, hfbs, hfcs, has,
        hnext]
    · simp [hidx]
  rw [hn_node, hns_node]
  symm
  by_cases heven : (n - boundaryCycleSecondOddStart q) % 2 = 0
  · exact boundaryCycleSecondOddLane_step_even q
      (n - boundaryCycleSecondOddStart q) hlane hlane_succ heven
  · exact boundaryCycleSecondOddLane_step_odd q
      (n - boundaryCycleSecondOddStart q) hlane hlane_succ heven

theorem boundaryCycleNodeAt_secondOddLane_to_final (q : Nat)
    (hn : boundaryCycleSecondOddFinalStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleSecondOddFinalStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleSecondOddFinalStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleSecondOddFinalStart q - 1) hn) := by
  have hprev_sp :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleSpineCount q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      quarter, half]
    omega
  have hprev_fe :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleB2BridgeStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      quarter, half]
    omega
  have hprev_b2 :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleFirstOddStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleB2BridgeCount,
      boundaryCycleFirstOddTailCount, boundaryCycleALastBridgeCount,
      boundaryCycleSecondOddLaneCount, quarter, half]
    omega
  have hprev_fo :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      quarter, half]
  have hprev_fb :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      boundaryCycleFirstOddCRunStart, boundaryCycleFirstOddBSubOneStart,
      boundaryCycleFirstOddLaneCount, boundaryCycleFirstOddBSubOneCount,
      quarter, half]
  have hprev_fc :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleALastBridgeStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      quarter]
  have hprev_a :
      ¬ boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleSecondOddStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddLaneCount,
      quarter]
    omega
  have hprev_so :
      boundaryCycleSecondOddFinalStart q - 1 <
        boundaryCycleSecondOddFinalStart q := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
      boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount,
      boundaryCycleB2BridgeCount, boundaryCycleFirstOddTailCount,
      boundaryCycleALastBridgeCount, boundaryCycleSecondOddLaneCount,
      quarter, half]
  have hprev_idx :
      boundaryCycleSecondOddFinalStart q - 1 -
          boundaryCycleSecondOddStart q =
        boundaryCycleSecondOddLaneCount q - 1 := by
    simp [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddLaneCount,
      quarter]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleSecondOddFinalStart q - 1) hn =
        boundaryCycleSecondOddLaneNode q
          (boundaryCycleSecondOddLaneCount q - 1)
          (by simp [boundaryCycleSecondOddLaneCount, quarter]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_fb, hprev_fc, hprev_a, hprev_so, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleSecondOddFinalStart q < boundaryCycleSpineCount q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
    simp [boundaryCycleSpineCount, half, modulus]
    omega
  have hnext_fe :
      ¬ boundaryCycleSecondOddFinalStart q < boundaryCycleB2BridgeStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleB2BridgeStart_eq_modulus_add_two]
    simp [half, modulus]
    omega
  have hnext_b2 :
      ¬ boundaryCycleSecondOddFinalStart q < boundaryCycleFirstOddStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddStart_eq_modulus_add_three]
    simp [half, modulus]
    omega
  have hnext_fo :
      ¬ boundaryCycleSecondOddFinalStart q <
        boundaryCycleFirstOddBSubOneStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
    simp [modulus]
  have hnext_fb :
      ¬ boundaryCycleSecondOddFinalStart q <
        boundaryCycleFirstOddCRunStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two]
    simp [modulus]
    omega
  have hnext_fc :
      ¬ boundaryCycleSecondOddFinalStart q < boundaryCycleALastBridgeStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
    simp [half]
  have hnext_a :
      ¬ boundaryCycleSecondOddFinalStart q < boundaryCycleSecondOddStart q := by
    rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleSecondOddStart_eq_two_modulus_add_two]
    simp [half]
  have hnext_so :
      ¬ boundaryCycleSecondOddFinalStart q <
        boundaryCycleSecondOddFinalStart q := by omega
  have hnext_sf :
      boundaryCycleSecondOddFinalStart q < boundaryCycleSecondEvenStart q := by
    simp [boundaryCycleSecondEvenStart, boundaryCycleSecondOddFinalStart,
      boundaryCycleSecondOddStart, boundaryCycleSecondOddTailCount,
      boundaryCycleSecondOddLaneCount, quarter]
    omega
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleSecondOddFinalStart q) hns =
        boundaryCycleSecondOddFinalNode q 0
          (by simp [boundaryCycleSecondOddFinalCount]) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fo,
      hnext_fb, hnext_fc, hnext_a, hnext_sf]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleSecondOddLane_to_final q
    (by simp [boundaryCycleSecondOddLaneCount, quarter])
    (by simp [boundaryCycleSecondOddFinalCount])

theorem boundaryCycleNodeAt_secondOddFinal_to_secondEven (q : Nat)
    (hn : boundaryCycleSecondEvenStart q - 1 < boundaryCycleLength q)
    (hns : boundaryCycleSecondEvenStart q < boundaryCycleLength q) :
    boundaryCycleNodeAt q (boundaryCycleSecondEvenStart q) hns =
      boundaryQuotient q
        (boundaryCycleNodeAt q (boundaryCycleSecondEvenStart q - 1) hn) := by
  have hprev_eq :
      boundaryCycleSecondEvenStart q - 1 =
        boundaryCycleSecondOddFinalStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
    simp [half, modulus]
  have hprev_sp :
      ¬ boundaryCycleSecondEvenStart q - 1 < boundaryCycleSpineCount q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
    simp [boundaryCycleSpineCount, half, modulus]
    omega
  have hprev_fe :
      ¬ boundaryCycleSecondEvenStart q - 1 < boundaryCycleB2BridgeStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleB2BridgeStart_eq_modulus_add_two]
    simp [half, modulus]
    omega
  have hprev_b2 :
      ¬ boundaryCycleSecondEvenStart q - 1 < boundaryCycleFirstOddStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddStart_eq_modulus_add_three]
    simp [half, modulus]
    omega
  have hprev_fo :
      ¬ boundaryCycleSecondEvenStart q - 1 <
        boundaryCycleFirstOddBSubOneStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
    simp [modulus]
  have hprev_fb :
      ¬ boundaryCycleSecondEvenStart q - 1 <
        boundaryCycleFirstOddCRunStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two]
    simp [modulus]
    omega
  have hprev_fc :
      ¬ boundaryCycleSecondEvenStart q - 1 < boundaryCycleALastBridgeStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
    simp [half]
  have hprev_a :
      ¬ boundaryCycleSecondEvenStart q - 1 < boundaryCycleSecondOddStart q := by
    rw [hprev_eq, boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half,
      boundaryCycleSecondOddStart_eq_two_modulus_add_two]
    simp [half]
  have hprev_so :
      ¬ boundaryCycleSecondEvenStart q - 1 <
        boundaryCycleSecondOddFinalStart q := by
    rw [hprev_eq]
    omega
  have hprev_sf :
      boundaryCycleSecondEvenStart q - 1 < boundaryCycleSecondEvenStart q := by
    rw [hprev_eq]
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
    simp [half, modulus]
  have hprev_idx :
      boundaryCycleSecondEvenStart q - 1 -
          boundaryCycleSecondOddFinalStart q = 0 := by
    rw [hprev_eq]
    omega
  have hprev_node :
      boundaryCycleNodeAt q (boundaryCycleSecondEvenStart q - 1) hn =
        boundaryCycleSecondOddFinalNode q 0
          (by simp [boundaryCycleSecondOddFinalCount]) := by
    simp [boundaryCycleNodeAt, hprev_sp, hprev_fe, hprev_b2, hprev_fo,
      hprev_fb, hprev_fc, hprev_a, hprev_so, hprev_sf, hprev_idx]
  have hnext_sp :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleSpineCount q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one]
    simp [boundaryCycleSpineCount, half, modulus]
    omega
  have hnext_fe :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleB2BridgeStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleB2BridgeStart_eq_modulus_add_two]
    simp [half, modulus]
    omega
  have hnext_b2 :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleFirstOddStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleFirstOddStart_eq_modulus_add_three]
    simp [half, modulus]
    omega
  have hnext_fo :
      ¬ boundaryCycleSecondEvenStart q <
        boundaryCycleFirstOddBSubOneStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
    simp [modulus]
  have hnext_fb :
      ¬ boundaryCycleSecondEvenStart q <
        boundaryCycleFirstOddCRunStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two]
    simp [modulus]
  have hnext_fc :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleALastBridgeStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
    simp [half]
  have hnext_a :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleSecondOddStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleSecondOddStart_eq_two_modulus_add_two]
    simp [half]
  have hnext_so :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleSecondOddFinalStart q := by
    rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one,
      boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
    simp [half]
  have hnext_sf :
      ¬ boundaryCycleSecondEvenStart q < boundaryCycleSecondEvenStart q := by
    omega
  have hnext_node :
      boundaryCycleNodeAt q (boundaryCycleSecondEvenStart q) hns =
        boundaryCycleSecondEvenTailNode q 0
          (by simp [boundaryCycleSecondEvenTailCount, quarter]; omega) := by
    simp [boundaryCycleNodeAt, hnext_sp, hnext_fe, hnext_b2, hnext_fo,
      hnext_fb, hnext_fc, hnext_a, hnext_so]
  rw [hprev_node, hnext_node]
  symm
  exact boundaryCycleSecondOddFinal_to_secondEvenTail q
    (by simp [boundaryCycleSecondOddFinalCount])
    (by simp [boundaryCycleSecondEvenTailCount, quarter]; omega)

theorem boundaryCycleNodeAt_succ_secondEven (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q)
    (hstart : boundaryCycleSecondEvenStart q ≤ n) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  have hsp : ¬ n < boundaryCycleSpineCount q := by
    have hle : boundaryCycleSpineCount q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      simp [boundaryCycleSpineCount, half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfe : ¬ n < boundaryCycleB2BridgeStart q := by
    have hle : boundaryCycleB2BridgeStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleB2BridgeStart_eq_modulus_add_two]
      simp [half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hb2 : ¬ n < boundaryCycleFirstOddStart q := by
    have hle : boundaryCycleFirstOddStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleFirstOddStart_eq_modulus_add_three]
      simp [half, modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfo : ¬ n < boundaryCycleFirstOddBSubOneStart q := by
    have hle : boundaryCycleFirstOddBSubOneStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleFirstOddBSubOneStart_eq_modulus_add_half_add_one]
      simp [modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfb : ¬ n < boundaryCycleFirstOddCRunStart q := by
    have hle : boundaryCycleFirstOddCRunStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleFirstOddCRunStart_eq_modulus_add_half_add_two]
      simp [modulus] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hfc : ¬ n < boundaryCycleALastBridgeStart q := by
    have hle : boundaryCycleALastBridgeStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleALastBridgeStart_eq_two_modulus_add_one]
      simp [half] at hs ⊢
      omega
    exact not_lt.mpr hle
  have ha : ¬ n < boundaryCycleSecondOddStart q := by
    have hle : boundaryCycleSecondOddStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleSecondOddStart_eq_two_modulus_add_two]
      simp [half] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hso : ¬ n < boundaryCycleSecondOddFinalStart q := by
    have hle : boundaryCycleSecondOddFinalStart q ≤ n := by
      have hs := hstart
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hs
      rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half]
      simp [half] at hs ⊢
      omega
    exact not_lt.mpr hle
  have hsf : ¬ n < boundaryCycleSecondEvenStart q := not_lt.mpr hstart
  have hsps : ¬ n + 1 < boundaryCycleSpineCount q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hsp) (Nat.le_succ n))
  have hfes : ¬ n + 1 < boundaryCycleB2BridgeStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfe) (Nat.le_succ n))
  have hb2s : ¬ n + 1 < boundaryCycleFirstOddStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hb2) (Nat.le_succ n))
  have hfos : ¬ n + 1 < boundaryCycleFirstOddBSubOneStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfo) (Nat.le_succ n))
  have hfbs : ¬ n + 1 < boundaryCycleFirstOddCRunStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfb) (Nat.le_succ n))
  have hfcs : ¬ n + 1 < boundaryCycleALastBridgeStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hfc) (Nat.le_succ n))
  have has : ¬ n + 1 < boundaryCycleSecondOddStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp ha) (Nat.le_succ n))
  have hsos : ¬ n + 1 < boundaryCycleSecondOddFinalStart q :=
    not_lt.mpr (Nat.le_trans (not_lt.mp hso) (Nat.le_succ n))
  have hsfs : ¬ n + 1 < boundaryCycleSecondEvenStart q :=
    not_lt.mpr (Nat.le_trans hstart (Nat.le_succ n))
  have htail : n - boundaryCycleSecondEvenStart q <
      boundaryCycleSecondEvenTailCount q := by
    have hn' : n < boundaryCycleSecondEvenStart q +
        boundaryCycleSecondEvenTailCount q := by
      simpa [boundaryCycleSecondEvenEnd_eq_length q] using hn
    omega
  have hnext_tail : n + 1 - boundaryCycleSecondEvenStart q <
      boundaryCycleSecondEvenTailCount q := by
    have hns' : n + 1 < boundaryCycleSecondEvenStart q +
        boundaryCycleSecondEvenTailCount q := by
      simpa [boundaryCycleSecondEvenEnd_eq_length q] using hns
    omega
  have hidx :
      n + 1 - boundaryCycleSecondEvenStart q =
        (n - boundaryCycleSecondEvenStart q) + 1 := by omega
  have htail_succ : (n - boundaryCycleSecondEvenStart q) + 1 <
      boundaryCycleSecondEvenTailCount q := by
    rw [← hidx]
    exact hnext_tail
  have hn_node :
      boundaryCycleNodeAt q n hn =
        boundaryCycleSecondEvenTailNode q
          (n - boundaryCycleSecondEvenStart q) htail := by
    simp [boundaryCycleNodeAt, hsp, hfe, hb2, hfo, hfb, hfc, ha, hso, hsf]
  have hns_node :
      boundaryCycleNodeAt q (n + 1) hns =
        boundaryCycleSecondEvenTailNode q
          ((n - boundaryCycleSecondEvenStart q) + 1) htail_succ := by
    trans boundaryCycleSecondEvenTailNode q
      (n + 1 - boundaryCycleSecondEvenStart q) hnext_tail
    · simp [boundaryCycleNodeAt, hsps, hfes, hb2s, hfos, hfbs, hfcs, has,
        hsos, hsfs]
    · simp [hidx]
  rw [hn_node, hns_node]
  symm
  by_cases heven : (n - boundaryCycleSecondEvenStart q) % 2 = 0
  · exact boundaryCycleSecondEvenTail_step_even q
      (n - boundaryCycleSecondEvenStart q) htail htail_succ heven
  · exact boundaryCycleSecondEvenTail_step_odd q
      (n - boundaryCycleSecondEvenStart q) htail htail_succ heven

theorem boundaryCycleNodeAt_succ (q n : Nat)
    (hn : n < boundaryCycleLength q)
    (hns : n + 1 < boundaryCycleLength q) :
    boundaryCycleNodeAt q (n + 1) hns =
      boundaryQuotient q (boundaryCycleNodeAt q n hn) := by
  by_cases hsps : n + 1 < boundaryCycleSpineCount q
  · exact boundaryCycleNodeAt_succ_spine q n hn hns (by omega) hsps
  by_cases hsp : n < boundaryCycleSpineCount q
  · have hn_eq : n = boundaryCycleFirstEvenStart q - 1 := by
      simp [boundaryCycleFirstEvenStart] at hsp hsps ⊢
      omega
    subst n
    simpa [boundaryCycleFirstEvenStart, boundaryCycleSpineCount, half] using
      boundaryCycleNodeAt_spine_to_firstEven q hn hns
  by_cases hfe_next : n + 1 < boundaryCycleB2BridgeStart q
  · exact boundaryCycleNodeAt_succ_firstEven q n hn hns
      (by simpa [boundaryCycleFirstEvenStart] using not_lt.mp hsp)
      hfe_next
  by_cases hfe : n < boundaryCycleB2BridgeStart q
  · have hn_eq : n = boundaryCycleB2BridgeStart q - 1 := by omega
    subst n
    have hadd :
        boundaryCycleB2BridgeStart q - 1 + 1 =
      boundaryCycleB2BridgeStart q := by
      simp [boundaryCycleB2BridgeStart, boundaryCycleFirstEvenStart,
        boundaryCycleSpineCount, boundaryCycleFirstEvenTailCount, quarter, half]
      omega
    simpa [hadd]
      using boundaryCycleNodeAt_firstEven_to_B2Bridge q hn hns
  by_cases hb2 : n < boundaryCycleFirstOddStart q
  · have hn_eq : n = boundaryCycleFirstOddStart q - 1 := by
      rw [boundaryCycleFirstOddStart, boundaryCycleB2BridgeCount] at hb2 ⊢
      omega
    subst n
    simpa [boundaryCycleFirstOddStart, boundaryCycleB2BridgeStart,
      boundaryCycleB2BridgeCount]
      using boundaryCycleNodeAt_B2Bridge_to_firstOdd q hn hns
  by_cases hfo_next : n + 1 < boundaryCycleFirstOddBSubOneStart q
  · exact boundaryCycleNodeAt_succ_firstOddLane q n hn hns
      (not_lt.mp hb2) hfo_next
  by_cases hfo : n < boundaryCycleFirstOddBSubOneStart q
  · have hn_eq : n = boundaryCycleFirstOddBSubOneStart q - 1 := by omega
    subst n
    simpa [boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddStart,
      boundaryCycleFirstOddLaneCount, quarter]
      using boundaryCycleNodeAt_firstOddLane_to_BSubOne q hn hns
  by_cases hfb : n < boundaryCycleFirstOddCRunStart q
  · have hn_eq : n = boundaryCycleFirstOddCRunStart q - 1 := by
      rw [boundaryCycleFirstOddCRunStart,
        boundaryCycleFirstOddBSubOneCount] at hfb ⊢
      omega
    subst n
    simpa [boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddBSubOneCount]
      using boundaryCycleNodeAt_BSubOne_to_CRun q hn hns
  by_cases hfc_next : n + 1 < boundaryCycleALastBridgeStart q
  · exact boundaryCycleNodeAt_succ_firstOddCRun q n hn hns
      (not_lt.mp hfb) hfc_next
  by_cases hfc : n < boundaryCycleALastBridgeStart q
  · have hn_eq : n = boundaryCycleALastBridgeStart q - 1 := by omega
    subst n
    simpa [boundaryCycleALastBridgeStart, boundaryCycleFirstOddStart,
      boundaryCycleFirstOddTailCount, boundaryCycleFirstOddCRunStart,
      boundaryCycleFirstOddBSubOneStart, boundaryCycleFirstOddLaneCount,
      boundaryCycleFirstOddBSubOneCount, boundaryCycleFirstOddCRunCount,
      quarter, half]
      using boundaryCycleNodeAt_firstOddCRun_to_ALast q hn hns
  by_cases ha : n < boundaryCycleSecondOddStart q
  · have hn_eq : n = boundaryCycleSecondOddStart q - 1 := by
      rw [boundaryCycleSecondOddStart, boundaryCycleALastBridgeCount] at ha ⊢
      omega
    subst n
    simpa [boundaryCycleSecondOddStart, boundaryCycleALastBridgeCount]
      using boundaryCycleNodeAt_ALast_to_secondOdd q hn hns
  by_cases hso_next : n + 1 < boundaryCycleSecondOddFinalStart q
  · exact boundaryCycleNodeAt_succ_secondOddLane q n hn hns
      (not_lt.mp ha) hso_next
  by_cases hso : n < boundaryCycleSecondOddFinalStart q
  · have hn_eq : n = boundaryCycleSecondOddFinalStart q - 1 := by omega
    subst n
    simpa [boundaryCycleSecondOddFinalStart, boundaryCycleSecondOddStart,
      boundaryCycleSecondOddLaneCount, quarter]
      using boundaryCycleNodeAt_secondOddLane_to_final q hn hns
  by_cases hsf : n < boundaryCycleSecondEvenStart q
  · have hn_eq : n = boundaryCycleSecondEvenStart q - 1 := by
      rw [boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one] at hsf ⊢
      rw [boundaryCycleSecondOddFinalStart_eq_two_modulus_add_half] at hso
      simp [half, modulus] at hsf hso ⊢
      omega
    subst n
    simpa [boundaryCycleSecondEvenStart, boundaryCycleSecondOddFinalStart,
      boundaryCycleSecondOddStart, boundaryCycleSecondOddTailCount,
      boundaryCycleSecondOddLaneCount, quarter, half]
      using boundaryCycleNodeAt_secondOddFinal_to_secondEven q hn hns
  exact boundaryCycleNodeAt_succ_secondEven q n hn hns (not_lt.mp hsf)

theorem boundaryCycleNode_step (q : Nat)
    (i : Fin (boundaryCycleLength q)) :
    boundaryCycleNode q (finRotate (boundaryCycleLength q) i) =
      boundaryQuotient q (boundaryCycleNode q i) := by
  haveI := i.neZero
  by_cases hnext : i.val + 1 < boundaryCycleLength q
  · rw [finRotate_of_lt i hnext]
    change boundaryCycleNodeAt q (i.val + 1) hnext =
      boundaryQuotient q (boundaryCycleNodeAt q i.val i.2)
    exact boundaryCycleNodeAt_succ q i.val i.2 hnext
  · have hlast : i.val + 1 = boundaryCycleLength q := by omega
    rw [finRotate_of_last i hlast]
    have hi :
        i =
          ⟨boundaryCycleLength q - 1,
            by simp [boundaryCycleLength, modulus]; omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi]
    symm
    exact boundaryCycleNode_last_to_zero q

set_option linter.flexible false in
theorem boundaryCycleSpineNode_eq_zero_iff (q i : Nat)
    (hi : i < boundaryCycleSpineCount q) :
    boundaryCycleSpineNode q i hi = routeEBoundaryZero ↔ i = 0 := by
  constructor
  · intro h
    by_cases h0 : i = 0
    · exact h0
    · exfalso
      simp [boundaryCycleSpineNode, routeEBoundaryZero, routeEBoundaryNode,
        h0] at h
      repeat' (split at h)
      all_goals contradiction
  · intro h
    subst i
    simp [boundaryCycleSpineNode, routeEBoundaryZero]

set_option linter.flexible false in
theorem boundaryCycleNodeAt_eq_zero_iff (q n : Nat)
    (hn : n < boundaryCycleLength q) :
    boundaryCycleNodeAt q n hn = routeEBoundaryZero ↔ n = 0 := by
  by_cases hsp : n < boundaryCycleSpineCount q
  · simp [boundaryCycleNodeAt, hsp,
      boundaryCycleSpineNode_eq_zero_iff q n hsp]
  · have hnot :
        boundaryCycleNodeAt q n hn ≠ routeEBoundaryZero := by
      intro h
      simp [boundaryCycleNodeAt, hsp, routeEBoundaryZero,
        routeEBoundaryNode, boundaryCycleFirstEvenTailNode,
        boundaryCycleB2BridgeNode, boundaryCycleFirstOddLaneNode,
        boundaryCycleFirstOddBSubOneNode, boundaryCycleFirstOddCRunNode,
        boundaryCycleALastBridgeNode, boundaryCycleSecondOddLaneNode,
        boundaryCycleSecondOddFinalNode, boundaryCycleSecondEvenTailNode] at h
      repeat' (split at h)
      all_goals contradiction
    constructor
    · intro h
      exact (hnot h).elim
    · intro h
      subst n
      have : 0 < boundaryCycleSpineCount q := by
        simp [boundaryCycleSpineCount, half]
      exact (hsp this).elim

theorem boundaryCycleNode_eq_zero_iff (q : Nat)
    (i : Fin (boundaryCycleLength q)) :
    boundaryCycleNode q i = routeEBoundaryZero ↔ i.val = 0 := by
  simpa [boundaryCycleNode] using
    boundaryCycleNodeAt_eq_zero_iff q i.val i.2

theorem boundaryCycleNode_iterate (q : Nat)
    (i : Fin (boundaryCycleLength q)) (k : Nat) :
    boundaryCycleNode q (((finRotate (boundaryCycleLength q))^[k]) i) =
      ((boundaryQuotient q)^[k]) (boundaryCycleNode q i) := by
  induction k generalizing i with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        boundaryCycleNode_step q, ih]

theorem boundaryCycleNode_injective (q : Nat) :
    Function.Injective (boundaryCycleNode q) := by
  intro i j hij
  haveI : NeZero (boundaryCycleLength q) := by
    exact ⟨by simp [boundaryCycleLength, modulus]; omega⟩
  by_cases hval : i.val = j.val
  · exact Fin.ext hval
  · rcases Nat.lt_or_gt_of_ne hval with hijlt | hjilt
    · let k := boundaryCycleLength q - j.val
      have hiter := congrArg (((boundaryQuotient q)^[k])) hij
      rw [← boundaryCycleNode_iterate q i k,
        ← boundaryCycleNode_iterate q j k] at hiter
      have hjzero :
          (((finRotate (boundaryCycleLength q))^[k]) j).val = 0 := by
        rw [finRotate_iterate_val]
        dsimp [k]
        have hsum : j.val + (boundaryCycleLength q - j.val) =
            boundaryCycleLength q := by omega
        rw [hsum, Nat.mod_self]
      have hright :
          boundaryCycleNode q
              (((finRotate (boundaryCycleLength q))^[k]) j) =
            routeEBoundaryZero := by
        exact (boundaryCycleNode_eq_zero_iff q
          (((finRotate (boundaryCycleLength q))^[k]) j)).2 hjzero
      have hleft :
          boundaryCycleNode q
              (((finRotate (boundaryCycleLength q))^[k]) i) =
            routeEBoundaryZero := hiter.trans hright
      have hizero :=
        (boundaryCycleNode_eq_zero_iff q
          (((finRotate (boundaryCycleLength q))^[k]) i)).1 hleft
      have hival :
          (((finRotate (boundaryCycleLength q))^[k]) i).val =
            boundaryCycleLength q - (j.val - i.val) := by
        rw [finRotate_iterate_val]
        dsimp [k]
        have hN : j.val ≤ boundaryCycleLength q := Nat.le_of_lt j.2
        have hsum :
            i.val + (boundaryCycleLength q - j.val) =
              boundaryCycleLength q - (j.val - i.val) := by omega
        rw [hsum]
        have hpos : 0 < boundaryCycleLength q - (j.val - i.val) := by
          omega
        have hlt : boundaryCycleLength q - (j.val - i.val) <
            boundaryCycleLength q := by
          omega
        exact Nat.mod_eq_of_lt hlt
      omega
    · let k := boundaryCycleLength q - i.val
      have hiter := congrArg (((boundaryQuotient q)^[k])) hij
      rw [← boundaryCycleNode_iterate q i k,
        ← boundaryCycleNode_iterate q j k] at hiter
      have hizero :
          (((finRotate (boundaryCycleLength q))^[k]) i).val = 0 := by
        rw [finRotate_iterate_val]
        dsimp [k]
        have hsum : i.val + (boundaryCycleLength q - i.val) =
            boundaryCycleLength q := by omega
        rw [hsum, Nat.mod_self]
      have hleft :
          boundaryCycleNode q
              (((finRotate (boundaryCycleLength q))^[k]) i) =
            routeEBoundaryZero := by
        exact (boundaryCycleNode_eq_zero_iff q
          (((finRotate (boundaryCycleLength q))^[k]) i)).2 hizero
      have hright :
          boundaryCycleNode q
              (((finRotate (boundaryCycleLength q))^[k]) j) =
            routeEBoundaryZero := hiter.symm.trans hleft
      have hjzero :=
        (boundaryCycleNode_eq_zero_iff q
          (((finRotate (boundaryCycleLength q))^[k]) j)).1 hright
      have hjval :
          (((finRotate (boundaryCycleLength q))^[k]) j).val =
            boundaryCycleLength q - (i.val - j.val) := by
        rw [finRotate_iterate_val]
        dsimp [k]
        have hN : i.val ≤ boundaryCycleLength q := Nat.le_of_lt i.2
        have hsum :
            j.val + (boundaryCycleLength q - i.val) =
              boundaryCycleLength q - (i.val - j.val) := by omega
        rw [hsum]
        have hlt : boundaryCycleLength q - (i.val - j.val) <
            boundaryCycleLength q := by
          omega
        exact Nat.mod_eq_of_lt hlt
      omega

theorem boundaryCycleNode_bijective (q : Nat) :
    Function.Bijective (boundaryCycleNode q) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact boundaryCycleNode_injective q
  · rw [Fintype.card_fin, boundaryCycleLength_eq_card q]

structure BoundaryQuotientCycleEnumeration (q : Nat) where
  node :
    Fin (boundaryCycleLength q) → RouteEBoundaryNode (modulus q)
  step :
    ∀ i : Fin (boundaryCycleLength q),
      node (finRotate (boundaryCycleLength q) i) =
        boundaryQuotient q (node i)
  bijective : Function.Bijective node

theorem BoundaryQuotientCycleEnumeration.singleCycle {q : Nat}
    (cert : BoundaryQuotientCycleEnumeration q) :
    IsSingleCycleMap (boundaryQuotient q) := by
  exact single_cycle_of_bijective_semiconj
    (f := finRotate (boundaryCycleLength q))
    (g := boundaryQuotient q)
    (phi := cert.node)
    cert.bijective
    (by intro i; exact cert.step i)
    (finRotate_single_cycle (boundaryCycleLength q))

theorem BoundaryQuotientCycleEnumeration.oneCycleTarget {q : Nat}
    (cert : BoundaryQuotientCycleEnumeration q) :
    BoundaryQuotientOneCycleTarget q := by
  exact ⟨boundaryQuotient q, boundaryQuotient_formulaTarget q,
    cert.singleCycle⟩

noncomputable def boundaryQuotientCycleEnumeration (q : Nat) :
    BoundaryQuotientCycleEnumeration q where
  node := boundaryCycleNode q
  step := boundaryCycleNode_step q
  bijective := boundaryCycleNode_bijective q

theorem boundaryQuotient_singleCycle (q : Nat) :
    IsSingleCycleMap (boundaryQuotient q) := by
  exact (boundaryQuotientCycleEnumeration q).singleCycle

theorem boundaryQuotient_oneCycleTarget (q : Nat) :
    BoundaryQuotientOneCycleTarget q := by
  exact (boundaryQuotientCycleEnumeration q).oneCycleTarget

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

/--
All-pair B20 target in the same shape as the complete CSV/verifier package:
each section point has an all-pair label, and every label fiber has the
expected time mass.  The fiber sums imply the certificate-level total time
sum, while first-return, no-early, and section-cycle proofs remain explicit.
-/
structure AllPairLabelTraceTarget (q : Nat) where
  data : D5EvenSeamData (modulus q)
  sectionReturn :
    Color → RouteEAllPairSection (modulus q) →
      RouteEAllPairSection (modulus q)
  returnTime :
    Color → RouteEAllPairSection (modulus q) → Nat
  returnTime_pos : ∀ c a, 0 < returnTime c a
  firstReturn_equation :
    ∀ c a,
      (seamRootReturn data c)^[returnTime c a] a.1 =
        (sectionReturn c a).1
  firstReturn_minimal :
    ∀ c a k, 0 < k → k < returnTime c a →
      ¬ ∃ b : RouteEAllPairSection (modulus q),
        (seamRootReturn data c)^[k] a.1 = b.1
  sectionReturn_single :
    ∀ c, IsSingleCycleMap (sectionReturn c)
  labelOf : RouteEAllPairSection (modulus q) → AllPairLabel
  label_time_sum :
    ∀ c label,
      ((Finset.univ : Finset (RouteEAllPairSection (modulus q))).filter
          fun a => labelOf a = label).sum (fun a => returnTime c a) =
        allPairTimeMass q label

namespace AllPairLabelTraceTarget

theorem returnTime_sum {q : Nat} (target : AllPairLabelTraceTarget q)
    (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection (modulus q) =>
          target.returnTime c a) =
      modulus q ^ 4 := by
  rw [← allPairTimeMass_sum_eq_modulus_pow_four q]
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset (RouteEAllPairSection (modulus q))))
    (g := target.labelOf)
    (f := fun a => target.returnTime c a)]
  apply Finset.sum_congr rfl
  intro label _hlabel
  simpa using target.label_time_sum c label

end AllPairLabelTraceTarget

noncomputable def allPairSectionCertificateOfLabelTraceTarget (q : Nat)
    (target : AllPairLabelTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) where
  data := target.data
  routeCounts := routeCounts q
  sectionReturn := target.sectionReturn
  returnTime := target.returnTime
  returnTime_pos := target.returnTime_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  sectionReturn_single := target.sectionReturn_single
  returnTime_sum := fun c => target.returnTime_sum c

/--
Index-level version of `AllPairLabelTraceTarget`, matching the package CSV
rows (`idx`, `dst_idx`, `src_label`, `time`).  A bijection from indices to
`RouteEAllPairSection` transports the indexed return map and label-fiber time
sums to the certificate-facing section type.
-/
structure AllPairIndexedLabelTraceTarget (q : Nat) where
  N : Nat
  data : D5EvenSeamData (modulus q)
  point : Fin N → RouteEAllPairSection (modulus q)
  point_bijective : Function.Bijective point
  indexReturn : Color → Fin N → Fin N
  returnTime : Color → Fin N → Nat
  returnTime_pos : ∀ c i, 0 < returnTime c i
  firstReturn_equation :
    ∀ c i,
      (seamRootReturn data c)^[returnTime c i] (point i).1 =
        (point (indexReturn c i)).1
  firstReturn_minimal :
    ∀ c i k, 0 < k → k < returnTime c i →
      ¬ ∃ j : Fin N,
        (seamRootReturn data c)^[k] (point i).1 = (point j).1
  indexReturn_single :
    ∀ c, IsSingleCycleMap (indexReturn c)
  labelOfIndex : Fin N → AllPairLabel
  label_time_sum :
    ∀ c label,
      ((Finset.univ : Finset (Fin N)).filter
          fun i => labelOfIndex i = label).sum (fun i => returnTime c i) =
        allPairTimeMass q label

namespace AllPairIndexedLabelTraceTarget

noncomputable def pointEquiv {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q) :
    Fin target.N ≃ RouteEAllPairSection (modulus q) :=
  Equiv.ofBijective target.point target.point_bijective

noncomputable def pointIndex {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q)
    (a : RouteEAllPairSection (modulus q)) : Fin target.N :=
  (target.pointEquiv).symm a

@[simp] theorem point_pointIndex {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q)
    (a : RouteEAllPairSection (modulus q)) :
    target.point (target.pointIndex a) = a := by
  exact target.pointEquiv.apply_symm_apply a

@[simp] theorem pointIndex_point {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q) (i : Fin target.N) :
    target.pointIndex (target.point i) = i := by
  exact target.pointEquiv.symm_apply_apply i

noncomputable def toLabelTraceTarget {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q) :
    AllPairLabelTraceTarget q where
  data := target.data
  sectionReturn := fun c a =>
    target.point (target.indexReturn c (target.pointIndex a))
  returnTime := fun c a => target.returnTime c (target.pointIndex a)
  returnTime_pos := by
    intro c a
    exact target.returnTime_pos c (target.pointIndex a)
  firstReturn_equation := by
    intro c a
    simpa using target.firstReturn_equation c (target.pointIndex a)
  firstReturn_minimal := by
    intro c a k hkpos hklt hhit
    apply target.firstReturn_minimal c (target.pointIndex a) k hkpos
      (by simpa using hklt)
    rcases hhit with ⟨b, hb⟩
    exact ⟨target.pointIndex b, by simpa using hb⟩
  sectionReturn_single := by
    intro c
    exact single_cycle_of_bijective_semiconj
      (f := target.indexReturn c)
      (g := fun a =>
        target.point (target.indexReturn c (target.pointIndex a)))
      (phi := target.point)
      target.point_bijective
      (by
        intro i
        simp)
      (target.indexReturn_single c)
  labelOf := fun a => target.labelOfIndex (target.pointIndex a)
  label_time_sum := by
    intro c label
    let sIdx : Finset (Fin target.N) :=
      (Finset.univ.filter fun i => target.labelOfIndex i = label)
    let sSec : Finset (RouteEAllPairSection (modulus q)) :=
      (Finset.univ.filter fun a =>
        target.labelOfIndex (target.pointIndex a) = label)
    have hsum :
        sIdx.sum (fun i => target.returnTime c i) =
          sSec.sum (fun a => target.returnTime c (target.pointIndex a)) := by
      exact Finset.sum_bijective
        (s := sIdx)
        (t := sSec)
        (f := fun i => target.returnTime c i)
        (g := fun a => target.returnTime c (target.pointIndex a))
        target.point
        target.point_bijective
        (by
          intro i
          simp [sIdx, sSec])
        (by
          intro i _hi
          simp)
    calc
      sSec.sum (fun a => target.returnTime c (target.pointIndex a)) =
          sIdx.sum (fun i => target.returnTime c i) := hsum.symm
      _ = allPairTimeMass q label := target.label_time_sum c label

end AllPairIndexedLabelTraceTarget

noncomputable def allPairSectionCertificateOfIndexedLabelTraceTarget
    (q : Nat) (target : AllPairIndexedLabelTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) :=
  allPairSectionCertificateOfLabelTraceTarget q target.toLabelTraceTarget

def SymbolicAllPairBranchTarget : Prop :=
  ∀ q, 0 < q → Nonempty (RouteEAllPairSectionCertificate (modulus q))

def FiniteM20AllPairTarget : Prop :=
  Nonempty (RouteEAllPairSectionCertificate (modulus 0))

def AllPairBranchTarget : Prop :=
  ∀ q, Nonempty (RouteEAllPairSectionCertificate (modulus q))

theorem symbolicAllPairBranchTarget_of_labelTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q)) :
    SymbolicAllPairBranchTarget := by
  intro q hq
  rcases h q hq with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget q target⟩

theorem finiteM20AllPairTarget_of_labelTraceTarget
    (h : Nonempty (AllPairLabelTraceTarget 0)) :
    FiniteM20AllPairTarget := by
  rcases h with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget 0 target⟩

theorem allPairBranchTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm20 : Nonempty (AllPairLabelTraceTarget 0)) :
    AllPairBranchTarget := by
  intro q
  cases q with
  | zero =>
      exact finiteM20AllPairTarget_of_labelTraceTarget hm20
  | succ q =>
      exact symbolicAllPairBranchTarget_of_labelTraceTarget hsymbolic
        (Nat.succ q) (Nat.succ_pos q)

theorem symbolicAllPairBranchTarget_of_indexedLabelTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro q hq
      rcases h q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM20AllPairTarget_of_indexedLabelTraceTarget
    (h : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    FiniteM20AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM20AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm20 : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro q hq
      rcases hsymbolic q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm20 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem allPairBranchTarget_of_symbolic_and_m20
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm20 : FiniteM20AllPairTarget) :
    AllPairBranchTarget := by
  intro q
  cases q with
  | zero =>
      simpa [FiniteM20AllPairTarget] using hm20
  | succ q =>
      exact hsymbolic (Nat.succ q) (Nat.succ_pos q)

theorem hamiltonTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toHamiltonDecomposition⟩

theorem torusTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toTorusHamiltonDecomposition⟩

theorem cayleyTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toCayleyHamiltonDecomposition⟩

theorem hamiltonTarget_of_symbolic_and_m20
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm20 : FiniteM20AllPairTarget) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m20 hsymbolic hm20) q

theorem torusTarget_of_symbolic_and_m20
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm20 : FiniteM20AllPairTarget) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m20 hsymbolic hm20) q

theorem cayleyTarget_of_symbolic_and_m20
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm20 : FiniteM20AllPairTarget) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m20 hsymbolic hm20) q

theorem hamiltonTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm20 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm20) q

theorem torusTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm20 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm20) q

theorem cayleyTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm20 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm20) q

theorem hamiltonTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm20 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm20) q

theorem torusTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm20 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm20) q

theorem cayleyTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm20 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm20) q

end RouteEB20

/--
Branch-independent all-pair label target.  A branch supplies the modulus,
Route-E counts, and label-wise time mass polynomial; this target supplies the
actual section map, first-return facts, one-cycle proof, and label fibers.
-/
structure RouteEAllPairLabelTraceTarget (m : Nat) [NeZero m]
    (timeMass : RouteEB20.AllPairLabel → Nat) where
  data : D5EvenSeamData m
  sectionReturn :
    Color → RouteEAllPairSection m → RouteEAllPairSection m
  returnTime :
    Color → RouteEAllPairSection m → Nat
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
  labelOf : RouteEAllPairSection m → RouteEB20.AllPairLabel
  label_time_sum :
    ∀ c label,
      ((Finset.univ : Finset (RouteEAllPairSection m)).filter
          fun a => labelOf a = label).sum (fun a => returnTime c a) =
        timeMass label

namespace RouteEAllPairLabelTraceTarget

theorem returnTime_sum {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairLabelTraceTarget m timeMass)
    (timeMass_sum : Finset.univ.sum timeMass = m ^ 4) (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection m => target.returnTime c a) =
      m ^ 4 := by
  rw [← timeMass_sum]
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset (RouteEAllPairSection m)))
    (g := target.labelOf)
    (f := fun a => target.returnTime c a)]
  apply Finset.sum_congr rfl
  intro label _hlabel
  simpa using target.label_time_sum c label

noncomputable def toSectionCertificate {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairLabelTraceTarget m timeMass)
    (routeCounts : RouteECounts m)
    (timeMass_sum : Finset.univ.sum timeMass = m ^ 4) :
    RouteEAllPairSectionCertificate m where
  data := target.data
  routeCounts := routeCounts
  sectionReturn := target.sectionReturn
  returnTime := target.returnTime
  returnTime_pos := target.returnTime_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  sectionReturn_single := target.sectionReturn_single
  returnTime_sum := fun c => target.returnTime_sum timeMass_sum c

end RouteEAllPairLabelTraceTarget

/--
Branch-independent row-indexed version of `RouteEAllPairLabelTraceTarget`.
The verifier/CSV row index can be transported to the canonical all-pair section
through the supplied bijection.
-/
structure RouteEAllPairIndexedLabelTraceTarget (m : Nat) [NeZero m]
    (timeMass : RouteEB20.AllPairLabel → Nat) where
  N : Nat
  data : D5EvenSeamData m
  point : Fin N → RouteEAllPairSection m
  point_bijective : Function.Bijective point
  indexReturn : Color → Fin N → Fin N
  returnTime : Color → Fin N → Nat
  returnTime_pos : ∀ c i, 0 < returnTime c i
  firstReturn_equation :
    ∀ c i,
      (seamRootReturn data c)^[returnTime c i] (point i).1 =
        (point (indexReturn c i)).1
  firstReturn_minimal :
    ∀ c i k, 0 < k → k < returnTime c i →
      ¬ ∃ j : Fin N,
        (seamRootReturn data c)^[k] (point i).1 = (point j).1
  indexReturn_single :
    ∀ c, IsSingleCycleMap (indexReturn c)
  labelOfIndex : Fin N → RouteEB20.AllPairLabel
  label_time_sum :
    ∀ c label,
      ((Finset.univ : Finset (Fin N)).filter
          fun i => labelOfIndex i = label).sum (fun i => returnTime c i) =
        timeMass label

namespace RouteEAllPairIndexedLabelTraceTarget

noncomputable def pointEquiv {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass) :
    Fin target.N ≃ RouteEAllPairSection m :=
  Equiv.ofBijective target.point target.point_bijective

noncomputable def pointIndex {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass)
    (a : RouteEAllPairSection m) : Fin target.N :=
  (target.pointEquiv).symm a

@[simp] theorem point_pointIndex {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass)
    (a : RouteEAllPairSection m) :
    target.point (target.pointIndex a) = a := by
  exact target.pointEquiv.apply_symm_apply a

@[simp] theorem pointIndex_point {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass)
    (i : Fin target.N) :
    target.pointIndex (target.point i) = i := by
  exact target.pointEquiv.symm_apply_apply i

noncomputable def toLabelTraceTarget {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass) :
    RouteEAllPairLabelTraceTarget m timeMass where
  data := target.data
  sectionReturn := fun c a =>
    target.point (target.indexReturn c (target.pointIndex a))
  returnTime := fun c a => target.returnTime c (target.pointIndex a)
  returnTime_pos := by
    intro c a
    exact target.returnTime_pos c (target.pointIndex a)
  firstReturn_equation := by
    intro c a
    simpa using target.firstReturn_equation c (target.pointIndex a)
  firstReturn_minimal := by
    intro c a k hkpos hklt hhit
    apply target.firstReturn_minimal c (target.pointIndex a) k hkpos
      (by simpa using hklt)
    rcases hhit with ⟨b, hb⟩
    exact ⟨target.pointIndex b, by simpa using hb⟩
  sectionReturn_single := by
    intro c
    exact single_cycle_of_bijective_semiconj
      (f := target.indexReturn c)
      (g := fun a =>
        target.point (target.indexReturn c (target.pointIndex a)))
      (phi := target.point)
      target.point_bijective
      (by
        intro i
        simp)
      (target.indexReturn_single c)
  labelOf := fun a => target.labelOfIndex (target.pointIndex a)
  label_time_sum := by
    intro c label
    let sIdx : Finset (Fin target.N) :=
      (Finset.univ.filter fun i => target.labelOfIndex i = label)
    let sSec : Finset (RouteEAllPairSection m) :=
      (Finset.univ.filter fun a =>
        target.labelOfIndex (target.pointIndex a) = label)
    have hsum :
        sIdx.sum (fun i => target.returnTime c i) =
          sSec.sum (fun a => target.returnTime c (target.pointIndex a)) := by
      exact Finset.sum_bijective
        (s := sIdx)
        (t := sSec)
        (f := fun i => target.returnTime c i)
        (g := fun a => target.returnTime c (target.pointIndex a))
        target.point
        target.point_bijective
        (by
          intro i
          simp [sIdx, sSec])
        (by
          intro i _hi
          simp)
    calc
      sSec.sum (fun a => target.returnTime c (target.pointIndex a)) =
          sIdx.sum (fun i => target.returnTime c i) := hsum.symm
      _ = timeMass label := target.label_time_sum c label

noncomputable def toSectionCertificate {m : Nat} [NeZero m]
    {timeMass : RouteEB20.AllPairLabel → Nat}
    (target : RouteEAllPairIndexedLabelTraceTarget m timeMass)
    (routeCounts : RouteECounts m)
    (timeMass_sum : Finset.univ.sum timeMass = m ^ 4) :
    RouteEAllPairSectionCertificate m :=
  target.toLabelTraceTarget.toSectionCertificate routeCounts timeMass_sum

end RouteEAllPairIndexedLabelTraceTarget

abbrev RouteEAllPairLabelDst :=
  RouteEB20.AllPairLabel × RouteEB20.AllPairLabel

/--
Branch-independent all-pair target with source-label/destination-label fibers.
This is the proof-facing shape of the `label_dst_sum_polynomials` emitted by
the Route-E verifier packages.
-/
structure RouteEAllPairLabelDstTraceTarget (m : Nat) [NeZero m]
    (labelTimeMass : RouteEB20.AllPairLabel → Nat)
    (labelDstTimeMass : RouteEAllPairLabelDst → Nat) where
  data : D5EvenSeamData m
  sectionReturn :
    Color → RouteEAllPairSection m → RouteEAllPairSection m
  returnTime :
    Color → RouteEAllPairSection m → Nat
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
  labelOf : RouteEAllPairSection m → RouteEB20.AllPairLabel
  dstLabelOf : RouteEAllPairSection m → RouteEB20.AllPairLabel
  label_dst_time_sum :
    ∀ c src dst,
      ((Finset.univ : Finset (RouteEAllPairSection m)).filter
          fun a => labelOf a = src ∧ dstLabelOf a = dst).sum
            (fun a => returnTime c a) =
        labelDstTimeMass (src, dst)
  labelDst_sum_by_src :
    ∀ src,
      Finset.univ.sum (fun dst : RouteEB20.AllPairLabel =>
        labelDstTimeMass (src, dst)) = labelTimeMass src

namespace RouteEAllPairLabelDstTraceTarget

noncomputable def toLabelTraceTarget {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairLabelDstTraceTarget m labelTimeMass labelDstTimeMass) :
    RouteEAllPairLabelTraceTarget m labelTimeMass where
  data := target.data
  sectionReturn := target.sectionReturn
  returnTime := target.returnTime
  returnTime_pos := target.returnTime_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  sectionReturn_single := target.sectionReturn_single
  labelOf := target.labelOf
  label_time_sum := by
    intro c label
    rw [← target.labelDst_sum_by_src label]
    rw [← Finset.sum_fiberwise
      (s := ((Finset.univ : Finset (RouteEAllPairSection m)).filter
        fun a => target.labelOf a = label))
      (g := target.dstLabelOf)
      (f := fun a => target.returnTime c a)]
    apply Finset.sum_congr rfl
    intro dst _hdst
    simpa [Finset.filter_filter, and_left_comm, and_assoc] using
      target.label_dst_time_sum c label dst

noncomputable def toSectionCertificate {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairLabelDstTraceTarget m labelTimeMass labelDstTimeMass)
    (routeCounts : RouteECounts m)
    (timeMass_sum : Finset.univ.sum labelTimeMass = m ^ 4) :
    RouteEAllPairSectionCertificate m :=
  target.toLabelTraceTarget.toSectionCertificate routeCounts timeMass_sum

end RouteEAllPairLabelDstTraceTarget

/--
Branch-independent indexed source/destination-label target.  This matches
verifier output where CSV rows are indexed and label-destination fibers are
checked before transport to the canonical all-pair section.
-/
structure RouteEAllPairIndexedLabelDstTraceTarget (m : Nat) [NeZero m]
    (labelTimeMass : RouteEB20.AllPairLabel → Nat)
    (labelDstTimeMass : RouteEAllPairLabelDst → Nat) where
  N : Nat
  data : D5EvenSeamData m
  point : Fin N → RouteEAllPairSection m
  point_bijective : Function.Bijective point
  indexReturn : Color → Fin N → Fin N
  returnTime : Color → Fin N → Nat
  returnTime_pos : ∀ c i, 0 < returnTime c i
  firstReturn_equation :
    ∀ c i,
      (seamRootReturn data c)^[returnTime c i] (point i).1 =
        (point (indexReturn c i)).1
  firstReturn_minimal :
    ∀ c i k, 0 < k → k < returnTime c i →
      ¬ ∃ j : Fin N,
        (seamRootReturn data c)^[k] (point i).1 = (point j).1
  indexReturn_single :
    ∀ c, IsSingleCycleMap (indexReturn c)
  labelOfIndex : Fin N → RouteEB20.AllPairLabel
  dstLabelOfIndex : Fin N → RouteEB20.AllPairLabel
  label_dst_time_sum :
    ∀ c src dst,
      ((Finset.univ : Finset (Fin N)).filter
          fun i => labelOfIndex i = src ∧ dstLabelOfIndex i = dst).sum
            (fun i => returnTime c i) =
        labelDstTimeMass (src, dst)
  labelDst_sum_by_src :
    ∀ src,
      Finset.univ.sum (fun dst : RouteEB20.AllPairLabel =>
        labelDstTimeMass (src, dst)) = labelTimeMass src

namespace RouteEAllPairIndexedLabelDstTraceTarget

noncomputable def pointEquiv {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass) :
    Fin target.N ≃ RouteEAllPairSection m :=
  Equiv.ofBijective target.point target.point_bijective

noncomputable def pointIndex {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass)
    (a : RouteEAllPairSection m) : Fin target.N :=
  (target.pointEquiv).symm a

@[simp] theorem point_pointIndex {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass)
    (a : RouteEAllPairSection m) :
    target.point (target.pointIndex a) = a := by
  exact target.pointEquiv.apply_symm_apply a

@[simp] theorem pointIndex_point {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass)
    (i : Fin target.N) :
    target.pointIndex (target.point i) = i := by
  exact target.pointEquiv.symm_apply_apply i

noncomputable def toLabelDstTraceTarget {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass) :
    RouteEAllPairLabelDstTraceTarget m labelTimeMass labelDstTimeMass where
  data := target.data
  sectionReturn := fun c a =>
    target.point (target.indexReturn c (target.pointIndex a))
  returnTime := fun c a => target.returnTime c (target.pointIndex a)
  returnTime_pos := by
    intro c a
    exact target.returnTime_pos c (target.pointIndex a)
  firstReturn_equation := by
    intro c a
    simpa using target.firstReturn_equation c (target.pointIndex a)
  firstReturn_minimal := by
    intro c a k hkpos hklt hhit
    apply target.firstReturn_minimal c (target.pointIndex a) k hkpos
      (by simpa using hklt)
    rcases hhit with ⟨b, hb⟩
    exact ⟨target.pointIndex b, by simpa using hb⟩
  sectionReturn_single := by
    intro c
    exact single_cycle_of_bijective_semiconj
      (f := target.indexReturn c)
      (g := fun a =>
        target.point (target.indexReturn c (target.pointIndex a)))
      (phi := target.point)
      target.point_bijective
      (by
        intro i
        simp)
      (target.indexReturn_single c)
  labelOf := fun a => target.labelOfIndex (target.pointIndex a)
  dstLabelOf := fun a => target.dstLabelOfIndex (target.pointIndex a)
  label_dst_time_sum := by
    intro c src dst
    let sIdx : Finset (Fin target.N) :=
      (Finset.univ.filter fun i =>
        target.labelOfIndex i = src ∧ target.dstLabelOfIndex i = dst)
    let sSec : Finset (RouteEAllPairSection m) :=
      (Finset.univ.filter fun a =>
        target.labelOfIndex (target.pointIndex a) = src ∧
          target.dstLabelOfIndex (target.pointIndex a) = dst)
    have hsum :
        sIdx.sum (fun i => target.returnTime c i) =
          sSec.sum (fun a => target.returnTime c (target.pointIndex a)) := by
      exact Finset.sum_bijective
        (s := sIdx)
        (t := sSec)
        (f := fun i => target.returnTime c i)
        (g := fun a => target.returnTime c (target.pointIndex a))
        target.point
        target.point_bijective
        (by
          intro i
          simp [sIdx, sSec])
        (by
          intro i _hi
          simp)
    calc
      sSec.sum (fun a => target.returnTime c (target.pointIndex a)) =
          sIdx.sum (fun i => target.returnTime c i) := hsum.symm
      _ = labelDstTimeMass (src, dst) :=
        target.label_dst_time_sum c src dst
  labelDst_sum_by_src := target.labelDst_sum_by_src

noncomputable def toLabelTraceTarget {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass) :
    RouteEAllPairLabelTraceTarget m labelTimeMass :=
  target.toLabelDstTraceTarget.toLabelTraceTarget

noncomputable def toSectionCertificate {m : Nat} [NeZero m]
    {labelTimeMass : RouteEB20.AllPairLabel → Nat}
    {labelDstTimeMass : RouteEAllPairLabelDst → Nat}
    (target :
      RouteEAllPairIndexedLabelDstTraceTarget m labelTimeMass labelDstTimeMass)
    (routeCounts : RouteECounts m)
    (timeMass_sum : Finset.univ.sum labelTimeMass = m ^ 4) :
    RouteEAllPairSectionCertificate m :=
  target.toLabelTraceTarget.toSectionCertificate routeCounts timeMass_sum

end RouteEAllPairIndexedLabelDstTraceTarget

namespace RouteEB16

instance modulus_neZero (q : Nat) : NeZero (modulus q) :=
  ⟨by simp [modulus]⟩

def quarter (q : Nat) : Nat := 6 * q + 4

def boundaryMacroLengthTotalTarget (q : Nat) : Nat :=
  72 * q + 46

theorem boundaryMacroLengthTotalTarget_eq_boundary_card (q : Nat) :
    boundaryMacroLengthTotalTarget q =
      Fintype.card (RouteEBoundaryNode (modulus q)) := by
  rw [card_routeEBoundaryNode]
  simp [boundaryMacroLengthTotalTarget, modulus]
  omega

/--
B16 closed boundary quotient formula from `B16_closure_package_20260506.zip`.
The formulas are stated with equality in `ZMod (modulus q)`, so targets such as
`h - 3a` and `h - 1 - 4a` keep their intended modulo-`m` meaning.
-/
structure BoundaryQuotientFormulaTarget (q : Nat)
    (Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)) : Prop where
  zero_to_A :
    ∃ a : RouteENonzeroSeam (modulus q),
      a.1 = (half q : ZMod (modulus q)) ∧
        Q routeEBoundaryZero =
          routeEBoundaryNode RouteEBoundaryLabel.L03 a
  A_special_to_A :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = modulus q - 3 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = (half q + 6 : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  A_mod4_zero_to_C :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val % 4 = 0 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((modulus q - a.1.val / 4 : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  A_mod4_one_to_B :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ modulus q - 3 → a.1.val % 4 = 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 =
            (((2 * q + 1) * a.1.val + 6 * q + 2 : Nat) :
              ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_mod4_two_to_B :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val % 4 = 2 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 =
            (((2 * q + 1) * a.1.val + 12 * q + 8 : Nat) :
              ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_mod4_three_to_B :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val % 4 = 3 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 =
            (((2 * q + 1) * a.1.val + 18 * q + 10 : Nat) :
              ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  B_h_add_two_to_zero :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = half q + 2 →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
          routeEBoundaryZero
  B_two_to_A :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = 2 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = (half q - 1 : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_mod4_three_to_C :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val % 4 = 3 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = ((3 * ((a.1.val + 1) / 4) : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_mod4_one_to_A :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val % 4 = 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 =
            ((half q : Nat) : ZMod (modulus q)) -
              ((3 * a.1.val : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_mod4_even_to_A :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val ≠ half q + 2 → a.1.val ≠ 2 →
        (a.1.val % 4 = 0 ∨ a.1.val % 4 = 2) →
          ∃ b : RouteENonzeroSeam (modulus q),
            b.1 =
              ((half q + 6 : Nat) : ZMod (modulus q)) -
                ((3 * a.1.val : Nat) : ZMod (modulus q)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_low_to_A :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val < quarter q →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 =
            ((half q - 1 : Nat) : ZMod (modulus q)) -
              ((4 * a.1.val : Nat) : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_last_to_B :
    ∀ a : RouteENonzeroSeam (modulus q),
      a.1.val = modulus q - 1 →
        ∃ b : RouteENonzeroSeam (modulus q),
          b.1 = (modulus q - 1 : ZMod (modulus q)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  C_high_mod3_two_to_B :
    ∀ a : RouteENonzeroSeam (modulus q),
      quarter q ≤ a.1.val → a.1.val ≠ modulus q - 1 →
        (a.1.val - quarter q) % 3 = 2 →
          ∃ b : RouteENonzeroSeam (modulus q),
            b.1 =
              ((4 * ((a.1.val - quarter q + 1) / 3) : Nat) :
                ZMod (modulus q)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L04 b
  C_high_other_to_C :
    ∀ a : RouteENonzeroSeam (modulus q),
      quarter q ≤ a.1.val → a.1.val ≠ modulus q - 1 →
        (a.1.val - quarter q) % 3 ≠ 2 →
          ∃ b : RouteENonzeroSeam (modulus q),
            b.1 = ((a.1.val - quarter q + 1 : Nat) : ZMod (modulus q)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L34 b

def BoundaryQuotientOneCycleTarget (q : Nat) : Prop :=
  ∃ Q : RouteEBoundaryNode (modulus q) → RouteEBoundaryNode (modulus q),
    BoundaryQuotientFormulaTarget q Q ∧ IsSingleCycleMap Q

def SymbolicBoundaryQuotientOneCycleTarget : Prop :=
  ∀ q, 0 < q → BoundaryQuotientOneCycleTarget q

abbrev BoundaryMacroNode (q : Nat) :=
  Unit ⊕ { a : RouteENonzeroSeam (modulus q) // a.1.val < quarter q }

def boundaryMacroBase (q : Nat) :
    BoundaryMacroNode q → RouteEBoundaryNode (modulus q) :=
  routeEBoundaryMacroBase

theorem boundaryMacroBase_injective (q : Nat) :
    Function.Injective (boundaryMacroBase q) :=
  routeEBoundaryMacroBase_injective

/--
B16 boundary macro-return target from the closure package.  For `q > 0`, the
package gives the first return from the closed boundary quotient to
`{Z} union {34(a) : 1 <= a < m/4}` with total excursion length `3m - 2`.
-/
structure BoundaryMacroReturnTarget (q : Nat)
    (Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)) where
  Q_bijective : Function.Bijective Q
  next : BoundaryMacroNode q → BoundaryMacroNode q
  time : BoundaryMacroNode q → Nat
  time_pos : ∀ x, 0 < time x
  firstReturn_equation :
    ∀ x, Q^[time x] (boundaryMacroBase q x) =
      boundaryMacroBase q (next x)
  firstReturn_minimal :
    ∀ x k, 0 < k → k < time x →
      ¬ ∃ y, Q^[k] (boundaryMacroBase q x) = boundaryMacroBase q y
  next_single : IsSingleCycleMap next
  time_sum :
    Finset.univ.sum time = Fintype.card (RouteEBoundaryNode (modulus q))

namespace BoundaryMacroReturnTarget

noncomputable def toBoundaryFirstReturnTarget {q : Nat}
    {Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)}
    (target : BoundaryMacroReturnTarget q Q) :
    RouteEBoundaryFirstReturnTarget (modulus q) (BoundaryMacroNode q) where
  Q := Q
  Q_bijective := target.Q_bijective
  base := boundaryMacroBase q
  base_injective := boundaryMacroBase_injective q
  next := target.next
  time := target.time
  time_pos := target.time_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  next_single := target.next_single
  time_sum := target.time_sum

theorem boundaryQuotient_singleCycle {q : Nat}
    {Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)}
    (target : BoundaryMacroReturnTarget q Q) :
    IsSingleCycleMap Q :=
  target.toBoundaryFirstReturnTarget.boundaryMap_singleCycle

end BoundaryMacroReturnTarget

theorem boundaryQuotientOneCycleTarget_of_formula_and_macro {q : Nat}
    {Q : RouteEBoundaryNode (modulus q) →
      RouteEBoundaryNode (modulus q)}
    (hformula : BoundaryQuotientFormulaTarget q Q)
    (hmacro : Nonempty (BoundaryMacroReturnTarget q Q)) :
    BoundaryQuotientOneCycleTarget q := by
  rcases hmacro with ⟨target⟩
  exact ⟨Q, hformula, target.boundaryQuotient_singleCycle⟩

theorem symbolicBoundaryQuotientOneCycleTarget_of_formula_and_macro
    (h : ∀ q, 0 < q →
      ∃ Q : RouteEBoundaryNode (modulus q) →
          RouteEBoundaryNode (modulus q),
        BoundaryQuotientFormulaTarget q Q ∧
          Nonempty (BoundaryMacroReturnTarget q Q)) :
    SymbolicBoundaryQuotientOneCycleTarget := by
  intro q hq
  rcases h q hq with ⟨Q, hformula, hmacro⟩
  exact boundaryQuotientOneCycleTarget_of_formula_and_macro hformula hmacro

def SymbolicBoundaryMacroReturnTarget : Prop :=
  ∀ q, 0 < q →
    ∃ Q : RouteEBoundaryNode (modulus q) →
        RouteEBoundaryNode (modulus q),
      Nonempty (BoundaryMacroReturnTarget q Q)

def FiniteM16BoundaryQuotientTarget : Prop :=
  ∃ Q : RouteEBoundaryNode (modulus 0) →
      RouteEBoundaryNode (modulus 0),
    IsSingleCycleMap Q

abbrev AllPairLabelTraceTarget (q : Nat) :=
  RouteEAllPairLabelTraceTarget (modulus q) (allPairTimeMassTarget q)

abbrev AllPairIndexedLabelTraceTarget (q : Nat) :=
  RouteEAllPairIndexedLabelTraceTarget (modulus q) (allPairTimeMassTarget q)

abbrev AllPairLabelDstTraceTarget (q : Nat) :=
  RouteEAllPairLabelDstTraceTarget (modulus q) (allPairTimeMassTarget q)
    (allPairLabelDstTimeMassTarget q)

abbrev AllPairIndexedLabelDstTraceTarget (q : Nat) :=
  RouteEAllPairIndexedLabelDstTraceTarget (modulus q) (allPairTimeMassTarget q)
    (allPairLabelDstTimeMassTarget q)

namespace AllPairLabelTraceTarget

theorem returnTime_sum {q : Nat} (target : AllPairLabelTraceTarget q)
    (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection (modulus q) =>
          target.returnTime c a) =
      modulus q ^ 4 :=
  RouteEAllPairLabelTraceTarget.returnTime_sum target
    (allPairTimeMassTarget_sum_eq_modulus_pow_four q) c

end AllPairLabelTraceTarget

noncomputable def allPairSectionCertificateOfLabelTraceTarget (q : Nat)
    (target : AllPairLabelTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) :=
  target.toSectionCertificate (routeCounts q)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four q)

namespace AllPairLabelDstTraceTarget

noncomputable def toLabelTraceTarget {q : Nat}
    (target : AllPairLabelDstTraceTarget q) :
    AllPairLabelTraceTarget q :=
  RouteEAllPairLabelDstTraceTarget.toLabelTraceTarget target

theorem returnTime_sum {q : Nat} (target : AllPairLabelDstTraceTarget q)
    (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection (modulus q) =>
          target.returnTime c a) =
      modulus q ^ 4 :=
  AllPairLabelTraceTarget.returnTime_sum target.toLabelTraceTarget c

end AllPairLabelDstTraceTarget

noncomputable def allPairSectionCertificateOfLabelDstTraceTarget (q : Nat)
    (target : AllPairLabelDstTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) :=
  target.toSectionCertificate (routeCounts q)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four q)

namespace AllPairIndexedLabelTraceTarget

noncomputable def toLabelTraceTarget {q : Nat}
    (target : AllPairIndexedLabelTraceTarget q) :
    AllPairLabelTraceTarget q :=
  RouteEAllPairIndexedLabelTraceTarget.toLabelTraceTarget target

end AllPairIndexedLabelTraceTarget

noncomputable def allPairSectionCertificateOfIndexedLabelTraceTarget
    (q : Nat) (target : AllPairIndexedLabelTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) :=
  target.toSectionCertificate (routeCounts q)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four q)

namespace AllPairIndexedLabelDstTraceTarget

noncomputable def toLabelDstTraceTarget {q : Nat}
    (target : AllPairIndexedLabelDstTraceTarget q) :
    AllPairLabelDstTraceTarget q :=
  RouteEAllPairIndexedLabelDstTraceTarget.toLabelDstTraceTarget target

noncomputable def toLabelTraceTarget {q : Nat}
    (target : AllPairIndexedLabelDstTraceTarget q) :
    AllPairLabelTraceTarget q :=
  RouteEAllPairIndexedLabelDstTraceTarget.toLabelTraceTarget target

end AllPairIndexedLabelDstTraceTarget

noncomputable def allPairSectionCertificateOfIndexedLabelDstTraceTarget
    (q : Nat) (target : AllPairIndexedLabelDstTraceTarget q) :
    RouteEAllPairSectionCertificate (modulus q) :=
  target.toSectionCertificate (routeCounts q)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four q)

def SymbolicAllPairBranchTarget : Prop :=
  ∀ q, 0 < q → Nonempty (RouteEAllPairSectionCertificate (modulus q))

def FiniteM16AllPairTarget : Prop :=
  Nonempty (RouteEAllPairSectionCertificate (modulus 0))

def AllPairBranchTarget : Prop :=
  ∀ q, Nonempty (RouteEAllPairSectionCertificate (modulus q))

theorem symbolicAllPairBranchTarget_of_labelTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q)) :
    SymbolicAllPairBranchTarget := by
  intro q hq
  rcases h q hq with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget q target⟩

theorem finiteM16AllPairTarget_of_labelTraceTarget
    (h : Nonempty (AllPairLabelTraceTarget 0)) :
    FiniteM16AllPairTarget := by
  rcases h with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget 0 target⟩

theorem allPairBranchTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm16 : Nonempty (AllPairLabelTraceTarget 0)) :
    AllPairBranchTarget := by
  intro q
  cases q with
  | zero =>
      exact finiteM16AllPairTarget_of_labelTraceTarget hm16
  | succ q =>
      exact symbolicAllPairBranchTarget_of_labelTraceTarget hsymbolic
        (Nat.succ q) (Nat.succ_pos q)

theorem symbolicAllPairBranchTarget_of_indexedLabelTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro q hq
      rcases h q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM16AllPairTarget_of_indexedLabelTraceTarget
    (h : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    FiniteM16AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM16AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm16 : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro q hq
      rcases hsymbolic q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm16 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem symbolicAllPairBranchTarget_of_labelDstTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairLabelDstTraceTarget q)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro q hq
      rcases h q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM16AllPairTarget_of_labelDstTraceTarget
    (h : Nonempty (AllPairLabelDstTraceTarget 0)) :
    FiniteM16AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM16AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_labelDstTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelDstTraceTarget q))
    (hm16 : Nonempty (AllPairLabelDstTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro q hq
      rcases hsymbolic q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm16 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem symbolicAllPairBranchTarget_of_indexedLabelDstTraceTarget
    (h : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelDstTraceTarget q)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro q hq
      rcases h q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM16AllPairTarget_of_indexedLabelDstTraceTarget
    (h : Nonempty (AllPairIndexedLabelDstTraceTarget 0)) :
    FiniteM16AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM16AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_indexedLabelDstTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelDstTraceTarget q))
    (hm16 : Nonempty (AllPairIndexedLabelDstTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro q hq
      rcases hsymbolic q hq with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm16 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem allPairBranchTarget_of_symbolic_and_m16
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm16 : FiniteM16AllPairTarget) :
    AllPairBranchTarget := by
  intro q
  cases q with
  | zero =>
      simpa [FiniteM16AllPairTarget] using hm16
  | succ q =>
      exact hsymbolic (Nat.succ q) (Nat.succ_pos q)

theorem hamiltonTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toHamiltonDecomposition⟩

theorem torusTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toTorusHamiltonDecomposition⟩

theorem cayleyTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) := by
  rcases h q with ⟨cert⟩
  exact ⟨cert.toCayleyHamiltonDecomposition⟩

theorem hamiltonTarget_of_symbolic_and_m16
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm16 : FiniteM16AllPairTarget) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m16 hsymbolic hm16) q

theorem torusTarget_of_symbolic_and_m16
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm16 : FiniteM16AllPairTarget) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m16 hsymbolic hm16) q

theorem cayleyTarget_of_symbolic_and_m16
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm16 : FiniteM16AllPairTarget) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m16 hsymbolic hm16) q

theorem hamiltonTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm16 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm16) q

theorem torusTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm16 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm16) q

theorem cayleyTarget_of_labelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairLabelTraceTarget q))
    (hm16 : Nonempty (AllPairLabelTraceTarget 0)) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm16) q

theorem hamiltonTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm16 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus q)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm16) q

theorem torusTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm16 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus q)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm16) q

theorem cayleyTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ q, 0 < q → Nonempty (AllPairIndexedLabelTraceTarget q))
    (hm16 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (q : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus q)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm16) q

end RouteEB16

namespace RouteER14e

instance modulus_neZero (k : Nat) : NeZero (modulus k) :=
  ⟨by simp [modulus]⟩

def macroBound (k : Nat) : Nat := 8 * k + 2

def boundaryMacroLengthTotalTarget (k : Nat) : Nat :=
  144 * k + 40

theorem boundaryMacroLengthTotalTarget_eq_boundary_card (k : Nat) :
    boundaryMacroLengthTotalTarget k =
      Fintype.card (RouteEBoundaryNode (modulus k)) := by
  rw [card_routeEBoundaryNode]
  simp [boundaryMacroLengthTotalTarget, modulus]
  omega

def insertionBoundaryCountTarget (k : Nat) : Nat :=
  1 +
  ((32 * k + 8) + (3 * k + 1) + (10 * k + 2) + (3 * k + 2)) +
  ((24 * k + 7) + (6 * k + 1) + (12 * k + 3) + (6 * k + 1) + 1) +
  ((40 * k + 9) + 1 + (3 * k) + (2 * k + 2) + (3 * k) + 1)

theorem insertionBoundaryCountTarget_eq_boundary_card (k : Nat) :
    insertionBoundaryCountTarget k =
      Fintype.card (RouteEBoundaryNode (modulus k)) := by
  rw [card_routeEBoundaryNode]
  simp [insertionBoundaryCountTarget, modulus]
  omega

def insertionWeightedCountTarget (k : Nat) : Nat :=
  1 +
  (1 * (32 * k + 8) + 4 * (3 * k + 1) +
    5 * (10 * k + 2) + 6 * (3 * k + 2)) +
  (1 * (24 * k + 7) + 4 * (6 * k + 1) +
    5 * (12 * k + 3) + 6 * (6 * k + 1) +
    (2 * modulus k + 1)) +
  (1 * (40 * k + 9) + 2 * 1 + 4 * (3 * k) +
    5 * (2 * k + 2) + 6 * (3 * k) + modulus k)

def allPairRowCountTarget (k : Nat) : Nat :=
  1 + 10 * (modulus k - 1)

theorem insertionWeightedCountTarget_eq_allPairRowCountTarget (k : Nat) :
    insertionWeightedCountTarget k = allPairRowCountTarget k := by
  simp [insertionWeightedCountTarget, allPairRowCountTarget, modulus]
  omega

def boundaryP (k : Nat) : Nat := 6 * k + 2

def boundaryA (k : Nat) : Nat := 2 * macroBound k + 1

def boundaryD (k : Nat) : Nat := 2 * macroBound k + 2

def boundaryAlpha (k : Nat) : Nat := 18 * k + 6

def boundaryBeta (k : Nat) : Nat := 42 * k + 13

def res24_03_to_04_add_half (a : Nat) : Prop :=
  a % 24 = 0 ∨ a % 24 = 2 ∨ a % 24 = 10 ∨
    a % 24 = 16 ∨ a % 24 = 18

def res24_03_to_04_plain (a : Nat) : Prop :=
  a % 24 = 4 ∨ a % 24 = 6 ∨ a % 24 = 12 ∨
    a % 24 = 14 ∨ a % 24 = 22

def res24_03_to_34_sub (a : Nat) : Prop :=
  a % 24 = 7 ∨ a % 24 = 9 ∨ a % 24 = 19 ∨
    a % 24 = 21

def res24_03_to_34_plain (a : Nat) : Prop :=
  a % 24 = 8 ∨ a % 24 = 11 ∨ a % 24 = 20 ∨
    a % 24 = 23

/--
R14e closed boundary quotient formula from
`routeE_R14e_boundary_closed_form_v2_2.md`.  As in the verifier, all coordinate
formulas are equalities in `ZMod (modulus k)`, preserving reduced nonzero
representatives without baking a particular representative function into Lean.
-/
structure BoundaryQuotientFormulaTarget (k : Nat)
    (Q : RouteEBoundaryNode (modulus k) →
      RouteEBoundaryNode (modulus k)) : Prop where
  zero_to_A_three :
    ∃ a : RouteENonzeroSeam (modulus k),
      a.1 = (3 : ZMod (modulus k)) ∧
        Q routeEBoundaryZero =
          routeEBoundaryNode RouteEBoundaryLabel.L03 a
  A_h_add_two_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val = half k + 2 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = (half k - 3 : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  A_to_04_add_half :
    ∀ a : RouteENonzeroSeam (modulus k),
      res24_03_to_04_add_half a.1.val →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            ((boundaryP k * a.1.val : Nat) : ZMod (modulus k)) +
              (half k : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_to_04_plain :
    ∀ a : RouteENonzeroSeam (modulus k),
      res24_03_to_04_plain a.1.val →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((boundaryP k * a.1.val : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_to_04_sub_two_p :
    ∀ a : RouteENonzeroSeam (modulus k),
      (a.1.val % 24 = 3 ∨
        (a.1.val % 24 = 13 ∧ a.1.val < half k)) →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            ((boundaryP k * a.1.val : Nat) : ZMod (modulus k)) -
              ((2 * boundaryP k : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_to_04_add_two_p_sub_one :
    ∀ a : RouteENonzeroSeam (modulus k),
      (a.1.val % 24 = 15 ∨
        (a.1.val % 24 = 1 ∧ a.1.val < half k)) →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            (((boundaryP k * a.1.val) + 2 * boundaryP k - 1 : Nat) :
              ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  A_to_34_sub :
    ∀ a : RouteENonzeroSeam (modulus k),
      (res24_03_to_34_sub a.1.val ∨
        ((a.1.val % 24 = 5 ∨ a.1.val % 24 = 17) ∧
          a.1.val < half k)) →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            ((boundaryA k * a.1.val : Nat) : ZMod (modulus k)) -
              ((macroBound k + 1 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  A_to_34_plain :
    ∀ a : RouteENonzeroSeam (modulus k),
      (res24_03_to_34_plain a.1.val ∨
        ((a.1.val % 24 = 1 ∨ a.1.val % 24 = 13) ∧
          half k < a.1.val) ∨
        ((a.1.val % 24 = 5 ∨ a.1.val % 24 = 17) ∧
          half k < a.1.val)) →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((boundaryA k * a.1.val : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L03 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_one_to_A_one :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val = 1 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = (1 : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_low_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      2 ≤ a.1.val → a.1.val ≤ boundaryP k →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((4 * a.1.val + half k - 3 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_mid_mod3_zero_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      boundaryP k < a.1.val → a.1.val ≤ 3 * boundaryP k →
        a.1.val % 3 = 0 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((boundaryD k * a.1.val : Nat) : ZMod (modulus k)) -
                ((macroBound k + 1 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_mid_other_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      boundaryP k < a.1.val → a.1.val ≤ 3 * boundaryP k →
        a.1.val % 3 ≠ 0 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((4 * a.1.val + half k - 3 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_pre_half_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      3 * boundaryP k < a.1.val → a.1.val < half k →
        a.1.val % 3 ≠ 1 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((boundaryD k * a.1.val : Nat) : ZMod (modulus k)) -
                ((macroBound k + 1 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_pre_half_mod3_one_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      3 * boundaryP k < a.1.val → a.1.val < half k →
        a.1.val % 3 = 1 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((4 * a.1.val + half k - 3 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_post_half_mod3_one_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      half k ≤ a.1.val → a.1.val ≤ 6 * boundaryP k - 2 →
        a.1.val % 3 = 1 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((boundaryD k * a.1.val : Nat) : ZMod (modulus k)) +
                ((macroBound k + 1 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_post_half_other_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      half k ≤ a.1.val → a.1.val ≤ 6 * boundaryP k - 2 →
        a.1.val % 3 ≠ 1 →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 = ((4 * a.1.val + 3 : Nat) : ZMod (modulus k)) ∧
              Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
                routeEBoundaryNode RouteEBoundaryLabel.L03 b
  B_top_mod3_one_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      6 * boundaryP k - 1 ≤ a.1.val → a.1.val % 3 = 1 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            ((boundaryD k * a.1.val : Nat) : ZMod (modulus k)) +
              ((macroBound k + 1 : Nat) : ZMod (modulus k)) ∧
          Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
            routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_top_mod3_two_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      6 * boundaryP k - 1 ≤ a.1.val → a.1.val % 3 = 2 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            ((boundaryD k * a.1.val : Nat) : ZMod (modulus k)) +
              (boundaryD k : ZMod (modulus k)) ∧
          Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
            routeEBoundaryNode RouteEBoundaryLabel.L34 b
  B_top_mod3_zero_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      6 * boundaryP k - 1 ≤ a.1.val → a.1.val % 3 = 0 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((4 * a.1.val + 3 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L04 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_r_to_A_h_add_one :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val = macroBound k →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = (half k + 1 : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_two_r_to_zero :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val = 2 * macroBound k →
        Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
          routeEBoundaryZero
  C_three_r_to_A_two :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val = 3 * macroBound k →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = (2 : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_odd_low_mod4_one_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val < 2 * macroBound k → a.1.val % 4 = 1 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((3 * a.1.val + 2 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_odd_low_mod4_three_to_B :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val < 2 * macroBound k → a.1.val % 4 = 3 →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = (((3 * a.1.val + 3) / 4 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  C_odd_high_mod8_one_or_seven_to_B :
    ∀ a : RouteENonzeroSeam (modulus k),
      2 * macroBound k < a.1.val →
        (a.1.val % 8 = 1 ∨ a.1.val % 8 = 7) →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((boundaryAlpha k * a.1.val : Nat) : ZMod (modulus k)) +
                (boundaryAlpha k : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  C_odd_high_mod8_three_or_five_to_B :
    ∀ a : RouteENonzeroSeam (modulus k),
      2 * macroBound k < a.1.val →
        (a.1.val % 8 = 3 ∨ a.1.val % 8 = 5) →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((boundaryAlpha k * a.1.val : Nat) : ZMod (modulus k)) +
                (boundaryBeta k : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b
  C_even_mod4_zero_low_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val % 4 = 0 → a.1.val < half k →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((3 * a.1.val + 2 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_even_mod4_zero_high_to_C :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val % 4 = 0 → half k < a.1.val →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((a.1.val - macroBound k : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L34 b
  C_even_mod4_two_low_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val % 4 = 2 → a.1.val < macroBound k →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 = ((3 * a.1.val + 2 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_even_mod4_two_middle_to_A :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val % 4 = 2 → macroBound k < a.1.val →
        a.1.val < modulus k - macroBound k →
          ∃ b : RouteENonzeroSeam (modulus k),
            b.1 =
              ((3 * a.1.val : Nat) : ZMod (modulus k)) -
                ((half k - 4 : Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L03 b
  C_even_mod4_two_high_to_B :
    ∀ a : RouteENonzeroSeam (modulus k),
      a.1.val % 4 = 2 → modulus k - macroBound k < a.1.val →
        ∃ b : RouteENonzeroSeam (modulus k),
          b.1 =
            (((3 * (a.1.val - (modulus k - macroBound k)) + 2) / 4 :
              Nat) : ZMod (modulus k)) ∧
            Q (routeEBoundaryNode RouteEBoundaryLabel.L34 a) =
              routeEBoundaryNode RouteEBoundaryLabel.L04 b

def BoundaryQuotientOneCycleTarget (k : Nat) : Prop :=
  ∃ Q : RouteEBoundaryNode (modulus k) → RouteEBoundaryNode (modulus k),
    BoundaryQuotientFormulaTarget k Q ∧ IsSingleCycleMap Q

def SymbolicBoundaryQuotientOneCycleTarget : Prop :=
  ∀ k, 0 < k → BoundaryQuotientOneCycleTarget k

abbrev BoundaryMacroNode (k : Nat) :=
  Unit ⊕ { a : RouteENonzeroSeam (modulus k) // a.1.val < macroBound k }

def boundaryMacroBase (k : Nat) :
    BoundaryMacroNode k → RouteEBoundaryNode (modulus k) :=
  routeEBoundaryMacroBase

theorem boundaryMacroBase_injective (k : Nat) :
    Function.Injective (boundaryMacroBase k) :=
  routeEBoundaryMacroBase_injective

/--
R14e boundary macro-return target from the closure package.  For `k > 0`, the
macro section is `{Z} union {34(a) : 1 <= a < 8k+2}`; for `k = 0`, the same
type is the finite two-node section `{Z, 34(1)}`.
-/
structure BoundaryMacroReturnTarget (k : Nat)
    (Q : RouteEBoundaryNode (modulus k) →
      RouteEBoundaryNode (modulus k)) where
  Q_bijective : Function.Bijective Q
  next : BoundaryMacroNode k → BoundaryMacroNode k
  time : BoundaryMacroNode k → Nat
  time_pos : ∀ x, 0 < time x
  firstReturn_equation :
    ∀ x, Q^[time x] (boundaryMacroBase k x) =
      boundaryMacroBase k (next x)
  firstReturn_minimal :
    ∀ x n, 0 < n → n < time x →
      ¬ ∃ y, Q^[n] (boundaryMacroBase k x) = boundaryMacroBase k y
  next_single : IsSingleCycleMap next
  time_sum :
    Finset.univ.sum time = Fintype.card (RouteEBoundaryNode (modulus k))

namespace BoundaryMacroReturnTarget

noncomputable def toBoundaryFirstReturnTarget {k : Nat}
    {Q : RouteEBoundaryNode (modulus k) →
      RouteEBoundaryNode (modulus k)}
    (target : BoundaryMacroReturnTarget k Q) :
    RouteEBoundaryFirstReturnTarget (modulus k) (BoundaryMacroNode k) where
  Q := Q
  Q_bijective := target.Q_bijective
  base := boundaryMacroBase k
  base_injective := boundaryMacroBase_injective k
  next := target.next
  time := target.time
  time_pos := target.time_pos
  firstReturn_equation := target.firstReturn_equation
  firstReturn_minimal := target.firstReturn_minimal
  next_single := target.next_single
  time_sum := target.time_sum

theorem boundaryQuotient_singleCycle {k : Nat}
    {Q : RouteEBoundaryNode (modulus k) →
      RouteEBoundaryNode (modulus k)}
    (target : BoundaryMacroReturnTarget k Q) :
    IsSingleCycleMap Q :=
  target.toBoundaryFirstReturnTarget.boundaryMap_singleCycle

end BoundaryMacroReturnTarget

theorem boundaryQuotientOneCycleTarget_of_formula_and_macro {k : Nat}
    {Q : RouteEBoundaryNode (modulus k) →
      RouteEBoundaryNode (modulus k)}
    (hformula : BoundaryQuotientFormulaTarget k Q)
    (hmacro : Nonempty (BoundaryMacroReturnTarget k Q)) :
    BoundaryQuotientOneCycleTarget k := by
  rcases hmacro with ⟨target⟩
  exact ⟨Q, hformula, target.boundaryQuotient_singleCycle⟩

theorem symbolicBoundaryQuotientOneCycleTarget_of_formula_and_macro
    (h : ∀ k, 0 < k →
      ∃ Q : RouteEBoundaryNode (modulus k) →
          RouteEBoundaryNode (modulus k),
        BoundaryQuotientFormulaTarget k Q ∧
          Nonempty (BoundaryMacroReturnTarget k Q)) :
    SymbolicBoundaryQuotientOneCycleTarget := by
  intro k hk
  rcases h k hk with ⟨Q, hformula, hmacro⟩
  exact boundaryQuotientOneCycleTarget_of_formula_and_macro hformula hmacro

def SymbolicBoundaryMacroReturnTarget : Prop :=
  ∀ k, 0 < k →
    ∃ Q : RouteEBoundaryNode (modulus k) →
        RouteEBoundaryNode (modulus k),
      Nonempty (BoundaryMacroReturnTarget k Q)

def FiniteM14BoundaryMacroReturnTarget : Prop :=
  ∃ Q : RouteEBoundaryNode (modulus 0) →
      RouteEBoundaryNode (modulus 0),
    Nonempty (BoundaryMacroReturnTarget 0 Q)

abbrev AllPairLabelTraceTarget (k : Nat) :=
  RouteEAllPairLabelTraceTarget (modulus k) (allPairTimeMassTarget k)

abbrev AllPairIndexedLabelTraceTarget (k : Nat) :=
  RouteEAllPairIndexedLabelTraceTarget (modulus k) (allPairTimeMassTarget k)

abbrev AllPairLabelDstTraceTarget (k : Nat) :=
  RouteEAllPairLabelDstTraceTarget (modulus k) (allPairTimeMassTarget k)
    (allPairLabelDstTimeMassTarget k)

abbrev AllPairIndexedLabelDstTraceTarget (k : Nat) :=
  RouteEAllPairIndexedLabelDstTraceTarget (modulus k) (allPairTimeMassTarget k)
    (allPairLabelDstTimeMassTarget k)

namespace AllPairLabelTraceTarget

theorem returnTime_sum {k : Nat} (target : AllPairLabelTraceTarget k)
    (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection (modulus k) =>
          target.returnTime c a) =
      modulus k ^ 4 :=
  RouteEAllPairLabelTraceTarget.returnTime_sum target
    (allPairTimeMassTarget_sum_eq_modulus_pow_four k) c

end AllPairLabelTraceTarget

noncomputable def allPairSectionCertificateOfLabelTraceTarget (k : Nat)
    (target : AllPairLabelTraceTarget k) :
    RouteEAllPairSectionCertificate (modulus k) :=
  target.toSectionCertificate (routeCounts k)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four k)

namespace AllPairLabelDstTraceTarget

noncomputable def toLabelTraceTarget {k : Nat}
    (target : AllPairLabelDstTraceTarget k) :
    AllPairLabelTraceTarget k :=
  RouteEAllPairLabelDstTraceTarget.toLabelTraceTarget target

theorem returnTime_sum {k : Nat} (target : AllPairLabelDstTraceTarget k)
    (c : Color) :
    Finset.univ.sum
        (fun a : RouteEAllPairSection (modulus k) =>
          target.returnTime c a) =
      modulus k ^ 4 :=
  AllPairLabelTraceTarget.returnTime_sum target.toLabelTraceTarget c

end AllPairLabelDstTraceTarget

noncomputable def allPairSectionCertificateOfLabelDstTraceTarget (k : Nat)
    (target : AllPairLabelDstTraceTarget k) :
    RouteEAllPairSectionCertificate (modulus k) :=
  target.toSectionCertificate (routeCounts k)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four k)

namespace AllPairIndexedLabelTraceTarget

noncomputable def toLabelTraceTarget {k : Nat}
    (target : AllPairIndexedLabelTraceTarget k) :
    AllPairLabelTraceTarget k :=
  RouteEAllPairIndexedLabelTraceTarget.toLabelTraceTarget target

end AllPairIndexedLabelTraceTarget

noncomputable def allPairSectionCertificateOfIndexedLabelTraceTarget
    (k : Nat) (target : AllPairIndexedLabelTraceTarget k) :
    RouteEAllPairSectionCertificate (modulus k) :=
  target.toSectionCertificate (routeCounts k)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four k)

namespace AllPairIndexedLabelDstTraceTarget

noncomputable def toLabelDstTraceTarget {k : Nat}
    (target : AllPairIndexedLabelDstTraceTarget k) :
    AllPairLabelDstTraceTarget k :=
  RouteEAllPairIndexedLabelDstTraceTarget.toLabelDstTraceTarget target

noncomputable def toLabelTraceTarget {k : Nat}
    (target : AllPairIndexedLabelDstTraceTarget k) :
    AllPairLabelTraceTarget k :=
  RouteEAllPairIndexedLabelDstTraceTarget.toLabelTraceTarget target

end AllPairIndexedLabelDstTraceTarget

noncomputable def allPairSectionCertificateOfIndexedLabelDstTraceTarget
    (k : Nat) (target : AllPairIndexedLabelDstTraceTarget k) :
    RouteEAllPairSectionCertificate (modulus k) :=
  target.toSectionCertificate (routeCounts k)
    (allPairTimeMassTarget_sum_eq_modulus_pow_four k)

def SymbolicAllPairBranchTarget : Prop :=
  ∀ k, 0 < k → Nonempty (RouteEAllPairSectionCertificate (modulus k))

def FiniteM14AllPairTarget : Prop :=
  Nonempty (RouteEAllPairSectionCertificate (modulus 0))

def AllPairBranchTarget : Prop :=
  ∀ k, Nonempty (RouteEAllPairSectionCertificate (modulus k))

theorem symbolicAllPairBranchTarget_of_labelTraceTarget
    (h : ∀ k, 0 < k → Nonempty (AllPairLabelTraceTarget k)) :
    SymbolicAllPairBranchTarget := by
  intro k hk
  rcases h k hk with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget k target⟩

theorem finiteM14AllPairTarget_of_labelTraceTarget
    (h : Nonempty (AllPairLabelTraceTarget 0)) :
    FiniteM14AllPairTarget := by
  rcases h with ⟨target⟩
  exact ⟨allPairSectionCertificateOfLabelTraceTarget 0 target⟩

theorem allPairBranchTarget_of_labelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairLabelTraceTarget k))
    (hm14 : Nonempty (AllPairLabelTraceTarget 0)) :
    AllPairBranchTarget := by
  intro k
  cases k with
  | zero =>
      exact finiteM14AllPairTarget_of_labelTraceTarget hm14
  | succ k =>
      exact symbolicAllPairBranchTarget_of_labelTraceTarget hsymbolic
        (Nat.succ k) (Nat.succ_pos k)

theorem symbolicAllPairBranchTarget_of_indexedLabelTraceTarget
    (h : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelTraceTarget k)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro k hk
      rcases h k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM14AllPairTarget_of_indexedLabelTraceTarget
    (h : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    FiniteM14AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM14AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelTraceTarget k))
    (hm14 : Nonempty (AllPairIndexedLabelTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro k hk
      rcases hsymbolic k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm14 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem symbolicAllPairBranchTarget_of_labelDstTraceTarget
    (h : ∀ k, 0 < k → Nonempty (AllPairLabelDstTraceTarget k)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro k hk
      rcases h k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM14AllPairTarget_of_labelDstTraceTarget
    (h : Nonempty (AllPairLabelDstTraceTarget 0)) :
    FiniteM14AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM14AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_labelDstTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairLabelDstTraceTarget k))
    (hm14 : Nonempty (AllPairLabelDstTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro k hk
      rcases hsymbolic k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm14 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem symbolicAllPairBranchTarget_of_indexedLabelDstTraceTarget
    (h : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelDstTraceTarget k)) :
    SymbolicAllPairBranchTarget :=
  symbolicAllPairBranchTarget_of_labelTraceTarget
    (by
      intro k hk
      rcases h k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem finiteM14AllPairTarget_of_indexedLabelDstTraceTarget
    (h : Nonempty (AllPairIndexedLabelDstTraceTarget 0)) :
    FiniteM14AllPairTarget := by
  rcases h with ⟨target⟩
  exact finiteM14AllPairTarget_of_labelTraceTarget
    ⟨target.toLabelTraceTarget⟩

theorem allPairBranchTarget_of_indexedLabelDstTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelDstTraceTarget k))
    (hm14 : Nonempty (AllPairIndexedLabelDstTraceTarget 0)) :
    AllPairBranchTarget :=
  allPairBranchTarget_of_labelTraceTargets
    (by
      intro k hk
      rcases hsymbolic k hk with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)
    (by
      rcases hm14 with ⟨target⟩
      exact ⟨target.toLabelTraceTarget⟩)

theorem allPairBranchTarget_of_symbolic_and_m14
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm14 : FiniteM14AllPairTarget) :
    AllPairBranchTarget := by
  intro k
  cases k with
  | zero =>
      simpa [FiniteM14AllPairTarget] using hm14
  | succ k =>
      exact hsymbolic (Nat.succ k) (Nat.succ_pos k)

theorem hamiltonTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (k : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus k)) := by
  rcases h k with ⟨cert⟩
  exact ⟨cert.toHamiltonDecomposition⟩

theorem torusTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (k : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus k)) := by
  rcases h k with ⟨cert⟩
  exact ⟨cert.toTorusHamiltonDecomposition⟩

theorem cayleyTarget_of_allPairBranchTarget
    (h : AllPairBranchTarget) (k : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus k)) := by
  rcases h k with ⟨cert⟩
  exact ⟨cert.toCayleyHamiltonDecomposition⟩

theorem hamiltonTarget_of_symbolic_and_m14
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm14 : FiniteM14AllPairTarget) (k : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus k)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m14 hsymbolic hm14) k

theorem torusTarget_of_symbolic_and_m14
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm14 : FiniteM14AllPairTarget) (k : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus k)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m14 hsymbolic hm14) k

theorem cayleyTarget_of_symbolic_and_m14
    (hsymbolic : SymbolicAllPairBranchTarget)
    (hm14 : FiniteM14AllPairTarget) (k : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus k)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_symbolic_and_m14 hsymbolic hm14) k

theorem hamiltonTarget_of_labelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairLabelTraceTarget k))
    (hm14 : Nonempty (AllPairLabelTraceTarget 0)) (k : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus k)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm14) k

theorem torusTarget_of_labelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairLabelTraceTarget k))
    (hm14 : Nonempty (AllPairLabelTraceTarget 0)) (k : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus k)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm14) k

theorem cayleyTarget_of_labelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairLabelTraceTarget k))
    (hm14 : Nonempty (AllPairLabelTraceTarget 0)) (k : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus k)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_labelTraceTargets hsymbolic hm14) k

theorem hamiltonTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelTraceTarget k))
    (hm14 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (k : Nat) :
    Nonempty (HamiltonDecompositionD5 (modulus k)) :=
  hamiltonTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm14) k

theorem torusTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelTraceTarget k))
    (hm14 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (k : Nat) :
    Nonempty (TorusHamiltonDecompositionD5 (modulus k)) :=
  torusTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm14) k

theorem cayleyTarget_of_indexedLabelTraceTargets
    (hsymbolic : ∀ k, 0 < k → Nonempty (AllPairIndexedLabelTraceTarget k))
    (hm14 : Nonempty (AllPairIndexedLabelTraceTarget 0)) (k : Nat) :
    Nonempty (CayleyHamiltonDecompositionD5 (modulus k)) :=
  cayleyTarget_of_allPairBranchTarget
    (allPairBranchTarget_of_indexedLabelTraceTargets hsymbolic hm14) k

end RouteER14e

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
