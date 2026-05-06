# Route E v3.6 Analysis

Date: 2026-05-06.

Source bundle:

- `/data/angel/repos/etc/routeE_proof_bundle_v3_6_20260506.zip`

Working branch:

- `route-e-v3-6-20260506`

This note records the current repo comparison and the first Lean-facing
formalization slice.  The bundle is useful proof evidence, but it is not a
Lean formalization and it does not yet claim the full D5 even Route-E theorem.

## Current Target

Formalize Route E as a branch/menu proof, starting with the B20 branch:

```text
m = 24*q + 20 = 6*c + 2
c = 4*q + 3
h = m/2 = 12*q + 10
nu = (c, 4*c + 1, 0, c, 0)
```

The proof route is the all-pair section:

```text
P_all = {0} union {(i,j,a) : 0 <= i < j <= 4, 1 <= a < m}
```

For a closed branch, the required pieces are:

1. exact first return on `P_all`;
2. no early return before that first hit;
3. one-cycle induced map;
4. total return-time mass `sum tau = m^4`;
5. adapter into the existing `RouteETheta*` / `D5EvenRouteE*` Lean endpoints.

## Lean Slice Added

`D5Odd/EvenRouteE.lean` now records the B20 v3.6 all-pair label time-mass
surface in namespace `RouteEB20`.

New arithmetic names include:

- `quarter`
- `modulus_eq_four_quarter`
- `half_eq_two_quarter`
- `allPairTimeZ`
- `allPairTime01`
- `allPairTime02`
- `allPairTime03Target`
- `allPairTime04Target`
- `allPairTime12`
- `allPairTime13`
- `allPairTime14`
- `allPairTime23`
- `allPairTime24`
- `allPairTime34`
- `allPairTimeMassTotal`
- `allPairTime01_eq_three_quarter_sq`
- `allPairTimeZ_eq_half_add_three`
- `allPairTime02_lane_sum_eq`
- `allPairTime12_lane_sum_eq`
- `allPairTime13_two_clock_eq`
- `allPairTime34_boundary_defect_eq`
- `allPairTime03Target_add_allPairTime04Target`
- `allPairTimeMassTotal_eq_modulus_pow_four`

The file checks with:

```bash
lake env lean D5Odd/EvenRouteE.lean
```

This slice intentionally does not assert that the all-pair time masses are
already first-return theorems.  The `03` and `04` entries are named as
`Target` formulas because the bundle explicitly leaves their boundary-clock
derivation as the remaining B20 symbolic time gap.

## Bundle Arithmetic Correction

The v3.6 proof draft prints:

```text
T_03 + T_04 = 10368*q^3 + 24426*q^2 + 19079*q + 5038
```

But the two displayed target polynomials are:

```text
T_03 = 5184*q^3 + 12528*q^2 + 10080*q + 2703
T_04 = 5184*q^3 + 11898*q^2 +  9099*q + 2335
```

Adding them gives:

```text
T_03 + T_04 = 10368*q^3 + 24426*q^2 + 19179*q + 5038
```

The corrected coefficient `19179` is also forced by the Lean theorem
`RouteEB20.allPairTimeMassTotal_eq_modulus_pow_four`.  Using `19079` leaves a
residual error of `100*q` in the B20 total time budget.

## B20 Status

Closed or proof-facing in the bundle:

- count admissibility;
- 02 and 12 lane time masses;
- 01 and 13 two-clock time masses;
- 14, 23, and 24 residual-core time masses;
- 34 finite-defect boundary time mass;
- boundary quotient one-cycle proof sketch.

Remaining B20 obligations:

- derive `T_03` and `T_04` from the boundary-clock formulas, not only from
  sample-verified target polynomials;
- turn the no-early package into Lean-level hypotheses or lemmas;
- connect the all-pair first-return map to the current Theta small-seam
  certificate interface, or state a new all-pair certificate adapter and prove
  the collapse.

## B16 and R14e Status

B16:

- direct count-admissible;
- boundary quotient formula and time-mass evidence are extracted and
  sample-verified;
- residual-core symbolic depth is still behind B20.

R14e:

- direct count-admissible;
- 03/04/34 boundary formulas are extracted and sample-verified;
- symbolic one-cycle proof and time-mass derivation remain pending.

## Reproduction Caveat

The bundle Python scripts `routeE_B20_twoclock_time_pass_v3_6.py` and
`routeE_B20_time_mass_pass_v3_5.py` currently expect absolute CSV inputs under
`/mnt/data` and are not self-contained from the zip extraction alone.  The JSON
evidence and proof drafts are still readable and useful, but script
reproduction needs either the missing CSV dumps or a small path/input adapter.

## Next Divisible Implementation Slices

1. B20 boundary time slice:
   formalize the boundary quotient formula for labels `03`, `04`, and `34`,
   then prove the corrected `T_03 + T_04` target from boundary clocks.

2. B20 no-early slice:
   introduce a Lean structure for all-pair first-return certificates with
   explicit minimality/no-early fields, then instantiate its arithmetic side
   with the newly recorded B20 time masses.

3. B20 residual-core slice:
   formalize the shared `S(s,b,l)` macro theorem for hard labels `14`, `23`,
   and `24`, separating entrance lemmas, macro transitions, exit
   classification, and calendar sums.

4. Branch-menu slice:
   compare B16/R14e branch data against the B20 interfaces and decide whether
   the final all-even route should be a finite branch menu or a unified direct
   core-certificate theorem.
