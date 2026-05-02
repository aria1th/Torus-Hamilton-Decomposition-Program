# Current Flow and Next Bundle Plan

Date: 2026-05-02.

This note records the current research flow after absorbing the D7 odd
`4+2` bridge bundles, the D7 Target-A exceptional phase-splice bundle, the D5
even Route-E bundles, and the later D5 small-seam/branch searches.  It is not
a completion claim.  The purpose is to make the next goal revision and next
bundle shape explicit.

## Current Flow

The stable regression target is unchanged:

- keep the closed odd D7 torus/Cayley endpoint green;
- treat the additive `A7 ~= A5 x A3` bridge as a structural explanation that
  should eventually lower to the same endpoint;
- keep D5 even and D7 even on separate tracks.

The shared Lean infrastructure is no longer the main blocker.  The root-flat
lift, local additive bridge, skew-product monodromy, rank-cycle, Cayley/Torus
wrappers, and composite-product adapters are already available as target
interfaces.  The remaining work is to supply the missing mathematical
certificate families that plug into those interfaces.

## D7 Odd Track

The closed D7 odd endpoint remains the regression target.  The additive bridge
track has been sharpened into two independent proof obligations.

Target A is the A5 base problem:

- construct all-zero-set multi-P A5 base row families for every odd `m >= 5`;
- prove row/column exact cover;
- prove the folded base return has a rank step into `ZMod (m^4)`.

The current `23/32` seam quotient work is real progress, but it is not the full
Target-A row-family theorem.  Lean closes the arithmetic quotient cycle for
the good class, while the verifier still supplies Q-hitting, Q-first-return,
length-sum, and small-modulus evidence.  The exceptional class should now be
tracked separately: `A5_exceptional_phase_splice_bundle_v0_4.zip` reduces
`m = 10*t+7` to a five-lane phase-splice system and identifies `00` as the
correction block whose phase table should be formalized before choosing the
exceptional correction schedule.

Target B' is the A3 fiber/scalar problem:

- choose a zero-set-only or congruence-family `K_m(Z)` compatible with the
  selected row schedule;
- prove the triangular A3 round-return equation;
- prove the scalar units and the `m^2` fiber rank-step.

The `m = 9` zero-set scalar/full bridge certificates and the compact
`m = 11,13,17` fingerprints are useful finite evidence, but no uniform
`K_m(Z)` theorem has been proved.

## D5 Even Track

D5 even should stay on the Route-E periodic-excursion track, not the older
seam-SAT framing.

Closed or well-isolated pieces:

- `m = 4` finite Route-E branch is closed in Lean.
- The all-large Route-E targets lower to all-even Hamilton/Torus/Cayley
  endpoints once the large-even certificate is supplied.
- The `Theta_s = {rho_s(0,a,0,0,-a) : a != 0}` small seam of size `m-1` is
  now the main proof-facing section for non-open schedules.
- The open-port `m^2` section normal form is named in Lean, including the
  canonical odometer carry law.
- The finite bundle table `m = 6,8,...,60` is validated against the source
  zip, Python replay, C++ replay, block summaries, and rank certs.

The key discovery since the bundle absorption is that the recorded
`SMALL_SEAM_CASES` are validated witnesses, not a canonical all-even formula.
Full count-prefix scans show multiple alternative normalized count vectors at
small moduli.  Therefore fitting the recorded table directly is the wrong
objective.

The current candidate-family evidence is more specific, but it has also been
partly superseded by the branch-extraction bundle `v0.7`:

- open-port small-seam hits occur at `m = 10,12,14,18,20`, but not in the
  tested open-port search at `m = 6,8,16`;
- low-support support-pattern search for vectors `(a,b,0,c,0)` gives exact
  full-shape evidence through `m = 14,16,...,30`;
- `d5_even_routeE_branch_extraction_v0_7.zip` groups the verified
  `m = 6,8,...,60` witnesses by residue branch and extracts a cleaner
  candidate branch `B20` for `m == 20 mod 24` with normalized counts
  `(r,0,0,h+r,r)` and a two-block seam map;
- the best full-shape candidates found on that support pattern are:

```text
m  counts           blocks max_block hits
14 (1,3,0,9,0)     8      4         3
16 (1,13,0,1,0)    11     3         4
18 (5,7,0,5,0)     9      2         3
20 (3,13,0,3,0)    7      4         5
22 (11,3,0,7,0)    7      5         10
24 (5,13,0,5,0)    11     3         4
26 (13,5,0,7,0)    8      8         13
28 (3,5,0,19,0)    8      10        13
30 (11,7,0,11,0)   8      6         9
```

This is finite evidence for a sharper D5 even search objective, not yet an
all-even theorem.  The `v0.7` bundle changes the best objective from "fit this
one observed support shape" to "extract a finite branch menu".  The first
proof-facing branch should be `B20`, where

```text
m = 24*q + 20, h = m/2, r = (h-1)/3,
nu = (r,0,0,h+r,r),
T_h(a) = a+h+1 on 1 <= a <= h-2,
       = a+h+2 on h-1 <= a <= 2*h-1.
```

The remaining task for this branch is a symbolic port-time/first-return proof
and the return-time sum `sum tau = m^4`.

## D7 Even Track

D7 even remains separate behind the `RootFlatSchedule` certificate interface.
Nothing in the D7 odd `4+2` bridge should be silently reused as a D7 even
proof.  A future D7 even bundle should provide a root-flat schedule family and
return certificates on that track.

## Proposed Goal Revision

The active goal should remain proof-driven, but both the D7 Target-A and D5
even clauses should be sharpened.

Suggested replacement for the D7 Target-A item:

```text
D7 Target A:
  Target A1 good-class 23/32 branch for odd m with m % 5 != 2:
    prove Q-hitting, Q-first-return formulas, length sum, and small cases;
  Target A2 exceptional branch m = 10*t+7:
    formalize the five-lane system and 00 phase table,
    choose/prove a correction schedule,
    and lift it back to Q-hitting, length-sum, and m^4 base rank;
  Target A3 assembly:
    combine good + exceptional branches into seven all-zero-set rows,
    prove column exact-cover, and package the A5 base m^4 rank-step.
```

Suggested replacement for the D5 even item:

```text
D5 even Route-E:
  keep m=4 finite branch closed;
  keep the Theta small-seam target as the large-even endpoint;
  extract and formalize a finite residue-branch menu of one-Lambda_E families;
  use B20 (m == 20 mod 24) as the first branch-level target;
  for each branch prove count formulas, piecewise first-return maps,
  seam rank/single-cycle data, and sum tau = m^4.
```

For D7 Target B', the current goal remains schedule-dependent: once the base
row schedule is fixed, the next proof must supply a compatible zero-set-only
or congruence-family `K_m(Z)` and the triangular A3 scalar/rank theorem.

## Next Bundle Shape

A useful next bundle should be concrete enough to plug into Lean/program
interfaces.  The minimum useful contents are:

For D7 Target A:

- row-family formulas, with exact cover proof data;
- base first-return/rank formulas into `ZMod (m^4)`;
- Q-hitting, Q-first-return, and length-sum proofs or verifier manifests for
  the `23/32` branch;
- for the exceptional class `m = 10*t+7`, a correction word or insertion
  schedule in the five-lane `00` phase-splice system, plus proof that the
  reduced lane map is one cycle and lifts back to Q-hitting/length-sum data;
- explicit handling of small odd moduli.

For D7 Target B':

- an explicit `K_m(Z)` family or zero-set-only table formula;
- proof or verifier data for the triangular A3 round-return equation;
- scalar unit proofs and fiber rank-step certificates;
- compatibility with the selected Target-A row schedule.

For D5 even:

- residue formulas for a finite branch menu of one-`Lambda_E` counts,
  starting with the B20 branch `(r,0,0,h+r,r)`;
- generated block/rank certificates for the `Theta` seam;
- return-time sum identities;
- exact notes distinguishing exploratory capped searches from proof-grade
  uncapped checks.

For D7 even:

- a separate `RootFlatSchedule` certificate family, not a mutation of the D7
  odd bridge.

## Current Blocking Propositions

1. D7 Target A row-family exact cover and `m^4` base rank-step.
2. D7 Target A good-class `23/32` Q-hitting, Q-first-return, length-sum, and
   small-modulus packaging in Lean.
3. D7 Target A exceptional class `m = 10*t+7`: formalize the `00` phase table,
   choose/prove a five-lane correction schedule, and lift it back to the
   base-return/rank package.
4. D7 Target B' uniform `K_m(Z)`/congruence family and triangular A3 scalar
   proof.
5. D5 even finite residue-branch menu for all even `m >= 6`, beginning with
   the B20 symbolic first-return/return-time proof, plus seam rank and
   return-time-sum proofs for the remaining branches.
6. D7 even root-flat schedule certificate family.
