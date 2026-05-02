# D3 A2 Bridge Rewrite Bundle

Date: 2026-05-02.

Source artifact:

- `/data/angel/repos/etc/d3_A2_bridge_rewrite_v0_1.zip`

This note records the impact of the D3 Route-E rewrite bundle.  The bundle is
not a new construction; it rewrites the existing even `D_3(m)` Route-E
construction as an `A_2`-fiber finite-defect bridge.

## Core Point

The rewrite changes the conceptual model for even Route-E.

Instead of viewing even `D_3` Route-E as an isolated low-dimensional table, the
bundle writes it as the first `2r -> 2r+1` bridge:

```text
D2(m) -> D3(m)
A3(m) ~= A2(m) x A2(m)
```

In coordinates

```text
S = x0 + x1 + x2
r = x0
y = x0 + x1
```

the inverse is

```text
x0 = r
x1 = y - r
x2 = S - y
```

and the three directions act on the root-flat coordinates `(r,y)` by

```text
e0 : (r,y) -> (r+1,y+1)
e1 : (r,y) -> (r,y+1)
e2 : (r,y) -> (r,y)
```

Thus `r` is the `A_2` base coordinate and `y` is the `A_2` fiber coordinate.

## Pure A2 Voltage Obstruction

The bundle isolates a parity obstruction for a pure `A_2`-fiber voltage bridge
when `m` is even.

If a color return had pure skew form

```text
R_c(r,y) = (Rbar_c(r), y + phi_c(r)),
```

and `Rbar_c` were a single cycle on `ZMod m`, then the full return would be a
single cycle on `ZMod m x ZMod m` exactly when the total voltage

```text
V_c = sum_r phi_c(r)
```

is a unit modulo `m`.

For a pure `D2 -> D3` bridge, the local fiber increments across the three
colors are always `1,1,0`, so the total voltage sum over all colors is even.
For even `m`, all units are odd, so all three colors cannot have unit voltage.

Therefore even `D3` cannot be closed by a pure `A_2` voltage bridge.

## Route-E Repair Mechanism

Route-E avoids the obstruction by leaving the pure-voltage class.  The low
layers introduce finite affine defect tracks that depend on the fiber
coordinate.

The rewritten low-layer tests are:

```text
S = 1: original x0 = 0 becomes r = 0
S = 2: original x1 = 0 becomes y = r
S = 0: original Route-E track sets become finite affine tracks in (r,y)
```

For `m % 6 in {0,2}`, the `S=0` bridge-coordinate tracks are:

```text
X102' = {(0,0)} union {(i,i+1) : 1 <= i <= m-3} union {(m-1,1)}
X021' = {(0,1)} union {(i,0) : 1 <= i <= m-3} union {(m-1,m-1)}
X210' = {(0,j) : 2 <= j <= m-1} union {(1,1)}
```

For `m % 6 = 4`, the corresponding `Y` tracks add the residue-3 repair:

```text
Y210' includes {(1,j+1) : 2 <= j <= m-2} and {(2,2),(2,1)}
```

This repair is not cosmetic.  It changes the finite-defect fiber circle map so
that the lane quotient becomes connected.

## Lane Maps

The full `m`-step return can be analyzed by adapted lane coordinates.  The
bulk motion is an inner odometer, while the finite defects induce a
one-dimensional lane map on `ZMod m`.

The reusable condition is:

```text
A2 fiber circle + finite affine defect tracks
  -> one-cycle lane map
  -> full m^2 root-flat return cycle
```

For color `2`, the lane map is uniform for all even `m >= 6`:

```text
T2(0) = 1
T2(1) = m - 1
T2(2) = 0
T2(x) = x - 1 for 3 <= x <= m - 1
```

Its orbit is

```text
0 -> 1 -> m-1 -> m-2 -> ... -> 2 -> 0
```

For colors `0` and `1`, the bundle gives separate lane maps for
`m % 6 in {0,2}` and for `m % 6 = 4`.  Each map is proved by explicit block
decomposition in the note and checked computationally.

## Verification

The bundled verifier was run from the zip with Python.  It checks even
`m = 6,8,10,12,14,16,18,20`.

The run reports:

```text
bridge_rewrite_eq=1
full color cycles = [m^3] for all three colors
P0 returns = [m^2] for all three colors
lane maps = [m] cycles
ALL_OK=1
```

This agrees with the bundle output.

## Impact on D5 Even Route-E

This is the important research consequence.

The current D5 even Route-E goal is a finite residue branch menu, beginning
with B20.  The D3 rewrite suggests a stronger structural lens:

```text
D4(m) -> D5(m)
A5(m) ~= A4(m) x A2(m)
```

Under that lens, the one-`Lambda_E` D5 branches may be shadows of hidden
`A_2` fiber finite-defect lane-splice modules, rather than unrelated residue
tables.

This does not close D5 even.  It changes the next useful search target:

- find D5 bridge coordinates analogous to `(S,r,y)`;
- identify the `A_4` base coordinate and the `A_2` fiber circle;
- rewrite the B20 branch in those coordinates;
- see whether B20's seam map and return-time blocks come from a finite
  lane-splice map on the `A_2` fiber;
- then search additional branches by lane-map repair patterns, not only by
  raw residue-class count vectors.

## Lean Targets

The immediate Lean-facing targets are small and reusable.

1. `A2FiberVoltageNoGo`

   A theorem saying that a pure `A_2` voltage bridge cannot make all three
   colors primitive for even `m`, because the sum of three unit voltages would
   be odd while the local total is even.

2. `D3RouteEBridgeCoordinates`

   A coordinate equivalence between vertex coordinates and `(S,r,y)`, plus
   direction-decomposition lemmas for `e0`, `e1`, and `e2`.

3. `D3RouteELaneMapTarget`

   Named lane-map formulas for `T2`, `T1I`, `T0I`, `T1II`, and `T0II`, with
   one-cycle proofs by explicit interval/block orbit decompositions.

4. `A2FiniteDefectLaneSpliceCertificate`

   A generic structure for future `D4 -> D5` work:

```text
structure A2FiniteDefectLaneSpliceCertificate (m : Nat) where
  laneMap : ZMod m -> ZMod m
  laneSingleCycle : IsSingleCycleMap laneMap
  innerOdometerSweep : ...
  returnConjugacy : ...
```

The D3 instance can be the first theorem using this structure.  D5 B20 should
then be tested against the same interface.

## Goal Adjustment

Do not replace the D5 even branch-menu target yet.  Add a parallel structural
investigation:

```text
D5 even Route-E:
  keep B20 symbolic trace as first branch target;
  in parallel, attempt an A4 -> A5, A2-fiber finite-defect rewrite;
  prefer future branches whose seam/return formulas arise from lane-splice
  maps in the hidden A2 fiber coordinate.
```

This may turn the branch menu from a collection of residue certificates into a
finite set of lane-splice repair modules.
