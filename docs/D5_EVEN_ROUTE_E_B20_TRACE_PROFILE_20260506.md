# D5 Even Route E B20 Trace Profile

Date: 2026-05-06.

This note records a finer diagnostic for the B20 branch of the D5 even Route-E
program.  The point is not to add another finite verification result.  The
point is to identify what the symbolic Lean proof still has to explain.

## Scope

B20 is the residue branch

```text
m = 24*q + 20
h = m/2
r = (h - 1)/3 = 4*q + 3
counts = (r, 0, 0, h + r, r)
slot = 0
```

The existing verifier `scripts/verify_d5_routeE_b20_branch.py` checks the
small-seam first-return map and the six-value return-time formula.  The new
diagnostic

```bash
python3 scripts/analyze_d5_routeE_b20_trace_profiles.py \
  --moduli 20,44,68 \
  --json-out /tmp/d5_routeE_b20_profiles_20260506.json
```

walks each Theta-seam first-return trace and records:

- the stop-rank counts selected by the `Lambda_E` layer;
- the shifted zero-mask counts seen along the trace;
- the B20 source class of the starting seam parameter.

## Main Observation

For `m = 20,44,68`, the stop-rank count profile is constant on each broad B20
source class, while the full shifted zero-mask profile is not.

Example output shape:

```text
m=20 q=0 counts=(3, 0, 0, 13, 3) step_formula_ok=True
  L-gen size= 6 steps=[[8246, 6]] stop_profiles=1 mask_profiles=6
  U-gen size= 6 steps=[[7826, 6]] stop_profiles=1 mask_profiles=6

m=44 q=1 counts=(7, 0, 0, 29, 7) step_formula_ok=True
  L-gen size=18 steps=[[86246, 18]] stop_profiles=1 mask_profiles=18
  U-gen size=18 steps=[[84266, 18]] stop_profiles=1 mask_profiles=18

m=68 q=2 counts=(11, 0, 0, 45, 11) step_formula_ok=True
  L-gen size=30 steps=[[316886, 30]] stop_profiles=1 mask_profiles=30
  U-gen size=30 steps=[[312194, 30]] stop_profiles=1 mask_profiles=30
```

Thus a symbolic proof that groups traces only by the six B20 return-time
classes is too coarse if it tries to match complete zero-mask words.  The
stable object appears to be the aggregate stop-rank profile, not the raw mask
profile.

## Representative Stop Profiles

The following stop profiles were observed.

For `m = 20`:

```text
L-gen: 0:7442, 1:391,  2:20, 3:2,   4:391
L-ex:  0:7422, 1:391,  2:20, 3:2,   4:391
Mid:   0:7442, 1:372,  2:20, 3:2,   4:390
U-gen: 0:7062, 1:372,  2:20, 3:2,   4:370
U-ex:  0:7042, 1:372,  2:20, 3:2,   4:370
F:     0:10494,1:572,  2:20, 3:174, 4:602
Last:  0:10152,1:552,  2:20, 3:172, 4:520
```

For `m = 44`:

```text
L-gen: 0:82370, 1:1915, 2:44, 3:2,   4:1915
L-ex:  0:82326, 1:1915, 2:44, 3:2,   4:1915
Mid:   0:82370, 1:1872, 2:44, 3:2,   4:1914
U-gen: 0:80478, 1:1872, 2:44, 3:2,   4:1870
U-ex:  0:80434, 1:1872, 2:44, 3:2,   4:1870
F:     0:120234,1:2840, 2:44, 3:906, 4:2906
Last:  0:118428,1:2796, 2:44, 3:904, 4:2728
```

For `m = 68`:

```text
L-gen: 0:307634,1:4591, 2:68, 3:2,    4:4591
L-ex:  0:307566,1:4591, 2:68, 3:2,    4:4591
Mid:   0:307634,1:4524, 2:68, 3:2,    4:4590
U-gen: 0:303078,1:4524, 2:68, 3:2,    4:4522
U-ex:  0:303010,1:4524, 2:68, 3:2,    4:4522
F:     0:453462,1:6836, 2:68, 3:2214, 4:6938
Last:  0:449040,1:6768, 2:68, 3:2212, 4:6664
```

The lower and upper exceptional classes differ from their generic classes by
exactly `m` in the stop-rank `0` count, matching the return-time formula:

```text
L-gen time = L-ex time + m
U-gen time = U-ex time + m
```

## Proof Consequence

The next Lean-facing B20 proof should not try to characterize the complete
shifted zero-mask sequence by source class alone.  A more plausible target is:

```text
1. Prove the two-block Theta seam map.
2. Prove no-earlier-return/minimality.
3. Prove classwise aggregate stop-rank counts by affine hit-time sums.
4. Derive the six return-time values and weighted m^4 sum.
```

This is compatible with the current Lean shape: the weighted time sum is
already proved algebraically for B20, while the open field is still the
pointwise trace/minimality theorem.

## Note On m = 2

The `m = 2` full layered SAT witness is useful only as a diagnostic that the
encoding is not vacuous.  It should not be used as evidence for or against the
general Route-E theorem.  The actual Route-E even target is `m >= 4`, and the
branch-formula target starts at the one-`Lambda_E` range `m >= 6`.

