# D5 Even Route E Ansatz Status

Date: 2026-05-06.

This note records the current prove/disprove status of the D5 even Route-E
ansatz after converting the problem to a four-level nested root-flat repair.

## Claim Under Test

The broad target is:

```text
D5 even Route E should be explained by a four-level Q4 repair:
  z1, z2, z3, z4 are repaired by adjacent stop-rank switches
  0/1, 1/2, 2/3, 3/4.
```

This is still too broad to be a single finite theorem.  The current practical
test is whether concrete candidate tables pass:

```text
RF1 local Latin
RF2 layer bijectivity
even sign product
four nested first-return gates
```

The generic checker is:

```bash
python3 scripts/d5_routeE_nested_diagnostics.py candidate.json
```

## Negative Evidence

### Stationary seam-table class

The old SAT encoding in `scripts/d5_even_seam_sat_search.py` searches a
stationary seam table, not a full layered repair.

With `python-sat` installed in a temporary venv:

```bash
/tmp/routee_sat_venv_20260506/bin/python \
  scripts/d5_even_seam_sat_search.py --m 2 --solver cadical153
```

Result:

```text
m=2 vertices=16 vars=5040 clauses=16485
result=unsat
```

This does not say that D5(2) is impossible.  It says the stationary seam-table
sub-ansatz is already too narrow at the smallest even modulus.

For `m=4`, the same stationary SAT instance had:

```text
m=4 vertices=256 vars=1002240 clauses=3642885
```

and did not solve within a 60 second exploratory timeout.  No mathematical
claim is made from that timeout.

### Fixed symmetric packet laws

The earlier symmetric direct-packet probe found tempting fixed-`x` streaks, but
one such law already failed:

```text
m = 48*k + 38, x = 11 succeeds for k=0,1,2,3
m = 48*k + 38, x = 11 fails for k=4
```

At `m=230` the section map splits into cycles `3,3,223` and the total return
time is not `m^4`.

Conclusion: fixed symmetric packet laws are branch finders/falsifiers, not a
proof method.

## Positive Evidence

### Full layered SAT at m=2

A broader full-layered root-flat SAT search was added:

```bash
/tmp/routee_sat_venv_20260506/bin/python \
  scripts/d5_routeE_layered_sat_search.py \
  --m 2 \
  --solver cadical153 \
  --json-out /tmp/d5_routeE_layered_sat_m2_20260506.json
```

Result:

```text
m=2 vertices=16 vars=6400 clauses=44965
result=sat
```

Running the nested diagnostic on the SAT witness gives:

```text
rf1_ok=True
rf2_ok=True
sign_product=-1 sign_target=-1 sign_ok=True
each color return_cycles=[16]
levels have cycles [8], [4], [2], [1]
all nested time sums are correct
```

Because `m=2` may be an exceptional small modulus, this is only a sanity
check.  It shows that the full layered root-flat certificate format itself is
not immediately obstructed.

### Existing finite witnesses pass the nested gates

The exporter

```bash
python3 scripts/export_d5_even_routeE_layers.py --m M --json-out out.json
```

converts embedded D5 even witnesses from `verify_d5_even_routeE.py` into the
JSON format accepted by `d5_routeE_nested_diagnostics.py`.

For the finite `m=4` witness:

```bash
python3 scripts/export_d5_even_routeE_layers.py \
  --m 4 \
  --json-out /tmp/d5_routeE_layers_m4_20260506.json

python3 scripts/d5_routeE_nested_diagnostics.py \
  /tmp/d5_routeE_layers_m4_20260506.json
```

Result:

```text
rf1_ok=True
rf2_ok=True
sign_product=-1 sign_target=-1 sign_ok=True
each color return_cycles=[256]
levels have cycles [64], [16], [4], [1]
all nested time sums are correct
```

For the one-`Lambda_E` `m=6` witness:

```text
rf1_ok=True
rf2_ok=True
sign_product=-1 sign_target=-1 sign_ok=True
color 0 return_cycles=[1296]
levels have cycles [216], [36], [6], [1]
all nested time sums are correct
```

For the one-`Lambda_E` `m=8` witness:

```text
rf1_ok=True
rf2_ok=True
sign_product=-1 sign_target=-1 sign_ok=True
color 0 return_cycles=[4096]
levels have cycles [512], [64], [8], [1]
all nested time sums are correct
```

The exported one-`Lambda_E` witnesses are highly compressed at the layer level.
For `m=6`, layers `0..4` are constant Latin rows and only layer `5` is
state-dependent; that defect layer has `26` distinct local permutations.  For
`m=8`, layers `0..6` are constant and only layer `7` is state-dependent, again
with `26` distinct local permutations.  This suggests that the next useful
extraction problem is to factor the single `Lambda_E` defect layer into
adjacent switches and then test whether those switches satisfy the triangular
dependency discipline.

Thus the nested first-return viewpoint is not merely philosophical: existing
D5 even witnesses already satisfy it after conversion to prefix coordinates.

## Current Verdict

The broad four-level Route-E ansatz is not disproved.

What is disproved or strongly disfavored:

```text
single stationary seam-table ansatz;
fixed-constant symmetric direct-packet branch laws;
promoting short hit streaks without next-sample falsification.
```

What is positively supported:

```text
full layered root-flat certificate format;
nested first-return diagnostics;
known finite/small-seam witnesses passing all nested gates.
```

What remains open:

```text
a uniform adjacent-rank switch formula for all even m >= 4 or m >= 6;
closed RF2 inverses for that formula;
closed nested first-return/splice formulas;
symbolic no-early-return and time-sum proofs.
```

Therefore the mathematical blocker is no longer the nested first-return
criterion.  The blocker is extracting a stable, non-fragmenting adjacent-switch
law from the existing finite witnesses.

## Next Productive Step

Use `export_d5_even_routeE_layers.py` to export the known witnesses for
`m=4,6,8,...,60`, then study the local difference between those tables and a
chosen bulk Latin rule.  The goal is to identify whether the differences can be
compressed into triangular adjacent switch slabs:

```text
0/1 depending on t,z2,z3,z4
1/2 depending on t,z3,z4
2/3 depending on t,z4
3/4 depending on finite z4 lane data
```

If the extracted difference keeps fragmenting by modulus/residue with no small
description, this adjacent-switch ansatz should be marked false.
