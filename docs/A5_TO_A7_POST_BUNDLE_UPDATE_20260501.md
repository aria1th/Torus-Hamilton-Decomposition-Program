# A5 to A7 Post Bundle Update

Date: 2026-05-01.

Source bundle:

- `/data/angel/repos/etc/A5_to_A7_post_bundle_update_v0_2.zip`

This note records the update after reading the post-bundle material.  It is a
research-state update, not a completion certificate.

## Main Update

Target A has a much sharper shape than in the previous baseline.

The short all-zero-set A5 base words

```text
23
32
```

are now the leading generic primitive-row candidates.  The post bundle records
the following empirical theorem candidate for odd `m >= 5`:

```text
Phi_23 and Phi_32 are one cycles on Sigma
  iff m != 2 mod 5.
```

Since `m` is odd, the failing class is equivalently `m == 7 mod 10`.

The section is the D5 normalized-return section

```text
Sigma = {(0,a,b,0,-a-b) : a+b != 0}.
```

For both `23` and `32`, all tested odd moduli still satisfy the excursion
identity

```text
sum_{x in Sigma} ell_W(x) = m^4.
```

Thus the obstruction in the bad class is not coverage of `A5(m)`.  It is
exactly that the induced first-return map on `Sigma` splits into multiple
cycles.

## Bad-Class Five-Cycle Pattern

When `m == 2 mod 5`, the induced map for `W = 23` appears to split into five
cycles with lengths

```text
(m^2 + 9m - 2) / 5
(m^2 -  m + 3) / 5
(m^2 -  m - 2) / 5
(m^2 - 6m + 3) / 5
(m^2 - 6m - 2) / 5
```

For `W = 32`, the corresponding observed lengths are

```text
(m^2 + 9m - 12) / 5
(m^2 -  m +  8) / 5
(m^2 -  m -  2) / 5
(m^2 - 6m +  3) / 5
(m^2 - 6m +  3) / 5
```

These formulas match the tested bad moduli in the bundle output.  They also
explain why our previous live data saw failures at `m = 7,17,27,37`: those are
the first odd values in `m == 2 mod 5`.

## Sigma0 Mechanism

Let

```text
Sigma0 = {(a,0) : a != 0} subset Sigma.
```

The post bundle records a stable mechanism for both `23` and `32`: the return
to `Sigma0` acts as

```text
a -> a + 1.
```

So the cycle meeting `Sigma0` is already a single large component.  The
primitiveity theorem reduces to seam connectivity:

```text
every point of Sigma eventually reaches Sigma0
```

for `m != 2 mod 5`, and a five-component seam split for `m == 2 mod 5`.

This is the cleanest symbolic proof target exposed so far for Target A.

## Updated Target-A Strategy

The base-row program should now be split into two branches.

1. Generic branch: prove the `23/32` section theorem for all odd
   `m >= 5` with `m != 2 mod 5`.
2. Exceptional branch: prove the five-cycle decomposition for
   `m == 2 mod 5`, then design correction row words that splice these five
   seam components.

The earlier `m = 27` and `m = 37` primitive words remain useful, but should be
treated as finite/congruence evidence for the exceptional branch rather than
as the beginning of a blind global search.

Known exceptional examples in the current repo baseline include:

```text
m = 27: 22414, 24142, 441144, 332332
m = 37: 404432, 044324, 324044, 432404, 443240
```

The post bundle also confirms that `332` is meaningful but not universal:
it succeeds in sampled moduli such as `m = 9,27,39`, while it splits on many
other odd moduli.  It is therefore better viewed as a congruence-specific row
word, not the generic Target-A word.

## Revised Missing Propositions

The clearest new proof obligations are:

1. **23/32 first-return formulas:** derive the compressed first-return table
   for `Phi_23` and `Phi_32` on `Sigma`.
2. **Sigma0 return law:** prove the return to `Sigma0` is `a -> a+1`.
3. **Excursion identity:** prove `sum ell_W = m^4` for `W = 23,32`.
4. **Generic seam connectivity:** prove every `Sigma` point reaches `Sigma0`
   when `m != 2 mod 5`.
5. **Bad-class decomposition:** prove the five-cycle formulas when
   `m == 2 mod 5`.
6. **Exceptional correction rows:** construct row words or insertions that
   splice the five bad-class seam cycles.
7. **Exact-cover row schedules:** after the primitive-word library is fixed,
   assemble seven rows with column exact cover.
8. **Target B' for those rows:** construct the zero-set-only or finite
   congruence-family `K_m(Z)` and prove the A3 scalar unit conditions.

## Verification Performed

The bundle notes and outputs were read from the extracted directory
`/tmp/a5_to_a7_post_bundle_update_v0_2`.

As a lightweight local cross-check, the repo analyzer was run on the small
range

```bash
python3 scripts/analyze_targetA_section.py \
  --moduli 5,7,9,17 \
  --words 23,32
```

The local output agrees with the bundle pattern in that range:

- `m = 5,9`: one section cycle for both `23` and `32`;
- `m = 7,17`: five section cycles for both words;
- `return_time_sum = m^4` in all four tested moduli.

A focused verifier has now been added as
`scripts/verify_targetA_23_32.py`.  It checks only the theorem-candidate
conditions needed here: section cycle structure, `sum ell = m^4`, the
`Sigma0` return law, and the bad-class five-cycle formulas.

The default representative range passes:

```bash
python3 scripts/verify_targetA_23_32.py \
  --json-out /tmp/targetA_23_32_default.json
```

The broader odd range matching the post-bundle evidence through `m = 51` also
passes:

```bash
python3 scripts/verify_targetA_23_32.py \
  --moduli 5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51 \
  --json-out /tmp/targetA_23_32_5_to_51.json
```

Both runs reported `all_ok=True`.
