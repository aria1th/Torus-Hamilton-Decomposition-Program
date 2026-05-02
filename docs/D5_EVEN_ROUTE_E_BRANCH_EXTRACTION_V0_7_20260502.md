# D5 Even Route-E Branch Extraction v0.7

Date: 2026-05-02.

Source bundle:

- `/data/angel/repos/etc/d5_even_routeE_branch_extraction_v0_7.zip`

This note records the mathematical payload of the branch-extraction bundle.
It is an extraction and target-selection note, not an all-even proof claim.

## Bundle Contents

The bundle contains:

- `notes/branch_extraction_report.md`: grouped report for the currently
  verified one-`Lambda_E` small-seam schedules;
- `outputs/source_cases.tsv`: the original verified small-seam cases;
- `outputs/branch_table.tsv`: normalized branch table with `h=m/2`,
  `m mod 6`, normalized slot-zero counts, seam orbit, and jump-run count;
- `outputs/small_seam_branch_maps.txt`: full seam maps and return times
  produced by `dump_one.cpp`;
- `notes/candidate_branch_B20.md`: a clean extracted branch candidate for
  `m == 20 mod 24`;
- `scripts/fast_small_seam_verify.cpp`, `scripts/dump_one.cpp`, and
  `scripts/make_branch_table.py`: reproduction tools.

The verified table is still the same finite range `m = 6,8,...,60` as the
non-open small-seam bundle.  The new information is the branch classification
and the explicit extraction of a simple residue branch candidate.

## Main Finding

The branch table supports a finite branch/menu proof more strongly than a
single global count formula.  The witnesses are heterogeneous after slot-zero
normalization, and the bundle status explicitly records that stable closed
count formulas for all even `m` have not yet been extracted.

This changes the D5 even search objective:

- do not try to interpolate the recorded `SMALL_SEAM_CASES` as one canonical
  formula;
- search for a finite list of residue branches, each with its own count
  formula and one-dimensional seam map proof;
- use the recorded table as evidence and regression data, not as the final
  branch menu.

## Candidate Branch B20

The clean branch in the bundle is `B20`, for

```text
m = 24*q + 20,
h = m/2 = 12*q + 10,
r = 4*q + 3 = (h-1)/3.
```

Use slot `s = 0` and the one-`Lambda_E` count vector

```text
nu = (r, 0, 0, h+r, r)
   = ((m-2)/6, 0, 0, (2*m-1)/3, (m-2)/6).
```

This is a support pattern `(0,3,4)` in normalized slot-zero coordinates.  It
is therefore different from the earlier exploratory support pattern
`(0,1,3)` / `(a,b,0,c,0)`.

The claimed small-seam first-return map is the two-block translation

```text
T_h(a) =
  a + h + 1,  1 <= a <= h-2,
  a + h + 2,  h-1 <= a <= 2*h-1,
mod 2*h.
```

For this branch `m == 2 mod 6`, so the two-block map avoids the residue-3
obstruction class described in the bundle note.

The bundle records verified instances:

```text
m  q  r   counts              seam cycle  return sum
20 0  3   (3,0,0,13,3)       19          20^4
44 1  7   (7,0,0,29,7)       43          44^4
68 2  11  (11,0,0,45,11)     67          68^4
92 3  15  (15,0,0,61,15)     91          92^4
```

Locally, the bundle C++ verifier was compiled and rerun on these four
instances.  It reported `ok 1` in each case.  The dumped seam maps for
`m = 20` and `m = 44` have exactly the advertised two translation blocks:

```text
m = 20: [1,8]  -> delta 11, [9,19]  -> delta 12
m = 44: [1,20] -> delta 23, [21,43] -> delta 24
```

The repo now has a B20-specific Python regression:

```bash
python3 scripts/verify_d5_routeE_b20_branch.py \
  --moduli 20,44 \
  --json-out /tmp/d5_routeE_b20_branch_20_44.json
```

It checks the B20 count formula, the `Theta_0` small-seam criterion, the
two-block translation table, a fitted six-value return-time distribution, and
the return-time sum.  The default `20,44` run reports `all_ok=True`; the
slower `m = 68` run was also checked locally and reports `times_ok=True`.

The fitted return-time distribution is written in terms of `m = 24*q+20` and
`h = m/2`.  Define

```text
A(q) = 13824*q^3 + 34272*q^2 + 28320*q + 7806
C(q) = A(q) + m*(m+1)
E(q) = 20736*q^3 + 50976*q^2 + 41772*q + 11416
F(q) = 20736*q^3 + 51552*q^2 + 42780*q + 11862
```

Then the observed distribution is:

```text
A(q)       occurs 2 times
A(q)+m     occurs h-4 times
C(q)       occurs 3 times
C(q)+m     occurs h-4 times
E(q)       occurs 1 time
F(q)       occurs 1 time
```

The pointwise partition verified by the B20 script is:

```text
tau(a) = D(q)  for 1 <= a <= h-2 except a = r, 2*r
tau(a) = C(q)  for a = r, 2*r, h
tau(a) = F(q)  for a = h-1
tau(a) = B(q)  for h+1 <= a <= m-2 except a = h+r, h+2*r
tau(a) = A(q)  for a = h+r, h+2*r
tau(a) = E(q)  for a = m-1
```

The stronger pointwise formula was checked on the default `m = 20,44` run and
again at `m = 68`.  This gives a sharper proof target for `sum tau = m^4`:
prove the pointwise return-time partition, then prove the weighted sum
identity.  The latter arithmetic target is now recorded in Lean as
`RouteEB20.returnTimeWeightedSum_eq_modulus_pow_four`.

## Proof Obligations Exposed by B20

For the B20 branch, the all-even proof target is now concrete:

1. prove that `nu = (r,0,0,h+r,r)` is a valid one-`Lambda_E` schedule for
   all `m = 24*q + 20`;
2. prove that every point of `Theta_0` first returns to `Theta_0`;
3. prove the first-return equation is the two-block map `T_h`;
4. prove the two-block map is a single cycle on `{1,...,m-1}`;
5. prove the return-time sum identity `sum tau = m^4`;
6. package these equations into `RouteEThetaRankedPiecewiseTranslationCertificate`
   or directly into `RouteEThetaSmallSeamCertificate`.

The strongest missing item is the symbolic port-time proof behind item 3,
plus the pointwise return-time partition needed by item 5.  The arithmetic
weighted-sum identity for the extracted distribution is already a Lean target.
The seam one-cycle proof itself looks small once `T_h` is available.

## Goal Impact

The D5 even clause of the active goal should be revised from a single
low-support family to a finite residue-branch program:

```text
D5 even Route-E:
  keep m=4 finite branch closed;
  keep Theta small-seam as the large-even endpoint;
  extract a finite menu of residue branches for all even m >= 6;
  formalize each branch by count formulas, piecewise seam first-return maps,
  seam rank/single-cycle proofs, and return-time sums;
  use B20 (m == 20 mod 24) as the first branch-level formalization target.
```

The previous `(a,b,0,c,0)` support-pattern search remains useful evidence, but
it should no longer be treated as the primary D5 even route.  B20 shows that a
different low-support pattern can give a cleaner symbolic map.

## Relative Position

The bundle was ahead of the repo-state search in three ways:

1. it selected a branch/menu interpretation rather than continuing to fit one
   global support pattern;
2. it extracted a concrete first branch, B20, with a closed count formula and
   a two-block candidate seam map;
3. it supplied classification data for the verified `m = 6,8,...,60` table by
   `m mod 6`, normalized counts, orbit, and jump-run count.

The repo was ahead of the bundle in the formal endpoint infrastructure:

1. Lean already has the `Theta_s` small-seam certificate, the ranked seam
   certificate, the piecewise translation certificate, and the combined
   `RouteEThetaRankedPiecewiseTranslationCertificate`;
2. the finite `m = 4` Route-E branch is already closed and the all-large
   Route-E targets already lower to D5 Hamilton, torus, and Cayley endpoints;
3. the repo-side verifiers already check bundle-to-repo consistency, rank
   steps on the finite seam, block maximality, and return-time sums;
4. the earlier count scans had already exposed non-uniqueness of the recorded
   witnesses, which agrees with the bundle's warning that the verified table is
   heterogeneous.

Thus v0.7 is ahead on target discovery, while the repo is ahead on proof
interfaces and endpoint plumbing.  The two pieces are compatible: B20 fits
the existing ranked-piecewise `Theta` interface almost exactly.

## Reachability Assessment

B20 looks realistically reachable as a first symbolic Route-E branch.  The
seam map has only two translation blocks:

```text
1 <= a <= h-2:      delta = h+1
h-1 <= a <= 2*h-1:  delta = h+2
```

Once the first-return equation is proved, the single-cycle proof should be a
small number-theoretic lemma about this two-block map.  The Lean endpoint work
after that is mostly packaging.

The hard part is not the seam one-cycle.  The hard part is the symbolic
port-time proof: starting from `Theta_0(a)`, prove the excursion first returns
to `Theta_0` at the claimed target, with no earlier return, and prove the
pointwise return-time partition.  The verified return-time distributions for
B20 have only a few values, and the resulting weighted-sum identity has now
been extracted into Lean, but the trace theorem producing those values is
still open.

The full all-even D5 Route-E theorem is less immediate.  It becomes plausible
if the remaining even residue classes admit a small finite menu of branches
with comparable block structure.  It is not plausible as a direct fit of the
recorded table or of the earlier `(a,b,0,c,0)` support pattern alone.  The
next practical target is therefore:

1. close B20 symbolically;
2. search for sibling branches covering the remaining even residue classes;
3. only then assemble the all-even Route-E target.
