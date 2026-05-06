# Route E Even Branch Discovery Program

Date: 2026-05-06.

This note records the current discovery program for the remaining even-modulus
Route-E branches.  It is intentionally evidence-facing, not proof-facing:
search hits here are candidates for later modular criteria, boundary formulas,
and Lean endpoints.

## Current Baseline

The proof-facing modular branch evidence already preserved in
`ROUTE_E_MODULAR_CRITERIA_EVIDENCE_20260506.md` covers:

| branch | residue class |
| --- | --- |
| B20 | `m = 20 mod 24`, i.e. `20,44 mod 48` |
| B16 | `m = 16 mod 24`, i.e. `16,40 mod 48` |
| R14e | `m = 14 mod 48` |

The existing small-seam table covers even `6 <= m <= 60`.  Therefore the
discovery task is not to reprove those cases, but to find robust parametric
families for the remaining high even residue classes.

## Added Discovery Tools

### Support-pattern C++ search

`scripts/fast_d5_routeE_small_seam_search.cpp` is a fast C++ searcher for
normalized slot-zero small-seam packets.  It enumerates count vectors with a
specified support pattern and runs the same section-return test as
`fast_d5_routeE_small_seam_verify.cpp`.

Basic form:

```bash
g++ -O3 -std=c++17 scripts/fast_d5_routeE_small_seam_search.cpp \
  -o /tmp/fast_d5_routeE_small_seam_search

/tmp/fast_d5_routeE_small_seam_search \
  44 0,3,4 2 0 5000
```

The last two arguments are a step cap and a candidate limit.  Use cap `0` for
exact search up to the full `m^4` return-time budget.

Smoke result:

```text
m=44, support 0,3,4, exact cap, candidate_limit=5000
hits include counts (1,0,0,13,29) and (1,0,0,25,17)
```

### Parallel support-pattern driver

`scripts/search_d5_routeE_cpp_residue_branches.py` compiles the C++ searcher
and runs it over many moduli and support patterns in parallel.  It writes a
compact JSON summary instead of raw maps.

Smoke command:

```bash
python3 scripts/search_d5_routeE_cpp_residue_branches.py \
  --moduli 44 \
  --patterns '0,3,4' \
  --hit-limit 2 \
  --candidate-limit 100 \
  --cap-m3-factor 0 \
  --jobs 1 \
  --json-out /tmp/routee_cpp_driver_smoke.json
```

Smoke result:

```text
m 44 pattern 0,3,4 hits 2 checked 25
```

### Symmetric direct-packet probe

`scripts/search_d5_routeE_symmetric_packets.py` tests the smaller family

```text
nu_x(m) = (x, m - 1 - 2*x, 0, x, 0).
```

This family is much cheaper to probe than a full support-pattern enumeration
and is a good branch-finder for direct modular packets.

Smoke command:

```bash
python3 scripts/search_d5_routeE_symmetric_packets.py \
  --moduli 86 \
  --x-values 11 \
  --timeout 8 \
  --jobs 1 \
  --json-out /tmp/routee_symmetric_smoke.json
```

Smoke result:

```text
HIT 86 11 [85]
SUMMARY
86 [11]
```

## Direct Symmetric Branch Evidence

The most tempting simple candidate was:

```text
R38-sym11:
  m = 38 mod 48
  nu = (11, m - 23, 0, 11, 0)
```

Exact verifier checks:

| `m` | `x` | result |
| ---: | ---: | --- |
| 38 | 11 | one section cycle of length `37`, total time `m^4` |
| 86 | 11 | one section cycle of length `85`, total time `m^4` |
| 134 | 11 | one section cycle of length `133`, total time `m^4` |
| 182 | 11 | one section cycle of length `181`, total time `m^4` |
| 230 | 11 | fails: cycles `3,3,223`, total time is not `m^4` |

Conclusion: this fixed-constant law is not a modular branch.  It is useful as
a negative control because it shows why search hits must not be promoted from a
few samples alone.

Negative controls:

| candidate | observation |
| --- | --- |
| `m=86`, `x=5` | total time is `m^4`, but the section map splits into cycles `7,7,71` |
| `m=230`, `x=5` | section map splits and total time is not `m^4` |
| `m=230`, `x=11` | invalidates the fixed `R38-sym11` extrapolation |
| `m=162`, `x=9` | residue `18`; section map splits into cycles `3,3,11,11,133` and total time is not `m^4` |

These controls prevent the false extrapolation that every small symmetric
constant on a residue class gives a branch.

## Symmetric Probe 62..128

Command shape:

```bash
python3 scripts/search_d5_routeE_symmetric_packets.py \
  --moduli 62:128:2 \
  --x-values 1:31:2 \
  --timeout 8 \
  --jobs 8
```

Compact result by residue class:

| residue mod 48 | samples and successful `x` values | fixed `x` intersection |
| ---: | --- | --- |
| 0 | `96:[17,31]` | `[17,31]` |
| 2 | `98:[15,19]` | `[15,19]` |
| 4 | `100:[23]` | `[23]` |
| 6 | `102:[23]` | `[23]` |
| 8 | `104:[7,9,27,31]` | `[7,9,27,31]` |
| 10 | `106:[3,5,11,23,27]` | `[3,5,11,23,27]` |
| 12 | `108:[5,23]` | `[5,23]` |
| 14 | `62:[3,5,7,9,17,27]; 110:[9,19,31]` | `[9]` |
| 16 | `64:[11,15,23,27,31]; 112:[9,11,19]` | `[11]` |
| 18 | `66:[17,23]; 114:[11]` | `[]` |
| 20 | `68:[3,7,11,13,19,31]; 116:[5,9,15,19,27,31]` | `[19,31]` |
| 22 | `70:[9,11]; 118:[3,5,7,9,31]` | `[9]` |
| 24 | `72:[17,23]; 120:[23]` | `[23]` |
| 26 | `74:[3,5,7,9,11,13,23,27]; 122:[15,17,19,23,31]` | `[23]` |
| 28 | `76:[3,11,17,27]; 124:[23,27]` | `[27]` |
| 30 | `78:[5,17]; 126:[11,23]` | `[]` |
| 32 | `80:[31]; 128:[3,7,9,11,13,23,31]` | `[31]` |
| 34 | `82:[5,7,17,19,31]` | `[5,7,17,19,31]` |
| 36 | `84:[11]` | `[11]` |
| 38 | `86:[11,13,23,27,31]` | `[11,13,23,27,31]` |
| 40 | `88:[3,9,19,23,31]` | `[3,9,19,23,31]` |
| 42 | `90:[11,23]` | `[11,23]` |
| 44 | `92:[3,15,19,27]` | `[3,15,19,27]` |
| 46 | `94:[5,11,15]` | `[5,11,15]` |

Interpretation:

- Direct symmetric packets are abundant and likely sufficient to generate many
  local hits.
- Residues `18` and `30` did not have a fixed small `x` intersection in this
  first two-sample window, so they probably need either a larger `x` search, a
  parametric `x(k)`, or a broader support pattern.
- Existing proof-facing branches already cover `14,16,20,40,44 mod 48`, so
  symmetric hits on those residues are useful as controls but not urgent.
- A fixed `x` law can still fail after four successful samples, as `R38-sym11`
  does at `m=230`.  Therefore the symmetric packet probe is now classified as a
  branch-finder and falsifier, not as a branch proof method.

## Failure Criterion

For a proposed residue law to be worth promotion, it should stabilize with a
small closed formula.  If the search repeatedly requires splitting a residue
class into new exceptional subfamilies, the working hypothesis should be marked
false for Route E rather than chased indefinitely.

In the current run, fixed-constant symmetric packets show fragmentation:

```text
m = 48*k + 38, x = 11 succeeds for k = 0,1,2,3
m = 48*k + 38, x = 11 fails for k = 4

m = 48*k + 18, x = 9 is not a branch candidate at k = 3
```

This does not refute all Route-E even branches, but it refutes the simple
fixed-constant symmetric-packet hypothesis for that residue.

## Next Proof-Facing Promotion Steps

1. Prefer already proof-facing B20/B16/R14e-style laws over fixed symmetric
   constants.
2. For any new law, require at least one next-sample falsification check before
   fitting formulas.
3. Dump the all-pair/boundary maps only after the law survives the next sample.
4. Fit boundary and macro return formulas.
5. Prove no-early-return and time-exhaustion identities symbolically.
6. Promote the branch to a `RouteEAllPairSectionCertificate`-style endpoint.
7. Use the symmetric/support-pattern drivers only to discover the next residue
   candidate, not as a replacement for the modular proof package.
