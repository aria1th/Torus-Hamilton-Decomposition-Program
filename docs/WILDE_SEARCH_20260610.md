# H1b wild run-collapse realization — SOLVED design (rail-seam schedule), 2026-06-10

Target: the D3-even root-flat schedule hole (H1b, per-color form,
`EvenV11/Main.lean: assume_d3TerminalRealization` /
`RootFlatCycle.D3EvenCycleDataFamily`).  For every even `m ≥ 4`, construct
`dir : ZMod m → (ZMod m)² → TorusColor 3 → TorusDirection 3` with RF1 (Latin per
cell), RF2 (each layer map `L_{t,c} : w ↦ w + e_{dir(t,w,c)}` bijective,
`e₀=(1,0), e₁=(0,1), e₂=(0,0)`), RF3 (each `R_c = L_{m−1,c} ∘ ⋯ ∘ L_{0,c}` a
single `m²`-cycle).

**Outcome: a fully explicit, closed-form parametric construction (one wild
layer + m−1 constant layers) that passes exact RF1/RF2/RF3 verification for
every even `m ∈ [4, 60]`, including all `3 ∣ m` cases.**  Tool:
`scripts/search_d3_even_dir.py`; certificates:
`scripts/d3_even_dir_m{6,8,10,12}.json` (plus `m4` extracted from
`EvenV11/D3EvenM4.lean` as anchor).  This note records the parity calculus that
shaped the search, the (new, provable) negative results that kill all tame
ansatz families, the construction, and the Lean proof route.

---

## 1. Parity calculus (the load-bearing bookkeeping)

All statements below are for even `m`, state space `K = (ZMod m)²`.

* **(P1)** A single `m²`-cycle is an **odd** permutation (`m²` even).  So RF3
  forces `sign(R_c) = −1` for each color and `∏_c sign(R_c) = −1`.
* **(P2)** Every translation of `K` is an **even** permutation.  (Orbits of
  `T_v` are `⟨v⟩`-cosets; if `ord(v)` is odd each orbit is even; if `ord(v)` is
  even the orbit count `m²/ord(v) = m·(m/ord(v))` is even.)  In particular
  constant Latin layers contribute sign `+1` to every color.
* **(P3, deviation cycles)** Fix any constant Latin base `σ ∈ S₃` for a layer
  with table `π : K → S₃` (RF1/RF2).  The deviation
  `ρ_c := T_{e_{σ(c)}}^{−1} ∘ L_{t,c}`, i.e. `ρ_c(w) = w + e_{π_w(c)} − e_{σ(c)}`,
  is a permutation of `K` whose **every nontrivial cycle has length ≡ 0
  (mod m)**: along a cycle the steps lie in `{e_d − e_{σ(c)} : d ≠ σ(c)}` and
  the two step-counts must separately vanish mod `m` (telescoping in each
  coordinate).  Hence (m even) every nontrivial `ρ_c`-cycle is an **odd**
  permutation, and

  > `N(layer) := ∏_c sign(L_{t,c}) = (−1)^{total number of nontrivial
  > ρ-cycles over the three colors}` — independent of the chosen base.

* **(P4, schedule constraint)** `∏_t N(layer t) = ∏_c sign(R_c) = −1`, so
  **every valid even-m schedule contains an odd number of layers with
  `N = −1`**, i.e. layers whose three deviations have odd total cycle count.
  We call these *wild seams*.  (Cross-check: the `m=4` witness
  `D3EvenM4.lean`, pulled through the root-flat chart `t = x₀+x₁+x₂`,
  `w = (x₀,x₂)`, has layer `N`-vector `(+1,−1,−1,−1)` — three wild seams, each
  with per-color ρ-cycle counts `(1,1,1)`, lengths `(2m or 3m)`.)
* **(P5, pair swaps never flip N)** A legal two-color swap of `(α,β)` on `U`
  (legality `U + (e_β − e_α) = U`) changes `sign(L_α)` and `sign(L_β)` by the
  same factor `(−1)^{#δ-lines of U}` and leaves `N` unchanged — in general,
  for any pair move, the flip criterion is `|U| + |L_α(U) ∩ L_β(U)|` odd, and
  δ-invariance forces `|L_α(U) ∩ L_β(U)| = |U|`.  **Hence cut-splice designs
  built from constant bases by two-color line swaps alone can never satisfy
  RF3 for even m** (this is why the H2-style swap grammar stalls at one
  stuck color, observed as `score 1` plateaus in annealing).  Wild seams are
  genuinely 3-color-entangled and cannot be reached through RF2-legal
  intermediate pair swaps.

## 2. Negative results: every single-functional trigger family is dead

The mod-3 lattice obstruction (`H1B_REALIZATION_OBSTRUCTION_20260609.md` §1)
does **not** by itself rule out clock/trigger rules `dir(t,w,c) = f_c(t, ℓ(w))`
— those are state-dependent, not translation-equivariant.  They die anyway,
for sharper reasons (all verified numerically by
`search_d3_even_dir.py negative --m M`):

* **(N1) ℓ = y (and symmetrically ℓ = x).**  The induced stripe map
  `j ↦ j + [dir = e₁]` is bijective on `ZMod m` only if all-or-nothing, so per
  layer exactly one color is the y-mover; color c's y-drift is `r_c` = its
  mover-layer count, and the y-factor of `R_c` is `y ↦ y + r_c`, which must be
  transitive: `gcd(r_c, m) = 1`, i.e. `r_c` odd.  But `r₀+r₁+r₂ = m` is even.
  **Contradiction** (this is exactly why `TorusD3Odd`'s design works for odd m
  only: there `(1, 1, m−2)` are all coprime to odd m).
* **(N2) ℓ = x+y.**  Same all-or-nothing argument (both `e₀,e₁` advance the
  stripe); per layer one color reads `e₂` everywhere; moving-layer counts
  `n_c` need `gcd(n_c, m) = 1` and `n₀+n₁+n₂ = 2m`.  **Contradiction.**
* **(N3) ℓ = x−y.**  Richer family (stripe deltas `{+1,−1,0}` can mix), but a
  closed sign formula kills it: for a stripe-rule layer,
  `sign(L_{t,c}) = (−1)^{A_c}` where `A_c` = number of stripes on which c
  reads `e₀` (block-permutation sign computation, using `gcd(a,m) ≡ a mod 2`
  for even m).  Since each stripe gives `e₀` to exactly one color,
  `N(layer) = (−1)^{ΣA_c} = (−1)^m = +1` for **every** layer in the family —
  contradicting P4.  (Verified exhaustively: all 12/24/72 valid layers at
  m=2/4/6 have `N = +1`; for odd m the same formula gives `N = −1`
  automatically, consistent with odd-m feasibility.)
* **(N4) pure 3-cycle seams.**  The maximally entangled candidate seam (all
  cells 3-cycles, each `ρ_c` a single pure-line m-cycle… (1,1,1) with all
  cycles of length m) is impossible: per-color pure m-cycles must be
  δ-lines, and the S₃ consistency chain forces one set to be simultaneously a
  row, a column and an anti-diagonal (the closing recurrence demands
  `3 ≡ 0 (mod m)`).  Wild seams therefore need *mixed* cell types
  (transposition cells + zigzag routing), with per-color cycle lengths ≥ 2m.

These four no-gos plus P4/P5 fully explain why even-m D3 resisted every tame
design: **the schedule must contain a 3-color-entangled layer, and no
single linear functional ℓ can host one.**

## 3. The construction (rail-seam schedule)

Found by structured search (DFS over seam routing + exact drift scan), then
closed-formed.  `scripts/search_d3_even_dir.py construct --m M`.

### 3.1 The wild layer (one per schedule)

Three pairwise-disjoint m-cell sets ("rails"; indices mod m):

```
P = {(0,0)} ∪ {(x, m−x) : 3 ≤ x ≤ m−1} ∪ {(1, m−2), (2, m−1)}      (01-swap cells)
Q = {(x, m−1) : x ∈ {0} ∪ [3, m−1]}  ∪ {(1, 0),   (2, m−2)}        (02-swap cells)
S = {(2, y) : 0 ≤ y ≤ m−3}           ∪ {(1, m−1), (3, m−2)}        (12-swap cells)
```

Geometry: `P ≈` anti-diagonal `{x+y=0}`, `Q ≈` row `{y=m−1}`, `S ≈` column
`{x=2}`; the three pairwise crossing cells `(1,m−1) ∈ L_P∩L_Q`,
`(2,m−2) ∈ L_P∩L_S`, `(2,m−1) ∈ L_Q∩L_S` are **cyclically reassigned to the
third rail**, with three shifted replacement cells `(1,m−2), (1,0), (3,m−2)`
closing the routing.  The wild layer's table is `id` off `P∪Q∪S`, the
transposition `(01)`/`(02)`/`(12)` of colors on `P`/`Q`/`S` respectively.

Effect: each color's deviation `ρ_c` is a **single 2m-zigzag**
(`ρ₀` through `P∪Q` with steps `(−1,1)/(−1,0)`, `ρ₁` through `P∪S` with
`(1,−1)/(0,−1)`, `ρ₂` through `Q∪S` with `(1,0)/(0,1)`), so the layer maps are
bijective (RF2) and the total ρ-cycle count is 3 — odd — giving `N = −1`
exactly once in the schedule (P4 satisfied).  At `m = 4` this seam is the
**unique** rail seam up to translation, and it extends verbatim to every even
m.

### 3.2 The cheap layers and drifts

Layers `0..m−2` are constant Latin rows built from
`id : c ↦ c`, `ρ⁺ : c ↦ c+1`, `ρ⁺⁺ : c ↦ c+2` (colors→directions, mod 3):

| case | cheap-layer multiset | per-color conjugated drifts `u_c` (`R_c ≅ T_{u_c} ∘ ρ_c`) |
|---|---|---|
| `3 ∤ m` | `1×ρ⁺, (m−2)×ρ⁺⁺` | `u = ((1,1), (m−2,1), (1,m−2))` |
| `3 ∣ m` | `(m−5)×id, 1×ρ⁺, 3×ρ⁺⁺` | `u = ((m−4,1), (3,m−4), (1,3))` |

(Cheap-layer order is irrelevant — translations commute; the wild layer sits
at `t = m−1`.  `u_c = e_c + Σ_t e_{σ_t(c)}`; conjugating `R_c` by the cheap
translation gives `R_c ≅ T_{u_c} ∘ ρ_c`, so RF3 reduces to: *translation with
drift `u_c`, kicked along one explicit 2m-zigzag, is a single `m²`-cycle*.)
The mod-3 case split is the familiar one (`H1B` §1 said `3 ∣ m` is the hard
lattice case; here it only changes the drift constants).

### 3.3 Verification status (exact, full cycle checks)

* `construct-scan`: RF1/RF2/RF3 **pass for every even `m ∈ [4, 40]`**, and a
  continued scan passes `m ∈ [42, 60]`.  Nothing sampled — each check
  verifies the three full return permutations.
* Certificates (JSON, format documented in the file header):
  `scripts/d3_even_dir_m6.json`, `…m8…`, `…m10…`, `…m12.json` (canonical
  construction output, `verify --cert` re-checks them), plus
  `scripts/d3_even_dir_m4_from_lean.json` (the existing Lean witness
  `D3EvenM4` exported through the root-flat chart — sanity anchor for the
  chart conventions).
* Independent annealing search (JM-chase + line swaps with a parity-aware
  objective) also solved m=6 (iteration ~1.2k) and m=8 (~20k) from scratch,
  confirming solutions are not isolated; the structured construction is the
  one to formalize.

## 4. Lean proof route (proposed)

The hole consumed by `EvenV11/Main.lean` is
`RootFlatCycle.D3EvenCycleDataFamily : ∀ even m ≥ 4, Nonempty (RootFlatCycleData 2 m)`
(dir + RF1 + RF2 + RF3).  The per-color carrier form
(`TerminalA2PerColorRealizationFamily`) follows from RF3 by rank transport
(below).  Proposed modules:

1. **`EvenV11/V28Hard/D3EvenRailSeam.lean`** — the seam.
   * `P, Q, S : Finset ((ZMod m)²)` as decidable predicates (closed form
     above); disjointness + cardinality lemmas (mechanical case splits;
     the only seams touching small coordinates are at `x ∈ {0,1,2,3}`,
     `y ∈ {0, m−2, m−1}`).
   * `ρ_c` as explicit permutations: define forward maps, prove bijectivity by
     exhibiting the inverse region-by-region (each rail is ≤ 4 arithmetic
     runs; same style as `TerminalA2IntervalSplice` run lemmas).
   * The 2m-cycle traversal lemma per color (the run order is explicit, e.g.
     `ρ₀`: anti-diagonal run from `(0,0)` down to `(3,3)`, defect hop, row run,
     hop, close — O(1) runs of length O(m)).
   * `N = −1` is *not needed* by the proof — it was a search guide; only
     RF2 + RF3 enter the Lean obligations.
2. **`EvenV11/V28Hard/D3EvenRailSchedule.lean`** — the schedule.
   * `dir` (cheap constants by case `3 ∣ m`, wild layer at `m−1`); RF1 by
     cell-type cases; RF2: constants are translations
     (`Equiv.addRight`), wild layer maps are `T_{e_c} ∘ ρ_c`.
3. **`EvenV11/V28Hard/D3EvenRailReturn.lean`** — RF3.
   * Cheap-layer collapse: `R_c = (T_{e_c} ∘ ρ_c) ∘ T_{t_c}` and the
     conjugation `R_c ≅ T_{u_c} ∘ ρ_c` (translation conjugacy preserves
     cycle type — `Shared.single_cycle_of_equiv_conj`).
   * Core lemma per color and case: **`T_{u_c} ∘ ρ_c` is a single
     `m²`-cycle.**  Two viable engines, both in-repo:
     (a) *rank construction* — exhibit `rank_c : (ZMod m)² ≃ ZMod (m²)` with
     `rank(R_c w) = rank w + 1`; since `T_{u_c}` has exactly m orbits
     (all the chosen `u_c` have `ord(u_c) = m`: components include a unit or
     `gcd(m−4,m) ∈ {2,4}` with lcm m) and the seam's 2m kicks visit the
     orbits in an explicit pattern, the rank is piecewise affine with O(1)
     branches — heavier but gives the strongest payload;
     (b) *section/monodromy* — first-return to one `⟨u_c⟩`-coset through
     `Shared.Monodromy.sectionReturn_skewProductMap_eq_fiberIterate` +
     `ReturnLift.single_cycle_of_periodic_return_cover`: the coset-index
     dynamics is a `ZMod m` map (translation + explicit carry at the seam
     crossings), closed by `UnitCarry`.  Recommended: (b), it matches the
     D2/odd-m proofs one level up.
4. **Wiring** — provide `D3EvenCycleDataFamily` directly (replacing
   `assume_d3CycleData`'s two-input derivation), and *derive* the per-color
   realization: `e_c := rank_{F_c}⁻¹ ∘ rank_{R_c}` via
   `CompletionTower.rankEquiv_of_singleCycle` on both the schedule return
   (RF3) and the terminal carrier (H1a closed cyclicity) — this *is* the wild
   run-collapse reindexing, constructed rather than postulated; it fills
   `TerminalA2PerColorRealizationFamily.sectionEquiv/return_eq_terminal` and
   keeps `Main` unchanged if preferred.
5. **Optional negative theorems** (`D3EvenNegative.lean`, H2-precedent
   style): N1–N3 of §2 and P5 — finite `decide` at m=4/6 plus the parametric
   sign formula of N3.

### Remaining mathematical obligation (honest)

The single open proof item is 3(core): single-cyclicity of the six explicit
maps `T_{u_c} ∘ ρ_c` (3 colors × 2 mod-3 cases), parametric in m.  This is no
longer a *design* hole — the maps are concrete, low-complexity (translation +
one 2m-zigzag kick), with `m ∈ [4,60]` exact certification and an
odometer-style proof route.  Estimated comparable to the closed
`D2AntiDiagonal`/`TorusD3Odd.FullCycles` arguments (run-based induction), not
to H1a's interval splice.

## 5. Relation to neighboring holes

* **H2 (D5(4))**: the wild seam grammar explains the H2 observation that no
  pair-swap repair could fix the last color; the finite `native_decide`
  witness there could now be *replaced* by a structured schedule if desired
  (not urgent — H2 is closed).
* **H6/E6 (`EndpointRunCollapseRealization`)**: Wall 3's parity side-condition
  ("each line-cut is odd; donations come in even total") is the
  higher-dimensional shadow of P4/P5.  The rail-seam trick — route an odd
  number of 3-color zigzags through the crossing cells of the donation lines
  — is the prime candidate for the lane-color `q`-attachment, with the same
  `T_u ∘ ρ` return shape on the `(q, lane)` blocks.
* **Common-e H1b form** (`TerminalA2RootFlatRealizationFamily`): not needed by
  `Main` anymore (per-color suffices); if ever wanted, the rank-transport
  `e_c` differ per color only through `rank_{R_c}`, so a common `e` would
  need the three rank functions aligned — no obstruction known, but no need.

## 6. Reproduction

```
python3 scripts/search_d3_even_dir.py construct-scan --mmax 40   # full sweep
python3 scripts/search_d3_even_dir.py construct --m 12           # one case, verbose
python3 scripts/search_d3_even_dir.py verify --cert scripts/d3_even_dir_m12.json
python3 scripts/search_d3_even_dir.py negative --m 6             # no-go checks
python3 scripts/search_d3_even_dir.py analyze --cert scripts/d3_even_dir_m6.json
python3 scripts/search_d3_even_dir.py search --m 6 --mode general --seed 2  # independent annealer
python3 scripts/search_d3_even_dir.py export-m4                  # chart anchor
```
